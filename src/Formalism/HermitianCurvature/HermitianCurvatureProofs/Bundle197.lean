module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutER
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle083
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle090
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle069
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle084
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle070
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SeminormCompletion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftVectorZeroBlock
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModuleFormEqRadialFormOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle187
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadicalUnipotentFirstBasisEqOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.CutMP.ER

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section consts

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rw_const (a : E) : ∀ v : List (B.Mat k r),
    B.Rw v (fun _ => a) = (fun _ => a) ∨ B.Rw v (fun _ => a) = (fun _ => (0 : E))
  | [] => Or.inl rfl
  | X :: v => by
    right
    funext g
    simp only [B.Rw, List.foldr_cons]
    rcases rw_const a v with h | h
    · simp only [B.Rw] at h
      rw [h]; simp [RdV]
    · simp only [B.Rw] at h
      rw [h]; simp [RdV]

theorem dLR_const (a : E) (u v : List (B.Mat k r)) :
    B.dLR u v (fun _ => a) = (fun _ => a) ∨ B.dLR u v (fun _ => a) = (fun _ => (0 : E)) := by
  induction u with
  | nil => exact rw_const a v
  | cons X u ih =>
    right
    simp only [Formalism.FourierDecayAlt.B.dLR, List.foldr_cons] at ih ⊢
    rcases ih with h | h <;> (rw [h]; funext g; simp [Formalism.FourierDecayAlt.B.LdV])

theorem norm_dLR_const_le (a : E) (u v : List (B.Mat k r)) (g : B.Mat k r) : ‖B.dLR u v (fun _ => a) g‖ ≤ ‖a‖ := by
  rcases dLR_const a u v with h | h <;> simp [h]

theorem ckOn_const' {m : ℕ∞} {UU : Set (B.Mat k r)} (a : E) : B.CkOn m UU (fun _ => a) := by
  intro g₀ _
  exact ⟨Set.univ, fun _ => a, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

end consts

theorem mem_capOp {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (s : ℂ)
    (Lw : List (ℂ × List (B.Mat k r))) {T : B.DTerm k r Wp Wq} (hT : T ∈ TLB.capOp k r Wp Wq s Lw) :
    ∃ (c : ℂ) (w : List (B.Mat k r)), T = TLB.cTerm c w := by
  unfold TLB.capOp at hT
  rcases List.mem_cons.1 hT with h | h
  · exact ⟨0, _, h⟩
  · obtain ⟨cw, -, rfl⟩ := List.mem_map.1 h
    exact ⟨_, _, rfl⟩

theorem capacity_theta_facts : CapThFacts := by
  intro k r Wp Wq _ _ _ _ _ _ D s Y ε m
  obtain ⟨hLw, hCV⟩ := Classical.choose_spec (Formalism.FourierDecayAlt.P.capelli_word_sum k r Y)
  have hLie : ∀ cw ∈ capLw k r Y, ∀ X ∈ cw.2, B.inLie k r X := fun cw h X hX => ((hLw cw h).1 X hX).1
  have hlen : ∀ cw ∈ capLw k r Y, cw.2.length ≤ 2 * r + k + 1 := fun cw h => (hLw cw h).2
  have hord : B.opOrder (capTh k r Wp Wq s Y) = 2 * r + k + 1 := TLB.opOrder_capOp s _ hlen
  have hApp : ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (B.GV k r) F →
      ∀ g ∈ B.GV k r, B.opApply (capTh k r Wp Wq s Y) F g = s • Q.CV k r Y F g := by
    intro F hF g hg
    unfold capTh
    rw [TLB.opApply_capOp s _ hLie, hCV _ _ F hF g hg hg]
    rfl
  refine ⟨hord, ?_, ?_, ?_, hApp⟩
  · intro T hT
    obtain ⟨c, w, rfl⟩ := mem_capOp s _ hT
    exact ⟨ckOn_const' _, ckOn_const' _⟩
  · intro p hp f hf g hg
    rw [hord] at hf
    have hgG : g ∈ B.GV k r := hg.1
    have hs' := Formalism.FourierDecayAlt.P.B7.sgs_mem D hp hgG
    rw [hApp _ (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hf) g hgG,
      Formalism.FourierDecayAlt.P.capelli_rho_commute k r Wp Wq D Y f p hp hf g hgG]
    simp only [B.rho]
    rw [hApp f hf _ hs', ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  · intro T hT
    obtain ⟨c, w, rfl⟩ := mem_capOp s _ hT
    refine ⟨‖c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)‖ + ‖conj c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)‖,
      fun u v _ _ _ g _ _ => ?_⟩
    rw [Real.rpow_zero, mul_one]
    have h1 := norm_dLR_const_le (c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) u v g
    have h2 := norm_dLR_const_le (conj c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) u v g
    have n1 := norm_nonneg (c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))
    have n2 := norm_nonneg (conj c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))
    exact ⟨by simp only [TLB.cTerm]; linarith, by simp only [TLB.cTerm]; linarith⟩

theorem beta_form_congr_holds : BetaCongr := by
  intro k r Wp Wq _ _ _ _ _ _ D F F₁ F' F₁' hF hF'
  unfold B.beta
  refine Formalism.FourierDecayAlt.P.JFxG.betaBig_congr D (fun g hg => ?_) (fun g hg => ?_)
  · have h := Formalism.FourierDecayAlt.P.Qx8.JF_congr D (F := F) (F' := F₁) (a := 1) (fun g hg => by rw [one_smul, hF g hg]) hg.1
    rw [h, one_smul]
  · have h := Formalism.FourierDecayAlt.P.Qx8.JF_congr D (F := F') (F' := F₁') (a := 1) (fun g hg => by rw [one_smul, hF' g hg]) hg.1
    rw [h, one_smul]

end

end Formalism.FourierDecayAlt.P.CutMP.ER
end

section

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.ER

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem coefficient_vector_in_class : CVCC := by
  intro k r Wp Wq _ _ _ _ _ _ s Y A m F _ hF
  exact Formalism.FourierDecayAlt.P.CutMP.En.coefficient_vector_in_L2_class k r _ A m F Y s hF

theorem coefficient_vector_congr : CVCongr := by
  intro k r Wp Wq _ _ _ _ _ _ s Y F F₁ hF hF₁ heq g hg
  have hmono : ∀ G : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) G →
      B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (Set.univ ∩ B.GV k r) G := by
    intro G hG g₀ hg₀
    obtain ⟨U, f', hU, hgU, hcd, hfe⟩ := hG g₀ hg₀.2
    exact ⟨U, f', hU, hgU, hcd.of_le (WithTop.coe_le_coe.mpr le_top), hfe⟩
  have h := Formalism.FourierDecayAlt.P.CutMP.En.coefficient_vector_locality k r (Wq →L[ℂ] Wp) Set.univ F F₁ Y isOpen_univ
    (hmono F hF) (hmono F₁ hF₁) (fun x hx => heq x hx.2) g ⟨trivial, hg⟩
  simp only [Pi.smul_apply]
  rw [h]

theorem cV_zero {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (Y : ℂ) :
    Q.CV k r Y (0 : B.Mat k r → E) = 0 := by
  have hop : ∀ (u : ℂ) (a b : Fin (2 * r + k + 1)),
      Formalism.QuantumDeterminants.Top (Q.EH k r) u a b (0 : B.Mat k r → E) = 0 := by
    intro u a b
    funext g
    simp [Formalism.QuantumDeterminants.Top, Q.EH, Formalism.QuantumDeterminants.EabH, Formalism.REAL.RdV]
  have hfold : ∀ l : List ((B.Mat k r → E) → (B.Mat k r → E)), (∀ T ∈ l, T 0 = 0) →
      l.foldr (fun T h => T h) 0 = 0 := by
    intro l hl
    induction l with
    | nil => rfl
    | cons T l ih =>
      simp only [List.foldr_cons]
      rw [ih (fun T' hT' => hl T' (List.mem_cons_of_mem _ hT'))]
      exact hl T List.mem_cons_self
  unfold Q.CV Q.capL Formalism.QuantumDeterminants.qminorOp
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [hfold _ ?_, smul_zero]
  intro T hT
  rw [List.mem_ofFn] at hT
  obtain ⟨i, rfl⟩ := hT
  exact hop _ _ _

theorem coefficient_vector_support : CVSupp := by
  intro k r Wp Wq _ _ _ _ _ _ z z' c s Y F hF hsupp g hg hne
  by_contra hlt
  push_neg at hlt
  have hU : IsOpen {x | Gf k r z z' x < c} :=
    isOpen_lt (Formalism.FourierDecayAlt.P.Ux8.cont_Gf k r z z') continuous_const
  have hF0 : ∀ x ∈ {x | Gf k r z z' x < c} ∩ B.GV k r,
      F x = (0 : B.Mat k r → (Wq →L[ℂ] Wp)) x := by
    intro x hx
    by_contra hne'
    exact absurd (hsupp x hx.2 hne') (not_le.mpr hx.1)
  have hCk0 : B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) ({x | Gf k r z z' x < c} ∩ B.GV k r)
      (0 : B.Mat k r → (Wq →L[ℂ] Wp)) :=
    fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  have hCkF : B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) ({x | Gf k r z z' x < c} ∩ B.GV k r) F := by
    intro g₀ hg₀
    obtain ⟨U, f', hU', hgU, hcd, hfe⟩ := hF g₀ hg₀.2
    exact ⟨U, f', hU', hgU, hcd.of_le (WithTop.coe_le_coe.mpr le_top), hfe⟩
  have h := Formalism.FourierDecayAlt.P.CutMP.En.coefficient_vector_locality k r (Wq →L[ℂ] Wp) {x | Gf k r z z' x < c} F 0 Y hU
    hCkF hCk0 hF0 g ⟨hlt, hg⟩
  apply hne
  simp only [Pi.smul_apply]
  rw [h, cV_zero, Pi.zero_apply, smul_zero]

theorem coefficient_vector_smoothness : CVSmooth := by
  intro k r Wp Wq _ _ _ _ _ _ s Y F hF
  have hadd : ∀ {f g : B.Mat k r → (Wq →L[ℂ] Wp)}, B.CkOn ⊤ (B.GV k r) f → B.CkOn ⊤ (B.GV k r) g →
      B.CkOn ⊤ (B.GV k r) (f + g) := by
    intro f g hf hg g₀ hg₀
    obtain ⟨U1, f1, hU1, h1, hc1, he1⟩ := hf g₀ hg₀
    obtain ⟨U2, f2, hU2, h2, hc2, he2⟩ := hg g₀ hg₀
    refine ⟨U1 ∩ U2, f1 + f2, hU1.inter hU2, ⟨h1, h2⟩,
      (hc1.mono Set.inter_subset_left).add (hc2.mono Set.inter_subset_right), ?_⟩
    intro x hx hxG
    simp [he1 x hx.1 hxG, he2 x hx.2 hxG]
  have hsmul : ∀ (c : ℂ) {f : B.Mat k r → (Wq →L[ℂ] Wp)}, B.CkOn ⊤ (B.GV k r) f →
      B.CkOn ⊤ (B.GV k r) (c • f) := by
    intro c f hf g₀ hg₀
    obtain ⟨U1, f1, hU1, h1, hc1, he1⟩ := hf g₀ hg₀
    refine ⟨U1, c • f1, hU1, h1, hc1.const_smul c, ?_⟩
    intro x hx hxG
    simp [he1 x hx hxG]
  have hzero : B.CkOn ⊤ (B.GV k r) (0 : B.Mat k r → (Wq →L[ℂ] Wp)) :=
    fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  have hrd : ∀ X : B.Mat k r, B.inLie k r X → ∀ {f : B.Mat k r → (Wq →L[ℂ] Wp)},
      B.CkOn ⊤ (B.GV k r) f → B.CkOn ⊤ (B.GV k r) (Formalism.REAL.RdV X f) := by
    intro X hX f hf
    have h1 : B.CkOn ((⊤ : ℕ∞) + 1) (B.GV k r) f := by
      rw [top_add]
      exact hf
    exact Formalism.FourierDecayAlt.P.B5.ckOn_RdV hX h1
  have hTop : ∀ (u : ℂ) (a b : Fin (2 * r + k + 1)) {f : B.Mat k r → (Wq →L[ℂ] Wp)},
      B.CkOn ⊤ (B.GV k r) f → B.CkOn ⊤ (B.GV k r) (Formalism.QuantumDeterminants.Top (Q.EH k r) u a b f) := by
    intro u a b f hf
    have e : Formalism.QuantumDeterminants.Top (Q.EH k r) u a b f = (if a = b then u • f else 0) +
        (Formalism.REAL.RdV (hpart1 (Hpk k r) (Matrix.single a b 1)) f +
          Complex.I • Formalism.REAL.RdV (hpart2 (Hpk k r) (Matrix.single a b 1)) f) := by
      funext g
      simp only [Formalism.QuantumDeterminants.Top, Q.EH, Formalism.QuantumDeterminants.EabH, Pi.add_apply, Pi.smul_apply]
      split_ifs <;> simp
    rw [e]
    refine hadd ?_ (hadd (hrd _ (Formalism.FourierDecayAlt.P.Qb1.lie1 _) hf) (hsmul _ (hrd _ (Formalism.FourierDecayAlt.P.Qb1.lie2 _) hf)))
    split_ifs
    · exact hsmul u hf
    · exact hzero
  have hfold : ∀ l : List ((B.Mat k r → (Wq →L[ℂ] Wp)) → (B.Mat k r → (Wq →L[ℂ] Wp))),
      (∀ T ∈ l, ∀ f, B.CkOn ⊤ (B.GV k r) f → B.CkOn ⊤ (B.GV k r) (T f)) →
      ∀ f, B.CkOn ⊤ (B.GV k r) f → B.CkOn ⊤ (B.GV k r) (l.foldr (fun T h => T h) f) := by
    intro l hl f hf
    induction l with
    | nil => exact hf
    | cons T l ih =>
      simp only [List.foldr_cons]
      exact hl T List.mem_cons_self _ (ih (fun T' hT' => hl T' (List.mem_cons_of_mem _ hT')))
  apply hsmul s
  unfold Q.CV Q.capL Formalism.QuantumDeterminants.qminorOp
  refine Finset.sum_induction _ (fun f => B.CkOn ⊤ (B.GV k r) f) (fun a b ha hb => hadd ha hb) hzero ?_
  intro σ _
  apply hsmul
  refine hfold _ ?_ F hF
  intro T hT f hf
  rw [List.mem_ofFn] at hT
  obtain ⟨i, rfl⟩ := hT
  exact hTop _ _ _ hf

end Formalism.FourierDecayAlt.P.CutMP.ER
end

section

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

section cell

variable {k ρ : ℕ}

theorem finRange_one_add (ρ : ℕ) :
    List.finRange (1 + ρ) = (⟨0, by omega⟩ : Fin (1 + ρ)) :: (List.finRange ρ).map PBH.shS := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    rcases i with _ | i
    · simp
    · simp [PBH.shS]

theorem weyl_cell_shift_eq_level_embedding (a : Fin ρ) (x : ℂ) : w1 k (1 + ρ) (PBH.shS a) x = ιLev k 1 ρ (w1 k ρ a x) := by
  ext ⟨p, hp⟩ ⟨q, hq⟩
  have ha := a.isLt
  unfold w1 ιLev
  simp only [eI, esI, PBH.shS, Fin.mk.injEq]
  split_ifs <;> first | rfl | (exfalso; omega) | (simp_all; done) | (simp_all; omega)

theorem iota_list_prod (l : List (Mx k ρ)) : ιLev k 1 ρ l.prod = (l.map (ιLev k 1 ρ)).prod := by
  induction l with
  | nil => simpa using Formalism.FourierDecayAlt.P.Dx2.Tower.lev_one (k := k) 1 ρ
  | cons a l ih => rw [List.prod_cons, Formalism.FourierDecayAlt.P.Dx2.Tower.lev_mul, ih, List.map_cons, List.prod_cons]

theorem wCell_consC (t : ℂ) (c : Fin ρ → ℂ) :
    wCell k (1 + ρ) (Fin.last (1 + ρ)) (PBH.consC t c) =
      w1 k (1 + ρ) ⟨0, by omega⟩ t * ιLev k 1 ρ (wCell k ρ (Fin.last ρ) c) := by
  unfold wCell
  rw [List.filter_eq_self.2 (fun a _ => by simp),
    List.filter_eq_self.2 (fun a _ => by simp), finRange_one_add, iota_list_prod]
  rw [List.map_cons, List.prod_cons, PBH.consC_zero, List.map_map, List.map_map]
  congr 2
  refine List.map_congr_left (fun a _ => ?_)
  simp only [Function.comp, PBH.consC_sh, weyl_cell_shift_eq_level_embedding]

theorem weyl_cell_zero_eq_embedding {t : ℂ} (ht : t ≠ 0) :
    w1 k (1 + ρ) ⟨0, by omega⟩ t = U.mMap k 1 ρ (Matrix.of fun _ _ => t) 1 := by
  have hinv : ((Matrix.of fun _ _ : Fin 1 => t)ᴴ)⁻¹ = Matrix.of fun _ _ : Fin 1 => (star t)⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    ext a b
    fin_cases a; fin_cases b
    simp [Matrix.mul_apply, ht]
  ext i l
  obtain ⟨x, rfl⟩ := (U.eB k 1 ρ).surjective i
  obtain ⟨y, rfl⟩ := (U.eB k 1 ρ).surjective l
  rw [U.mMap, PBH.weyl_lift_eq_pair, Matrix.mul_one, Matrix.one_mul, hinv, Ux3.block3_apply]
  have hX : ∀ x : Fin 1, U.eB k 1 ρ (Sum.inl (Sum.inl x)) = ⟨0, by omega⟩ := fun x =>
    Fin.ext (by rw [Ux3.block_index_first_val]; simp)
  have hV : ∀ v : Fin (2 * ρ + k + 1), U.eB k 1 ρ (Sum.inl (Sum.inr v)) = ⟨1 + v.val, by omega⟩ := fun v =>
    Fin.ext (by rw [Ux3.block_index_middle_val])
  have hS : ∀ x : Fin 1, U.eB k 1 ρ (Sum.inr x) = ⟨2 * (1 + ρ) + k, by omega⟩ := fun x =>
    Fin.ext (by rw [Ux3.block_index_last_val]; have := x.isLt; simp; omega)
  rcases x with ((x | x) | x) <;> rcases y with ((y | y) | y) <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_apply, Matrix.of_apply, Matrix.one_apply, hX, hV, hS] <;>
    unfold w1 <;>
    simp only [eI, esI, Fin.ext_iff] <;>
    (have hx := x.isLt; have hy := y.isLt; split_ifs <;> first | rfl | (exfalso; omega) | (simp_all; done) | (simp_all; omega))

theorem cell_iota {t : ℂ} (ht : t ≠ 0) (c : Fin ρ → ℂ) (g : Mx k ρ) :
    wCell k (1 + ρ) (Fin.last (1 + ρ)) (PBH.consC t c) * ιLev k 1 ρ g =
      U.mMap k 1 ρ (Matrix.of fun _ _ => t) (wCell k ρ (Fin.last ρ) c * g) := by
  rw [wCell_consC, Matrix.mul_assoc, ← Formalism.FourierDecayAlt.P.Dx2.Tower.lev_mul, weyl_cell_zero_eq_embedding ht,
    ← Formalism.FourierDecayAlt.P.Dx2.MN.embG_eq, Formalism.FourierDecayAlt.P.Ux4.mMap_mul_embG, Matrix.one_mul]

theorem gauge_consC (t : ℂ) (c : Fin ρ → ℂ) :
    (∏ a : Fin (1 + ρ), (if a.val < (Fin.last (1 + ρ)).val then ‖PBH.consC t c a‖ ^ (Mdim k (1 + ρ) a - 1)
      else 1 : ℝ)) =
      ‖t‖ ^ (2 * (1 + ρ) + k) *
        ∏ a : Fin ρ, (if a.val < (Fin.last ρ).val then ‖c a‖ ^ (Mdim k ρ a - 1) else 1 : ℝ) := by
  rw [Finset.prod_congr rfl (fun a _ => if_pos (by rw [Fin.val_last]; exact a.isLt)),
    Finset.prod_congr rfl (fun (a : Fin ρ) _ => if_pos (by rw [Fin.val_last]; exact a.isLt))]
  rw [← Fintype.prod_equiv (finCongr (Nat.add_comm ρ 1))
    (fun a : Fin (ρ + 1) => ‖PBH.consC t c (finCongr (Nat.add_comm ρ 1) a)‖ ^
      (Mdim k (1 + ρ) (finCongr (Nat.add_comm ρ 1) a) - 1)) _ (fun _ => rfl)]
  rw [Fin.prod_univ_succ]
  refine congrArg₂ (· * ·) ?_ ?_
  · have h0 : finCongr (Nat.add_comm ρ 1) (0 : Fin (ρ + 1)) = ⟨0, by omega⟩ := Fin.ext rfl
    rw [h0, PBH.consC_zero]
    congr 1
  · refine Finset.prod_congr rfl fun a _ => ?_
    have hs : finCongr (Nat.add_comm ρ 1) a.succ = PBH.shS a := Fin.ext (by simp [PBH.shS])
    rw [hs, PBH.consC_sh]
    congr 1
    simp only [Mdim, PBH.shS]
    omega

theorem resG_consC {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {t : ℂ} (ht : t ≠ 0)
    (J : Mx k (1 + ρ) → E) (c : Fin ρ → ℂ) (g : Mx k ρ) :
    resG k (1 + ρ) (Fin.last (1 + ρ)) J (PBH.consC t c) (ιLev k 1 ρ g) =
      ((‖t‖ ^ (2 * (1 + ρ) + k) : ℝ) : ℂ) •
        resG k ρ (Fin.last ρ) (fun γ => J (U.mMap k 1 ρ (Matrix.of fun _ _ => t) γ)) c g := by
  unfold resG
  rw [cell_iota ht, smul_smul, gauge_consC, ← Complex.ofReal_mul]

theorem resG_cast {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ} (hn : n = 1 + ρ) {t : ℂ} (ht : t ≠ 0)
    (J : Mx k n → E) (c : Fin ρ → ℂ) (g : Mx k ρ) :
    resG k n (Fin.last n) J (fun l => PBH.consC t c (Fin.cast hn l)) (D.castM hn.symm (ιLev k 1 ρ g)) =
      ((‖t‖ ^ (2 * n + k) : ℝ) : ℂ) •
        resG k ρ (Fin.last ρ) (fun γ => J (D.castM hn.symm (U.mMap k 1 ρ (Matrix.of fun _ _ => t) γ))) c g := by
  subst hn
  simp only [Fin.cast_eq_self, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  exact resG_consC ht J c g

end cell

end Formalism.FourierDecayAlt.P.PBP

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBP

theorem pb_radHead_of_headPic (hHP : HeadPic) : KB.RadHead :=
  pb_radHead_of module_form_eq_radial_form_one exists_zeta_normalized_haar hHP

end Formalism.FourierDecayAlt.P
end
end
