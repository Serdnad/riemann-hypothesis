module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
public import Mathlib.Algebra.Module.Lattice.Full
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledBasisMemChainLattice
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle009
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle041
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.ChainLattice

theorem exists_smul_mem {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    (M : Submodule R V) {v : V} (hv : v ∈ Submodule.span K (M : Set V)) :
    ∃ a : R, a ≠ 0 ∧ a • v ∈ M := by
  first
  | (rename_i h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11; revert R K V h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 M v hv; exact @_root_.GlobalTheory.SmulMemOfMemSpan.main)
  | exact @_root_.GlobalTheory.SmulMemOfMemSpan.main
  | exact _root_.GlobalTheory.SmulMemOfMemSpan.main
  | (apply _root_.GlobalTheory.SmulMemOfMemSpan.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmulMemOfMemSpan.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmulMemOfMemSpan.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmulMemOfMemSpan.main ..)

theorem span_eq_top_of_smul_mem {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    (M : Submodule R V) (h : ∀ v : V, ∃ a : R, a ≠ 0 ∧ a • v ∈ M) :
    Submodule.span K (M : Set V) = ⊤ := by
  first
  | (rename_i h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11; revert R K V h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 M h; exact @_root_.GlobalTheory.LemmaTwoFortyThirteen.main)
  | exact @_root_.GlobalTheory.LemmaTwoFortyThirteen.main
  | exact _root_.GlobalTheory.LemmaTwoFortyThirteen.main
  | (apply _root_.GlobalTheory.LemmaTwoFortyThirteen.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LemmaTwoFortyThirteen.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LemmaTwoFortyThirteen.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LemmaTwoFortyThirteen.main ..)

theorem isLattice_chainLat_and_comap :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (n : Type) [Fintype n] [DecidableEq n] (c : ℕ),
      (∀ (ϖ : 𝒪[k]), (ϖ : k) ≠ 0 → ∀ L : Submodule 𝒪[k] (n → k), Submodule.IsLattice k L →
        Submodule.IsLattice k (chainLat ϖ c L)) ∧
      ∀ Λ : Submodule 𝒪[k] (n ⊕ Fin c → k), Submodule.IsLattice k Λ →
        Submodule.IsLattice k (Λ.comap (inX k n c)) := by
  intro k _ _ _ _ n _ _ c
  refine ⟨fun ϖ hϖ L hL => ⟨?_, ?_⟩, fun Λ hΛ => ⟨?_, ?_⟩⟩
  · exact (hL.fg.map _).sup (Submodule.fg_span (Set.finite_range _))
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
  · refine Submodule.fg_of_fg_map_injective (inX k n c) ?_
      (hΛ.fg.of_le (Submodule.map_comap_le _ _))
    intro x y hxy
    funext r
    have := congrFun hxy (Sum.inl r)
    simpa [inX_apply] using this
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli

end GlobalTheory.RootEx.ChainLattice
end

section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.UnfoldShape

theorem stabiliser_finite_cosets_mod (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) [Fintype ι] [DecidableEq ι] (ϖ : 𝒪[k])
    (M : Submodule 𝒪[k] (ι → k)) (S : Finset (ι → k)) (hM : M.FG) (hS : IsReps ϖ M S) :
    ∃ T : Finset (GL ι k), (∀ t ∈ T, act t M = M) ∧ ∀ t : GL ι k, act t M = M →
      ∃ t₀ ∈ T, ∃ j : GL ι k, act j M = M ∧ MapsInto (j.val - 1) M (ϖ • M) ∧ t = t₀ * j := by
  classical
  obtain ⟨s, hs⟩ := hM
  have hmem : ∀ t : GL ι k, act t M = M → ∀ x ∈ M, t.val *ᵥ x ∈ M := fun t ht x hx => by
    have h : t.val *ᵥ x ∈ act t M := mem_act.2 ⟨x, hx, rfl⟩
    rwa [ht] at h
  have hsM : ∀ x : s, x.1 ∈ M := fun x => hs ▸ Submodule.subset_span x.2
  have hex : ∀ (t : {t : GL ι k // act t M = M}) (x : s), ∃ r : S, t.1.val *ᵥ x.1 - r.1 ∈ ϖ • M := by
    intro t x
    obtain ⟨r, hr, -⟩ := hS.2 _ (hmem t.1 t.2 x.1 (hsM x))
    exact ⟨⟨r, hr.1⟩, hr.2⟩
  choose f hf using hex
  have hsec : ∀ y : Set.range f, ∃ t, f t = y.1 := fun y => y.2
  choose g hg using hsec
  have : Fintype (Set.range f) := Fintype.ofFinite _
  refine ⟨Finset.univ.image fun y => (g y).1, ?_, fun t ht => ?_⟩
  · intro t ht
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 ht
    exact (g y).2
  · set t₀ := g ⟨f ⟨t, ht⟩, ⟨_, rfl⟩⟩ with ht₀
    have hft : f t₀ = f ⟨t, ht⟩ := hg _
    have hinv : act (t₀.1)⁻¹ M = M := by
      have h := act_mul (t₀.1)⁻¹ t₀.1 M
      rw [inv_mul_cancel, act_one, t₀.2] at h
      exact h.symm
    refine ⟨t₀.1, Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, (t₀.1)⁻¹ * t, ?_, ?_, ?_⟩
    · rw [act_mul, ht, hinv]
    · intro v hv
      rw [← hs] at hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        have h1 := hf ⟨t, ht⟩ ⟨x, hx⟩
        have h2 := hf t₀ ⟨x, hx⟩
        rw [hft] at h2
        have h3 := sub_mem h1 h2
        rw [sub_sub_sub_cancel_right] at h3
        obtain ⟨w, hw, hw'⟩ := mem_smul_iff.1 h3
        refine mem_smul_iff.2 ⟨_, hmem _ hinv w hw, ?_⟩
        rw [← Matrix.mulVec_smul, hw', Matrix.mulVec_sub, Matrix.sub_mulVec, Matrix.mulVec_mulVec,
          Matrix.mulVec_mulVec, Units.inv_mul, Units.val_mul]
      | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
      | smul a x _ hx =>
        rw [Matrix.mulVec_smul]
        exact Submodule.smul_mem _ a hx
    · rw [mul_inv_cancel_left]

end GlobalTheory.RootEx.UnfoldShape
end

section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

noncomputable section
namespace GlobalTheory.RootEx.UnfoldFlag

variable {k : Type} [Field k] [ValuativeRel k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def flagMat (y : Fin c → (n ⊕ Fin c → k)) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k :=
  Matrix.of fun r s =>
    Sum.elim (fun s => (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (Sum.inl s)) (fun i => y i r) s

theorem flagMat_mulVec (y : Fin c → (n ⊕ Fin c → k)) (v : n ⊕ Fin c → k) :
    flagMat y *ᵥ v = inX k n c (fun r => v (Sum.inl r)) + ∑ i, v (Sum.inr i) • y i := by
  funext r
  rw [inX_apply]
  simp only [mulVec, dotProduct, flagMat, of_apply, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  · rcases r with r | l
    · simp [Matrix.one_apply]
    · simp [one_apply]
  · exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem flagMat_uni {y : Fin c → (n ⊕ Fin c → k)} (hY : ∀ i, y i ∈ Yle k n c (i.val + 1))
    (h1 : ∀ i, y i (Sum.inr i) = 1) (h0 : ∀ i : Fin c, i.val = 0 → ∀ r, y i (Sum.inl r) = 0) :
    Radical.Uni (lev 1) (flagMat y) := by
  intro r s hrs
  rcases s with s | i
  · simp [flagMat]
  · simp only [flagMat, of_apply, Sum.elim_inr]
    rcases r with r | l
    · have hi : i.val = 0 := by
        simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs
        omega
      rw [h0 i hi r, one_apply_ne (by simp)]
    · simp only [lev, Sum.elim_inr] at hrs
      rcases Nat.lt_or_eq_of_le hrs with h | h
      · rw [(mem_Yle.mp (hY i)) l h,
          one_apply_ne (fun e => by simp only [Sum.inr.injEq] at e; subst e; omega)]
      · have e : i = l := Fin.ext (by omega)
        subst e
        rw [h1, one_apply_eq]

theorem exists_unipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (hc : 1 ≤ c) (ϖ : 𝒪[k]), (ϖ : k) ≠ 0 → ∀ Λ : Submodule 𝒪[k] (n ⊕ Fin c → k), (∀ i : Fin c, (Λ ⊓ Yle k n c (i.val + 1)).map (LinearMap.proj (Sum.inr i)) = Submodule.span 𝒪[k] {(ϖ : k) ^ (i.val + 1)}) → (ϖ : k) • aux k n (⟨0, hc⟩ : Fin c) ∈ Λ → ∃ u ∈ N k n c 1, act u Λ = chainLat ϖ c (Λ.comap (inX k n c)) := by
  intro k _ _ _ _ n _ _ c hc ϖ hϖ Λ hΛ hfirst
  have hpow : ∀ i : Fin c, (ϖ : k) ^ (i.val + 1) ≠ 0 := fun i => pow_ne_zero _ hϖ

  have hpick : ∀ i : Fin c, ∃ w : n ⊕ Fin c → k, w ∈ Λ ∧ w ∈ Yle k n c (i.val + 1) ∧
      w (Sum.inr i) = (ϖ : k) ^ (i.val + 1) ∧ (i.val = 0 → ∀ r, w (Sum.inl r) = 0) := by
    intro i
    by_cases hi : i.val = 0
    · have e : i = ⟨0, hc⟩ := Fin.ext hi
      subst e
      refine ⟨(ϖ : k) • aux k n (⟨0, hc⟩ : Fin c), hfirst, ?_, ?_, fun _ r => ?_⟩
      · rw [mem_Yle]
        intro l hl
        have hl0 : l ≠ ⟨0, hc⟩ := fun e => by subst e; simp at hl
        simp [aux, hl0]
      · simp [aux]
      · simp [aux]
    · have hmem : (ϖ : k) ^ (i.val + 1) ∈
          (Λ ⊓ Yle k n c (i.val + 1)).map (LinearMap.proj (R := 𝒪[k]) (Sum.inr i)) := by
        rw [hΛ i]
        exact Submodule.mem_span_singleton_self _
      obtain ⟨w, hw, hwi⟩ := Submodule.mem_map.1 hmem
      exact ⟨w, (Submodule.mem_inf.1 hw).1, (Submodule.mem_inf.1 hw).2, hwi, fun h => absurd h hi⟩
  choose w hwΛ hwY hw1 hw0 using hpick

  obtain ⟨y, hy⟩ : ∃ y : Fin c → (n ⊕ Fin c → k), ∀ i, y i = ((ϖ : k) ^ (i.val + 1))⁻¹ • w i :=
    ⟨_, fun _ => rfl⟩
  have hyY : ∀ i, y i ∈ Yle k n c (i.val + 1) := by
    intro i
    rw [mem_Yle]
    intro l hl
    rw [hy, Pi.smul_apply, (mem_Yle.mp (hwY i)) l hl, smul_zero]
  have hy1 : ∀ i, y i (Sum.inr i) = 1 := by
    intro i
    rw [hy, Pi.smul_apply, hw1, smul_eq_mul, inv_mul_cancel₀ (hpow i)]
  have hy0 : ∀ i : Fin c, i.val = 0 → ∀ r, y i (Sum.inl r) = 0 := by
    intro i hi r
    rw [hy, Pi.smul_apply, hw0 i hi r, smul_zero]
  have hyw : ∀ i, (ϖ : k) ^ (i.val + 1) • y i = w i := by
    intro i
    rw [hy, smul_smul, mul_inv_cancel₀ (hpow i), one_smul]
  have hU := flagMat_uni hyY hy1 hy0
  have hdet : IsUnit (flagMat y).det := by
    rw [hU.det]
    exact isUnit_one
  obtain ⟨g, hg⟩ : ∃ g : GL (n ⊕ Fin c) k, g.val = flagMat y := ⟨Matrix.nonsingInvUnit _ hdet, rfl⟩

  have himg : act g (chainLat ϖ c (Λ.comap (inX k n c))) = Λ := by
    apply le_antisymm
    · intro v hv
      obtain ⟨u, hu, rfl⟩ := mem_act.1 hv
      obtain ⟨huL, hua⟩ := mem_chainLat.1 hu
      rw [hg, flagMat_mulVec]
      refine Λ.add_mem (Submodule.mem_comap.1 huL) (Λ.sum_mem fun i _ => ?_)
      obtain ⟨a, ha⟩ := hua i
      rw [ha, mul_smul, hyw i]
      exact Λ.smul_mem a (hwΛ i)
    · have hX : ∀ x ∈ Λ.comap (inX k n c),
          inX k n c x ∈ act g (chainLat ϖ c (Λ.comap (inX k n c))) := by
        intro x hx
        refine mem_act.2 ⟨inX k n c x, inX_mem_chainLat.2 hx, ?_⟩
        rw [hg, flagMat_mulVec]
        simp [inX_apply]
      have hW : ∀ i, w i ∈ act g (chainLat ϖ c (Λ.comap (inX k n c))) := by
        intro i
        refine mem_act.2 ⟨(ϖ : k) ^ (i.val + 1) • aux k n i, scaled_basis_mem_chainLattice ϖ _ i, ?_⟩
        rw [hg, mulVec_smul, ← hyw i]
        congr 1
        rw [aux, mulVec_single_one]
        rfl

      have key : ∀ j, j ≤ c → ∀ v ∈ Λ, v ∈ Yle k n c j →
          v ∈ act g (chainLat ϖ c (Λ.comap (inX k n c))) := by
        intro j
        induction j with
        | zero =>
          intro _ v hv hv0
          have e : v = inX k n c (fun r => v (Sum.inl r)) := by
            funext r
            rcases r with r | l
            · simp [inX_apply]
            · simp [inX_apply, (mem_Yle.mp hv0) l (by omega)]
          rw [e]
          apply hX
          rw [Submodule.mem_comap, ← e]
          exact hv
        | succ j ih =>
          intro hj v hv hvY
          obtain ⟨i, hi⟩ : ∃ i : Fin c, i.val = j := ⟨⟨j, by omega⟩, rfl⟩
          subst hi
          have hmem : v (Sum.inr i) ∈ Submodule.span 𝒪[k] {(ϖ : k) ^ (i.val + 1)} := by
            rw [← hΛ i]
            exact Submodule.mem_map_of_mem (Submodule.mem_inf.2 ⟨hv, hvY⟩)
          obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
          have hrest : v - a • w i ∈ Yle k n c i.val := by
            rw [mem_Yle]
            intro l hl
            rcases eq_or_ne l i with rfl | hne
            · rw [Pi.sub_apply, Pi.smul_apply, hw1, ha, sub_self]
            · have hne' : l.val ≠ i.val := fun h => hne (Fin.ext h)
              have hl' : i.val + 1 < l.val + 1 := by omega
              rw [Pi.sub_apply, Pi.smul_apply, (mem_Yle.mp hvY) l hl', (mem_Yle.mp (hwY i)) l hl',
                smul_zero, sub_zero]
          have h1 := ih (by omega) (v - a • w i) (Λ.sub_mem hv (Λ.smul_mem a (hwΛ i))) hrest
          have h2 := Submodule.add_mem _ h1 (Submodule.smul_mem _ a (hW i))
          rwa [sub_add_cancel] at h2
      intro v hv
      exact key c le_rfl v hv (mem_Yle.2 fun l hl => absurd hl (by have := l.isLt; omega))
  refine ⟨g⁻¹, (Radical.mem_N_iff g⁻¹).2 ?_, ?_⟩
  · exact Radical.Uni.inv (g := g) (by rw [hg]; exact hU)
  · conv_lhs => rw [← himg]
    rw [← act_mul, inv_mul_cancel, act_one]

end GlobalTheory.RootEx.UnfoldFlag
end
end

section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.UnfoldShape

theorem exists_eq_act_stdLat (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) [Fintype ι] [DecidableEq ι]
    (L : Submodule 𝒪[k] (ι → k)) (hL : Submodule.IsFullLattice k L) :
    ∃ g : GL ι k, L = act g (stdLat k ι) := by
  haveI := hL
  haveI : Module.Free 𝒪[k] L := Submodule.IsLattice.free k L
  haveI : Module.Finite 𝒪[k] L := Module.Finite.iff_fg.mpr hL.fg
  have hr : Module.finrank 𝒪[k] L = Fintype.card ι := ((Submodule.IsFullLattice.finrank_eq k L).trans (Module.finrank_fintype_fun_eq_card k))
  let b : Module.Basis ι 𝒪[k] L :=
    (Module.finBasisOfFinrankEq 𝒪[k] L hr).reindex (Fintype.equivFin ι).symm
  let c : Module.Basis ι k (ι → k) := b.extendOfIsLattice k
  have hc : ∀ i, c i = (b i : ι → k) := fun i => Module.Basis.extendOfIsLattice_apply k b i
  let A : Matrix ι ι k := Matrix.of fun i j => (b j : ι → k) i
  have hA : IsUnit A := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    have : A.col = c := by
      funext j i
      rw [hc]; rfl
    rw [this]; exact c.linearIndependent
  obtain ⟨g, hg⟩ := hA
  have key : ∀ a : ι → 𝒪[k], (g : Matrix ι ι k) *ᵥ (fun i => (a i : k))
      = ((∑ j, a j • b j : L) : ι → k) := by
    intro a
    funext i
    rw [hg, Submodule.coe_sum, Finset.sum_apply]
    simp only [Matrix.mulVec, dotProduct, A, Matrix.of_apply, Submodule.coe_smul, Pi.smul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]; rfl
  refine ⟨g, ?_⟩
  ext v
  rw [mem_act]
  constructor
  · intro hv
    refine ⟨fun i => (b.repr ⟨v, hv⟩ i : k), mem_stdLat.2 fun i => (b.repr ⟨v, hv⟩ i).2, ?_⟩
    rw [key, b.sum_repr]
  · rintro ⟨w, hw, rfl⟩
    rw [mem_stdLat] at hw
    have := key fun i => ⟨w i, hw i⟩
    change (g : Matrix ι ι k) *ᵥ w = _ at this
    rw [this]
    exact Subtype.property _

end GlobalTheory.RootEx.UnfoldShape
end

section

namespace GlobalTheory.SplitFlip

def vertexDiff (X : ℕ × ℕ) : ℤ := (X.1 : ℤ) - X.2

theorem vertexDiff_tgt (e : Edge) : vertexDiff e.tgt = vertexDiff e.src + 1 := by
  cases e <;> simp [vertexDiff, Edge.src, Edge.tgt] <;> omega

theorem IsPath.pairwise_vertexDiff : ∀ {γ : List Edge}, IsPath γ →
    γ.Pairwise fun a b => vertexDiff a.src < vertexDiff b.src := by
  intro γ h
  let r : Edge → Edge → Prop := fun a b => vertexDiff a.src < vertexDiff b.src
  let : Trans r r r := ⟨fun hab hbc => lt_trans hab hbc⟩
  change γ.Pairwise r
  apply List.IsChain.pairwise
  refine List.IsChain.imp (fun {a b} hab => ?_) h
  change vertexDiff a.src < vertexDiff b.src
  rw [← hab, vertexDiff_tgt]
  omega

theorem IsPath.eq_of_vertexDiff_eq {γ : List Edge} (hγ : IsPath γ) {a b : Edge} (ha : a ∈ γ) (hb : b ∈ γ)
    (h : vertexDiff a.src = vertexDiff b.src) : a = b := by
  by_contra hne
  have hpw := hγ.pairwise_vertexDiff
  have key : ∀ {l : List Edge}, l.Pairwise (fun a b => vertexDiff a.src < vertexDiff b.src) →
      ∀ {a b : Edge}, a ∈ l → b ∈ l → a ≠ b → vertexDiff a.src ≠ vertexDiff b.src := by
    intro l hl
    induction hl with
    | nil => intro a b ha; simp at ha
    | @cons x l hx _ ih =>
      intro a b ha hb hab
      rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd rfl hab
      · exact (hx b hb').ne
      · exact (hx a ha').ne'
      · exact ih ha' hb' hab
  exact key hpw ha hb hne h

theorem pathAvoid : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ →
    ∀ b ∈ γ, b.src ≠ (i + 1, j + 1) ∧ b.tgt ≠ (i + 1, j + 1) := by
  intro γ i j hγ hp b hb
  have hθ : Edge.theta i j ∈ γ := hp.subset (by simp)
  have hx : Edge.ex i j ∈ γ := hp.subset (by simp)
  refine ⟨fun hs => ?_, fun ht => ?_⟩
  · have := hγ.eq_of_vertexDiff_eq hb hx (by rw [hs]; simp [vertexDiff, Edge.src])
    subst this
    simp [Edge.src] at hs
  · have h1 := vertexDiff_tgt b
    rw [ht] at h1
    have := hγ.eq_of_vertexDiff_eq hb hθ (by simp [vertexDiff, Edge.src] at h1 ⊢; omega)
    subst this
    simp [Edge.tgt] at ht

end GlobalTheory.SplitFlip
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

theorem _root_.GlobalTheory.T.exists_schwartzBruhat_convolution_localFieldPower : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ν : Measure k) [ν.IsAddHaarMeasure] (Φ Ψ : SB (n → k)), ∃ (T : (n → k) → SB (n → k)) (w : SB (n → k)), (∀ y x, (T y).1 x = Ψ.1 (x - y)) ∧ (∀ x, w.1 x = ∫ y, Φ.1 y * Ψ.1 (x - y) ∂(Measure.pi fun _ => ν)) ∧ (∀ x, w.1 x = ∫ y, Ψ.1 y * Φ.1 (x - y) ∂(Measure.pi fun _ => ν)) ∧ ∀ l : SB (n → k) →ₗ[ℂ] ℂ, l w = ∫ y, Φ.1 y * l (T y) ∂(Measure.pi fun _ => ν) := by
  first | exact @GlobalTheory.SBConv.exists_convolution | exact GlobalTheory.SBConv.exists_convolution | (intros; apply GlobalTheory.SBConv.exists_convolution <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

theorem _root_.GlobalTheory.T.exists_sum_smul_of_locallyConstant_compactSupport : ∀ (Z : Type) [TopologicalSpace Z] [T2Space Z] (V : Type) [AddCommGroup V] [Module ℂ V] (T : Z → V) (_ : IsLocallyConstant T) (K : Set Z) (_ : IsCompact K) (_ : ∀ y, y ∉ K → T y = 0), ∃ (m : ℕ) (v : Fin m → V) (Φ : Fin m → SB Z), ∀ y, T y = ∑ i, (Φ i).1 y • v i := by
  first | exact @GlobalTheory.LocConstTensor.exists_sum | exact GlobalTheory.LocConstTensor.exists_sum | (intros; apply GlobalTheory.LocConstTensor.exists_sum <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.fockVacua_smooth_family_complexGaussians : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ q, (∀ x, β x q = 0) → q = 0) →
    ∀ J : ℝ → (V × V) →ₗ[ℝ] (V × V), (∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => J t w) → (∀ t w, J t (J t w) = -w) →
    (∀ t, ∃ g : SchwartzMap V ℂ, g ≠ 0 ∧ ∀ w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑g x = Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑g x) →
    ∃ M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ, (∀ x y, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => M t x y) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => M p.1 p.2 p.2) ∧
      (∀ t₀ : ℝ, ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2)) ∧
      (∀ t (g : SchwartzMap V ℂ), (∀ w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑g x = Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑g x) →
        ∀ x, g x = g 0 * Complex.exp (M t x x)) ∧
      ∃ (n : ℕ) (qs qs' : Fin n → V) (cs : Fin n → ℂ), ∀ x,
        HasDerivAt (fun t => M t x x) (∑ i, cs i * (β x (qs i) : ℂ) * (β x (qs' i) : ℂ)) 0 := by
  first | exact @GlobalTheory.FockFamily.fock_vacua_family | exact GlobalTheory.FockFamily.fock_vacua_family | (intros; apply GlobalTheory.FockFamily.fock_vacua_family <;> assumption)
end
