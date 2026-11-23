module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle002
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousWittExtendByZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeSupportAndFourierRelation
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle040
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle013
public import Mathlib.LinearAlgebra.Dimension.Basic
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
public import Mathlib.LinearAlgebra.PID
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.Extension
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledBasisMemChainLattice
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.UnfoldShape

theorem exists_isReps_of_fg (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) [Fintype ι] [DecidableEq ι] (ϖ : 𝒪[k])
    (hϖ : Irreducible ϖ) (M : Submodule 𝒪[k] (ι → k)) (hM : M.FG) :
    ∃ T : Finset (ι → k), IsReps ϖ M T := by
  classical
  have h1 : Finite (𝒪[k] ⧸ Ideal.span {ϖ}) := by
    rw [← hϖ.maximalIdeal_eq]
    exact (inferInstance : Finite 𝓀[k])
  have hfin : Module.Finite 𝒪[k] M := Module.Finite.iff_fg.mpr hM
  set N : Submodule 𝒪[k] M := Ideal.span {ϖ} • ⊤ with hN
  have h2 : Finite (M ⧸ N) := by
    have : Finite (M ⧸ (⊤ : Submodule 𝒪[k] M)) := by
      have : Subsingleton (M ⧸ (⊤ : Submodule 𝒪[k] M)) :=
        Submodule.Quotient.subsingleton_iff.mpr rfl
      infer_instance
    exact Submodule.finite_quotient_smul _ Module.Finite.fg_top
  have hmem : ∀ x : M, x ∈ N ↔ (x : ι → k) ∈ ϖ • M := by
    intro x
    rw [hN, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists,
      Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨b, -, rfl⟩
      exact ⟨b, b.2, rfl⟩
    · rintro ⟨b, hb, h⟩
      exact ⟨⟨b, hb⟩, trivial, Subtype.ext h⟩
  have := Fintype.ofFinite (M ⧸ N)
  choose s hs using Submodule.Quotient.mk_surjective N
  refine ⟨Finset.univ.image fun q => (s q : ι → k), ?_, ?_⟩
  · intro t ht
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ht
    exact (s q).2
  · intro v hv
    have key : ∀ q, v - (s q : ι → k) ∈ ϖ • M ↔ Submodule.Quotient.mk (⟨v, hv⟩ : M) = q := by
      intro q
      conv_rhs => rw [← hs q, Submodule.Quotient.eq, hmem]
      rfl
    refine ⟨s (Submodule.Quotient.mk ⟨v, hv⟩), ⟨Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩,
      (key _).mpr rfl⟩, ?_⟩
    rintro t ⟨ht, h⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ht
    rw [(key q).mp h]

end GlobalTheory.RootEx.UnfoldShape
end

section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.UnfoldShape

theorem isLattice_stdLat_and_act : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) [Fintype ι] [DecidableEq ι], Submodule.IsLattice k (stdLat k ι) ∧ ∀ (g : GL ι k) (L : Submodule 𝒪[k] (ι → k)), Submodule.IsLattice k L → Submodule.IsLattice k (act g L) := by
  intro k _ _ _ _ ι _ _
  refine ⟨⟨?_, ?_⟩, fun g L hL => ⟨?_, ?_⟩⟩
  · unfold stdLat
    refine Submodule.fg_pi fun _ => ?_
    rw [Submodule.one_eq_span]
    exact Submodule.fg_span_singleton _
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
  · exact hL.fg.map _
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli

end GlobalTheory.RootEx.UnfoldShape
end

section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace

theorem hasFinTrace_of_range_le (X : Type) [AddCommGroup X] [Module ℂ X] (T : X →ₗ[ℂ] X)
    (Z : Submodule ℂ X) [FiniteDimensional ℂ Z] (hT : LinearMap.range T ≤ Z) :
    GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace T (LinearMap.trace ℂ Z (T.restrict (p := Z) (q := Z)
      fun x _ => hT (LinearMap.mem_range_self T x))) := by
  haveI : FiniteDimensional ℂ (LinearMap.range T) := Submodule.finiteDimensional_of_le hT
  refine ⟨inferInstance, ?_⟩
  have hmem : ∀ x : Z, (T.restrict (p := Z) (q := Z)
      fun x _ => hT (LinearMap.mem_range_self T x)) x ∈ (LinearMap.range T).comap Z.subtype :=
    fun x => LinearMap.mem_range_self T (x : X)
  rw [← LinearMap.trace_restrict_eq_of_forall_mem _ _ hmem,
    ← LinearMap.trace_conj' _ (Submodule.comapSubtypeEquivOfLe hT)]
  congr 1

end GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

noncomputable section
namespace GlobalTheory.RootEx.RowSign
open GlobalTheory.RootEx.Exchange

theorem mat_add_gRow {k : Type} [Field k] {n n' : Type} [DecidableEq n] {c : ℕ} (q : Fin c) (u : n' → k) (x₀ : Matrix n n' k)
    (y : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → k) :
    mat x₀ (y + gRow q u) = mat x₀ y + rowM n c (q.val + 1) u := by
  ext r s
  rcases r with r | l <;> rcases s with s | i <;>
    simp [mat, gRow, rowM, Fin.ext_iff, add_assoc]

private theorem ch_affPt_add_sRow {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] {c : ℕ} (q : Fin c) (u : n' → k) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k) :
    ch (affPt (q.val + 1) x₀ (e + sRow q u e)) = ch (affPt (q.val + 1) x₀ e) := by
  unfold ch
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [affPt, sRow]

theorem opE_om_rowE : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (u : n' → k) (x₀ : Matrix n n' k), opE ψ ν p (om μ (rowE (c + 1) p u) 1 Φ.1) x₀ = opE ψ ν p (fun x => Φ.1 (x + rowM n c p u)) x₀ := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp1 hpc ψ hψ ν _ μ Φ u x₀
  classical
  have := secondCountable k
  have := t2Space k
  obtain ⟨q, rfl⟩ : ∃ q : Fin c, q.val + 1 = p := ⟨⟨p - 1, by omega⟩, by show p - 1 + 1 = p; omega⟩
  have hΦ : IsLocallyConstant Φ.1 ∧ HasCompactSupport Φ.1 := Φ.2
  have hA : Continuous fun e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k =>
      affPt (q.val + 1) x₀ e :=
    ((continuous_mat x₀).comp (continuous_wittExtendByZero _)).congr fun e => (affPt_eq _ x₀ e).symm
  have hch : Continuous fun x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k => ch x :=
    continuous_finsetSum _ fun i _ => continuous_id.matrix_elem _ _
  set f : ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k) → ℂ := fun e =>
    Φ.1 (affPt (q.val + 1) x₀ e + rowM n c (q.val + 1) u) * (ψ (-ch (affPt (q.val + 1) x₀ e)) : ℂ) with hf_def
  have hf : Continuous f := by
    refine (hΦ.1.continuous.comp (hA.add continuous_const)).mul ?_
    exact continuous_subtype_val.comp (hψ.comp (hch.comp hA).neg)
  have hS : Continuous (sRow (n := n) (n' := n') q u) := by
    refine continuous_pi fun i => ?_
    rcases i with ⟨⟨r, s | s⟩, hi⟩
    · exact ((continuous_apply _).comp (continuous_wittExtendByZero _)).mul continuous_const
    · exact continuous_const
  have h0 : ∀ e (i : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs}),
      ¬ (∃ s, i.1.2 = Sum.inl s) → sRow q u e i = 0 := by
    rintro e ⟨⟨r, s | s⟩, hi⟩ h
    · exact absurd ⟨s, rfl⟩ h
    · rfl
  have h1 : ∀ e e' : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k,
      (∀ i, ¬ (∃ s, i.1.2 = Sum.inl s) → e i = e' i) → sRow q u e = sRow q u e' := by
    intro e e' he
    funext i
    rcases i with ⟨⟨r, s | s⟩, hi⟩
    · simp only [sRow, Sum.elim_inl]
      congr 1
      simp only [ext0]
      split_ifs with h
      · exact he _ (by simp)
      · rfl
    · rfl
  have hL : ∀ e, om μ (rowE (c + 1) (q.val + 1) u) 1 Φ.1 (affPt (q.val + 1) x₀ e) *
      (ψ (-ch (affPt (q.val + 1) x₀ e)) : ℂ) = f (e + sRow q u e) := by
    intro e
    rw [om_rowE, affPt_mul_rowE, mat_add_gRow, ← affPt_eq]
    simp only [hf_def, ch_affPt_add_sRow]
  unfold opE
  simp_rw [hL]
  exact integral_shear ν (fun i => ∃ s, i.1.2 = Sum.inl s) (sRow q u) hS h0 h1 f hf

end GlobalTheory.RootEx.RowSign
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

noncomputable section
namespace GlobalTheory.RootEx.HeisenbergSign

theorem colE_inv_eq {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] (c p : ℕ) (β : n → k) :
    ((colE c p β)⁻¹ : GL (n ⊕ Fin c) k).val = 1 - ((colE c p β).val - 1) := by
  rw [ExchangeSupport.colE_inv_val, ExchangeSupport.colE_val]
  ext (i | i) (j | j) <;> simp [Matrix.one_apply]

theorem mat_add_gCol {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {c : ℕ} (q : Fin c) (ξ : n → k) (x₀ : Matrix n n' k) (y : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → k) :
    Exchange.mat x₀ (y + Exchange.gCol q ξ) = Exchange.mat x₀ y + colM c (q.val + 1) ξ := by
  ext r s
  rcases r with r | l <;> rcases s with s | i <;>
    simp [Exchange.mat, Exchange.gCol, colM, add_assoc, Fin.ext_iff]

theorem sign : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c), (∀ (x₀ : Matrix n n' k) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (ρ + 1) rs} → k) (β : n → k) (r : n) (i : Fin (c + 1)), i.val + 1 = ρ + 1 → ((1 - ((colE c (ρ + 1) β).val - 1)) * affPt (ρ + 1) x₀ e : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (Sum.inl r) (Sum.inr i) = -β r) ∧ ∀ (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure], Continuous ψ → ∀ (μ : kˣ →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (β : n → k), (∀ x, om μ 1 (colE c (ρ + 1) β) Φ.1 x = Φ.1 ((1 - ((colE c (ρ + 1) β).val - 1)) * x)) ∧ ∀ x₀, fl ψ ν μ ρ Φ.1 x₀ β = opE ψ ν (ρ + 1) (fun x => Φ.1 (x + colM c (ρ + 1) (-β))) x₀ := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c ρ _ hρc
  refine ⟨fun x₀ e β r i hi => ?_, fun ψ ν _ hψ μ Φ β => ⟨fun x => ?_, fun x₀ => ?_⟩⟩
  ·
    have hi' : i = Fin.castSucc (⟨ρ, hρc⟩ : Fin c) := Fin.ext (by simp; omega)
    subst hi'
    have h := congrFun (Exchange.col_colE_inv_mul (n' := n') (⟨ρ, hρc⟩ : Fin c) β x₀ e) r
    simp only at h
    rw [← colE_inv_eq]
    exact neg_eq_iff_eq_neg.mp h
  · rw [Exchange.om_colE, colE_inv_eq]
  ·
    have hch : ∀ (y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (p : ℕ) (ξ : n → k),
        ch (y + colM c p ξ) = ch y := by
      intro y p ξ
      simp [ch, colM]
    have hmem : IsLocallyConstant Φ.1 ∧ HasCompactSupport Φ.1 := Φ.2
    have key := Exchange.opE_colE hψ ν μ (⟨ρ, hρc⟩ : Fin c) (⟨ρ, hρc⟩ : Fin c)
      (χ := fun _ => (1 : ℂ)) continuous_const hmem.1.continuous x₀ β
    dsimp only at key
    refine Eq.trans ?_ (key.trans ?_)
    · simp [fl]
    · rw [opE]
      congr 1
      funext e
      rw [mat_add_gCol, ← Exchange.affPt_eq]
      simp only [Exchange.big, one_mul, hch]

end GlobalTheory.RootEx.HeisenbergSign
end
end

section

open GlobalTheory.SplitFlip

namespace GlobalTheory.FlipPathPairwise

def srcDiff (e : Edge) : ℤ := (e.src.1 : ℤ) - e.src.2

theorem srcDiff_of_join {e e' : Edge} (h : e.tgt = e'.src) : srcDiff e' = srcDiff e + 1 := by
  cases e <;> cases e' <;> simp only [Edge.src, Edge.tgt, Prod.mk.injEq] at h <;>
    simp only [srcDiff, Edge.src] <;> omega

theorem pairwise_of_isPath {γ : List Edge} (h : IsPath γ) :
    γ.Pairwise fun a b => srcDiff a < srcDiff b := by
  have h' : γ.IsChain fun a b => srcDiff a < srcDiff b :=
    List.IsChain.imp (fun a b hab => by rw [srcDiff_of_join hab]; omega) h
  haveI : Trans (fun a b : Edge => srcDiff a < srcDiff b) (fun a b => srcDiff a < srcDiff b)
      (fun a b => srcDiff a < srcDiff b) := ⟨fun h1 h2 => lt_trans h1 h2⟩
  exact h'.pairwise

end GlobalTheory.FlipPathPairwise


open GlobalTheory.FlipPathPairwise in
theorem GlobalTheory.SplitFlip.isPath_flipPath : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ →
    IsPath (flipPath i j γ) := by
  intro γ i j hγ hP
  obtain ⟨s, t, rfl⟩ := hP
  have hpw := pairwise_of_isPath hγ
  rw [List.pairwise_append, List.pairwise_append] at hpw
  have hs : ∀ a ∈ s, a ≠ .theta i j ∧ a ≠ .ex i j := fun a ha => by
    have h1 := hpw.1.2.2 a ha (.theta i j) (by simp)
    have h2 := hpw.1.2.2 a ha (.ex i j) (by simp)
    exact ⟨fun h => by subst h; exact lt_irrefl _ h1, fun h => by subst h; exact lt_irrefl _ h2⟩
  have ht : ∀ a ∈ t, a ≠ .theta i j ∧ a ≠ .ex i j := fun a ha => by
    have h1 := hpw.2.2 (.theta i j) (by simp) a ha
    have h2 := hpw.2.2 (.ex i j) (by simp) a ha
    exact ⟨fun h => by subst h; exact lt_irrefl _ h1, fun h => by subst h; exact lt_irrefl _ h2⟩
  have hflip : flipPath i j (s ++ [Edge.theta i j, Edge.ex i j] ++ t) =
      s ++ Edge.ex i (j + 1) :: Edge.theta (i + 1) j :: t := by
    have key : ∀ l : List Edge, (∀ a ∈ l, a ≠ .theta i j ∧ a ≠ .ex i j) →
        l.map (fun e => if e = .theta i j then Edge.ex i (j + 1) else if e = .ex i j then .theta (i + 1) j else e)
          = l := fun l hl =>
      (List.map_congr_left fun a ha => by simp [hl a ha]).trans (List.map_id l)
    unfold flipPath
    rw [List.map_append, List.map_append, key s hs, key t ht]
    simp
  rw [hflip]
  unfold IsPath at hγ ⊢
  rw [List.append_assoc, List.cons_append, List.cons_append, List.nil_append, List.isChain_append] at hγ
  obtain ⟨h1, h2, h3⟩ := hγ
  rw [List.isChain_cons_cons] at h2
  obtain ⟨-, h2⟩ := h2
  rw [List.isChain_cons] at h2
  refine List.isChain_append.2 ⟨h1, ?_, ?_⟩
  · rw [List.isChain_cons_cons, List.isChain_cons]
    exact ⟨rfl, h2.1, h2.2⟩
  · intro x hx y hy
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hy
    exact h3 x hx (Edge.theta i j) rfl
end

section

namespace GlobalTheory.SplitFlip

def pathInnerDiff (X : ℕ × ℕ) : ℤ := (X.1 : ℤ) - X.2

theorem pathInnerDiff_tgt (e : Edge) : pathInnerDiff e.tgt = pathInnerDiff e.src + 1 := by
  cases e <;> simp [pathInnerDiff, Edge.tgt, Edge.src] <;> push_cast <;> ring

theorem IsPath.pairwise_lt_source_index_difference_along_path {γ : List Edge} (hγ : IsPath γ) :
    (γ.map fun e => pathInnerDiff e.src).Pairwise (· < ·) := by
  have h : (γ.map fun e => pathInnerDiff e.src).IsChain (· < ·) :=
    List.isChain_map_of_isChain _ (R := fun a b : Edge => a.tgt = b.src) (fun a b (hab : a.tgt = b.src) => by
      show pathInnerDiff a.src < pathInnerDiff b.src
      rw [← hab, pathInnerDiff_tgt]; omega) (by unfold IsPath at hγ; exact hγ)
  exact h.pairwise

theorem IsPath.eq_of_src_eq_of_mem {γ : List Edge} (hγ : IsPath γ) {a b : Edge} (ha : a ∈ γ) (hb : b ∈ γ)
    (h : a.src = b.src) : a = b :=
  List.inj_on_of_nodup_map hγ.pairwise_lt_source_index_difference_along_path.nodup ha hb (by simp [h])

theorem src_flipEdge_pathInner (i j : ℕ) (e : Edge) :
    (if e = .theta i j then Edge.ex i (j + 1) else if e = .ex i j then .theta (i + 1) j else e).src =
      if e = .ex i j then (i + 1, j + 1) else e.src := by
  by_cases h1 : e = .theta i j
  · subst h1; simp
  · by_cases h2 : e = .ex i j
    · subst h2; simp
    · simp [h1, h2]

theorem mem_innerVertices_flipPath {γ : List Edge} {i j : ℕ} (hγ : IsPath γ) (hp : PassesThrough i j γ) :
    ∀ X ∈ innerVertices (flipPath i j γ), X ≠ (i, j) ∧ (X ≠ (i + 1, j + 1) → X ∈ innerVertices γ) := by
  intro X hX
  rw [innerVertices, flipPath, ← List.map_tail, List.map_map, List.mem_map] at hX
  obtain ⟨e, he, rfl⟩ := hX
  rw [Function.comp_apply, src_flipEdge_pathInner]
  have hex : Edge.ex i j ∈ γ := hp.subset (by simp)
  have heγ : e ∈ γ := List.mem_of_mem_tail he
  by_cases h : e = .ex i j
  · simp only [h, if_true]
    refine ⟨fun H => ?_, fun H => absurd rfl H⟩
    simp at H
  · simp only [h, if_false]
    refine ⟨fun H => h (hγ.eq_of_src_eq_of_mem heγ hex (by simpa using H)), fun _ => List.mem_map.2 ⟨e, he, rfl⟩⟩

end GlobalTheory.SplitFlip
end

section

namespace GlobalTheory.SplitFlip.PathSplit
open GlobalTheory.SplitFlip

def vdiff (X : ℕ × ℕ) : ℤ := (X.1 : ℤ) - X.2

theorem vdiff_tgt (e : Edge) : vdiff e.tgt = vdiff e.src + 1 := by
  cases e <;> simp [vdiff] <;> push_cast <;> ring

theorem pairwise_of_isPath : ∀ {γ : List Edge}, IsPath γ → γ.Pairwise (fun a b => vdiff a.src < vdiff b.src)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    unfold IsPath at h
    rw [List.isChain_cons_cons] at h
    have ih : (b :: l).Pairwise (fun a b => vdiff a.src < vdiff b.src) :=
      pairwise_of_isPath (γ := b :: l) (show IsPath (b :: l) from h.2)
    have hab : vdiff a.src < vdiff b.src := by
      have := vdiff_tgt a; rw [h.1] at this; omega
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.1 hc with rfl | hc
    · exact hab
    · exact hab.trans (List.rel_of_pairwise_cons ih hc)

theorem nodup_of_isPath {γ : List Edge} (h : IsPath γ) : γ.Nodup :=
  (pairwise_of_isPath h).imp fun hab heq => by subst heq; exact lt_irrefl _ hab

end GlobalTheory.SplitFlip.PathSplit

namespace GlobalTheory.SplitFlip
open GlobalTheory.SplitFlip.PathSplit

theorem flipPath_split : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ →
    ∃ l₁ l₂ : List Edge, γ = l₁ ++ [Edge.theta i j, Edge.ex i j] ++ l₂ ∧
      flipPath i j γ = l₁ ++ [Edge.ex i (j + 1), Edge.theta (i + 1) j] ++ l₂ := by
  intro γ i j hγ hp
  obtain ⟨l₁, l₂, rfl⟩ := hp
  have hnd := nodup_of_isPath hγ
  refine ⟨l₁, l₂, rfl, ?_⟩
  have hfix : ∀ l : List Edge, Edge.theta i j ∉ l → Edge.ex i j ∉ l →
      l.map (fun e => if e = .theta i j then .ex i (j + 1) else if e = .ex i j then .theta (i + 1) j else e) = l :=
    fun l h1 h2 => by
      refine (List.map_congr_left fun e he => ?_).trans (List.map_id l)
      have e1 : e ≠ .theta i j := fun h => h1 (h ▸ he)
      have e2 : e ≠ .ex i j := fun h => h2 (h ▸ he)
      simp [e1, e2]
  rw [List.nodup_append, List.nodup_append] at hnd
  obtain ⟨⟨_, _, hd1⟩, _, hd2⟩ := hnd
  have a1 : Edge.theta i j ∉ l₁ := fun h => hd1 _ h _ (by simp) rfl
  have a2 : Edge.ex i j ∉ l₁ := fun h => hd1 _ h _ (by simp) rfl
  have b1 : Edge.theta i j ∉ l₂ := fun h => hd2 _ (by simp) _ h rfl
  have b2 : Edge.ex i j ∉ l₂ := fun h => hd2 _ (by simp) _ h rfl
  simp only [flipPath, List.map_append, hfix l₁ a1 a2, hfix l₂ b1 b2]
  simp

end GlobalTheory.SplitFlip
end

section

namespace GlobalTheory.LocAsm

def exOne {X : GlobalTheory.SplitFlip.Edge → Type} (φ : ∀ b, X b → ℂ) : ∀ b, X b → ℂ := fun b x =>
  match b, x with
  | .ex _ _, _ => 1
  | .theta i j, x => φ (.theta i j) x

@[simp] theorem exOne_theta {X : GlobalTheory.SplitFlip.Edge → Type} (φ : ∀ b, X b → ℂ) (i j : ℕ) (x : X (.theta i j)) :
    exOne φ (.theta i j) x = φ (.theta i j) x := rfl

end GlobalTheory.LocAsm
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

theorem _root_.GlobalTheory.T.linear_change_of_variables_localField_matrix : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (ν : Measure k) [ν.IsAddHaarMeasure], (∀ (g : GL a k) (f : (a → k) → ℂ), ∫ x, f (g.val.mulVec x) ∂(Measure.pi fun _ => ν) = ((nabs k (Matrix.GeneralLinearGroup.det g))⁻¹ : ℝ) • ∫ x, f x ∂(Measure.pi fun _ => ν)) ∧ ∀ (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ), ∫ x, Φ (h.val * x * g.val) ∂(volM ν b a) = (nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card a : ℝ)) * nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card b : ℝ))) • ∫ x, Φ x ∂(volM ν b a) := by
  first | exact @GlobalTheory.SplitWeil.linear_change_of_variables | exact GlobalTheory.SplitWeil.linear_change_of_variables | (intros; apply GlobalTheory.SplitWeil.linear_change_of_variables <;> assumption)
end

section

open scoped TensorProduct


theorem _root_.GlobalTheory.T.simpleOverStableSubmodule_tensorPureKernelSpan : ∀ {V₀ V₁ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
    (A : Set (Module.End ℂ V₀)) (B : Set (Module.End ℂ V₁)) (K₀ : Submodule ℂ V₀) (K₁ : Submodule ℂ V₁),
    Module.rank ℂ V₀ ≤ Cardinal.aleph0 → GlobalTheory.TensHead.Stab A K₀ → GlobalTheory.TensHead.Stab B K₁ →
    GlobalTheory.TensHead.SimpleOver A K₀ → GlobalTheory.TensHead.SimpleOver B K₁ →
    GlobalTheory.TensHead.SimpleOver (GlobalTheory.TensHead.tensOps A B) (GlobalTheory.TensHead.tensKer K₀ K₁) := by
  first | exact @GlobalTheory.TensHead.simpleOver_tensKer | exact GlobalTheory.TensHead.simpleOver_tensKer | (intros; apply GlobalTheory.TensHead.simpleOver_tensKer <;> assumption)
end
