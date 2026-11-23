module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartHOfSs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle006
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Matrix NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Geo
open scoped ContDiff

namespace UpperTheory.V.Cj.A

theorem absTrans_of (h1 : HdFacts) (h2 : ZigFwd) (h3 : ZigBwd) (h4 : BwdLast) (h5 : ZigFormal) (h6 : PullOp) (h7 : PullAct)
    (h8 : ZigMap) (h9 : CoverEx) (h10 : SatClosed) (h11 : SatFacts) : AbsTrans := by
  intro Γ V S _ _ _ _ d d' G ξ' τ hτ hc hn hcone hp ⟨l, hl⟩ q w hw hdw ⟨T, K, hT, hK, hKY, hz⟩
  obtain ⟨K1, hK1, hKK, hK1Y⟩ := exists_compact_between hK G.isOpen hKY
  obtain ⟨s1, -, s3, -⟩ := h11 Γ V S d G T K
  obtain ⟨o1, o2, o3, -⟩ := h11 Γ V S d G T (interior K1)
  obtain ⟨-, -, -, f4⟩ := h11 Γ V S d G T K1
  obtain ⟨C, φ, hC, hφ, hCA, hCO⟩ := h9 Γ V S d G hp (fun s => G.Y \ sat G T K s) (sat G T (interior K1))
    (fun s => ⟨h10 Γ V S d G hp hcone l hl T K hT hK hKY s, Set.diff_subset, o2 isOpen_interior s, fun p hp' => by
      by_cases h : p ∈ sat G T K s
      · exact Or.inr (s3 _ hKK s h)
      · exact Or.inl ⟨hp', h⟩⟩)
    (fun γ s p => by simp only [Set.mem_diff, G.ρ_mem_iff, s1 γ s p]) o1
  obtain ⟨c, z1, z2, z3, z4⟩ := h2 Γ V S (Idx Γ V) d G hc hn Idx.g (fun _ _ => rfl) C hC q 0 q (zero_add q) (fun _ => w)
    (fun γ _ _ => (hw γ).symm) (fun _ _ => hdw) (fun x hx => by simp [hd, hx, Finset.sum_range_succ])
    (fun x hx s p _ h => by
      obtain ⟨i, rfl⟩ := List.length_eq_one_iff.1 hx
      have := hCA i s (h i (by simp))
      exact hz s p this.1 this.2)
  let G' := chg G ξ'
  let f : (S → Fin d → ℂ) →+ (S → Fin d' → ℂ) := τ.compLeft S
  have hC' : IsCvx G' C := ⟨hC.1, hC.2, hC.3, hC.4⟩
  have hφ' : IsPart G' φ := ⟨hφ.1, hφ.2, hφ.3, hφ.4⟩
  have hF : ∀ i s, ∀ p ∈ G.Y \ sat G T K1 s, φ i s p ≠ 0 → p ∈ C i s := fun i s p hp' h =>
    hCO i s p (fun h' => hp'.2 (o3 _ interior_subset s h')) h
  obtain ⟨u, u1, u2, u3, u4, u5⟩ := h3 Γ V S (Idx Γ V) d' G' hc hn φ hφ' C (fun s => G.Y \ sat G T K1 s) hC'
    (h10 Γ V S d G hp hcone l hl T K1 hT hK1 hK1Y) hF q (fun x => f (c x))
    (fun γ x hx => by
      beta_reduce
      rw [z2 γ x hx]
      exact funext fun s => hτ γ _)
    (fun x hx => by rw [h1.2.2.2.1 _ _ _ f c x, z3 x hx, map_zero])
    (fun x hx s p h => by
      change τ (c x s) = 0
      rw [z4 x hx s p h, map_zero]) q 0 (zero_add q)
  obtain ⟨w', w1, w2, w3⟩ := h4 Γ V S (Idx Γ V) d' G' φ hφ' C _ hF q u u2 u4 u5
  have hl' : G'.IsInvGauge l := hl
  obtain ⟨P, p1, p2, p3⟩ := h6 Γ V S d' G' hcone l hl'
  have p4 := fun k => h7 Γ V S d' G' hcone l hl' k (P k) (p1 k)
  have hι : ∀ γ δ : Γ, (⟨γ * δ, 0⟩ : Idx Γ V) = γ • (⟨δ, 0⟩ : Idx Γ V) := fun _ _ => rfl
  have y1 := (h5 Γ V S (Idx Γ V) d G).2 (fun γ => ⟨γ, 0⟩) hι q 0 _ _ z1
  have y2 := (h5 Γ V S (Idx Γ V) d' G').2 (fun γ => ⟨γ, 0⟩) hι q 0 _ _ ((h5 Γ V S (Idx Γ V) d' G').1 q 0 u (fun _ => w') _ w2 u1)
  refine ⟨_, P q w', y1, h8 Γ V S d' G' P p2 p3 p4 q 0 _ _ y2, fun γ => by rw [p4, w1], ?_, fun s p hp' v i hv => ?_,
    T, K1, hT, hK1, hK1Y, fun s p hp' h => ?_⟩
  · rw [p2, ← w2 [⟨1, 0⟩] rfl, u3 _ rfl, map_zero]
  · rw [p1 q w' s p hp']
    exact (pullA V _ G.Y G.isOpen hcone (l s) (hl.1 s) q _).1 p hp' v i hv
  · have h0 := (hl.1 s).2.1 p hp'
    rw [p1 q w' s p hp', pull, w3 s _ ⟨hcone _ h0 p hp', fun h' => h ((f4 s p _ h0).1 h')⟩]
    rfl

theorem partA_of (h1 : AbsTrans) (h2 : SuppFwd) (h3 : SuppBwd) (h4 : LevCorr) : PartA := by
  intro E _ _ _ a ha U hUo hU σ Ξ Ξ' h hσ q α hα hd0 hs
  have ho : IsOpen (cone E a) := isOpen_iff_mem_nhds.2 fun p hp => by
    obtain ⟨τ, -, hτ⟩ := locSec E a p hp
    exact hτ.mono fun x hx => ⟨τ x, hx⟩
  obtain ⟨w, w1, w2, w3⟩ := (h4 E a ho U Ξ q).1 α hα hd0
  let τ : (Fin Ξ.d → ℂ) →+ (Fin Ξ'.d → ℂ) := AddMonoidHom.mk' (fun v i => σ (v (Fin.cast h.symm i))) fun v v' => by
    ext i
    simp
  have hτ : ∀ γ v, τ ((geo ho U Ξ).ξ γ *ᵥ v) = (geo ho U Ξ').ξ γ *ᵥ τ v := fun γ v => by
    ext i
    change σ (∑ j, ratC Ξ γ.1 (Fin.cast h.symm i) j * v j) = ∑ j, ratC Ξ' γ.1 i j * σ (v (Fin.cast h.symm j))

    rw [map_sum, ← (finCongr h).sum_comp]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← hσ]
    rfl
  obtain ⟨c, w', z1, z2, z3, z4, z5, z6⟩ := h1 _ _ _ _ _ (geo ho U Ξ) (geo ho U Ξ').ξ τ hτ (coneConvex E a).1
    ⟨_, hOne_mem_cone⟩ (coneConvex E a).2 (geoProper E a ho U Ξ hU) (Dr.gauge E a ha ho U Ξ hU) q w w2 w3
    (h2 E a ho U hUo Ξ q α _ w1 hs)
  obtain ⟨β, b1, b2, b3⟩ := (h4 E a ho U Ξ' q).2 w' z3 z4 z5
  refine ⟨U, le_rfl, hUo, hU, β, b3, h3 E a ho U hU Ξ' q β _ b1 z6, hα, b2, c, sigC σ h c, ⟨ho, w, w1, z1⟩,
    ⟨ho, w', b1, z2⟩, ?_⟩
  rw [sub_self]
  cases q with
  | zero => exact fun _ _ => rfl
  | succ q => exact ⟨0, fun _ _ _ => by simp, fun x _ => by simp [hd]⟩

end UpperTheory.V.Cj.A
end
end

section

open UpperTheory.V.Cj.A UpperTheory.V.Lit.Dr
open scoped ContDiff

theorem UpperTheory.V.Cj.A.pullOp :
    PullOp := by
  intro Γ V S _ _ _ _ d G hC l hl
  have hY : IsOpen G.Y := G.isOpen
  have hpos : ∀ s, ∀ p ∈ G.Y, l s p • p ∈ G.Y := fun s p hp => hC _ ((hl.1 s).2.1 p hp) p hp
  have hw : ∀ q (w : G.Om q) (s : S),
      ContDiffOn ℝ ∞ ((w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) G.Y ∧
        ∀ p ∉ G.Y, (w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p = 0 := fun q w => w.2
  have mem : ∀ q (w : G.Om q), (fun s => G.Y.indicator
      (pull (l s) ((w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s))) ∈ G.Om q := by
    intro q w s
    refine ⟨?_, fun p hp => Set.indicator_apply_eq_zero.2 fun h => absurd h hp⟩
    exact (pullB V (Fin d → ℂ) G.Y hY hC (l s) (hl.1 s) q _ (hw q w s).1).1.congr
      fun p hp => Set.indicator_of_mem hp _
  have padd : ∀ q (s : S) (a b : V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) (p : V),
      pull (l s) (a + b) p = pull (l s) a p + pull (l s) b p := by
    intro q s a b p
    ext v
    simp [pull]
  have psmul : ∀ q (s : S) (c : ℂ) (a : V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) (p : V),
      pull (l s) (c • a) p = c • pull (l s) a p := by
    intro q s c a p
    ext v
    simp [pull]
  have ext_ind : ∀ q (om : V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) p, p ∈ G.Y →
      extDeriv (G.Y.indicator om) p = extDeriv om p := by
    intro q om p hp
    simp only [extDeriv]
    rw [Filter.EventuallyEq.fderiv_eq
      (Filter.eventuallyEq_of_mem (hY.mem_nhds hp) fun x hx => Set.indicator_of_mem hx om)]
  let P : ∀ q, G.Om q →ₗ[ℂ] G.Om q := fun q =>
    { toFun := fun w => ⟨_, mem q w⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        funext s p
        simp only [Submodule.coe_add, Pi.add_apply]
        by_cases hp : p ∈ G.Y
        · simp only [Set.indicator_of_mem hp]
          exact padd q s _ _ p
        · simp [Set.indicator, hp]
      map_smul' := by
        intro c a
        apply Subtype.ext
        funext s p
        simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
        by_cases hp : p ∈ G.Y
        · simp only [Set.indicator_of_mem hp]
          exact psmul q s c _ p
        · simp [Set.indicator, hp] }
  refine ⟨P, ?_, ?_, ?_⟩
  · intro q w s p hp
    exact Set.indicator_of_mem hp _
  · intro q w
    apply Subtype.ext
    funext s p
    by_cases hp : p ∈ G.Y
    · rw [Geo.dOm_apply G _ s hp]
      change extDeriv (G.Y.indicator _) p = G.Y.indicator _ p
      rw [ext_ind _ _ _ hp, Set.indicator_of_mem hp,
        (pullB V (Fin d → ℂ) G.Y hY hC (l s) (hl.1 s) q _ (hw q w s).1).2 p hp]
      simp only [pull]
      rw [Geo.dOm_apply G w s (hpos s p hp)]
    · exact ((hw _ _ s).2 p hp).trans ((hw _ _ s).2 p hp).symm
  · intro f
    apply Subtype.ext
    funext s p
    by_cases hp : p ∈ G.Y
    · change G.Y.indicator _ p = _
      rw [Set.indicator_of_mem hp]
      ext v
      simp only [pull, ContinuousAlternatingMap.compContinuousLinearMap_apply]
      rw [Geo.incl_apply G f s (hpos s p hp), Geo.incl_apply G f s hp]
    · exact ((hw _ _ s).2 p hp).trans ((hw _ _ s).2 p hp).symm
end

section

open UpperTheory.V.Cj.A
open Matrix NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr

theorem UpperTheory.V.Cj.A.sandCpt :
    SandCpt := by
  intro E _ _ a
  have hcont : Continuous (fun g : GL (Fin a) (Cinf E) => sand g (hOne E a)) := by
    refine Continuous.subtype_mk (f := fun g : GL (Fin a) (Cinf E) => (sand g (hOne E a)).1) ?_ _
    change Continuous fun g : GL (Fin a) (Cinf E) =>
      (g.val * Matrix.of (hOne E a).1 * star g.val : Matrix (Fin a) (Fin a) (Cinf E))
    exact (Units.continuous_val.mul continuous_const).mul Units.continuous_val.star
  refine ⟨hcont, fun K hK hKc => ?_⟩
  obtain ⟨C, hC⟩ := boundInf E a (insert (hOne E a) K) (Set.insert_subset hOne_mem_cone hK) (hKc.insert _)
  have hB : IsCompact {m : Matrix (Fin a) (Fin a) (Cinf E) | ‖toL m‖ ≤ C} := by
    have h : IsCompact (Metric.closedBall (0 : Fin a → Fin a → Cinf E) C) := isCompact_closedBall _ _
    have e : Metric.closedBall (0 : Fin a → Fin a → Cinf E) C = {m | ‖m‖ ≤ C} := by
      ext m; simp
    rw [e] at h
    exact h
  have hT := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin a) (Fin a) (Cinf E))).isCompact_preimage
    (hB.prod (hB.image MulOpposite.continuous_op))
  refine hT.of_isClosed_subset (hKc.isClosed.preimage hcont) fun g hg => ⟨?_, (g⁻¹).val, ?_, rfl⟩
  · exact hC g _ (Set.mem_insert _ _) (Set.mem_insert_of_mem _ hg)
  · refine hC g⁻¹ _ (Set.mem_insert_of_mem _ hg) ?_
    have e : sand g⁻¹ (sand g (hOne E a)) = hOne E a := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
    rw [e]
    exact Set.mem_insert _ _
end
