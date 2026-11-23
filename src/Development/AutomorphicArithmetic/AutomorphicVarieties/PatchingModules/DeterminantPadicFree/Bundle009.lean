module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle008
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.eigen :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (κ la : G → Matrix (Fin n) (Fin n) F) (Y : Matrix (Fin n) (Fin n) F), TwCoc (fun _ => 1) D.r Set.univ κ → TwCoc D.χF D.r Set.univ la → (∀ g ∈ D.G', κ g + la g = dTw (fun _ => 1) D.r Y g) → (∃ Y₁, ∀ g ∈ D.G', κ g = dTw (fun _ => 1) D.r Y₁ g) ∧ ∃ Y₂, ∀ g ∈ D.G', la g = dTw (fun _ => 1) D.r Y₂ g := by
  intro F G _ _ n D κ la Y hκ hla hY
  set c : F := D.χF D.g₀ with hc
  have hc1 : c - 1 ≠ 0 := by
    intro h
    apply D.χ_ne
    ext
    exact sub_eq_zero.mp h
  set Z : Matrix (Fin n) (Fin n) F := D.r D.g₀ * Y * D.r D.g₀⁻¹ with hZ
  set Y₁ : Matrix (Fin n) (Fin n) F := (c - 1)⁻¹ • (c • Z - c • κ D.g₀ - la D.g₀ - Y) with hY₁
  have key : ∀ g ∈ D.G', κ g = dTw (fun _ => 1) D.r Y₁ g := by
    intro g hg
    have hg' : D.g₀⁻¹ * g * D.g₀ ∈ D.G' := by
      have := D.G'.mul_mem (D.comm D.g₀⁻¹ g) hg
      simpa using this
    set g' := D.g₀⁻¹ * g * D.g₀ with hgg
    have e : g * D.g₀ = D.g₀ * g' := by rw [hgg]; group
    have e' : g'⁻¹ * D.g₀⁻¹ = D.g₀⁻¹ * g⁻¹ := by rw [hgg]; group
    have h1 := hκ g trivial D.g₀ trivial
    have h2 := hla g trivial D.g₀ trivial
    rw [e, hκ D.g₀ trivial g' trivial] at h1
    rw [e, hla D.g₀ trivial g' trivial] at h2
    have hχ : D.χF g = 1 := by simp [DetFr.χF, D.χ_triv g hg]
    rw [hχ, ← hc] at h2
    have h3 := hY g hg
    have h4 : D.r D.g₀ * κ g' * D.r D.g₀⁻¹ + D.r D.g₀ * la g' * D.r D.g₀⁻¹
        = D.r g * Z * D.r g⁻¹ - Z := by
      rw [← add_mul, ← mul_add, hY g' hg', dTw, one_smul, mul_sub, sub_mul, hZ]
      congr 1
      calc D.r D.g₀ * (D.r g' * Y * D.r g'⁻¹) * D.r D.g₀⁻¹
          = (D.r D.g₀ * D.r g') * Y * (D.r g'⁻¹ * D.r D.g₀⁻¹) := by simp only [mul_assoc]
        _ = (D.r g * D.r D.g₀) * Y * (D.r D.g₀⁻¹ * D.r g⁻¹) := by
          rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, e, e']
        _ = _ := by simp only [mul_assoc]
    have h5 : (c - 1) • κ g = (c - 1) • dTw (fun _ => 1) D.r Y₁ g := by
      simp only [dTw, one_smul] at h1 h2 h3 ⊢
      rw [hY₁, smul_sub, mul_smul_comm, smul_mul_assoc, smul_inv_smul₀ hc1, smul_inv_smul₀ hc1]
      simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
      linear_combination (norm := module) c • h4 - c • h1 - h2 - h3
    exact smul_right_injective _ hc1 h5
  refine ⟨⟨Y₁, key⟩, Y - Y₁, fun g hg => ?_⟩
  have h3 := hY g hg
  rw [key g hg] at h3
  simp only [dTw, one_smul, mul_sub, sub_mul] at h3 ⊢
  rw [← sub_eq_zero] at h3 ⊢
  rw [← h3]; abel
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

namespace UpperTheory.V.Pa.Det

section Quad

variable {F : Type} [Field F] {n m : ℕ}

private abbrev Quad (F : Type) (n m : ℕ) :=
  Matrix (Fin n) (Fin n) F × (Fin m → Matrix (Fin n) (Fin n) F) × (Fin m → Matrix (Fin n) (Fin n) F) ×
    Matrix (Fin n) (Fin n) F

end Quad

end UpperTheory.V.Pa.Det

theorem UpperTheory.V.Pa.Det.relPair :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) {m : ℕ} (κ la : Fin m → G → Matrix (Fin n) (Fin n) F) (s : F) (ph : G → Matrix (Fin n) (Fin n) F), D.IsKap κ → D.IsTw κ s ph la → ∀ (c c' : G →₀ F), (∀ g ∈ c.support, g ∈ D.G') → (∀ g ∈ c'.support, g ∈ D.G') → c.sum (fun g x => x • D.r g) = 0 → c'.sum (fun g x => x • D.r g) = 0 → ∀ i j : Fin n, ¬ (((i : ℕ) < D.a) ↔ ((j : ℕ) < D.a)) → ∑ k, ((c.sum fun g x => x • (κ k g * D.r g)) i j * (c'.sum fun g x => x • (la k g * D.r g)) j i + (c.sum fun g x => x • (la k g * D.r g)) i j * (c'.sum fun g x => x • (κ k g * D.r g)) j i) = 0 := by
  intro F G _ _ n D m κ la s ph hK hT c c' hc hc' hRc hRc' i j _
  classical
  have hP : ∀ (g : G) (X : Matrix (Fin n) (Fin n) F), D.r g⁻¹ * (D.r g * X) = X := fun g X => by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have hχ : ∀ g ∈ D.G', D.χF g = 1 := fun g hg => by simp [DetFr.χF, D.χ_triv g hg]
  have eK : ∀ k g h, κ k (g * h) = κ k g + D.r g * κ k h * D.r g⁻¹ := fun k g h => by
    have e := (hK.coc k) g (Set.mem_univ g) h (Set.mem_univ h)
    simpa using e
  have eL : ∀ g ∈ D.G', ∀ k h, la k (g * h) = la k g + D.r g * la k h * D.r g⁻¹ := fun g hg k h => by
    have e := (hT.coc k) g (Set.mem_univ g) h (Set.mem_univ h)
    rw [hχ g hg, one_smul] at e
    exact e
  have pK : ∀ k g h, κ k (g * h) * D.r (g * h) = κ k g * D.r g * D.r h + D.r g * (κ k h * D.r h) := by
    intro k g h
    rw [eK, map_mul]
    simp only [add_mul, mul_assoc, hP]
  have pL : ∀ g ∈ D.G', ∀ k h, la k (g * h) * D.r (g * h) = la k g * D.r g * D.r h + D.r g * (la k h * D.r h) := by
    intro g hg k h
    rw [eL g hg, map_mul]
    simp only [add_mul, mul_assoc, hP]
  have pQ : ∀ g ∈ D.G', ∀ h, ph (g * h) * D.r (g * h) + ∑ k, la k (g * h) * κ k (g * h) * D.r (g * h) =
      (ph g * D.r g + ∑ k, la k g * κ k g * D.r g) * D.r h + D.r g * (ph h * D.r h + ∑ k, la k h * κ k h * D.r h) +
      ∑ k, (κ k g * D.r g * (la k h * D.r h) + la k g * D.r g * (κ k h * D.r h)) := by
    intro g hg h
    have e := hT.ph_mul g h
    rw [hχ g hg, one_smul] at e
    rw [e, map_mul]
    simp only [eK, eL g hg]
    simp only [add_mul, mul_add, sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_mul,
      Finset.mul_sum, mul_assoc, hP]
    abel
  let pr : (G →₀ F) → (G →₀ F) → (G →₀ F) := fun c d =>
    c.sum fun g a => d.sum fun h b => Finsupp.single (g * h) (a * b)
  have gen : ∀ (v : G → Matrix (Fin n) (Fin n) F) (c d : G →₀ F), Finsupp.linearCombination F v (pr c d) =
      c.sum fun g a => d.sum fun h b => (a * b) • v (g * h) := by
    intro v c d
    simp only [pr, map_finsuppSum, Finsupp.linearCombination_single]
  have lcMul : ∀ (v w : G → Matrix (Fin n) (Fin n) F) (c d : G →₀ F),
      Finsupp.linearCombination F v c * Finsupp.linearCombination F w d =
      c.sum fun g a => d.sum fun h b => (a * b) • (v g * w h) := by
    intro v w c d
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum_mul]
    refine Finsupp.sum_congr fun g _ => ?_
    rw [Finsupp.mul_sum]
    refine Finsupp.sum_congr fun h _ => ?_
    rw [smul_mul_smul_comm]
  have dK : ∀ (W : Fin m → G → G → Matrix (Fin n) (Fin n) F) (c d : G →₀ F),
      (∑ k, c.sum fun g a => d.sum fun h b => (a * b) • W k g h) =
      c.sum fun g a => d.sum fun h b => (a * b) • ∑ k, W k g h := by
    intro W c d
    simp only [Finsupp.sum, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.sum_comm]
  have memS : ∀ (p : G →₀ F), p ∈ Finsupp.supported F F (D.G' : Set G) → ∀ g ∈ p.support, g ∈ D.G' :=
    fun p hp g hg => (Finsupp.mem_supported F p).1 hp (Finset.mem_coe.2 hg)
  have prS : ∀ c ∈ Finsupp.supported F F (D.G' : Set G), ∀ d ∈ Finsupp.supported F F (D.G' : Set G),
      pr c d ∈ Finsupp.supported F F (D.G' : Set G) := by
    intro c hc d hd
    refine Submodule.finsuppSum_mem F _ c _ fun g hg => Submodule.finsuppSum_mem F _ d _ fun h hh => ?_
    exact Finsupp.single_mem_supported F _ (D.G'.mul_mem (memS c hc g (Finsupp.mem_support_iff.2 hg))
      (memS d hd h (Finsupp.mem_support_iff.2 hh)))
  have mR : ∀ c d, Finsupp.linearCombination F D.r (pr c d) =
      Finsupp.linearCombination F D.r c * Finsupp.linearCombination F D.r d := by
    intro c d
    rw [gen, lcMul]
    simp only [map_mul]
  have mK : ∀ k, ∀ c d, Finsupp.linearCombination F (fun g => κ k g * D.r g) (pr c d) =
      Finsupp.linearCombination F (fun g => κ k g * D.r g) c * Finsupp.linearCombination F D.r d +
      Finsupp.linearCombination F D.r c * Finsupp.linearCombination F (fun g => κ k g * D.r g) d := by
    intro k c d
    rw [gen, lcMul, lcMul, ← Finsupp.sum_add]
    refine Finsupp.sum_congr fun g _ => ?_
    rw [← Finsupp.sum_add]
    refine Finsupp.sum_congr fun h _ => ?_
    rw [pK, smul_add]
  have mL : ∀ c ∈ Finsupp.supported F F (D.G' : Set G), ∀ k d,
      Finsupp.linearCombination F (fun g => la k g * D.r g) (pr c d) =
      Finsupp.linearCombination F (fun g => la k g * D.r g) c * Finsupp.linearCombination F D.r d +
      Finsupp.linearCombination F D.r c * Finsupp.linearCombination F (fun g => la k g * D.r g) d := by
    intro c hc k d
    rw [gen, lcMul, lcMul, ← Finsupp.sum_add]
    refine Finsupp.sum_congr fun g hg => ?_
    rw [← Finsupp.sum_add]
    refine Finsupp.sum_congr fun h _ => ?_
    rw [pL g (memS c hc g hg), smul_add]
  have mQ : ∀ c ∈ Finsupp.supported F F (D.G' : Set G), ∀ d,
      Finsupp.linearCombination F (fun g => ph g * D.r g + ∑ k, la k g * κ k g * D.r g) (pr c d) =
      Finsupp.linearCombination F (fun g => ph g * D.r g + ∑ k, la k g * κ k g * D.r g) c *
        Finsupp.linearCombination F D.r d +
      Finsupp.linearCombination F D.r c *
        Finsupp.linearCombination F (fun g => ph g * D.r g + ∑ k, la k g * κ k g * D.r g) d +
      ∑ k, (Finsupp.linearCombination F (fun g => κ k g * D.r g) c *
          Finsupp.linearCombination F (fun g => la k g * D.r g) d +
        Finsupp.linearCombination F (fun g => la k g * D.r g) c *
          Finsupp.linearCombination F (fun g => κ k g * D.r g) d) := by
    intro c hc d
    have hs : (∑ k, (Finsupp.linearCombination F (fun g => κ k g * D.r g) c *
          Finsupp.linearCombination F (fun g => la k g * D.r g) d +
        Finsupp.linearCombination F (fun g => la k g * D.r g) c *
          Finsupp.linearCombination F (fun g => κ k g * D.r g) d)) =
        c.sum fun g a => d.sum fun h b => (a * b) •
          ∑ k, (κ k g * D.r g * (la k h * D.r h) + la k g * D.r g * (κ k h * D.r h)) := by
      refine Eq.trans ?_ (dK _ c d)
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [lcMul, lcMul, ← Finsupp.sum_add]
      refine Finsupp.sum_congr fun g _ => ?_
      rw [← Finsupp.sum_add]
      refine Finsupp.sum_congr fun h _ => ?_
      rw [smul_add]
    rw [gen, hs, lcMul, lcMul, ← Finsupp.sum_add, ← Finsupp.sum_add]
    refine Finsupp.sum_congr fun g hg => ?_
    rw [← Finsupp.sum_add, ← Finsupp.sum_add]
    refine Finsupp.sum_congr fun h _ => ?_
    rw [← smul_add, ← smul_add, pQ g (memS c hc g hg) h]
  have trQ : ∀ p ∈ Finsupp.supported F F (D.G' : Set G),
      (Finsupp.linearCombination F (fun g => ph g * D.r g + ∑ k, la k g * κ k g * D.r g) p).trace = 0 := by
    intro p hp
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Matrix.trace_sum]
    refine Finset.sum_eq_zero fun g hg => ?_
    rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_sum, hT.ell g (memS p hp g hg), smul_zero]
  have hEv : ∀ t : Fin n, Matrix.single t t (1 : F) ∈ Submodule.span F (D.r '' (D.G' : Set G)) := by
    intro t
    rw [D.span]
    intro i' j'
    refine ⟨fun _ => trivial, fun h => ?_⟩
    rw [Submodule.mem_bot, Matrix.single_apply]
    split_ifs with e
    · obtain ⟨rfl, rfl⟩ := e
      exact absurd Iff.rfl h
    · rfl
  have hS : c ∈ Finsupp.supported F F (D.G' : Set G) :=
    (Finsupp.mem_supported F c).2 fun g hg => hc g (Finset.mem_coe.1 hg)
  have hS' : c' ∈ Finsupp.supported F F (D.G' : Set G) :=
    (Finsupp.mem_supported F c').2 fun g hg => hc' g (Finset.mem_coe.1 hg)
  obtain ⟨dj, hdj, hj⟩ := (Finsupp.mem_span_image_iff_linearCombination F).1 (hEv j)
  obtain ⟨di, hdi, hi⟩ := (Finsupp.mem_span_image_iff_linearCombination F).1 (hEv i)
  have hR0 : Finsupp.linearCombination F D.r c = 0 := by
    rw [Finsupp.linearCombination_apply]; exact hRc
  have hR0' : Finsupp.linearCombination F D.r c' = 0 := by
    rw [Finsupp.linearCombination_apply]; exact hRc'
  have tr : ∀ A B : Matrix (Fin n) (Fin n) F,
      (A * Matrix.single j j 1 * (B * Matrix.single i i 1)).trace = A i j * B j i := by
    intro A B
    rw [← mul_assoc, Matrix.trace_mul_single]
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul]
  have key := trQ _ (prS _ (prS c hS dj hdj) _ (prS c' hS' di hdi))
  rw [mQ _ (prS c hS dj hdj)] at key
  simp only [mR, mK, mL c hS, mL c' hS', hR0, hR0', hi, hj, zero_mul, mul_zero, add_zero, zero_add] at key
  rw [Matrix.trace_sum] at key
  simp only [Matrix.trace_add, tr] at key
  simpa only [Finsupp.linearCombination_apply] using key
end

section

noncomputable section

open Matrix

namespace UpperTheory.V.Pa.Det

private theorem der_mul {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n)
    (z : G → Matrix (Fin n) (Fin n) F) (hz : TwCoc (fun _ => 1) D.r D.G' z) {g h : G} (hg : g ∈ D.G') (hh : h ∈ D.G') :
    z (g * h) * D.r (g * h) = z g * D.r g * D.r h + D.r g * (z h * D.r h) := by
  have h1 := hz g hg h hh
  simp only [one_smul] at h1
  have hinv : D.r g⁻¹ * D.r g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  rw [h1, map_mul, add_mul]
  congr 1
  · simp only [Matrix.mul_assoc]
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (D.r g⁻¹), hinv, Matrix.one_mul]

private theorem move_one {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n)
    (z : G → Matrix (Fin n) (Fin n) F) (i j : Fin n) (hz : TwCoc (fun _ => 1) D.r D.G' z) (hk : D.KillsRel z i j)
    (c : G →₀ F) (hc : ∀ g ∈ c.support, g ∈ D.G') (h0 : c.sum (fun g x => x • D.r g) = 0)
    {u v : G} (hu : u ∈ D.G') (hv : v ∈ D.G') :
    (D.r u * (c.sum fun g x => x • (z g * D.r g)) * D.r v) i j = 0 := by
  classical
  have hsum : ∀ M : G → Matrix (Fin n) (Fin n) F,
      (Finsupp.mapDomain (fun g => u * g * v) c).sum (fun g x => x • M g) = c.sum (fun g x => x • M (u * g * v)) := by
    intro M
    exact Finsupp.sum_mapDomain_index (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)
  have hsupp : ∀ g ∈ (Finsupp.mapDomain (fun g => u * g * v) c).support, g ∈ D.G' := by
    intro g hg
    obtain ⟨k, hk', rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hg)
    exact D.G'.mul_mem (D.G'.mul_mem hu (hc k hk')) hv
  have hr : ∀ M : G → Matrix (Fin n) (Fin n) F, ∀ P Q : Matrix (Fin n) (Fin n) F,
      P * (c.sum fun g x => x • M g) * Q = c.sum fun g x => x • (P * M g * Q) := by
    intro M P Q
    simp only [Finsupp.sum, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  have h0' : (Finsupp.mapDomain (fun g => u * g * v) c).sum (fun g x => x • D.r g) = 0 := by
    rw [hsum]
    simp only [map_mul]
    rw [← hr, h0, Matrix.mul_zero, Matrix.zero_mul]
  have key := hk _ hsupp h0'
  rw [hsum] at key
  have expand : ∀ g ∈ c.support, c g • (z (u * g * v) * D.r (u * g * v)) =
      c g • (z u * D.r u * D.r g * D.r v) + c g • (D.r u * (z g * D.r g) * D.r v) + c g • (D.r u * D.r g * (z v * D.r v)) := by
    intro g hg
    rw [mul_assoc, der_mul D z hz hu (D.G'.mul_mem (hc g hg) hv), der_mul D z hz (hc g hg) hv, ← smul_add, ← smul_add]
    congr 1
    simp only [map_mul, Matrix.mul_add, Matrix.mul_assoc, add_assoc]
  have eq : (c.sum fun g x => x • (z (u * g * v) * D.r (u * g * v))) =
      z u * D.r u * (c.sum fun g x => x • D.r g) * D.r v + D.r u * (c.sum fun g x => x • (z g * D.r g)) * D.r v
        + D.r u * (c.sum fun g x => x • D.r g) * (z v * D.r v) := by
    rw [hr, hr, hr]
    simp only [Finsupp.sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl expand
  rw [eq, h0] at key
  simpa using key

private theorem single_mem {F : Type} [Field F] {n a : ℕ} (i i' : Fin n) (h : (i : ℕ) < a ↔ (i' : ℕ) < a) :
    Matrix.single i i' (1 : F) ∈ Ev F F n a := by
  intro p q
  refine ⟨fun _ => Submodule.mem_top, fun hpq => ?_⟩
  rw [Submodule.mem_bot, Matrix.single_apply]
  split_ifs with hh
  · obtain ⟨rfl, rfl⟩ := hh
    exact absurd h hpq
  · rfl

theorem relMove {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n)
    (z : G → Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    TwCoc (fun _ => 1) D.r D.G' z → D.KillsRel z i j →
      ∀ i' j' : Fin n, ((i : ℕ) < D.a ↔ (i' : ℕ) < D.a) → ((j : ℕ) < D.a ↔ (j' : ℕ) < D.a) → D.KillsRel z i' j' := by
  intro hz hk i' j' hi hj c hc h0
  have hA : Matrix.single i i' (1 : F) ∈ Submodule.span F (D.r '' D.G') := by
    rw [D.span]
    exact single_mem i i' hi
  have hB : Matrix.single j' j (1 : F) ∈ Submodule.span F (D.r '' D.G') := by
    rw [D.span]
    exact single_mem j' j hj.symm
  have hgen : ∀ A ∈ Submodule.span F (D.r '' D.G'), ∀ B ∈ Submodule.span F (D.r '' D.G'),
      (A * (c.sum fun g x => x • (z g * D.r g)) * B) i j = 0 := by
    intro A hA' B hB'
    induction hA' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      induction hB' using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨v, hv, rfl⟩ := hy
        exact move_one D z i j hz hk c hc h0 hu hv
      | zero => simp
      | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_apply, hx, hy, add_zero]
      | smul a x _ hx => rw [Matrix.mul_smul, Matrix.smul_apply, hx, smul_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.add_mul, Matrix.add_mul, Matrix.add_apply, hx, hy, add_zero]
    | smul a x _ hx => rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_apply, hx, smul_zero]
  have := hgen _ hA _ hB
  simpa [Matrix.mul_apply, Matrix.single_apply] using this

end UpperTheory.V.Pa.Det
end
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem cut_conj {F : Type} [Field F] {n : ℕ} (p q : Fin n → Prop) [DecidablePred p] [DecidablePred q]
    [∀ i j, Decidable (p i ∧ q j)] (A Z B : Matrix (Fin n) (Fin n) F)
    (hA : ∀ i k, ¬ (p i ↔ p k) → A i k = 0) (hB : ∀ i k, ¬ (q i ↔ q k) → B i k = 0) :
    (Matrix.of fun i j => if p i ∧ q j then (A * Z * B) i j else 0) =
      A * (Matrix.of fun i j => if p i ∧ q j then Z i j else 0) * B := by
  ext i j
  have key : (if p i ∧ q j then (A * Z * B) i j else 0) =
      ∑ m, ∑ k, if p i ∧ q j then A i k * Z k m * B m j else 0 := by
    split_ifs
    · simp only [Matrix.mul_apply, Finset.sum_mul]
    · simp
  rw [Matrix.of_apply, key]
  simp only [Matrix.mul_apply, Finset.sum_mul, Matrix.of_apply]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases h1 : p i ↔ p k
  · by_cases h2 : q m ↔ q j
    · by_cases h : p i ∧ q j
      · rw [if_pos h, if_pos ⟨h1.1 h.1, h2.2 h.2⟩]
      · rw [if_neg h, if_neg (fun h' => h ⟨h1.2 h'.1, h2.1 h'.2⟩)]; simp
    · simp [hB m j h2]
  · simp [hA i k h1]

private theorem cV_conj {F : Type} [Field F] {n a : ℕ} {A B : Matrix (Fin n) (Fin n) F}
    (hA : A ∈ Ev F F n a) (hB : B ∈ Ev F F n a) (Z : Matrix (Fin n) (Fin n) F) :
    cV a (A * Z * B) = A * cV a Z * B ∧ cV' a (A * Z * B) = A * cV' a Z * B := by
  have hA' : ∀ i k : Fin n, ¬ ((i : ℕ) < a ↔ (k : ℕ) < a) → A i k = 0 := fun i k h => by
    simpa using (hA i k).2 h
  have hB' : ∀ i k : Fin n, ¬ ((i : ℕ) < a ↔ (k : ℕ) < a) → B i k = 0 := fun i k h => by
    simpa using (hB i k).2 h
  exact ⟨cut_conj (fun i => (i : ℕ) < a) (fun i => ¬ (i : ℕ) < a) A Z B hA'
      (fun i k h => hB' i k (fun e => h (not_congr e))),
    cut_conj (fun i => ¬ (i : ℕ) < a) (fun i => (i : ℕ) < a) A Z B
      (fun i k h => hA' i k (fun e => h (not_congr e))) hB'⟩

private theorem cV_lin {F : Type} [Field F] {n : ℕ} (a : ℕ) (c : F) (Y Z : Matrix (Fin n) (Fin n) F) :
    (cV a (Y + c • Z) = cV a Y + c • cV a Z ∧ cV' a (Y + c • Z) = cV' a Y + c • cV' a Z) ∧
    (cV a (c • Z - Y) = c • cV a Z - cV a Y ∧ cV' a (c • Z - Y) = c • cV' a Z - cV' a Y) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> ext i j <;>
    simp only [cV, cV', Matrix.of_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply] <;>
    split_ifs <;> simp

theorem UpperTheory.V.Pa.Det.cornerCoc :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (χ : G → F) (S : Set G) (z : G → Matrix (Fin n) (Fin n) F), TwCoc χ D.r S z → (TwCoc χ D.r S fun g => cV D.a (z g)) ∧ (TwCoc χ D.r S fun g => cV' D.a (z g)) ∧ (∀ Y g, cV D.a (dTw χ D.r Y g) = dTw χ D.r (cV D.a Y) g ∧ cV' D.a (dTw χ D.r Y g) = dTw χ D.r (cV' D.a Y) g) ∧ ∀ Z : Matrix (Fin n) (Fin n) F, cV D.a Z ∈ Od F F n D.a ∧ cV' D.a Z ∈ Od F F n D.a ∧ (cV D.a Z)ᵀ = cV' D.a Zᵀ ∧ (Z ∈ Od F F n D.a → cV D.a Z + cV' D.a Z = Z) := by
  intro F G _ _ n D χ S z hz
  refine ⟨fun g hg h hh => ?_, fun g hg h hh => ?_, fun Y g => ⟨?_, ?_⟩, fun Z => ⟨?_, ?_, ?_, fun hZ => ?_⟩⟩
  · beta_reduce
    rw [hz g hg h hh, (cV_lin _ _ _ _).1.1, (cV_conj (D.ev _) (D.ev _) _).1]
  · beta_reduce
    rw [hz g hg h hh, (cV_lin _ _ _ _).1.2, (cV_conj (D.ev _) (D.ev _) _).2]
  · unfold dTw
    rw [(cV_lin _ _ _ _).2.1, (cV_conj (D.ev _) (D.ev _) _).1]
  · unfold dTw
    rw [(cV_lin _ _ _ _).2.2, (cV_conj (D.ev _) (D.ev _) _).2]
  · intro i j
    refine ⟨fun e => ?_, fun _ => Submodule.mem_top⟩
    rw [Submodule.mem_bot, cV, Matrix.of_apply, if_neg (fun h => h.2 (e.1 h.1))]
  · intro i j
    refine ⟨fun e => ?_, fun _ => Submodule.mem_top⟩
    rw [Submodule.mem_bot, cV', Matrix.of_apply, if_neg (fun h => h.1 (e.2 h.2))]
  · ext i j
    simp only [cV, cV', Matrix.of_apply, Matrix.transpose_apply, and_comm]
  · ext i j
    have h0 : ((i : ℕ) < D.a ↔ (j : ℕ) < D.a) → Z i j = 0 := fun e => by simpa using (hZ i j).1 e
    simp only [cV, cV', Matrix.of_apply, Matrix.add_apply]
    by_cases hi : (i : ℕ) < D.a <;> by_cases hj : (j : ℕ) < D.a
    · simp [hi, hj, h0 (iff_of_true hi hj)]
    · rw [if_pos ⟨hi, hj⟩, if_neg (fun h => h.1 hi), add_zero]
    · rw [if_neg (fun h => hi h.1), if_pos ⟨hi, hj⟩, zero_add]
    · rw [if_neg (fun h => hi h.1), if_neg (fun h => hj h.2), add_zero, h0 (iff_of_false hi hj)]
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.central :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (Z : Matrix (Fin n) (Fin n) F), (∀ g ∈ D.G', D.r g * Z = Z * D.r g) → (Z ∈ Od F F n D.a → Z = 0) ∧ (Z ∈ Ev F F n D.a → ∀ g, D.r g * Z = Z * D.r g) := by
  intro F G _ _ n D Z hZ
  have key : ∀ X ∈ Ev F F n D.a, X * Z = Z * X := by
    intro X hX
    rw [← D.span] at hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      exact hZ g hg
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]
    | smul c x _ hx => rw [Matrix.smul_mul, Matrix.mul_smul, hx]
  refine ⟨fun hO => ?_, fun _ g => key _ (D.ev g)⟩
  ext i j
  by_cases hij : ((i : ℕ) < D.a ↔ (j : ℕ) < D.a)
  · simpa using (hO i j).1 hij
  · have hne : i ≠ j := fun h => hij (by rw [h])
    have hE : Matrix.diagonal (Pi.single i (1 : F)) ∈ Ev F F n D.a := by
      intro p q
      refine ⟨fun _ => Submodule.mem_top, fun h => ?_⟩
      have hpq : p ≠ q := fun e => h (by rw [e])
      simp [Matrix.diagonal_apply_ne _ hpq]
    have h := congrFun (congrFun (key _ hE) i) j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at h
    simpa [Pi.single_eq_of_ne hne.symm] using h
end
