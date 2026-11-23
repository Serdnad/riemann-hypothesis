module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle144
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle036
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle037
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle145
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.FiniteLength
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle146
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.LBSpreads
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle147
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatPdpEq

section
variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

def dq (i : ℕ) : ℚ := ((i.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ i

theorem dq_ne_zero (hl : l ≠ 0) (i : ℕ) : dq l M i ≠ 0 := by
  have h1 : (l : ℚ) ≠ 0 := by exact_mod_cast hl
  have h2 : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  unfold dq
  positivity

theorem dpE_eq_smul (i : ℕ) : Lat.dpE f ξ l M i = dq l M i • f ξ ^ i := by
  unfold Lat.dpE Lat.η dq
  rw [smul_pow, smul_smul]

theorem dpE_eq_zero {m i : ℕ} (hm : f ξ ^ m = 0) (hi : m ≤ i) : Lat.dpE f ξ l M i = 0 := by
  rw [dpE_eq_smul, ← Nat.add_sub_of_le hi, pow_add, hm, zero_mul, smul_zero]

theorem dpE_mem_span {k i : ℕ} (hi : k ≤ i) : Lat.dpE f ξ l M i ∈ Ideal.span {f ξ ^ k} := by
  rw [dpE_eq_smul, Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton.2 (pow_dvd_pow _ hi))

theorem ι_mem (x : Lat.A f ξ l M) : Lat.ι f ξ l M x ∈ Lat.sub f ξ l M :=
  Subtype.property (p := fun y => y ∈ Lat.sub f ξ l M) x

theorem dpA_one_mem : Lat.dpA f ξ l M 1 ∈ Lat.I f ξ l M := by
  show Lat.dpE f ξ l M 1 ∈ Lat.IB f ξ
  have := dpE_mem_span f ξ l M (k := 1) le_rfl
  simpa [Lat.IB] using this

theorem dpow_dpA (hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ)) (i : ℕ) :
    (Lat.γ f ξ l M hc).dpow i (Lat.dpA f ξ l M 1) = Lat.dpA f ξ l M i := by
  apply Lat.ι_injective f ξ l M
  rw [Lat.ι_γ f ξ l M hc (dpA_one_mem f ξ l M), Lat.ι_dpA, Lat.ι_dpA]
  have hy : Lat.dpE f ξ l M 1 ∈ Lat.IB f ξ := dpA_one_mem f ξ l M
  rw [RatAlgebra.dpow_eq_inv_fact_smul _ (Lat.γB f ξ) hy, Ring.inverse_eq_inv']
  simp [Lat.dpE]

theorem dpA_mem_pdP (hl : l ≠ 0) (hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ)) {r i : ℕ} (hi : r ≤ i) :
    Lat.dpA f ξ l M i ∈ pdP (Lat.γ f ξ l M hc) r := by
  refine Ideal.subset_span ⟨[(i, Lat.dpA f ξ l M 1)], ?_, by simpa using hi, ?_⟩
  · intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact dpA_one_mem f ξ l M
  · simp [dpow_dpA f ξ l M hc i]

variable {f ξ l M}

theorem coeff_dvd {m j : ℕ} (h : Lat.Hyp f ξ l m) (hl : l ≠ 0) (hj : j < m) (c : ℕ → W)
    (hy : ∑ i ∈ Finset.Ico j (m + 1), f (c i) * Lat.dpE f ξ l M i ∈ Ideal.span {f ξ ^ (j + 1)}) :
    ξ ∣ c j := by
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)] at hy
  have ht : ∑ i ∈ Finset.Ico (j + 1) (m + 1), f (c i) * Lat.dpE f ξ l M i ∈ Ideal.span {f ξ ^ (j + 1)} :=
    Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ (dpE_mem_span f ξ l M (Finset.mem_Ico.1 hi).1)
  have hh := (Ideal.add_mem_iff_left _ ht).1 hy
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 hh
  refine h.gr j hj (c j) ((dq l M j)⁻¹ • b) ?_
  rw [dpE_eq_smul, mul_smul_comm] at hb
  rw [mul_smul_comm, ← hb, smul_smul, inv_mul_cancel₀ (dq_ne_zero l M hl j), one_smul]

theorem push {m j : ℕ} (h : Lat.Hyp f ξ l m) (hl : l ≠ 0) (hj : j < m) (c : ℕ → W) {y : B}
    (e : y = ∑ i ∈ Finset.Ico j (m + 1), f (c i) * Lat.dpE f ξ l M i)
    (hy : y ∈ Ideal.span {f ξ ^ (j + 1)}) :
    ∃ c' : ℕ → W, y = ∑ i ∈ Finset.Ico (j + 1) (m + 1), f (c' i) * Lat.dpE f ξ l M i := by
  obtain ⟨d, hd⟩ := coeff_dvd h hl hj c (M := M) (e ▸ hy)
  refine ⟨Function.update c (j + 1) (c (j + 1) + d * ((l : W) ^ M * ((j : W) + 1))), ?_⟩
  rw [e, Finset.sum_eq_sum_Ico_succ_bot (by omega), Finset.sum_eq_sum_Ico_succ_bot (a := j + 1) (by omega),
    Finset.sum_eq_sum_Ico_succ_bot (a := j + 1) (by omega)]
  have hs : ∑ i ∈ Finset.Ico (j + 1 + 1) (m + 1), f (Function.update c (j + 1)
      (c (j + 1) + d * ((l : W) ^ M * ((j : W) + 1))) i) * Lat.dpE f ξ l M i =
      ∑ i ∈ Finset.Ico (j + 1 + 1) (m + 1), f (c i) * Lat.dpE f ξ l M i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (by have := (Finset.mem_Ico.1 hi).1; omega)]
  rw [hs, Function.update_self, hd, map_mul, mul_assoc, mul_left_comm (f ξ) (f d), GlobalTheory.CompanionTheory.LatDp.mul_divPow_eq f ξ l M hl j]
  simp only [map_add (f := _), map_mul, map_pow, map_natCast, map_one]
  ring

theorem exists_rep {m : ℕ} (hm : f ξ ^ m = 0) {y : B} (hy : y ∈ Lat.sub f ξ l M) :
    ∃ c : ℕ → W, y = ∑ i ∈ Finset.Ico 0 (m + 1), f (c i) * Lat.dpE f ξ l M i := by
  obtain ⟨n, c, rfl⟩ := (GlobalTheory.CompanionTheory.LatSpan.mem_sub_iff f ξ l M y).1 hy
  refine ⟨fun i => if h : i < n then c ⟨i, h⟩ else 0, ?_⟩
  have h1 : ∑ i : Fin n, f (c i) * Lat.dpE f ξ l M i =
      ∑ i ∈ Finset.range n, f (if h : i < n then c ⟨i, h⟩ else 0) * Lat.dpE f ξ l M i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => f (if h : i < n then c ⟨i, h⟩ else 0) * Lat.dpE f ξ l M i) n]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  rw [h1, Nat.Ico_zero_eq_range]
  have h2 := Finset.sum_subset (s₁ := Finset.range n) (s₂ := Finset.range (n + m + 1))
    (f := fun i => f (if h : i < n then c ⟨i, h⟩ else 0) * Lat.dpE f ξ l M i)
    (fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega)
    (fun i _ hi => by simp only [Finset.mem_range] at hi; simp [hi])
  have h3 := Finset.sum_subset (s₁ := Finset.range (m + 1)) (s₂ := Finset.range (n + m + 1))
    (f := fun i => f (if h : i < n then c ⟨i, h⟩ else 0) * Lat.dpE f ξ l M i)
    (fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega)
    (fun i _ hi => by
      simp only [Finset.mem_range] at hi
      simp only [dpE_eq_zero f ξ l M hm (show m ≤ i by omega), mul_zero])
  exact h2.trans h3.symm

theorem exists_rep_high {m r : ℕ} (h : Lat.Hyp f ξ l m) (hl : l ≠ 0) {y : B} (hy : y ∈ Lat.sub f ξ l M)
    (hr : y ∈ Ideal.span {f ξ ^ r}) (j : ℕ) (hjr : j ≤ r) (hjm : j ≤ m) :
    ∃ c : ℕ → W, y = ∑ i ∈ Finset.Ico j (m + 1), f (c i) * Lat.dpE f ξ l M i := by
  induction j with
  | zero => exact exists_rep h.nil hy
  | succ j ih =>
    obtain ⟨c, e⟩ := ih (by omega) (by omega)
    have hle : Ideal.span {f ξ ^ r} ≤ Ideal.span {f ξ ^ (j + 1)} :=
      Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ hjr)
    exact push h hl (by omega) c e (hle hr)

end

theorem dividedPowerFiltration_eq : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ),
    Lat.Hyp f ξ l m → ∀ hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ), ∀ r : ℕ,
    pdP (Lat.γ f ξ l M hc) r = (Ideal.span {f ξ ^ r}).comap (Lat.ι f ξ l M) := by
  intro W B _ _ _ f ξ l M m h hc r
  have hl : l ≠ 0 := fun e => h.l0 (by simp [e])
  apply le_antisymm
  · intro x hx
    have hdp : IsDPMorphism (Lat.γ f ξ l M hc) (Lat.γB f ξ) (Lat.ι f ξ l M) :=
      ⟨Ideal.map_le_iff_le_comap.2 le_rfl, fun {n} a ha => (Lat.ι_γ f ξ l M hc ha).symm⟩
    have := dividedPowerFiltration_map hdp r hx
    rwa [GlobalTheory.CompanionTheory.DPFiltration.pdP_γB f ξ r] at this
  · intro x hx
    obtain ⟨c, e⟩ := exists_rep_high h hl (ι_mem f ξ l M x) hx (min r m) (by omega) (by omega)
    have hx' : x = ∑ i ∈ Finset.Ico (min r m) (m + 1), Lat.ofW f ξ l M (c i) * Lat.dpA f ξ l M i := by
      apply Lat.ι_injective f ξ l M

      rw [e, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, Lat.ι_ofW, Lat.ι_dpA]
    rw [hx']
    refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hi
    by_cases hir : r ≤ i
    · exact dpA_mem_pdP f ξ l M hl hc hir
    · have : Lat.dpA f ξ l M i = 0 := by
        apply Lat.ι_injective f ξ l M
        rw [Lat.ι_dpA, map_zero]
        exact dpE_eq_zero f ξ l M h.nil (by omega)
      rw [this]
      exact Ideal.zero_mem _

end GlobalTheory.CompanionTheory.LatPdpEq
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.exists_dual_derivations_of_coords : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (d : ℕ) (c : Coord q V d), letI := (strV q V).toAlgebra; ∃ D : Fin d → Derivation K Γ(X, V) Γ(X, V), ∀ k j, D k (c.t j) = if k = j then 1 else 0 := by
  first | exact @GlobalTheory.CompanionTheory.ConeDerivs.exists_dual_derivations | exact GlobalTheory.CompanionTheory.ConeDerivs.exists_dual_derivations | (intros; apply GlobalTheory.CompanionTheory.ConeDerivs.exists_dual_derivations <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ChartFil

section Rings

variable {R B : Type} [CommRing R] [CommRing B] {I : Ideal R} {J : Ideal B}

theorem dividedPowerFiltration_anti (δ : DividedPowers J) {r r' : ℕ} (h : r ≤ r') : pdP δ r' ≤ pdP δ r :=
  Ideal.span_mono fun _ ⟨l, hl, hr, hz⟩ => ⟨l, hl, h.trans hr, hz⟩

theorem one_mem_pdP_zero (δ : DividedPowers J) : (1 : B) ∈ pdP δ 0 :=
  Ideal.subset_span ⟨[], by simp, by simp, by simp⟩

theorem mul_mem_map (γ : DividedPowers I) (i : R →+* B) (r r' : ℕ) {x y : B}
    (hx : x ∈ (pdP γ r).map i) (hy : y ∈ (pdP γ r').map i) : x * y ∈ (pdP γ (r + r')).map i := by
  have h := Ideal.mul_mem_mul hx hy
  rw [← Ideal.map_mul] at h
  exact Ideal.map_mono (GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_mul_le γ r r') h

theorem dpow_mem_map (γ : DividedPowers I) (δ : DividedPowers J) (i : R →+* B) (hi : IsDPMorphism γ δ i)
    (hJ : J = I.map i) {x : B} (hx : x ∈ J) (n : ℕ) : δ.dpow n x ∈ (pdP γ n).map i := by
  have h0 : ∀ y ∈ J, δ.dpow 0 y ∈ (pdP γ 0).map i := fun y hy => by
    rw [δ.dpow_zero hy, ← map_one i]
    exact Ideal.mem_map_of_mem i (one_mem_pdP_zero γ)
  rw [hJ] at hx
  revert n
  refine Submodule.span_induction (p := fun x _ => ∀ n, δ.dpow n x ∈ (pdP γ n).map i) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, ha, rfl⟩ n
    rw [hi.2 a ha]
    exact Ideal.mem_map_of_mem i (GlobalTheory.CompanionTheory.DPFil.dpow_mem_pdP γ n ha)
  · intro n
    by_cases hn : n = 0
    · subst hn
      exact h0 0 J.zero_mem
    · rw [δ.dpow_eval_zero hn]
      exact Ideal.zero_mem _
  · intro y z hy hz ihy ihz n
    have hy' : y ∈ J := hJ ▸ hy
    have hz' : z ∈ J := hJ ▸ hz
    rw [δ.dpow_add hy' hz']
    refine Ideal.sum_mem _ fun ab hab => ?_
    have e : ab.1 + ab.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
    rw [← e]
    exact mul_mem_map γ i _ _ (ihy _) (ihz _)
  · intro a y hy ihy n
    have hy' : y ∈ J := hJ ▸ hy
    rw [smul_eq_mul, δ.dpow_mul hy']
    exact Ideal.mul_mem_left _ _ (ihy n)

theorem dividedPowerFiltration_eq_map (γ : DividedPowers I) (δ : DividedPowers J) (i : R →+* B) (hi : IsDPMorphism γ δ i)
    (hJ : J = I.map i) (r : ℕ) : pdP δ r = (pdP γ r).map i := by
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.map_le_iff_le_comap.2 fun x hx => dividedPowerFiltration_map hi r hx)
  rintro _ ⟨l, hl, hr, rfl⟩
  have key : ∀ l : List (ℕ × B), (∀ q ∈ l, q.2 ∈ J) →
      (l.map fun q => δ.dpow q.1 q.2).prod ∈ (pdP γ (l.map Prod.fst).sum).map i := by
    intro l
    induction l with
    | nil =>
      intro _
      simp only [List.map_nil, List.prod_nil, List.sum_nil]
      rw [← map_one i]
      exact Ideal.mem_map_of_mem i (one_mem_pdP_zero γ)
    | cons a t ih =>
      intro h
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      exact mul_mem_map γ i _ _ (dpow_mem_map γ δ i hi hJ (h a (by simp)) _)
        (ih fun q hq => h q (List.mem_cons_of_mem _ hq))
  exact Ideal.map_mono (dividedPowerFiltration_anti γ hr) (key l hl)

end Rings

variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ}

theorem sub_mem_J (c : Chart γ p q κ V d) {T : Thick (nlFun γ p X q κ)} (hT : InU V T) (f g : c.D ⟶ T)
    (z : c.D.B) : f.φ z - g.φ z ∈ T.J := by
  obtain ⟨φ, -, hu⟩ := c.rep (CommRingCat.of (T.B ⧸ T.J)) T.y hT
  have e := (hu _ f.pt).trans (hu _ g.pt).symm
  exact Ideal.Quotient.eq.1 (RingHom.congr_fun e (Ideal.Quotient.mk _ z))

theorem sub_mem_pdP (c : Chart γ p q κ V d) {T : Thick (nlFun γ p X q κ)} (hT : InU V T) (f g : c.D ⟶ T)
    (n : ℕ) {x : c.D.B} (hx : x ∈ (pdP γ n).map c.D.i) : f.φ x - g.φ x ∈ pdP T.δ (n + 1) := by
  refine Submodule.span_induction (p := fun x _ => f.φ x - g.φ x ∈ pdP T.δ (n + 1)) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, -, rfl⟩
    have e : f.φ (c.D.i a) - g.φ (c.D.i a) = 0 := by rw [f.comm, g.comm, sub_self]
    rw [e]
    exact Ideal.zero_mem _
  · rw [map_zero, map_zero, sub_zero]
    exact Ideal.zero_mem _
  · intro y z _ _ hy hz
    rw [map_add (f := _), map_add (f := _), add_sub_add_comm]
    exact Ideal.add_mem _ hy hz
  · intro a y hy ih
    have e : f.φ (a • y) - g.φ (a • y) = f.φ a * (f.φ y - g.φ y) + (f.φ a - g.φ a) * g.φ y := by
      rw [smul_eq_mul, map_mul, map_mul]
      ring
    rw [e]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ih) ?_
    have h1 : f.φ a - g.φ a ∈ pdP T.δ 1 := T.J_le_pdPow_one (sub_mem_J c hT f g a)
    have hm : (pdP γ n).map c.D.i ≤ pdP c.D.δ n :=
      Ideal.map_le_iff_le_comap.2 fun x hx => dividedPowerFiltration_map c.D.compat n hx
    have hy' : y ∈ pdP c.D.δ n := hm hy
    have h2 : g.φ y ∈ pdP T.δ n := dividedPowerFiltration_map g.dp n hy'
    have h3 := GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_mul_le T.δ 1 n (Ideal.mul_mem_mul h1 h2)
    rwa [add_comm 1 n] at h3

theorem chart_grConst : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) (h : c.Good)
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (hQ : ∀ T, Q T → InU V T) (hD : Q c.D),
    (∀ r, c.D.pdPow r = (pdP γ r).map c.D.i) ∧ (c.frame h Q hQ hD).GrConst (sFil Q) := by
  intro O R _ _ I γ p X q κ V d c h Q hQ hD
  have h1 : ∀ r, c.D.pdPow r = (pdP γ r).map c.D.i := fun r =>
    dividedPowerFiltration_eq_map γ c.D.δ c.D.i c.D.compat c.J_eq r
  refine ⟨h1, ?_⟩
  intro n T σ σ' x hx
  have hx' : (show c.D.B from x) ∈ c.D.pdPow ((n : ℤ).toNat) := hx
  rw [Int.toNat_natCast, h1] at hx'
  change _ ∈ T.obj.pdPow (((n : ℤ) + 1).toNat)
  have e : ((n : ℤ) + 1).toNat = n + 1 := by omega
  rw [e]
  exact sub_mem_pdP c (hQ _ T.property) σ.hom σ'.hom n hx'

end GlobalTheory.CompanionTheory.ChartFil
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.coord_dim_eq_relative_dim : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n q] {V : X.Opens}, (V : Set X).Nonempty → ∀ {m : ℕ} (c : Coord q V m), m = n := by
  first | exact @GlobalTheory.CompanionTheory.CoordCard.main | exact GlobalTheory.CompanionTheory.CoordCard.main | (intros; apply GlobalTheory.CompanionTheory.CoordCard.main <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.exists_smooth_coordinate_cover : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [IsSeparated q] [QuasiCompact q],
    (Smooth q → Nonempty (Cov q)) ∧ ∀ d, SmoothOfRelativeDimension d q → ∃ U : Cov q, ∀ α, U.d α = d := by
  first | exact @GlobalTheory.CompanionTheory.CovEx.exists_cov | exact GlobalTheory.CompanionTheory.CovEx.exists_cov | (intros; apply GlobalTheory.CompanionTheory.CovEx.exists_cov <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.inOpen_of_thickening_morphism : ∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (V : X.Opens) {T T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T'), InU V T → InU V T' := by
  first | exact @GlobalTheory.CompanionTheory.ThickPt.inU_map | exact GlobalTheory.CompanionTheory.ThickPt.inU_map | (intros; apply GlobalTheory.CompanionTheory.ThickPt.inU_map <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.sheaf_filtration_property : ∀ {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)), IsFil (sP Q) (sFil Q) := by
  first | exact @GlobalTheory.CompanionTheory.DPFil.isFil_sFil | exact GlobalTheory.CompanionTheory.DPFil.isFil_sFil | (intros; apply GlobalTheory.CompanionTheory.DPFil.isFil_sFil <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.chart_is_good : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d), c.Good := by
  first | exact @GlobalTheory.CompanionTheory.ChartMaps.good | exact GlobalTheory.CompanionTheory.ChartMaps.good | (intros; apply GlobalTheory.CompanionTheory.ChartMaps.good <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.square_pull_bijective_of_acyclic : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (a b : IdF A) (ha : ∀ T, a.S T = ⊤),
    (∀ j, Subsingleton (CH.H (sq b (IdF.bot A)) j)) → ∀ j, Function.Bijective ((toSq a b ha).pull j) := by
  first | exact @GlobalTheory.CompanionTheory.LengthOneCochainExactness.pull_toSq_bijective | exact GlobalTheory.CompanionTheory.LengthOneCochainExactness.pull_toSq_bijective | (intros; apply GlobalTheory.CompanionTheory.LengthOneCochainExactness.pull_toSq_bijective <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.StFam

theorem st_all :
    (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) {ι : Type} (U : ι → X.Opens) (α : ι) ⦃T T' : Thick (nlFun γ p X q κ)⦄ (φ : T ⟶ T'), St Q {U α} T → (∃ β, St Q {U β} T') → St Q {U α} T') ∧ (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) {ι : Type} (U : ι → X.Opens), (fun T => ∃ α, St Q {U α} T) = St Q (Set.range U)) ∧ (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) {ι : Type} (U : ι → X.Opens) (S : Finset ι), S.Nonempty → capS (fun α => St Q {U α}) S = St Q {⨅ α ∈ S, U α}) ∧ (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin (n + 1) → ι), capT (fun α => St Q {U α}) i = St Q {capO U i}) := by
  have one : ∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
      {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}
      (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (V : X.Opens) (T : Thick (nlFun γ p X q κ)),
      St Q {V} T ↔ Q T ∧ InU V T := by
    intro O _ R _ I γ p X q κ Q V T
    constructor
    · rintro ⟨hQ, W, hW, hT⟩
      rw [Set.mem_singleton_iff] at hW
      subst hW
      exact ⟨hQ, hT⟩
    · rintro ⟨hQ, hT⟩
      exact ⟨hQ, V, rfl, hT⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro O _ R _ I γ p X q κ Q ι U α T T' φ h h'
    obtain ⟨β, hβ⟩ := h'
    exact (one Q _ T').2 ⟨((one Q _ T').1 hβ).1, GlobalTheory.CompanionTheory.ThickPt.inU_map (U α) φ ((one Q _ T).1 h).2⟩
  · intro O _ R _ I γ p X q κ Q ι U
    funext T
    refine propext ⟨?_, ?_⟩
    · rintro ⟨α, hα⟩
      obtain ⟨hQ, hT⟩ := (one Q _ T).1 hα
      exact ⟨hQ, U α, ⟨α, rfl⟩, hT⟩
    · rintro ⟨hQ, V, ⟨α, rfl⟩, hT⟩
      exact ⟨α, (one Q _ T).2 ⟨hQ, hT⟩⟩
  · intro O _ R _ I γ p X q κ Q ι U S hS
    funext T
    refine propext ⟨?_, ?_⟩
    · intro h
      obtain ⟨a, ha⟩ := hS
      exact (one Q _ T).2 ⟨((one Q _ T).1 (h a ha)).1,
        (GlobalTheory.CompanionTheory.Thick.inU_iInf_finset U S T).2 fun α hα => ((one Q _ T).1 (h α hα)).2⟩
    · intro h α hα
      obtain ⟨hQ, hT⟩ := (one Q _ T).1 h
      exact (one Q _ T).2 ⟨hQ, (GlobalTheory.CompanionTheory.Thick.inU_iInf_finset U S T).1 hT α hα⟩
  · intro O _ R _ I γ p X q κ Q ι U n i
    have key : ∀ T : Thick (nlFun γ p X q κ), InU (capO U i) T ↔ ∀ a, InU (U (i a)) T := by
      intro T
      have h := GlobalTheory.CompanionTheory.Thick.inU_iInf_finset (fun a => U (i a)) (Finset.univ : Finset (Fin (n + 1))) T
      have e : (⨅ a ∈ (Finset.univ : Finset (Fin (n + 1))), U (i a)) = capO U i := by
        simp [capO]
      rw [e] at h
      simpa using h
    funext T
    refine propext ⟨?_, ?_⟩
    · intro h
      exact (one Q _ T).2 ⟨((one Q _ T).1 (h 0)).1, (key T).2 fun a => ((one Q _ T).1 (h a)).2⟩
    · intro h a
      obtain ⟨hQ, hT⟩ := (one Q _ T).1 h
      exact (one Q _ T).2 ⟨hQ, (key T).1 hT a⟩

end GlobalTheory.CompanionTheory.StFam
end

section

open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

theorem _root_.GlobalTheory.T.module_finite_limit_of_lseq : ∀ (W : Type) [CommRing W] (l : ℕ) [IsAdicComplete (Ideal.span {(l : W)}) W] (S S' : Sys.{1} W) (_ : LSeq l S S'), IsFiniteLength W (S.M 1) → Module.Finite W S.lim := by
  first | exact @GlobalTheory.CompanionTheory.TowerLim.module_finite_lim | exact GlobalTheory.CompanionTheory.TowerLim.module_finite_lim | (intros; apply GlobalTheory.CompanionTheory.TowerLim.module_finite_lim <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.SpreadingModels

theorem _root_.GlobalTheory.T.has_model_of_spreading : GlobalTheory.SpreadingModels.SchemeModels → GlobalTheory.SpreadingModels.Spreads (fun _ _ f => Smooth f) → GlobalTheory.SpreadingModels.Spreads (fun _ _ f => IsProper f) → GlobalTheory.SpreadingModels.LBSpreads → ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)), Smooth f → IsProper f → ∀ M : LB Y, M.IsLB → GlobalTheory.SpreadingModels.HasModel f M := by
  first | exact @GlobalTheory.CompanionTheory.CubeModels.hasModel_of_spreads | exact GlobalTheory.CompanionTheory.CubeModels.hasModel_of_spreads | (intros; apply GlobalTheory.CompanionTheory.CubeModels.hasModel_of_spreads <;> assumption)
end
