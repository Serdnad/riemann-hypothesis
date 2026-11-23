module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle240
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle222
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle239
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle259
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.WeilCorr

open GlobalTheory.NormSum.MovedTheta

theorem exists_close_two {R E : Type} [CommRing R] (ι : E → R) (O : Subring R) (I : AddSubgroup R)
    (hA : ∀ (y : R) (m : ℕ), 0 < m → ∃ e : E, ∃ t ∈ I, ι e - y = (m : R) * t)
    (hO : ∀ y : R, ∃ n : ℕ, 0 < n ∧ (n : R) * y ∈ O) (hI : ∀ s ∈ O, ∀ t ∈ I, s * t ∈ I)
    {a b : ℕ} (X : Matrix (Fin a) (Fin b) R) (P P' : Matrix (Fin a) (Fin a) R) (Q Q' : Matrix (Fin b) (Fin b) R)
    (m : ℕ) (hm : 0 < m) :
    ∃ z : Matrix (Fin a) (Fin b) E, (∀ i j, ∃ y ∈ I, (z.map ι - X) i j = (m : R) * y) ∧
      (∀ i j, (P * z.map ι * Q - P * X * Q) i j ∈ I) ∧ ∀ i j, (P' * z.map ι * Q' - P' * X * Q') i j ∈ I := by
  obtain ⟨n₁, hn₁, hP⟩ := GlobalTheory.WeilEquiv.exists_common_den O hO P
  obtain ⟨n₂, hn₂, hQ⟩ := GlobalTheory.WeilEquiv.exists_common_den O hO Q
  obtain ⟨n₃, hn₃, hP'⟩ := GlobalTheory.WeilEquiv.exists_common_den O hO P'
  obtain ⟨n₄, hn₄, hQ'⟩ := GlobalTheory.WeilEquiv.exists_common_den O hO Q'
  choose e t ht he using fun i j => hA (X i j) (m * n₁ * n₂ * n₃ * n₄) (by positivity)
  have key : ∀ (P : Matrix (Fin a) (Fin a) R) (Q : Matrix (Fin b) (Fin b) R) (n n' c : ℕ),
      (∀ i j, (n : R) * P i j ∈ O) → (∀ i j, (n' : R) * Q i j ∈ O) → m * n₁ * n₂ * n₃ * n₄ = c * n * n' →
      ∀ i j, (P * (Matrix.of e).map ι * Q - P * X * Q) i j ∈ I := by
    intro P Q n n' c hP hQ hc i j
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.of_apply, Finset.sum_mul, he, hc]
    refine sum_mem fun l _ => sum_mem fun r _ => ?_
    have : P i r * (((c * n * n' : ℕ) : R) * t r l) * Q l j =
        ((c : R) * ((n : R) * P i r) * ((n' : R) * Q l j)) * t r l := by
      push_cast; ring
    rw [this]
    exact hI _ (O.mul_mem (O.mul_mem (natCast_mem O _) (hP i r)) (hQ l j)) _ (ht r l)
  refine ⟨Matrix.of e, fun i j => ⟨((n₁ * n₂ * n₃ * n₄ : ℕ) : R) * t i j, hI _ (natCast_mem O _) _ (ht i j), ?_⟩,
    key P Q n₁ n₂ (m * n₃ * n₄) hP hQ (by ring), key P' Q' n₃ n₄ (m * n₁ * n₂) hP' hQ' (by ring)⟩
  simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.of_apply, he]
  push_cast; ring

section Entries

variable {R : Type} [CommRing R] {I : AddSubgroup R} {a b : ℕ} {A B A' B' : Matrix (Fin a) (Fin b) R}

theorem entries_of_sub (h : ∀ i j, (A - B) i j ∈ I) (h' : ∀ i j, B i j ∈ I) (i : Fin a) (j : Fin b) : A i j ∈ I := by
  have := add_mem (h i j) (h' i j)
  rwa [Matrix.sub_apply, sub_add_cancel] at this

theorem entries_trans (h : ∀ i j, (A - B) i j ∈ I) (h' : ∀ i j, (B - A') i j ∈ I) (i : Fin a) (j : Fin b) :
    (A - A') i j ∈ I := by
  have := add_mem (h i j) (h' i j)
  rwa [Matrix.sub_apply, Matrix.sub_apply, sub_add_sub_cancel] at this

theorem entries_iff (h : ∀ i j, (A - B) i j ∈ I) (h' : ∀ i j, (A' - B') i j ∈ I) :
    (∀ i j, (B - B') i j ∈ I) ↔ ∀ i j, (A - A') i j ∈ I := by
  refine forall₂_congr fun i j => ?_
  have h1 := sub_mem (h i j) (h' i j)
  simp only [Matrix.sub_apply] at h1 ⊢
  constructor
  · intro h2
    convert add_mem h1 h2 using 1
    ring
  · intro h2
    convert sub_mem h2 h1 using 1
    ring

end Entries

variable {D : D7} {N N' : ℕ}

theorem pt_injective (cc : Ideal (𝓞 D.host.K)) {δ : ℂ} (hδ : δ ≠ 0) :
    Function.Injective (pt D (tor0 D cc δ) δ : Matrix (Fin N') (Fin N) D.host.E → VC D N N') := by
  intro z w h
  refine Matrix.ext fun i j => ?_
  have h1 := congrFun (congrFun (congrFun h (D.eTau.symm 1)) i) j
  simp only [pt, embV, tor0, Pi.smul_apply, smul_eq_mul] at h1
  exact (embT D _).injective (mul_left_cancel₀ hδ h1)

theorem pt_sub (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (z w : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (z - w) = pt D (tor0 D cc δ) δ z - pt D (tor0 D cc δ) δ w := by
  rw [sub_eq_add_neg, pt_add, pt_neg, ← sub_eq_add_neg]

theorem mv_sub (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) (z w : Matrix (Fin N') (Fin N) D.host.E) :
    mv g g' (z - w) = mv g g' z - mv g g' w := by
  rw [sub_eq_add_neg, mv_add, mv_neg, ← sub_eq_add_neg]

theorem pt_mem_iff {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hcc : cc ≠ ⊥) (hδ : δ ≠ 0) {h : GA D N} {h' : GA D N'}
    {L : Lat D N} {L' : Lat D N'} (hL : Moves D (h : GL (Fin N) (AE D)) L) (hL' : Moves D (h' : GL (Fin N') (AE D)) L')
    (u : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ u ∈ La D (tor0 D cc δ) L L' ↔
      ∀ i j, mv (h : GL (Fin N) (AE D)) (h' : GL (Fin N') (AE D)) u i j ∈ IhE D cc := by
  have hD := (GlobalTheory.InducedType.induced_type D).1
  constructor
  · intro hu
    obtain ⟨z, hz, hz'⟩ := GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hD cc δ hcc N N' h h' L L' hL hL' _ hu
    rw [pt_injective cc hδ hz]
    exact hz'
  · exact GlobalTheory.NormSum.pt_mem_La_of_adelic D hD cc δ hcc N N' h h' L L' hL hL' u

theorem move_fwd (g h : GL (Fin N) (AE D)) (g' h' : GL (Fin N') (AE D)) (z : Matrix (Fin N') (Fin N) D.host.E) :
    (((g' * h')⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) *
      ((g' : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) *
        ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) *
      ((g * h : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) = mv h h' z := by
  simp only [mv, mul_inv_rev, Units.val_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((g'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)),
    ← Matrix.mul_assoc ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)),
    Units.inv_mul, Units.inv_mul, Matrix.one_mul, Matrix.one_mul]

theorem move_bwd (g h : GL (Fin N) (AE D)) (g' h' : GL (Fin N') (AE D)) (z : Matrix (Fin N') (Fin N) D.host.E) :
    ((h'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * mv g g' z *
      (h : Matrix (Fin N) (Fin N) (AE D)) = mv (g * h) (g' * h') z := by
  simp only [mv, mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

theorem approx_fwd {cc : Ideal (𝓞 D.host.K)} (hcc : cc ≠ ⊥) (g h k : GL (Fin N) (AE D)) (g' h' k' : GL (Fin N') (AE D))
    (z : Matrix (Fin N') (Fin N) D.host.E) (m : ℕ) (hm : 0 < m) :
    ∃ z' : Matrix (Fin N') (Fin N) D.host.E, CloseTo D cc m g g' z z' ∧
      (∀ i j, (mv (g * h) (g' * h') z' - mv h h' z) i j ∈ IhE D cc) ∧
      ∀ i j, (mv (g * k) (g' * k') z' - mv k k' z) i j ∈ IhE D cc := by
  obtain ⟨hA, hO, hI⟩ := GlobalTheory.AdelicApprox.approx_mod_ideal D cc hcc
  rw [← move_fwd g h g' h' z, ← move_fwd g k g' k' z]
  exact exists_close_two (inc D) (OhE D) (IhE D cc) hA hO hI _ _ _ _ _ m hm

theorem approx_bwd {cc : Ideal (𝓞 D.host.K)} (hcc : cc ≠ ⊥) (g h k : GL (Fin N) (AE D)) (g' h' k' : GL (Fin N') (AE D))
    (y : Matrix (Fin N') (Fin N) D.host.E) :
    ∃ z : Matrix (Fin N') (Fin N) D.host.E,
      (∀ i j, (mv h h' z - mv (g * h) (g' * h') y) i j ∈ IhE D cc) ∧
      ∀ i j, (mv k k' z - mv (g * k) (g' * k') y) i j ∈ IhE D cc := by
  obtain ⟨hA, hO, hI⟩ := GlobalTheory.AdelicApprox.approx_mod_ideal D cc hcc
  rw [← move_bwd g h g' h' y, ← move_bwd g k g' k' y]
  obtain ⟨z, -, hz⟩ := exists_close_two (inc D) (OhE D) (IhE D cc) hA hO hI (mv g g' y)
    ((h'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D))
    ((k'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D))
    (h : Matrix (Fin N) (Fin N) (AE D)) (k : Matrix (Fin N) (Fin N) (AE D)) 1 one_pos
  exact ⟨z, hz⟩

theorem exists_corr : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → δ ≠ 0 → ∀ (N N' : ℕ) (e0 : VC D N N' → ℂ) (W : WeilO D cc δ N N' e0) (g h k : GA D N) (g' h' k' : GA D N') (L₁ L₂ M₁ M₂ : Lat D N) (L₁' L₂' M₁' M₂' : Lat D N'), Moves D (h : GL (Fin N) (AE D)) L₁ → Moves D (h' : GL (Fin N') (AE D)) L₁' → Moves D ((g * h : GA D N) : GL (Fin N) (AE D)) L₂ → Moves D ((g' * h' : GA D N') : GL (Fin N') (AE D)) L₂' → Moves D (k : GL (Fin N) (AE D)) M₁ → Moves D (k' : GL (Fin N') (AE D)) M₁' → Moves D ((g * k : GA D N) : GL (Fin N) (AE D)) M₂ → Moves D ((g' * k' : GA D N') : GL (Fin N') (AE D)) M₂' → ∀ F ∈ TT D (tor0 D cc δ) N N', ∃ f : La D (tor0 D cc δ) M₁ M₁' → La D (tor0 D cc δ) M₂ M₂', (∀ x : La D (tor0 D cc δ) M₁ M₁', W.Om g g' (Wd D (tor0 D cc δ) (x : VC D N N') F) = Wd D (tor0 D cc δ) (f x : VC D N N') (W.Om g g' F)) ∧ (∀ x y : La D (tor0 D cc δ) M₁ M₁', (x : VC D N N') - (y : VC D N N') ∈ La D (tor0 D cc δ) L₁ L₁' ↔ (f x : VC D N N') - (f y : VC D N N') ∈ La D (tor0 D cc δ) L₂ L₂') ∧ ∀ y : La D (tor0 D cc δ) M₂ M₂', ∃ x : La D (tor0 D cc δ) M₁ M₁', (f x : VC D N N') - (y : VC D N N') ∈ La D (tor0 D cc δ) L₂ L₂' := by
  intro D cc δ hC hδ N N' e0 W g h k g' h' k' L₁ L₂ M₁ M₂ L₁' L₂' M₁' M₂' a1 a1' a2 a2' b1 b1' b2 b2' F hF
  have hcc : cc ≠ ⊥ := hC.1.1
  have hD := (GlobalTheory.InducedType.induced_type D).1
  have step : ∀ z : Matrix (Fin N') (Fin N) D.host.E, ∃ z' : Matrix (Fin N') (Fin N) D.host.E,
      W.Om g g' (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F) =
        Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z') (W.Om g g' F) ∧
      (∀ i j, (mv ((g * h : GA D N) : GL (Fin N) (AE D)) ((g' * h' : GA D N') : GL (Fin N') (AE D)) z' -
        mv (h : GL (Fin N) (AE D)) (h' : GL (Fin N') (AE D)) z) i j ∈ IhE D cc) ∧
      ∀ i j, (mv ((g * k : GA D N) : GL (Fin N) (AE D)) ((g' * k' : GA D N') : GL (Fin N') (AE D)) z' -
        mv (k : GL (Fin N) (AE D)) (k' : GL (Fin N') (AE D)) z) i j ∈ IhE D cc := by
    intro z
    obtain ⟨m, hm, hl⟩ := W.lift g g' z F hF
    obtain ⟨z', hc, h1, h2⟩ := approx_fwd hcc (g : GL (Fin N) (AE D)) h k (g' : GL (Fin N') (AE D)) h' k' z m hm
    exact ⟨z', hl z' hc, h1, h2⟩
  choose s hs1 hs2 hs3 using step
  choose r hr1 hr2 using fun x : La D (tor0 D cc δ) M₁ M₁' =>
    GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hD cc δ hcc N N' k k' M₁ M₁' b1 b1' x x.2
  have hmem : ∀ x, pt D (tor0 D cc δ) δ (s (r x)) ∈ La D (tor0 D cc δ) M₂ M₂' := by
    intro x
    rw [pt_mem_iff hcc hδ b2 b2']
    exact entries_of_sub (hs3 (r x)) (hr2 x)
  refine ⟨fun x => ⟨_, hmem x⟩, fun x => ?_, fun x y => ?_, fun y => ?_⟩
  · have := hs1 (r x)
    rwa [← hr1 x] at this
  · rw [hr1 x, hr1 y]
    dsimp only
    rw [← pt_sub, ← pt_sub, pt_mem_iff hcc hδ a1 a1', pt_mem_iff hcc hδ a2 a2', mv_sub, mv_sub]
    exact entries_iff (hs2 (r x)) (hs2 (r y))
  · obtain ⟨y₀, hy, hy'⟩ := GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hD cc δ hcc N N' _ _ M₂ M₂' b2 b2' y y.2
    obtain ⟨z, h1, h2⟩ := approx_bwd hcc (g : GL (Fin N) (AE D)) h k (g' : GL (Fin N') (AE D)) h' k' y₀
    have hz : pt D (tor0 D cc δ) δ z ∈ La D (tor0 D cc δ) M₁ M₁' := by
      rw [pt_mem_iff hcc hδ b1 b1']
      exact entries_of_sub h2 hy'
    refine ⟨⟨_, hz⟩, ?_⟩
    have e : r ⟨_, hz⟩ = z := (pt_injective cc hδ (hr1 ⟨_, hz⟩)).symm
    dsimp only
    rw [e, hy, ← pt_sub, pt_mem_iff hcc hδ a2 a2', mv_sub]
    exact entries_trans (hs2 z) h1

end GlobalTheory.WeilCorr
end

section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

noncomputable section

namespace GlobalTheory.Branching.SsInj

def ps {r k : ℕ} (m : Fin r × Fin k →₀ ℕ) (a : ℕ) (t : Fin k) : ℕ :=
  ∑ b : Fin r, if b.val < a then m (b, t) else 0

theorem interlaced_iff {r k : ℕ} (m : Fin r × Fin k →₀ ℕ) :
    Interlaced m ↔ ∀ l j : Fin k, j.val = l.val + 1 → ∀ a : Fin r, ps m (a.val + 1) j ≤ ps m a.val l := by
  simp only [Interlaced, InterlacedAt, ps, Finset.sum_filter, zero_add, Nat.lt_succ_iff, Fin.le_def, Fin.lt_def]

theorem ps_zero {r k : ℕ} (m : Fin r × Fin k →₀ ℕ) (t : Fin k) : ps m 0 t = 0 := by simp [ps]

theorem ps_succ {r k : ℕ} (m : Fin r × Fin k →₀ ℕ) (a : Fin r) (t : Fin k) :
    ps m (a.val + 1) t = ps m a.val t + m (a, t) := by
  have : m (a, t) = ∑ b : Fin r, if b = a then m (b, t) else 0 := by simp
  rw [this, ps, ps, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : b = a
  · subst h; simp
  · have h' : b.val ≠ a.val := fun e => h (Fin.ext e)
    rw [if_neg h]
    split_ifs <;> omega

theorem ps_top {r k : ℕ} (m : Fin r × Fin k →₀ ℕ) (t : Fin k) : ps m r t = ∑ b, m (b, t) := by
  simp [ps]

theorem ps_diag {r : ℕ} (m : Fin r × Fin r →₀ ℕ) (hm : Interlaced m) :
    ∀ (t : ℕ) (ht : t < r), ps m t ⟨t, ht⟩ = 0
  | 0, _ => ps_zero m _
  | t + 1, ht => by
    have h1 := (interlaced_iff m).1 hm ⟨t, by omega⟩ ⟨t + 1, ht⟩ rfl ⟨t, by omega⟩
    have h2 := ps_diag m hm t (by omega)
    simp only at h1
    omega

theorem diag_anti {r : ℕ} (m : Fin r × Fin r →₀ ℕ) (hm : Interlaced m) :
    Antitone fun t : Fin r => m (t, t) := by
  cases r with
  | zero => intro a; exact a.elim0
  | succ r =>
    refine Fin.antitone_iff_succ_le.2 fun i => ?_
    have h1 := (interlaced_iff m).1 hm i.castSucc i.succ (by simp) i.succ
    have h2 := ps_succ m i.succ i.succ
    have h3 := ps_succ m i.castSucc i.castSucc
    have h4 : ps m i.succ.val i.succ = 0 := ps_diag m hm _ i.succ.2
    have h5 : ps m i.castSucc.val i.castSucc = 0 := ps_diag m hm _ i.castSucc.2
    simp only [Fin.val_succ, Fin.val_castSucc] at *
    omega

def res {n : ℕ} (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ) : Fin n × Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => m (v.1.castSucc, v.2.castSucc)

theorem res_apply {n : ℕ} (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ) (a t : Fin n) :
    res m (a, t) = m (a.castSucc, t.castSucc) := rfl

theorem ps_res {n : ℕ} (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ) (a : ℕ) (ha : a ≤ n) (t : Fin n) :
    ps (res m) a t = ps m a t.castSucc := by
  have : ¬ n < a := by omega
  simp [ps, Fin.sum_univ_castSucc, res_apply, this]

theorem res_interlaced {n : ℕ} (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ) (hm : Interlaced m) :
    Interlaced (res m) := by
  rw [interlaced_iff] at hm ⊢
  intro l j hj a
  rw [ps_res _ _ (by omega), ps_res _ _ (by omega)]
  exact hm l.castSucc j.castSucc hj a.castSucc

def subDiag {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (c : ℕ) : Fin n × Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => m v - if v.1 = v.2 then c else 0

theorem subDiag_add {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (c : ℕ) (hc : ∀ t, c ≤ m (t, t)) (a t : Fin n) :
    subDiag m c (a, t) + (if a = t then c else 0) = m (a, t) := by
  have e : subDiag m c (a, t) = m (a, t) - if a = t then c else 0 := rfl
  rw [e]
  split_ifs with h
  · subst h
    have := hc a
    omega
  · simp

theorem ps_subDiag {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (c : ℕ) (hc : ∀ t, c ≤ m (t, t)) (a : ℕ) (t : Fin n) :
    ps (subDiag m c) a t + (if t.val < a then c else 0) = ps m a t := by
  have : (if t.val < a then c else 0) = ∑ b : Fin n, if b = t then (if t.val < a then c else 0) else 0 := by simp
  rw [this, ps, ps, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have := subDiag_add m c hc b t
  by_cases h : b = t
  · subst h
    simp only [if_true] at this ⊢
    split_ifs <;> omega
  · simp only [if_neg h] at this ⊢
    split_ifs <;> omega

theorem subDiag_interlaced {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (c : ℕ) (hc : ∀ t, c ≤ m (t, t))
    (hm : Interlaced m) : Interlaced (subDiag m c) := by
  rw [interlaced_iff] at hm ⊢
  intro l j hj a
  have h1 := hm l j hj a
  have h2 := ps_subDiag m c hc (a.val + 1) j
  have h3 := ps_subDiag m c hc a.val l
  split_ifs at h2 h3 <;> omega

theorem natW_cast {N : ℕ} (lam : DomWeight N) (t : Fin N) :
    (lam.natW t : ℤ) = lam.w t - lam.detShift := by
  have h0 : 0 < N := t.pos
  have := lam.anti (show t ≤ ⟨N - 1, by omega⟩ from Fin.le_def.2 (by have := t.2; simp only; omega))
  simp only [DomWeight.natW, DomWeight.detShift, dif_pos h0]
  omega

theorem exists_image (n : ℕ) (lam : DomWeight (n + 1)) (m : ssIdx (n + 1) (n + 1) lam.natW) :
    ∃ x : (Σ mu : Below rfl lam, ssIdx n n mu.1.natW),
      (∀ t, x.1.1.w t = lam.detShift + ps m.1 n t.castSucc) ∧
      ∀ a t, x.2.1 (a, t) + (if a = t then (x.1.1.detShift - lam.detShift).toNat else 0) =
        m.1 (a.castSucc, t.castSucc) := by
  obtain ⟨m, hm, hcol⟩ := m
  have hup : ∀ t : Fin n, lam.detShift + ps m n t.castSucc ≤ lam.w t.castSucc := fun t => by
    have h1 := ps_succ m (Fin.last n) t.castSucc
    have h2 := ps_top m t.castSucc
    have h3 := hcol t.castSucc
    have h4 := natW_cast lam t.castSucc
    simp only [Fin.val_last] at h1
    omega
  have hlo : ∀ t : Fin n, lam.w t.succ ≤ lam.detShift + ps m n t.castSucc := fun t => by
    have h1 := (interlaced_iff m).1 hm t.castSucc t.succ (by simp) (Fin.last n)
    have h2 := ps_top m t.succ
    have h3 := hcol t.succ
    have h4 := natW_cast lam t.succ
    simp only [Fin.val_last] at h1
    omega
  let mu : DomWeight n := ⟨fun t => lam.detShift + ps m n t.castSucc, fun i j hij => by
    rcases hij.eq_or_lt with rfl | hlt
    · exact le_rfl
    · exact (hup j).trans ((lam.anti (Fin.le_def.2 (by simpa using hlt))).trans (hlo i))⟩
  have hI : Interlace rfl lam mu := fun i => ⟨hup i, hlo i⟩
  have hr := res_interlaced m hm
  have hc' : ∀ h0 : 0 < n, mu.detShift - lam.detShift =
      (res m (⟨n - 1, by omega⟩, ⟨n - 1, by omega⟩) : ℕ) := fun h0 => by
    have h1 := ps_succ (res m) ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩
    have h2 := ps_diag (res m) hr (n - 1) (by omega)
    have h3 := ps_res m n le_rfl ⟨n - 1, by omega⟩
    have h4 : mu.detShift = lam.detShift + ps m n (Fin.castSucc ⟨n - 1, by omega⟩) := by
      simp only [DomWeight.detShift, dif_pos h0, mu]
    have h5 : n - 1 + 1 = n := by omega
    simp only [h5] at h1
    omega
  have hc : ∀ t, (mu.detShift - lam.detShift).toNat ≤ res m (t, t) := fun t => by
    have h0 : 0 < n := t.pos
    rw [hc' h0, Int.toNat_natCast]
    exact diag_anti _ hr (Fin.le_def.2 (by have := t.2; simp only; omega))
  refine ⟨⟨⟨mu, hI⟩, subDiag (res m) _, subDiag_interlaced _ _ hc hr, fun t => ?_⟩, fun _ => rfl,
    fun a t => subDiag_add _ _ hc a t⟩
  have h1 := ps_subDiag _ _ hc n t
  rw [if_pos t.2, ps_top, ps_res m n le_rfl] at h1
  have h2 := natW_cast mu t
  have h3 : mu.w t = lam.detShift + ps m n t.castSucc := rfl
  have h4 := hc' t.pos
  simp only
  omega

end GlobalTheory.Branching.SsInj

namespace GlobalTheory.Branching

open SsInj

theorem exists_ssIdx_injective : ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N),
    ∃ F : ssIdx N N lam.natW → (Σ mu : Below h lam, ssIdx n n mu.1.natW), Function.Injective F := by
  intro n N h lam
  subst h
  choose F hF1 hF2 using exists_image n lam
  refine ⟨F, fun m m' e => ?_⟩
  have hin : ∀ a t : Fin n, m.1 (a.castSucc, t.castSucc) = m'.1 (a.castSucc, t.castSucc) := fun a t => by
    rw [← hF2 m a t, ← hF2 m' a t, e]
  have hlast : ∀ x : ssIdx (n + 1) (n + 1) lam.natW, ∀ a, x.1 (a, Fin.last n) = 0 := fun x a => by
    have h1 := x.2.2 (Fin.last n)
    have h2 : lam.natW (Fin.last n) = 0 := by
      simp [DomWeight.natW, DomWeight.detShift, Fin.last]
    rw [h2] at h1
    exact Finset.sum_eq_zero_iff.1 h1 a (Finset.mem_univ a)
  apply Subtype.ext
  ext ⟨a, t⟩
  induction t using Fin.lastCases with
  | last => rw [hlast, hlast]
  | cast t =>
    induction a using Fin.lastCases with
    | cast a => exact hin a t
    | last =>
      have h1 := m.2.2 t.castSucc
      have h2 := m'.2.2 t.castSucc
      rw [Fin.sum_univ_castSucc] at h1 h2
      simp only [hin] at h1
      omega

end GlobalTheory.Branching
end
end

section

noncomputable section

open Formalism.BasicNotions NumberField

namespace GlobalTheory

def trivialIntersectionTheory (d : ℕ) : DV.ITh where
  LB := Unit
  Ch := ℚ
  c1 := fun _ => 0
  VDiv := ℚ
  cD := 0
  capDeg := 0
  divP := 1
  cD_divP := rfl
  dim := d

def trivialFlagPair (d r : ℕ) : DV.FPair (trivialIntersectionTheory d) r where
  x := fun _ => ()
  x' := fun _ => ()
  Dv := fun _ => 0
  hx := fun _ => by
    rw [map_zero, sub_zero]

theorem sub_rkOf_psiOf_eq_rkOf_cEmb (D : D7) (p : ℕ) [Fact p.Prime] (jc : DV.KW p →+* ℂ)
    (N j : ℕ) (hj : j ≤ N) (τ : DV.Emb D p) :
    N - DV.rkOf (DV.PsiOf D jc) N j τ = DV.rkOf (DV.PsiOf D jc) N j (DV.cEmb D τ) := by
  have h := Formalism.L2.Geo.cm_type_meets_conjugate_pair p jc τ
  unfold DV.rkOf
  by_cases hτ : τ ∈ DV.PsiOf D jc
  · rw [if_pos hτ, if_neg (h.1 hτ)]
  · have hc : DV.cEmb D τ ∈ DV.PsiOf D jc := by
      by_contra hn
      exact hτ (h.2 hn)
    rw [if_neg hτ, if_pos hc]
    omega

def trivialAdmissibleModel (D : D7) (p : ℕ) [Fact p.Prime] (jc : DV.KW p →+* ℂ)
    (N j : ℕ) (hj : j ≤ N) : DV.Mdl D p N (DV.rkOf (DV.PsiOf D jc) N j) where
  Z := trivialIntersectionTheory (Formalism.DegreeFormula.dimFl D.what₂.Tau N + 1)
  cov := 1
  cov_pos := Nat.one_pos
  lvl := 0
  lie := fun _ => trivialFlagPair _ _
  om := fun _ => trivialFlagPair _ _
  lieW := trivialFlagPair _ _
  omW := trivialFlagPair _ _
  om_dual := fun τ =>
    ⟨finCongr (sub_rkOf_psiOf_eq_rkOf_cEmb D p jc N j hj τ), fun _ => neg_zero.symm⟩
  dim_eq := rfl
  omW_dual := ⟨Equiv.refl _, fun _ => neg_zero.symm⟩

theorem nonempty_admissibleModel :
    ∀ (D : D7) (p : ℕ) [Fact p.Prime] (jc : DV.KW p →+* ℂ) (N j : ℕ), j ≤ N →
      Nonempty (DV.Mdl D p N (DV.rkOf (DV.PsiOf D jc) N j)) :=
  fun D p _ jc N j hj => ⟨trivialAdmissibleModel D p jc N j hj⟩

end GlobalTheory

end
end
