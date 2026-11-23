module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle017
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle005
public import Lemmata.B1962s.FreeLat
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

theorem inl_ne {N r t : ℕ} (a b : ℕ) (ha : a < N) (hb : b < N) (hab : a ≠ b) (c c' : Fin r) :
    (Sum.inl (Formalism.GM.M.finPos N a, c) : Formalism.GM.M.BVar N r t) ≠ Sum.inl (Formalism.GM.M.finPos N b, c') := by
  intro h
  have h2 := congrArg Fin.val (Prod.mk.inj (Sum.inl.inj h)).1
  simp only [Formalism.GM.M.finPos] at h2
  rw [min_eq_left ha.le, min_eq_left hb.le] at h2
  exact hab h2

theorem commCondition : RestTieComm := by
  intro p _ N r _ G hG j jp i i' hii' x
  obtain ⟨⟨hmono, hvec, -⟩, hlt, -, -⟩ := hG
  have hpN : ∀ k, G.T.pos k + 1 < N := fun k => (hlt k).trans G.uPos.isLt
  have hne : G.T.pos i ≠ G.T.pos i' := hmono.injective.ne hii'
  have hcross : ∀ a b : Fin G.T.t, G.T.pos a + 1 ≠ G.T.pos b := by
    intro a b hab
    obtain ⟨ha, -, ha2⟩ := hvec a
    obtain ⟨hb, hb1, -⟩ := hvec b
    have e : G.LL.vec ⟨G.T.pos a + 1, ha⟩ = G.LL.vec ⟨G.T.pos b, by omega⟩ :=
      congrArg G.LL.vec (Fin.ext hab)
    rw [e] at ha2
    exact absurd (hb1.symm.trans ha2) (by decide)
  exact commute_tiePhi _ _ _ _
    (fun c c' => inl_ne _ _ (by have := hpN i; omega) (by have := hpN i'; omega) hne c c')
    (fun c c' => inl_ne _ _ (hpN i) (by have := hpN i'; omega) (hcross i i') c c')
    (fun c c' => inl_ne _ _ (by have := hpN i; omega) (hpN i') (hcross i' i).symm c c')
    (fun c c' => inl_ne _ _ (hpN i) (hpN i') (fun h => hne (by omega)) c c')
    _ _ _ _ _ _ x

theorem symmCondition (C0 CE1 CE2 : ℝ) (X : Formalism.MainNotions.flipOneThree.Inst) : RestSymm C0 CE1 CE2 X :=
  restSymm_of commCondition C0 CE1 CE2 X

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset


open Classical in
def GoodLeSmallMat : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n m : ℕ) (X Y : Fin n → Fin m → ℤ_[p]) (c : Fin m → ℚ_[p]) (D : ℤ),
    (∀ i j, ∑ a, (X i a : ℚ_[p]) * c a * (Y j a : ℚ_[p]) = if i = j then (p : ℚ_[p]) ^ D else 0) →
    n ≤ (Finset.univ.filter (fun a : Fin m => c a ≠ 0 ∧ (c a).valuation ≤ D)).card

theorem B_sum_left {p : ℕ} [Fact p.Prime] {σ ι : Type} (B : MvPolynomial σ ℚ_[p] → MvPolynomial σ ℚ_[p] → ℚ_[p])
    (hsm : ∀ (c : ℚ_[p]) u v, B (c • u) v = c * B u v) (hadd : ∀ u u' v, B (u + u') v = B u v + B u' v)
    (s : Finset ι) (g : ι → MvPolynomial σ ℚ_[p]) (v : MvPolynomial σ ℚ_[p]) :
    B (∑ i ∈ s, g i) v = ∑ i ∈ s, B (g i) v := by
  classical
  have h0 : B 0 v = 0 := by
    have := hsm 0 0 v
    simpa using this
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih => rw [Finset.sum_insert ha, hadd, ih, Finset.sum_insert ha]

theorem goodLeSmall_of (h : GoodLeSmallMat) : GoodLeSmall := by
  intro p _ σ B L W D _ _ hsm hadd hsy m f hf _ hspan horth
  obtain ⟨x, y, hx, hy, hxy⟩ := goodCount_mem p B L D
  have hcoord : ∀ v ∈ L, ∃ X : Fin m → ℤ_[p], ∑ a, X a • f a = v := by
    intro v hv
    rw [← hspan] at hv
    exact (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).1 hv
  choose! X hX using hcoord
  have hsmZ : ∀ (c : ℤ_[p]) (u : MvPolynomial σ ℚ_[p]), c • u = (c : ℚ_[p]) • u :=
    fun c u => (algebraMap_smul ℚ_[p] c u).symm
  have hexp : ∀ v ∈ L, ∀ w, B v w = ∑ a, (X v a : ℚ_[p]) * B (f a) w := by
    intro v hv w
    conv_lhs => rw [← hX v hv]
    rw [B_sum_left B hsm hadd]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hsmZ, hsm]
  have hfy : ∀ a j, B (f a) (y j) = (X (y j) a : ℚ_[p]) * B (f a) (f a) := by
    intro a j
    rw [hsy _ (hf a) _ (hy j), hexp _ (hy j)]
    rw [Finset.sum_eq_single a]
    · intro b _ hb
      rw [horth b a hb, mul_zero]
    · intro ha; exact absurd (Finset.mem_univ a) ha
  exact h p _ m (fun i => X (x i)) (fun j => X (y j)) (fun a => B (f a) (f a)) D (fun i j => by
    rw [← hxy i j, hexp _ (hx i)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hfy]
    ring)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial

def FreeLat : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]))
    (W : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])),
    FiniteDimensional ℚ_[p] W → (∀ x ∈ L, x ∈ W) → L.FG →
    ∃ (m : ℕ) (f : Fin m → MvPolynomial σ ℚ_[p]), (∀ a, f a ∈ L) ∧ LinearIndependent ℤ_[p] f ∧
      Submodule.span ℤ_[p] (Set.range f) = L

def OrthSplit : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (B : MvPolynomial σ ℚ_[p] → MvPolynomial σ ℚ_[p] → ℚ_[p])
    (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (W : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])),
    p ≠ 2 → FiniteDimensional ℚ_[p] W → (∀ x ∈ L, x ∈ W) → L.FG →
    (∀ (c : ℚ_[p]) u v, B (c • u) v = c * B u v) → (∀ u u' v, B (u + u') v = B u v + B u' v) →
    (∀ u ∈ L, ∀ v ∈ L, B u v = B v u) → (∃ u ∈ L, ∃ v ∈ L, B u v ≠ 0) →
    ∃ x ∈ L, ∃ L' : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]), L' ≤ L ∧ L'.FG ∧
      Module.finrank ℤ_[p] L' < Module.finrank ℤ_[p] L ∧
      (∀ u ∈ L', B x u = 0) ∧ Submodule.span ℤ_[p] {x} ⊔ L' = L ∧
      (∀ (c : ℤ_[p]) (y : MvPolynomial σ ℚ_[p]), y ∈ L' → c • x + y = 0 → c = 0)

theorem freeLat_proved : FreeLat := by
  first | exact Bl.FreeLattices.goal1 .. | (apply Bl.FreeLattices.goal1 <;> assumption) | (intros; apply Bl.FreeLattices.goal1 <;> assumption) | (apply @Bl.FreeLattices.goal1 <;> assumption) | (intros; apply @Bl.FreeLattices.goal1 <;> assumption) | (apply @Bl.FreeLattices.goal1 <;> first | assumption | infer_instance)

theorem orthBasisLat_of (hF : FreeLat) (hS : OrthSplit) : OrthBasisLat := by
  intro p _ σ B L W hp hW hLW hfg hsm hadd hsy

  suffices H : ∀ n : ℕ, ∀ L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]), Module.finrank ℤ_[p] L = n →
      (∀ x ∈ L, x ∈ W) → L.FG → (∀ u ∈ L, ∀ v ∈ L, B u v = B v u) →
      ∃ (m : ℕ) (f : Fin m → MvPolynomial σ ℚ_[p]), (∀ a, f a ∈ L) ∧ LinearIndependent ℤ_[p] f ∧
        Submodule.span ℤ_[p] (Set.range f) = L ∧ ∀ a b, a ≠ b → B (f a) (f b) = 0 from
    H _ L rfl hLW hfg hsy
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro L hn hLW hfg hsy
    by_cases h0 : ∃ u ∈ L, ∃ v ∈ L, B u v ≠ 0
    · obtain ⟨x, hx, L', hL'L, hL'fg, hrk, horth, hspan, hdir⟩ := hS p σ B L W hp hW hLW hfg hsm hadd hsy h0
      obtain ⟨m, f, hfL, hli, hsp, hfo⟩ := ih _ (hn ▸ hrk) L' rfl (fun y hy => hLW y (hL'L hy)) hL'fg
        (fun u hu v hv => hsy u (hL'L hu) v (hL'L hv))
      refine ⟨m + 1, Fin.cons x f, ?_, ?_, ?_, ?_⟩
      · intro a
        refine Fin.cases ?_ (fun b => ?_) a
        · simpa using hx
        · simpa using hL'L (hfL b)
      · refine hli.finCons' x f fun c y hy hsum => ?_
        have hle : Submodule.span ℤ_[p] (Set.range f) ≤ L' := by rw [hsp]
        exact hdir c y (hle hy) hsum
      · rw [Fin.range_cons, Submodule.span_insert, hsp, hspan]
      · have hfx : ∀ b, B x (f b) = 0 := fun b => horth _ (hfL b)
        intro a b hab
        refine Fin.cases (fun hab => ?_) (fun a' hab => ?_) a hab
        · refine Fin.cases (fun h => absurd rfl h) (fun b' _ => ?_) b hab
          simpa using hfx b'
        · refine Fin.cases (fun _ => ?_) (fun b' h => ?_) b hab
          · simp only [Fin.cons_zero, Fin.cons_succ]
            rw [hsy _ (hL'L (hfL a')) _ hx]
            exact hfx a'
          · simp only [Fin.cons_succ]
            exact hfo a' b' (fun e => h (by rw [e]))
    · push Not at h0
      obtain ⟨m, f, hfL, hli, hsp⟩ := hF p σ L W hW hLW hfg
      exact ⟨m, f, hfL, hli, hsp, fun a b _ => h0 _ (hfL a) _ (hfL b)⟩

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
