module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle574
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreEnvelopingAlgebraCommuteRealLieSmoothing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle572
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle570
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.TotallySplit
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle509
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocHypInert

open GlobalTheory.CompanionTheory.LocInert

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cjv_apply (hC : CjEx) {w : Pl E} (hw : ¬ IsSplitAt w)
    (x : Av (w.under (𝓞 (maximalRealSubfield E)))) : evR hw (cjv _ x) = cj w (evR hw x) := by
  have h := hC E (w.under (𝓞 (maximalRealSubfield E)))
  set X : Af E := sLoc E w (evR hw x) with hX
  have hp : pLoc E w X = evR hw x := by
    change (Pi.single w (evR hw x) : ∀ u : Pl E, u.adicCompletion E) w = _
    simp
  have hx : projv _ X = x := by
    funext u
    obtain rfl := eq_aw hw u
    exact hp
  have hs : cjv (w.under (𝓞 (maximalRealSubfield E))) = h.choose := by
    rw [cjv, dite_eq_left h]
  rw [← hx, hs, ← h.choose_spec.2 X, evR_apply, evR_apply]
  change pLoc E w (conjFin (IsCMField.complexConj E).toRingEquiv X) = cj w (pLoc E w X)
  rw [pLoc_conjFin]
  exact GlobalTheory.BCT.GlobLev.conjLoc_eq_cj hw X

theorem evY_thv (hC : CjEx) {w : Pl E} (hw : ¬ IsSplitAt w) (a b : ℕ)
    (y : Yv a b (w.under (𝓞 (maximalRealSubfield E)))) :
    evY hw a b (thv a b _ y) = ((thL a w).prodMap (thL b w)) (evY hw a b y) := by
  have h : ∀ n (g : GL (Fin n) (Av (w.under (𝓞 (maximalRealSubfield E))))),
      GeneralLinearGroup.map (evR hw).toRingHom (thetaGL n (cjv _) g) =
        thL n w (GeneralLinearGroup.map (evR hw).toRingHom g) := fun n g => by
    rw [thL, if_neg hw]
    exact GlobalTheory.ThetaPull.map_thetaGL _ _ _ (cjv_apply hC hw) g
  exact Prod.ext (h a y.1) (h b y.2)

theorem inert_iso : CjEx → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (v : PlF E) (w : Above v), ¬ IsSplitAt w.1 →
  ∃ e : Yv a b v ≃ₜ* (GLw a w.1 × GLw b w.1), (∀ y, e y = evw w y) ∧
    (∀ y, e (thv a b v y) = ((thL a w.1).prodMap (thL b w.1)) (e y)) ∧ ∀ y, y ∈ Kv a b v ↔ e y ∈ K2 a b w.1 := by
  intro hC E _ _ _ a b v w hw
  obtain ⟨w, rfl⟩ := w
  exact ⟨evY hw a b, evY_apply hw a b, evY_thv hC hw a b, mem_Kv_iff hw a b⟩

end GlobalTheory.CompanionTheory.LocHypInert

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue.SliceTypePf

theorem restrict_left {A B : Type} [One B] (W₁ : Submodule ℂ (A → ℂ)) (W₂ : Submodule ℂ (B → ℂ)) (f : A × B → ℂ)
    (hf : f ∈ Submodule.span ℂ {f : A × B → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}) :
    (fun k : A => f (k, 1)) ∈ W₁ := by
  induction hf using Submodule.span_induction with
  | mem f h =>
    obtain ⟨w₁, h₁, w₂, -, rfl⟩ := h
    have : (fun k : A => w₁ k * w₂ 1) = w₂ 1 • w₁ := by
      funext k
      simp [mul_comm]
    simpa [this] using W₁.smul_mem _ h₁
  | zero => exact W₁.zero_mem
  | add f g _ _ hf hg => exact W₁.add_mem hf hg
  | smul c f _ hf => exact W₁.smul_mem c hf

theorem restrict_right {A B : Type} [One A] (W₁ : Submodule ℂ (A → ℂ)) (W₂ : Submodule ℂ (B → ℂ)) (f : A × B → ℂ)
    (hf : f ∈ Submodule.span ℂ {f : A × B → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}) :
    (fun k : B => f (1, k)) ∈ W₂ := by
  induction hf using Submodule.span_induction with
  | mem f h =>
    obtain ⟨w₁, -, w₂, h₂, rfl⟩ := h
    have : (fun k : B => w₁ 1 * w₂ k) = w₁ 1 • w₂ := by
      funext k
      simp
    simpa [this] using W₂.smul_mem _ h₂
  | zero => exact W₂.zero_mem
  | add f g _ _ hf hg => exact W₂.add_mem hf hg
  | smul c f _ hf => exact W₂.smul_mem c hf

theorem main : GlobalTheory.CompanionTheory.EGlue.SliceType := by
  intro E _ _ _ a b K₁ K₂ W₁ W₂ F hF
  obtain ⟨hl, hk⟩ := hF
  refine ⟨?_, ?_⟩
  · rintro φ m₂ hφ
    refine ⟨?_, ?_⟩
    · intro u hu g
      have := hl u hu 1 K₂.one_mem (g, m₂)
      simpa [hφ, Prod.mk_mul_mk] using this
    · intro g
      have := restrict_left W₁ W₂ _ (hk (g, m₂))
      simpa [hφ, Prod.mk_mul_mk] using this
  · rintro φ m₁ hφ
    refine ⟨?_, ?_⟩
    · intro u hu g
      have := hl 1 K₁.one_mem u hu (m₁, g)
      simpa [hφ, Prod.mk_mul_mk] using this
    · intro g
      have := restrict_right W₁ W₂ _ (hk (m₁, g))
      simpa [hφ, Prod.mk_mul_mk] using this

end GlobalTheory.CompanionTheory.EGlue.SliceTypePf

end
end

section

open Filter Topology
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue

theorem convComp_proved : ConvComp := by
  intro E _ _ _ N t s φ h hφ
  induction h with
  | leaf V z z₀ h => exact Conv.leaf V (fun k => z (φ k)) z₀ (h.comp hφ.tendsto_atTop)
  | node _ _ i₁ i₂ => exact Conv.node i₁ i₂

end GlobalTheory.CompanionTheory.EGlue
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue.ConvInfProof

theorem tendsto_prod_shift (m₀ : Multiset ℂ) {z : ℕ → ℂ} {z₀ : ℂ} (h : Tendsto z atTop (𝓝 z₀)) (u : ℂ) :
    Tendsto (fun k => ((m₀.map (· + z k)).map (u + ·)).prod) atTop
      (𝓝 (((m₀.map (· + z₀)).map (u + ·)).prod)) := by
  induction m₀ using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (tendsto_const_nhds.add (h.const_add a)).mul ih

theorem convInf_of_discInf_topInf : DiscInf → TopInf → ConvInf := by
  intro hD hT E _ _ _ N t s τ hc hs
  induction hc with
  | leaf V z z₀ h =>
    have hex : ∃ m₀, HasInfCharGL V τ m₀ := by
      rcases hs with ⟨rfl, rfl, -⟩ | ⟨-, hV, -⟩
      · exact ⟨0, hT E τ⟩
      · exact hD E _ V hV τ
    obtain ⟨m₀, h₀⟩ := hex
    exact ⟨m₀.map (· + z₀), fun k => m₀.map (· + z k), ⟨m₀, h₀, rfl⟩, fun k => ⟨m₀, h₀, rfl⟩,
      fun u => tendsto_prod_shift m₀ h u⟩
  | node h₁ h₂ ih₁ ih₂ =>
    obtain ⟨a₀, a, ha₀, ha, hat⟩ := ih₁ hs.1
    obtain ⟨b₀, b, hb₀, hb, hbt⟩ := ih₂ hs.2
    refine ⟨a₀ + b₀, fun k => a k + b k, ⟨a₀, b₀, ha₀, hb₀, rfl⟩,
      fun k => ⟨a k, b k, ha k, hb k, rfl⟩, fun u => ?_⟩
    simp only [Multiset.map_add (f := _), Multiset.prod_add]
    exact (hat u).mul (hbt u)

end GlobalTheory.CompanionTheory.EGlue.ConvInfProof

end
end

section

open Filter Topology

namespace GlobalTheory.CompanionTheory.EGlue

theorem convShift_holds : ConvShift := by
  intro E _ _ _ N t s z z₀ h hz
  induction h with
  | leaf V w w₀ hw => exact Conv.leaf V (fun k => w k + z k) (w₀ + z₀) (hw.add hz)
  | node _ _ i₁ i₂ => exact Conv.node i₁ i₂

end GlobalTheory.CompanionTheory.EGlue
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue.LimT

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def lr : {N : ℕ} → Tr E N → ℕ
  | _, .leaf _ _ => 0
  | _, @Tr.node _ _ _ _ r _ _ _ => r

theorem lr_le {N : ℕ} (u : Tr E N) : lr u ≤ N := by
  cases u with
  | leaf V z => exact Nat.zero_le _
  | node t₁ t₂ => exact Nat.le_add_right _ _

theorem leaf_of {N : ℕ} (u : Tr E N) (h : lr u = 0) (hr : Red u) : ∃ V z, u = .leaf V z := by
  cases u with
  | leaf V z => exact ⟨V, z, rfl⟩
  | node t₁ t₂ => exact absurd (show _ = 0 from h) hr.1.ne'

theorem node_of {n : ℕ} (u : Tr E n) {r s : ℕ} (h : n = r + s) (hl : lr u = r) (hr : 0 < r) (hred : Red u) :
    ∃ (t₁ : Tr E r) (t₂ : Tr E s), h ▸ u = Tr.node t₁ t₂ ∧ Red t₁ ∧ Red t₂ := by
  cases u with
  | leaf V z => exact absurd (show 0 = r from hl) hr.ne
  | @node r' s' t₁ t₂ =>
    have hl' : r' = r := hl
    subst hl'
    have hs : s' = s := by omega
    subst hs
    exact ⟨t₁, t₂, rfl, hred.2.2.1, hred.2.2.2⟩

theorem pigeon {n : ℕ} (c : ℕ → ℕ) (h : ∀ k, c k ≤ n) : ∃ (r : ℕ) (φ : ℕ → ℕ), StrictMono φ ∧ ∀ k, c (φ k) = r := by
  let f : ℕ → Fin (n + 1) := fun k => ⟨c k, Nat.lt_succ_of_le (h k)⟩
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber f
  have hinf : (f ⁻¹' {y}).Infinite := Set.infinite_coe_iff.mp hy
  obtain ⟨φ, hφ, h2⟩ := extraction_of_frequently_atTop (P := fun k => f k = y)
    (Nat.frequently_atTop_iff_infinite.mpr hinf)
  exact ⟨y, φ, hφ, fun k => congrArg Fin.val (h2 k)⟩

theorem emb_refl {N : ℕ} (V : Submodule ℂ (Sm E N)) : Emb V (· ∈ V) :=
  ⟨LinearMap.id, fun _ h => h, fun _ _ h => h, fun _ _ _ => rfl⟩

theorem main (hc : ConvComp) (hs : TrStable) (hg : Graft)
    (Θs Θf : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) (Ωs Ωf : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) (N : ℕ)
    (hL : LimLeafP N Θs Ωs Θf Ωf) (hR : ReproAll E) (n : ℕ) : n ≤ N → ∀ (t : ℕ → Tr E n) (R : ℝ), (∀ k, Red (t k)) →
    (∀ k, (t k).Good) → (∀ k, (t k).AllLeaves (ListLeaf Θs Ωs)) →
    (∀ k, LeafZ (fun M V z => 0 < M → InfBdd R V ∧ ‖z‖ ≤ R) (t k)) →
    ∃ (φ : ℕ → ℕ) (t' : ℕ → Tr E n) (s : Tr E n), StrictMono φ ∧ Conv t' s ∧ Red s ∧ s.Good ∧
      s.AllLeaves (ListLeaf Θf Ωf) ∧ (∀ k, (t' k).Disc) ∧ ∀ k, Emb (t (φ k)).space (· ∈ (t' k).space) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn t R hred hgood hlist hz
  obtain ⟨r, φ₀, hφ₀, hr⟩ := pigeon (n := n) (fun k => lr (t k)) (fun k => lr_le _)
  by_cases h0 : r = 0
  · subst h0
    choose V z hVz using fun k => leaf_of (t (φ₀ k)) (hr k) (hred _)
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · have hk : ∀ k, t (φ₀ k) = .leaf ⊤ 0 := by
        intro k
        have h := hgood (φ₀ k)
        rw [hVz k] at h
        rcases h with ⟨-, hV, hz'⟩ | ⟨h, -, -⟩
        · rw [hVz k, hV, hz']
        · exact absurd h (lt_irrefl _)
      refine ⟨φ₀, fun _ => .leaf ⊤ 0, .leaf ⊤ 0, hφ₀, Conv.leaf ⊤ (fun _ => 0) 0 tendsto_const_nhds, trivial,
        Or.inl ⟨rfl, rfl, rfl⟩, Or.inl rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩, fun k => ?_⟩
      rw [hk k]
      exact emb_refl _
    · have hG : ∀ k, IsDiscrete (V k) ∧ (z k).re = 0 := by
        intro k
        have h := hgood (φ₀ k)
        rw [hVz k] at h
        rcases h with ⟨h, -, -⟩ | ⟨-, h⟩
        · exact absurd h hn0.ne'
        · exact h
      have hT : ∀ k, ∃ K' ∈ Θs n, ∃ W' ∈ Ωs n, HasType K' W' (V k) := by
        intro k
        have h := hlist (φ₀ k)
        rw [hVz k] at h
        rcases h with h | h
        · exact absurd h hn0.ne'
        · exact h
      have hB : ∀ k, InfBdd R (V k) ∧ ‖z k‖ ≤ R := by
        intro k
        have h := hz (φ₀ k)
        rw [hVz k] at h
        exact h hn0
      obtain ⟨φ, t', s, hφ, hc', hrs, hgs, hls, hd, he⟩ := hL n hn0 hn V z R hR (fun k => (hG k).1)
        (fun k => (hG k).2) hT (fun k => (hB k).1) (fun k => (hB k).2)
      refine ⟨φ₀ ∘ φ, t', s, hφ₀.comp hφ, hc', hrs, hgs, hls, hd, fun k => ?_⟩
      have e : t ((φ₀ ∘ φ) k) = .leaf (V (φ k)) (z (φ k)) := hVz _
      rw [e]
      exact he k
  · have hr0 : 0 < r := Nat.pos_of_ne_zero h0
    have hrn : r ≤ n := by
      have := lr_le (t (φ₀ 0))
      rwa [hr 0] at this
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hrn
    choose a b hab ha hb using fun k => node_of (t (φ₀ k)) rfl (hr k) hr0 (hred _)
    have hab' : ∀ k, t (φ₀ k) = .node (a k) (b k) := hab
    have hs0 : 0 < s := by
      have h := hred (φ₀ 0)
      rw [hab' 0] at h
      exact h.2.1
    have hG : ∀ k, (a k).Good ∧ (b k).Good := fun k => by
      have h := hgood (φ₀ k)
      rw [hab' k] at h
      exact h
    have hT : ∀ k, (a k).AllLeaves (ListLeaf Θs Ωs) ∧ (b k).AllLeaves (ListLeaf Θs Ωs) := fun k => by
      have h := hlist (φ₀ k)
      rw [hab' k] at h
      exact h
    have hB : ∀ k, LeafZ (fun M V z => 0 < M → InfBdd R V ∧ ‖z‖ ≤ R) (a k) ∧
        LeafZ (fun M V z => 0 < M → InfBdd R V ∧ ‖z‖ ≤ R) (b k) := fun k => by
      have h := hz (φ₀ k)
      rw [hab' k] at h
      exact h
    obtain ⟨φ₁, a', sa, hφ₁, hca, hra, hga, hla, hda, hea⟩ := ih r (by omega) (by omega) a R ha
      (fun k => (hG k).1) (fun k => (hT k).1) (fun k => (hB k).1)
    obtain ⟨φ₂, b', sb, hφ₂, hcb, hrb, hgb, hlb, hdb, heb⟩ := ih s (by omega) (by omega) (fun k => b (φ₁ k)) R
      (fun k => hb _) (fun k => (hG _).2) (fun k => (hT _).2) (fun k => (hB _).2)
    refine ⟨φ₀ ∘ φ₁ ∘ φ₂, fun k => .node (a' (φ₂ k)) (b' k), .node sa sb, hφ₀.comp (hφ₁.comp hφ₂),
      Conv.node (hc E r a' sa φ₂ hca hφ₂) hcb, ⟨hr0, hs0, hra, hrb⟩, ⟨hga, hgb⟩, ⟨hla, hlb⟩,
      fun k => ⟨hda _, hdb k⟩, fun k => ?_⟩
    have e : t ((φ₀ ∘ φ₁ ∘ φ₂) k) = .node (a (φ₁ (φ₂ k))) (b (φ₁ (φ₂ k))) := hab' _
    rw [e]
    exact hg E r s _ _ _ _ (hs E _ _ (disc_stable (good_disc (hG _).1))) (hs E _ _ (disc_stable (hda _)))
      (hs E _ _ (disc_stable (good_disc (hG _).2))) (hs E _ _ (disc_stable (hdb _))) (hea (φ₂ k)) (heb k)

theorem limTrees : ConvComp → LimTrees := by
  intro hc hs hg E _ _ _ Θs Θf Ωs Ωf N hL hR n hn t R h₁ h₂ h₃ h₄
  exact main hc hs hg Θs Θf Ωs Ωf N hL hR n hn t R h₁ h₂ h₃ h₄

end GlobalTheory.CompanionTheory.EGlue.LimT

end
end

section

open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue

theorem pairEmb_of_steps : PairSlices → PairStep₁ → PairStep₂ → PairEmb := by
  intro hS h₁ h₂ E _ _ _ a b ι _ K₁ K₂ W₁ W₂ X₁ Y₁ X₂ Y₂ G hW₁ hW₂ hX₁ hX₂ hE₁ hE₂ hG hGp hGt
  obtain ⟨e₁, he₁Y, he₁i, he₁q⟩ := hE₁
  obtain ⟨e₂, he₂Y, he₂i, he₂q⟩ := hE₂
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hG
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hi
  obtain ⟨hmem, hval⟩ := (hS E a b X₁ X₂ (G i) (hGp i)).1 x.2
  have hφ : sl₁ (G i) x.2 ≠ 0 := by
    intro h0
    apply hx
    have h := congrFun hval x.1
    rw [h0] at h
    simpa using h.symm
  obtain ⟨n₁, p₁, t₁, c₁⟩ := h₁ E a b ι K₁ K₂ W₁ W₂ X₁ Y₁ X₂ e₁ G hW₁ hW₂ hX₁ he₁q he₁Y hGp hGt
    ⟨i, x.2, sl₁ (G i) x.2, hval, fun h0 => hφ (he₁i _ hmem h0)⟩
  obtain ⟨j, hj⟩ := Function.ne_iff.mp n₁
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hj
  obtain ⟨hmem₂, hval₂⟩ := (hS E a b Y₁ X₂ (ap₁ e₁ (G j)) (p₁ j)).2 y.1
  have hψ : sl₂ (ap₁ e₁ (G j)) y.1 ≠ 0 := by
    intro h0
    apply hy
    have h := congrFun hval₂ y.2
    rw [h0] at h
    simpa using h.symm
  obtain ⟨n₂, p₂, t₂, c₂⟩ := h₂ E a b ι K₁ K₂ W₁ W₂ Y₁ X₂ Y₂ e₂ (fun i => ap₁ e₁ (G i)) hW₁ hW₂ hX₂ he₂q he₂Y p₁ t₁
    ⟨j, y.1, sl₂ (ap₁ e₁ (G j)) y.1, hval₂, fun h0 => hψ (he₂i _ hmem₂ h0)⟩
  exact ⟨fun i => ap₂ e₂ (ap₁ e₁ (G i)), n₂, p₂, t₂, fun h c hc => c₂ h c (c₁ h c hc)⟩

end GlobalTheory.CompanionTheory.EGlue
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue

theorem adjoin_lie_equiv {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}
    {U : Submodule ℂ (Sm E N)} (T : Sm E N →ₗ[ℂ] Sm E N) (hU : _root_.GlobalTheory.CuspRep.IsStable U)
    (hT : ∀ o, ∀ χ ∈ U, T (act o χ) = act o (T χ)) {z : Module.End ℂ (Sm E N)}
    (hz : z ∈ Algebra.adjoin ℂ (Set.range (lie E N))) :
    ∀ χ ∈ U, z χ ∈ U ∧ T (z χ) = z (T χ) := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨X, rfl⟩ := hx
    exact fun χ hχ => ⟨hU (.lie X) χ hχ, hT (.lie X) χ hχ⟩
  | algebraMap c =>
    intro χ hχ
    simpa [Module.algebraMap_end_apply] using U.smul_mem c hχ
  | add x y _ _ hx hy =>
    intro χ hχ
    obtain ⟨x₁, x₂⟩ := hx χ hχ
    obtain ⟨y₁, y₂⟩ := hy χ hχ
    exact ⟨by simpa using U.add_mem x₁ y₁, by simp [x₂, y₂]⟩
  | mul x y _ _ hx hy =>
    intro χ hχ
    obtain ⟨y₁, y₂⟩ := hy χ hχ
    obtain ⟨x₁, x₂⟩ := hx _ y₁
    exact ⟨by simpa [Module.End.mul_apply] using x₁, by simp [Module.End.mul_apply, x₂, y₂]⟩

theorem capEquiv : CapEquiv := by
  intro E _ _ _ N U T ψ m hU hT hψ hc τ u
  rw [← (adjoin_lie_equiv T hU hT (GlobalTheory.CentreSmooth.cap_mem τ u) ψ hψ).2, hc τ u, map_smul]

end GlobalTheory.CompanionTheory.EGlue

end
end

section

open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue

theorem infOfEq_holds : InfOfEq := by
  intro E _ _ _ N t ψ m τ m' hT hI hψ h0 hC
  have hS := hT E N t τ m' hI
  refine GlobalTheory.IsobaricOfPublished.multiset_eq_of_prod_map_add fun u => ?_
  exact smul_left_injective ℂ h0 ((hS.2 u ψ hψ).symm.trans (hC τ u))

end GlobalTheory.CompanionTheory.EGlue
end

section


theorem _root_.GlobalTheory.T.basic_character_unramified : PositivityTheory.SiegelWeilFormula.Gunr.PsiBasic := by
  first | exact @GlobalTheory.CompanionTheory.AdelicCharLocal.psiBasic | exact GlobalTheory.CompanionTheory.AdelicCharLocal.psiBasic | (intros; apply GlobalTheory.CompanionTheory.AdelicCharLocal.psiBasic <;> assumption)
end
