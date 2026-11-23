module

import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.TriSupportedLe
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ProdList
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.Bundle001
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.BernsteinZelevinsky.TopAdm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle350
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective

@[expose] public section

section

open MvPolynomial

namespace CompanionTheory.Groth.ChartWirtingerDerivatives

def toZAlg {σ : Type*} (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ) :
    MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial σ ℤ :=
  AlgHom.mk ψ (by
    intro r
    show ψ (algebraMap ℤ (MvPolynomial σ ℤ) r) = algebraMap ℤ (MvPolynomial σ ℤ) r
    rw [algebraMap_eq, eq_intCast C r]
    exact map_intCast ψ r)

theorem tri_supported_le {σ : Type*} (w : σ → ℕ) (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ)
    (h : ∀ s, ∃ (ε : ℤˣ) (p : MvPolynomial σ ℤ), (∀ t ∈ p.vars, w t < w s) ∧
      ψ (X s) = (ε : ℤ) • X s + p) (N : ℕ) :
    supported ℤ {t | w t < N} ≤ (supported ℤ {t | w t < N}).map (toZAlg ψ) := by
  induction N with
  | zero =>
    rw [supported_eq_adjoin_X, Algebra.adjoin_le_iff]
    rintro _ ⟨t, ht, rfl⟩
    exact absurd ht (by simp)
  | succ N ih =>
    rw [supported_eq_adjoin_X, Algebra.adjoin_le_iff]
    rintro _ ⟨t, ht, rfl⟩
    simp only [Set.mem_ofPred_eq] at ht
    have hmono : (supported ℤ {t | w t < N}).map (toZAlg ψ) ≤
        (supported ℤ {t | w t < N + 1}).map (toZAlg ψ) :=
      Subalgebra.map_mono (supported_mono fun t (ht : w t < N) => (Nat.lt_succ_of_lt ht : w t < N + 1))
    obtain ⟨ε, p, hp, hψ⟩ := h t
    have hpmem : p ∈ (supported ℤ {t | w t < N + 1}).map (toZAlg ψ) := by
      apply hmono; apply ih
      rw [mem_supported]
      intro u hu
      have := hp u hu
      simp only [Set.mem_ofPred_eq]; omega
    have hXmem : ψ (X t) ∈ (supported ℤ {t | w t < N + 1}).map (toZAlg ψ) :=
      Subalgebra.mem_map.2 ⟨X t, (X_mem_supported).2 (by simpa using ht), rfl⟩
    have heq : (X t : MvPolynomial σ ℤ) = (ε : ℤ) • ψ (X t) - (ε : ℤ) • p := by
      rw [hψ, smul_add, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul, add_sub_cancel_right]
    rw [SetLike.mem_coe, heq]
    exact Subalgebra.sub_mem _ (Subalgebra.smul_mem _ hXmem _) (Subalgebra.smul_mem _ hpmem _)

theorem tri_surj {σ : Type*} (w : σ → ℕ) (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ)
    (h : ∀ s, ∃ (ε : ℤˣ) (p : MvPolynomial σ ℤ), (∀ t ∈ p.vars, w t < w s) ∧
      ψ (X s) = (ε : ℤ) • X s + p) : Function.Surjective ψ := by
  intro y
  have hy : y ∈ supported ℤ {t | w t < y.vars.sup (fun t => w t + 1)} := by
    rw [mem_supported]
    intro t ht
    have := Finset.le_sup (f := fun t => w t + 1) (Finset.mem_coe.1 ht)
    simp only [Set.mem_ofPred_eq]; omega
  obtain ⟨x, -, hx⟩ := Subalgebra.mem_map.1 (tri_supported_le w ψ h _ hy)
  exact ⟨x, hx⟩

theorem tri_bij {σ : Type*} (w : σ → ℕ) (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ)
    (h : ∀ s, ∃ (ε : ℤˣ) (p : MvPolynomial σ ℤ), (∀ t ∈ p.vars, w t < w s) ∧
      ψ (X s) = (ε : ℤ) • X s + p) : Function.Bijective ψ := by
  apply PositivityTheory.Groth.ChartWirtingerDerivatives.tri_bij <;> assumption

theorem uni_inj {M I : Type*} (L : M ≃ I) (w : M → ℕ) (f : M → I →₀ ℤ)
    (h1 : ∀ m, f m (L m) = 1) (hlt : ∀ m n, f m (L n) ≠ 0 → m = n ∨ w m < w n) :
    Function.Injective (Finsupp.linearCombination ℤ f) := by
  apply PositivityTheory.Groth.ChartWirtingerDerivatives.uni_inj <;> assumption

theorem uni_exists {M I C : Type*} (L : M ≃ I) (c : M → C) (w : M → ℕ) (b : C → ℕ) (f : M → I →₀ ℤ)
    (hb : ∀ m, w m ≤ b (c m)) (h1 : ∀ m, f m (L m) = 1)
    (hlt : ∀ m n, f m (L n) ≠ 0 → c m = c n ∧ (m = n ∨ w m < w n)) :
    ∀ n, ∃ a : M →₀ ℤ, (∀ m ∈ a.support, c m = c n) ∧
      Finsupp.linearCombination ℤ f a = Finsupp.single (L n) 1 := by
  apply PositivityTheory.Groth.ChartWirtingerDerivatives.uni_exists <;> assumption

theorem uni_bij {M I C : Type*} (L : M ≃ I) (c : M → C) (w : M → ℕ) (b : C → ℕ) (f : M → I →₀ ℤ)
    (hb : ∀ m, w m ≤ b (c m)) (h1 : ∀ m, f m (L m) = 1)
    (hlt : ∀ m n, f m (L n) ≠ 0 → c m = c n ∧ (m = n ∨ w m < w n)) :
    Function.Bijective (Finsupp.linearCombination ℤ f) := by
  refine ⟨uni_inj L w f h1 fun m n h => (hlt m n h).2, ?_⟩
  intro y
  refine Finsupp.induction_linear y ?_ ?_ ?_
  · exact ⟨0, map_zero _⟩
  · rintro y z ⟨a, ha⟩ ⟨a', ha'⟩
    exact ⟨a + a', by rw [map_add (f := _), ha, ha']⟩
  · intro i r
    obtain ⟨a, -, ha⟩ := uni_exists L c w b f hb h1 hlt (L.symm i)
    exact ⟨r • a, by rw [map_smul, ha, L.apply_symm_apply, Finsupp.smul_single_one]⟩

end CompanionTheory.Groth.ChartWirtingerDerivatives

namespace CompanionTheory.Groth

theorem triAut : TriAut := fun _ w ψ h => ChartWirtingerDerivatives.tri_bij w ψ h

theorem uniTri : UniTri := fun _ _ _ L c w b f hb h1 hlt =>
  ⟨ChartWirtingerDerivatives.uni_bij L c w b f hb h1 hlt, ChartWirtingerDerivatives.uni_exists L c w b f hb h1 hlt⟩

end CompanionTheory.Groth
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos



namespace CompanionTheory.Groth.AltS

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def tN (Δ : Segment k) (n : ℕ) : IrrGL (k := k) := Δ.first.nu (n : ℂ)

theorem tN_injective (Δ : Segment k) : Function.Injective (tN Δ) := fun a b h =>
  GlobalTheory.T.cuspidal_twist_injective CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top Δ.first Δ.isCusp_first a b h

theorem tN_zero (Δ : Segment k) : tN Δ 0 = Δ.first := by
  simp [tN]

theorem vWord_eq (Δ : Segment k) (S : Finset (Fin Δ.len)) :
    vWord Δ S = (AltC.wN Δ.len (S.map Fin.valEmbedding)).map (tN Δ) := by
  have key : ∀ (p : Fin Δ.len → Bool) (q : ℕ → Bool), (∀ a : Fin Δ.len, p a = q a) →
      ((List.finRange Δ.len).filter p).map Fin.val = (List.range Δ.len).filter q := by
    intro p q hpq
    rw [← List.map_coe_finRange_eq_range, List.filter_map]
    congr 1
    exact List.filter_congr fun a _ => hpq a
  have hmemS : ∀ a : Fin Δ.len, (a : ℕ) ∈ S.map Fin.valEmbedding ↔ a ∈ S := fun a => Finset.mem_map' Fin.valEmbedding
  unfold vWord AltC.wN
  rw [← key (fun a => decide (a ∈ S)) (fun n => decide (n ∈ S.map Fin.valEmbedding)) (by intro a; simp only [hmemS]),
    ← key (fun a => decide (a ∉ S)) (fun n => decide (n ∉ S.map Fin.valEmbedding)) (by intro a; simp only [hmemS]),
    ← List.map_reverse, ← List.map_append, List.map_map]
  rfl

theorem decWord_eq (Δ Γ : Segment k) (b : ℕ) (hb : Γ.first = tN Δ b) :
    decWord Γ = ((List.range' b Γ.len).reverse).map (tN Δ) := by
  unfold decWord
  rw [List.map_reverse]
  congr 1
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range']
  rw [Segment.term, hb, tN, tN]
  simp [Nat.cast_add]

theorem first_mem_decWord (Γ : Segment k) : Γ.first ∈ decWord Γ := by
  unfold decWord
  rw [List.mem_reverse, List.mem_ofFn]
  exact ⟨⟨0, Γ.len_pos⟩, by simp [Segment.term]⟩

end CompanionTheory.Groth.AltS

namespace CompanionTheory.Groth

open AltS

theorem altSum (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    AltSum k := by
  intro Δ h Γ
  have hW : ∀ S, (vWord Δ S).Nodup := fun S => by
    rw [vWord_eq]; exact (AltC.nodup_wN _ _).map (tN_injective Δ)
  have hmapiff : (Finset.univ.val.map Γ = {Δ}) ↔ h = 1 ∧ ∀ i, Γ i = Δ := by
    rw [← Multiset.replicate_one, Multiset.eq_replicate]
    simp
  by_cases hex : ∀ i, ∃ n, (Γ i).first = tN Δ n
  · choose b hb using hex
    have hd : ∀ i, decWord (Γ i) = ((List.range' (b i) (Γ i).len).reverse).map (tN Δ) :=
      fun i => decWord_eq Δ (Γ i) (b i) (hb i)
    have H := AltC.altSumN Δ.len Δ.len_pos (vSets Δ) (by intro S; simp [vSets]) b (fun i => (Γ i).len)
      (fun i => (Γ i).len_pos)
      (fun S => (-1 : ℤ) ^ S.card * (shuffleCount (vWord Δ S) (fun i => decWord (Γ i)) : ℤ)) (by
        intro S
        congr 1
        rw [AltC.shuffleCount_eq _ _ (hW S)]
        have e : ((∀ i, (decWord (Γ i)).Sublist (vWord Δ S)) ∧ ∀ x ∈ vWord Δ S, ∃! i, x ∈ decWord (Γ i)) ↔
            AltC.Cond Δ.len (S.map Fin.valEmbedding) b (fun i => (Γ i).len) := by
          simp only [hd, vWord_eq]
          rw [AltC.cond_map (tN Δ) (tN_injective Δ)]
          rfl
        by_cases hC : AltC.Cond Δ.len (S.map Fin.valEmbedding) b (fun i => (Γ i).len)
        · rw [if_pos (e.2 hC), if_pos hC]; simp
        · rw [if_neg (mt e.1 hC), if_neg hC]; simp)
    rw [H]
    have hiff : (h = 1 ∧ ∀ i, b i = 0 ∧ (Γ i).len = Δ.len) ↔ Finset.univ.val.map Γ = {Δ} := by
      rw [hmapiff]
      refine and_congr_right fun _ => forall_congr' fun i => ⟨fun ⟨h0, hl⟩ => ?_, fun he => ⟨?_, by rw [he]⟩⟩
      · exact Segment.ext_first (by rw [hb i, h0, tN_zero]) hl
      · exact tN_injective Δ (by rw [← hb i, he, tN_zero])
    by_cases hc : Finset.univ.val.map Γ = {Δ}
    · rw [if_pos (hiff.2 hc), if_pos hc]
    · rw [if_neg (mt hiff.1 hc), if_neg hc]
  · push Not at hex
    obtain ⟨i, hi⟩ := hex
    rw [if_neg]
    · apply Finset.sum_eq_zero
      intro S _
      rw [AltC.shuffleCount_eq _ _ (hW S), if_neg]
      · simp
      rintro ⟨hs, _⟩
      have := (hs i).subset (first_mem_decWord (Γ i))
      rw [vWord_eq, List.mem_map] at this
      obtain ⟨n, _, hn⟩ := this
      exact hi n hn.symm
    · rw [hmapiff]
      rintro ⟨_, hall⟩
      exact hi 0 (by rw [hall i, tN_zero])

end CompanionTheory.Groth

end
end
