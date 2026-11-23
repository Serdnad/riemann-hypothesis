module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle564
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle002
import Aesop.Main
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue.LeafB

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_infOf (hD : DiscInf) (hT : TopInf) (τ : E →+* ℂ) :
    ∀ {N : ℕ} {t : Tr E N}, t.Good → ∃ m', t.InfOf τ m' := by
  intro N t
  induction t with
  | leaf V z =>
    intro h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨-, hV, -⟩
    · exact ⟨_, 0, hT E τ, rfl⟩
    · obtain ⟨m₀, hm₀⟩ := hD E _ V hV τ
      exact ⟨_, m₀, hm₀, rfl⟩
  | node t₁ t₂ i₁ i₂ =>
    intro h
    obtain ⟨m₁, h₁⟩ := i₁ h.1
    obtain ⟨m₂, h₂⟩ := i₂ h.2
    exact ⟨_, m₁, m₂, h₁, h₂, rfl⟩

theorem leaf_entries (hD : DiscInf) (hT : TopInf) (B : ℝ) :
    ∀ {N : ℕ} {t : Tr E N}, t.Good → (∀ τ m', t.InfOf τ m' → ∀ x ∈ m', ‖x‖ ≤ B) →
      LeafZ (fun M V z => 0 < M → GlobalTheory.UnitaryBC.IsDiscrete V ∧
        ∀ (τ : E →+* ℂ) (m₀ : Multiset ℂ), HasInfCharGL V τ m₀ → ∀ x ∈ m₀, ‖x + z‖ ≤ B) t := by
  intro N t
  induction t with
  | leaf V z =>
    intro h hb hM
    rcases h with ⟨h0, -, -⟩ | ⟨-, hV, -⟩
    · omega
    · refine ⟨hV, fun τ m₀ hm₀ x hx => ?_⟩
      exact hb τ (m₀.map (· + z)) ⟨m₀, hm₀, rfl⟩ _ (Multiset.mem_map_of_mem _ hx)
  | node t₁ t₂ i₁ i₂ =>
    intro h hb
    refine ⟨i₁ h.1 fun τ m₁ h₁ x hx => ?_, i₂ h.2 fun τ m₂ h₂ x hx => ?_⟩
    · obtain ⟨m₂, h₂⟩ := exists_infOf hD hT τ h.2
      exact hb τ (m₁ + m₂) ⟨m₁, m₂, h₁, h₂, rfl⟩ x (Multiset.mem_add.2 (Or.inl hx))
    · obtain ⟨m₁, h₁⟩ := exists_infOf hD hT τ h.1
      exact hb τ (m₁ + m₂) ⟨m₁, m₂, h₁, h₂, rfl⟩ x (Multiset.mem_add.2 (Or.inr hx))

theorem norm_sum_le (s : Multiset ℂ) (B : ℝ) (h : ∀ x ∈ s, ‖x‖ ≤ B) :
    ‖s.sum‖ ≤ (Multiset.card s : ℝ) * B := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.sum_cons, Multiset.card_cons]
    have h1 := h a (Multiset.mem_cons_self a s)
    have h2 := ih fun x hx => h x (Multiset.mem_cons_of_mem hx)
    have h3 := norm_add_le a s.sum
    push_cast
    linarith

theorem sum_map_add_const (s : Multiset ℂ) (z : ℂ) :
    (s.map (· + z)).sum = s.sum + (Multiset.card s : ℂ) * z := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.sum_cons, Multiset.card_cons]
    push_cast
    ring

theorem leaf_bound (hD : DiscInf) {M : ℕ} (hM : 0 < M) {V : Submodule ℂ (Sm E M)} (hV : GlobalTheory.UnitaryBC.IsDiscrete V) {z : ℂ} {B : ℝ}
    (hb : ∀ (τ : E →+* ℂ) (m₀ : Multiset ℂ), HasInfCharGL V τ m₀ → ∀ x ∈ m₀, ‖x + z‖ ≤ B) :
    InfBdd (2 * B) V ∧ ‖z‖ ≤ 2 * B := by
  choose m₀ hm₀ using hD E M V hV
  have htr : ∑ τ, (m₀ τ).sum = 0 := GlobalTheory.CompanionTheory.TotalTrace.total_trace_eq_zero hV hm₀
  have hcard : ∀ τ, Multiset.card (m₀ τ) = M := fun τ => (hm₀ τ).1
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hd : 0 < Fintype.card (E →+* ℂ) := Fintype.card_pos_iff.2 ⟨τ₀⟩
  have hB : 0 ≤ B := by
    obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.1 (by rw [hcard τ₀]; exact hM)
    exact (norm_nonneg _).trans (hb τ₀ _ (hm₀ τ₀) x hx)
  have hsum : ∑ τ, ((m₀ τ).map (· + z)).sum = (Fintype.card (E →+* ℂ) : ℂ) * ((M : ℂ) * z) := by
    simp only [sum_map_add_const, hcard, Finset.sum_add_distrib, htr, zero_add, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  have hle : ‖∑ τ, ((m₀ τ).map (· + z)).sum‖ ≤ (Fintype.card (E →+* ℂ) : ℝ) * ((M : ℝ) * B) := by
    refine (norm_sum_le_of_le Finset.univ (n := fun _ => (M : ℝ) * B) fun τ _ => ?_).trans_eq (by simp)
    have := norm_sum_le ((m₀ τ).map (· + z)) B (fun y hy => by
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hy
      exact hb τ _ (hm₀ τ) x hx)
    simpa [hcard] using this
  have hz : ‖z‖ ≤ B := by
    rw [hsum, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast] at hle
    have hdM : (0 : ℝ) < (Fintype.card (E →+* ℂ) : ℝ) * (M : ℝ) := by positivity
    have : ((Fintype.card (E →+* ℂ) : ℝ) * (M : ℝ)) * ‖z‖ ≤ ((Fintype.card (E →+* ℂ) : ℝ) * (M : ℝ)) * B := by
      nlinarith [hle]
    exact le_of_mul_le_mul_left this hdM
  refine ⟨fun τ => ⟨m₀ τ, hm₀ τ, fun x hx => ?_⟩, by linarith⟩
  have h1 := hb τ _ (hm₀ τ) x hx
  have h2 : ‖x‖ ≤ ‖x + z‖ + ‖z‖ := by simpa using norm_sub_le (x + z) z
  linarith

theorem leaves_of_entries (hD : DiscInf) (B : ℝ) : ∀ {N : ℕ} {t : Tr E N},
    LeafZ (fun M V z => 0 < M → GlobalTheory.UnitaryBC.IsDiscrete V ∧
      ∀ (τ : E →+* ℂ) (m₀ : Multiset ℂ), HasInfCharGL V τ m₀ → ∀ x ∈ m₀, ‖x + z‖ ≤ B) t →
    LeafZ (fun M V z => 0 < M → InfBdd (2 * B) V ∧ ‖z‖ ≤ 2 * B) t := by
  intro N t
  induction t with
  | leaf V z =>
    intro key hM
    obtain ⟨hV, hb⟩ := key hM
    exact leaf_bound hD hM hV hb
  | node t₁ t₂ i₁ i₂ => exact fun key => ⟨i₁ key.1, i₂ key.2⟩

theorem leafBound : DiscInf → TopInf → InfOfEq → LeafBound := by
  intro hD hT hQ E _ _ _ N t ψ m B hI hG hψ hψ0 hC hB
  refine leaves_of_entries hD B (leaf_entries hD hT B hG fun τ m' hm' x hx => ?_)
  rw [hQ E N t ψ m τ m' hI hm' hψ hψ0 hC] at hx
  exact hB τ x hx

end GlobalTheory.CompanionTheory.EGlue.LeafB

end
end

section

open MeasureTheory

namespace GlobalTheory.CompanionTheory.GunrVol

theorem selfDualVol : PositivityTheory.SiegelWeilFormula.Gunr.SelfDualVol := by
  intro V _ _ _ _ _ μ χ hsd L hLo hLc hadd _ hann
  obtain ⟨hH, hinv⟩ := hsd
  haveI := hH
  have hLcl : IsClosed (L : Set V) := AddSubgroup.isClosed_of_isOpen L hLo
  have hLm : MeasurableSet (L : Set V) := hLo.measurableSet
  have hfin : μ (L : Set V) ≠ ⊤ := hLc.measure_lt_top.ne
  have hpos : μ (L : Set V) ≠ 0 := (hLo.measure_pos μ ⟨0, L.zero_mem⟩).ne'
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : V → ℂ, Φ = (L : Set V).indicator 1 := ⟨_, rfl⟩
  have hΦin : ∀ x ∈ L, Φ x = 1 := fun x hx => by
    rw [hΦ]; exact Set.indicator_of_mem (s := (L : Set V)) hx _
  have hΦout : ∀ x, x ∉ L → Φ x = 0 := fun x hx => by
    rw [hΦ]; exact Set.indicator_of_notMem (s := (L : Set V)) hx _
  have hΦc : Continuous Φ := by
    rw [hΦ]
    exact continuous_one.indicator (by
      intro a ha
      rw [(IsClopen.frontier_eq ⟨hLcl, hLo⟩)] at ha
      exact absurd ha (Set.notMem_empty a))
  have hΦs : HasCompactSupport Φ := by
    refine HasCompactSupport.intro hLc ?_
    intro x hx
    exact hΦout x hx
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = μ.real (L : Set V) := ⟨_, rfl⟩
  have hI : ∀ y, ∫ x, Φ x * χ x y ∂μ = (L : Set V).indicator (fun _ => (m : ℂ)) y := by
    intro y
    by_cases hy : y ∈ L
    · have h1 : (fun x => Φ x * χ x y) = Φ := by
        funext x
        by_cases hx : x ∈ L
        · rw [(hann y).2 hy x hx, mul_one]
        · rw [hΦout x hx, zero_mul]
      rw [h1, Set.indicator_of_mem (s := (L : Set V)) hy, hΦ, integral_indicator hLm]
      simp [hm]
    · rw [Set.indicator_of_notMem (s := (L : Set V)) hy]
      have h2 := (hann y).not.2 hy
      push_neg at h2
      obtain ⟨x0, hx0, hne⟩ := h2
      have h3 : ∫ x, Φ x * χ x y ∂μ = χ x0 y * ∫ x, Φ x * χ x y ∂μ := by
        calc ∫ x, Φ x * χ x y ∂μ = ∫ x, (fun x => Φ x * χ x y) (x0 + x) ∂μ :=
              (integral_add_left_eq_self _ x0).symm
          _ = ∫ x, χ x0 y * (Φ x * χ x y) ∂μ := by
              congr 1
              funext x
              have : Φ (x0 + x) = Φ x := by
                by_cases hx : x ∈ L
                · rw [hΦin _ (L.add_mem hx0 hx), hΦin _ hx]
                · rw [hΦout _ (fun h => hx ((L.add_mem_cancel_left hx0).1 h)), hΦout _ hx]
              simp only [this, hadd]
              ring
          _ = χ x0 y * ∫ x, Φ x * χ x y ∂μ := integral_const_mul _ _
      have h4 : (1 - χ x0 y) * ∫ x, Φ x * χ x y ∂μ = 0 := by
        rw [sub_mul, one_mul, ← h3, sub_self]
      exact (mul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 (Ne.symm hne))
  have hInt : Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ := by
    rw [funext hI]
    exact (integrable_indicator_iff hLm).2 (integrableOn_const hfin)
  have h0 := hinv Φ hΦc hΦs hInt 0
  have hout : (fun y => (∫ x, Φ x * χ x y ∂μ) * χ y 0) = (L : Set V).indicator (fun _ => (m : ℂ)) := by
    funext y
    rw [hI]
    by_cases hy : y ∈ L
    · rw [(hann 0).2 L.zero_mem y hy, mul_one]
    · rw [Set.indicator_of_notMem (s := (L : Set V)) hy, zero_mul]
  rw [hout, integral_indicator hLm, neg_zero, hΦin 0 L.zero_mem] at h0
  have h5 : (m : ℂ) * m = 1 := by
    have := h0
    simp only [setIntegral_const, ← hm, Complex.real_smul] at this
    exact this
  have h6 : m * m = 1 := by exact_mod_cast h5
  have hm0 : 0 ≤ m := by rw [hm]; exact measureReal_nonneg
  have h7 : m = 1 := by nlinarith
  rw [hm, measureReal_def, ENNReal.toReal_eq_one_iff] at h7
  exact h7

end GlobalTheory.CompanionTheory.GunrVol
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.FixedPointsCM

open NumberField IsDedekindDomain HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct

theorem exists_eq_algebraMap_of_sigR_eq {F E K : Type} [Field F] [CharZero F] [Field E] [Algebra F E]
    [CommRing K] [Algebra F K] (σ : E →ₐ[F] E) (hfin : Module.finrank F E = 2)
    (hσ : ∀ x, σ (σ x) = x) (u : E) (hu : σ u ≠ u) (x : K ⊗[F] E) (hx : sigR K σ x = x) :
    ∃ c : K, x = algebraMap K (K ⊗[F] E) c := by
  have hli : LinearIndependent F ![(1 : E), u] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h2 : s • (1 : E) + t • σ u = 0 := by
      have := congrArg σ h
      simpa [map_add (f := _), map_smul] using this
    have h3 : t • (σ u - u) = 0 := by
      have : t • (σ u - u) = (s • (1 : E) + t • σ u) - (s • (1 : E) + t • u) := by module
      rw [this, h, h2, sub_zero]
    have ht : t = 0 := by
      rcases smul_eq_zero.mp h3 with h4 | h4
      · exact h4
      · exact absurd (sub_eq_zero.mp h4) hu
    subst ht
    refine ⟨?_, rfl⟩
    simpa using h
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by simp [hfin]
  let b : Module.Basis (Fin 2) F E := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = u := by simp [b]
  obtain ⟨p, q, hsu⟩ : ∃ p q : F, σ u = p • (1 : E) + q • u := by
    refine ⟨b.repr (σ u) 0, b.repr (σ u) 1, ?_⟩
    have := b.sum_repr (σ u)
    rw [Fin.sum_univ_two, hb0, hb1] at this
    exact this.symm
  have hrel : (p + q * p) • (1 : E) + (q * q - 1) • u = 0 := by
    have h1 : u = p • (1 : E) + q • σ u := by
      have := hσ u
      rw [hsu] at this
      simpa [map_add (f := _), map_smul] using this.symm
    rw [hsu] at h1
    have : (p + q * p) • (1 : E) + (q * q - 1) • u = (p • (1 : E) + q • (p • (1 : E) + q • u)) - u := by module
    rw [this, ← h1, sub_self]
  obtain ⟨hp, hq⟩ := LinearIndependent.pair_iff.mp hli _ _ hrel
  have hq' : q = -1 := by
    have : (q - 1) * (q + 1) = 0 := by linear_combination hq
    rcases mul_eq_zero.mp this with h | h
    · exfalso
      have hq1 : q = 1 := sub_eq_zero.mp h
      subst hq1
      have hp0 : p = 0 := by
        have : (2 : F) * p = 0 := by linear_combination hp
        simpa using this
      apply hu
      rw [hsu, hp0]
      simp
    · linear_combination h
  subst hq'
  let B := Algebra.TensorProduct.basis K b
  have hB0 : B 0 = (1 : K) ⊗ₜ[F] (1 : E) := by simp [B, hb0]
  have hB1 : B 1 = (1 : K) ⊗ₜ[F] u := by simp [B, hb1]
  obtain ⟨a, c, hac⟩ : ∃ a c : K, x = a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] u := by
    refine ⟨B.repr x 0, B.repr x 1, ?_⟩
    have := B.sum_repr x
    rw [Fin.sum_univ_two, hB0, hB1] at this
    simpa [TensorProduct.smul_tmul'] using this.symm
  have hs : sigR K σ x = a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] σ u := by
    rw [hac]
    simp [sigR]
  have hkey : (algebraMap F K p * c) • B 0 = (c + c) • B 1 := by
    rw [hB0, hB1]
    have h1 : a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] σ u = a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] u := by rw [← hs, hx, hac]
    have h2 := add_left_cancel h1
    rw [hsu, TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, neg_smul, one_smul] at h2
    have e0 : (algebraMap F K p * c) • ((1 : K) ⊗ₜ[F] (1 : E)) = p • (c ⊗ₜ[F] (1 : E)) := by
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul']
      congr 1
      simp [Algebra.smul_def]
    have e1 : (c + c) • ((1 : K) ⊗ₜ[F] u) = c ⊗ₜ[F] u + c ⊗ₜ[F] u := by
      rw [TensorProduct.smul_tmul', ← TensorProduct.add_tmul]
      simp
    rw [e0, e1]
    exact add_neg_eq_iff_eq_add.mp h2
  have hc : c = 0 := by
    have h1 := congrArg (fun y => B.repr y 1) hkey
    simp at h1
    have h2 : (2 : F) • c = 0 := by rw [two_smul]; exact h1.symm
    rcases smul_eq_zero.mp h2 with h | h
    · simp at h
    · exact h
  refine ⟨a, ?_⟩
  rw [hac, hc, Algebra.TensorProduct.algebraMap_apply]
  simp

theorem fixedK : PositivityTheory.SiegelWeilFormula.Gunr.FixedK := by
  intro F E _ _ _ _ _ σ h v x hx
  obtain ⟨-, hC, hfin, hconj⟩ := h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hσ : ∀ y, σ (σ y) = y := fun y => τ.injective (by rw [hconj, hconj, star_star])
  obtain ⟨u, hu⟩ : ∃ u, σ u ≠ u := by
    by_contra hall
    push Not at hall
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [ComplexEmbedding.isReal_iff]
    ext y
    rw [ComplexEmbedding.conjugate_coe_eq]
    have := hconj τ y
    rw [hall y] at this
    exact this.symm
  exact exists_eq_algebraMap_of_sigR_eq σ hfin hσ u hu x hx

end GlobalTheory.CompanionTheory.FixedPointsCM
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.GunrInv

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen
  PositivityTheory.SiegelWeilFormula.Gunr Filter
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trPair_add_left (R : Type) [CommRing R] [Algebra F R] {n : ℕ}
    (A B C : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    trPair (F := F) (E := E) R (A + B) C = trPair (F := F) (E := E) R A C + trPair (F := F) (E := E) R B C := by
  simp only [trPair, Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _), mul_add]

theorem trPair_add_right (R : Type) [CommRing R] [Algebra F R] {n : ℕ}
    (A B C : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    trPair (F := F) (E := E) R A (B + C) = trPair (F := F) (E := E) R A B + trPair (F := F) (E := E) R A C := by
  simp only [trPair, Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem multiplicity_add_lattice_preserving {R : Type} [CommRing R] [MeasurableSpace R] {n : ℕ} (lam : Measure (Fin n → R))
    (L : AddSubgroup (Fin n → R)) (b h : Matrix (Fin n) (Fin n) R) (hh : ∀ y ∈ L, h.mulVec y ∈ L) :
    nu2 lam L L (b + h) = nu2 lam L L b := by
  have e : {x | ∃ y ∈ L, ∃ y' ∈ L, x = y + (b + h).mulVec y'} = {x | ∃ y ∈ L, ∃ y' ∈ L, x = y + b.mulVec y'} := by
    ext x
    constructor
    · rintro ⟨y, hy, y', hy', rfl⟩
      refine ⟨y + h.mulVec y', L.add_mem hy (hh y' hy'), y', hy', ?_⟩
      rw [Matrix.add_mulVec]
      abel
    · rintro ⟨y, hy, y', hy', rfl⟩
      refine ⟨y - h.mulVec y', L.sub_mem hy (hh y' hy'), y', hy', ?_⟩
      rw [Matrix.add_mulVec]
      abel
  simp only [nu2, e]

section Good

variable {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
  {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ψv : Fv F v → ℂ} {S : Subring (Fv F v ⊗[F] E)}
  {σS : S →+* S} {ϖ : Fv F v} {ε : ℤ}

theorem trPair_mem (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) {A B : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)}
    (hA : ∀ i j, A i j ∈ S) (hB : ∀ i j, B i j ∈ S) :
    trPair (F := F) (E := E) (Fv F v) A B ∈ v.adicCompletionIntegers F := by
  have e : algebraMap F (Fv F v) (1 / 2) = (2 : Fv F v)⁻¹ := by
    rw [one_div, map_inv₀, map_ofNat]
  rw [trPair, e]
  exact mul_mem hG.half_mem (hG.trace_mem
    (sum_mem fun a _ => sum_mem fun c _ => mul_mem (hA a c) (hB c a)))

theorem gramR_mem (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) {Y : Fin n → Fin M → Fv F v ⊗[F] E}
    (hY : Y ∈ latV (M := M) (n := n) bs v) (a c : Fin n) : gramR (Fv F v) σ J Y a c ∈ S := by
  have hmem : ∀ a i, Y a i ∈ S := fun a i => by
    have : Y a i ∈ (S : Set (Fv F v ⊗[F] E)) := by
      rw [hG.carrier]
      exact fun k => hY a i k
    exact this
  have hsig : ∀ x ∈ S, sigR (Fv F v) σ x ∈ S := fun x hx => by
    have := (σS ⟨x, hx⟩).2
    rwa [hG.sig ⟨x, hx⟩] at this
  show ∑ i, ∑ j, sigR (Fv F v) σ (Y a i) * JR (Fv F v) J i j * Y c j ∈ S
  exact sum_mem fun i _ => sum_mem fun j _ =>
    mul_mem (mul_mem (hsig _ (hmem a i)) (hG.J_int i j)) (hmem c j)

theorem jtR_add (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (b h : HermR (Fv F v) σ n) (hh : h ∈ H0 S σ n) :
    jtR (Fv F v) σ J ψv μv ((latV bs v).indicator 1) (b + h) = jtR (Fv F v) σ J ψv μv ((latV bs v).indicator 1) b := by
  unfold jtR
  congr 1
  funext Y
  by_cases hY : Y ∈ latV (M := M) (n := n) bs v
  · have h1 : ψv (trPair (F := F) (E := E) (Fv F v) (h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (gramR (Fv F v) σ J Y)) = 1 :=
      hG.psi_of_mem (trPair_mem hG hh (gramR_mem hG hY))
    rw [AddSubgroup.coe_add, trPair_add_left, hG.psi_add, h1, mul_one]
  · simp [Set.indicator_of_notMem hY]

theorem character_add_integral_hermitian (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (hT : ∀ a b, σ (T b a) = T a b)
    (b h : HermR (Fv F v) σ n) (hh : h ∈ H0 S σ n) :
    ψv (-trPair (Fv F v) (hermOf (Fv F v) σ T hT).1 (b + h).1) = ψv (-trPair (Fv F v) (hermOf (Fv F v) σ T hT).1 b.1) := by
  have h1 : trPair (F := F) (E := E) (Fv F v) (hermOf (Fv F v) σ T hT).1 h.1 ∈ v.adicCompletionIntegers F :=
    trPair_mem hG (fun i j => hG.T_int i j) hh
  have h2 : ψv (-trPair (F := F) (E := E) (Fv F v) (hermOf (Fv F v) σ T hT).1 h.1) = 1 :=
    hG.psi_of_mem (neg_mem h1)
  rw [AddSubgroup.coe_add, trPair_add_right, neg_add, hG.psi_add, h2, mul_one]

theorem mulVec_mem_L (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (L : AddSubgroup (Fin n → Fv F v ⊗[F] E))
    (hL : (L : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v) (h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (hh : ∀ i j, h i j ∈ S) (y : Fin n → Fv F v ⊗[F] E) (hy : y ∈ L) : h.mulVec y ∈ L := by
  have key : ∀ w : Fin n → Fv F v ⊗[F] E, w ∈ L ↔ ∀ a, w a ∈ S := fun w => by
    have e1 : w ∈ L ↔ w ∈ (latO bs v : Set (Fin n → Fv F v ⊗[F] E)) := by
      rw [← hL]; rfl
    have e2 : ∀ x, x ∈ S ↔ x ∈ Rv bs v := fun x => by
      rw [← hG.carrier]; rfl
    rw [e1]
    simp only [e2]
    rfl
  rw [key] at hy ⊢
  intro a
  show ∑ j, h a j * y j ∈ S
  exact sum_mem fun j _ => mul_mem (hh a j) (hy j)

end Good

theorem integrand_invariant_integral_hermitian : HermitianLatticeInvariance := by
  intro F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG hT μv lam L hL z b h hh
  unfold whI
  rw [jtR_add hG μv b h hh, character_add_integral_hermitian hG hT b h hh]
  have e : nu2 lam L L (b + h).1 = nu2 lam L L b.1 := by
    rw [AddSubgroup.coe_add]
    exact multiplicity_add_lattice_preserving lam L _ _ (mulVec_mem_L hG L hL _ hh)
  rw [e]

end GlobalTheory.CompanionTheory.GunrInv

end
end
