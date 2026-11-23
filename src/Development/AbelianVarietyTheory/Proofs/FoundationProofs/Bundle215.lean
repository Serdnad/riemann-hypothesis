module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle205
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle153
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle058
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle206
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle169
public import Mathlib.NumberTheory.ModularForms.NormTrace
public import Mathlib.NumberTheory.ModularForms.Petersson
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle208
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReducesOfDetEvMEqZero
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle209
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011

@[expose] public section

section

noncomputable section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.AlmostEt.TrTower

section Sep

variable {L : Type*} [Field L] {G : Type*} [Group G] [MulSemiringAction G L]

theorem isSep_mul_right {v : Valuation L ℝ≥0} {N : Subgroup G} {n : ℕ} {a b : Fin n → L} {c : L}
    (h : IsSep v N a b c) {d : L} (hd : d ∈ Fix L N) (hdv : v d ≤ 1) (hcd : v (c * d) ≤ 1) :
    IsSep v N (fun i => a i * d) b (c * d) := by
  refine
    { a_mem := fun i => mul_mem (h.a_mem i) hd
      b_mem := h.b_mem
      c_mem := mul_mem h.c_mem hd
      a_le := ?_
      b_le := h.b_le
      c_le := hcd
      sum_in := ?_
      sum_out := ?_ }
  · intro i
    rw [map_mul]
    exact mul_le_one' (h.a_le i) hdv
  · intro σ hσ
    simp_rw [mul_right_comm _ d]; rw [← Finset.sum_mul, h.sum_in σ hσ]
  · intro σ hσ
    simp_rw [mul_right_comm _ d]; rw [← Finset.sum_mul, h.sum_out σ hσ, zero_mul]

theorem isSep_swap {v : Valuation L ℝ≥0} {N : Subgroup G} {n : ℕ} {a b : Fin n → L} {c : L}
    (h : IsSep v N a b c) : IsSep v N b a c := by
  refine
    { a_mem := h.b_mem
      b_mem := h.a_mem
      c_mem := h.c_mem
      a_le := h.b_le
      b_le := h.a_le
      c_le := h.c_le
      sum_in := ?_
      sum_out := ?_ }
  · intro σ hσ
    have h1 := congrArg (σ • ·) (h.sum_in σ⁻¹ (inv_mem hσ))
    have hc : σ • c = c := h.c_mem ⟨σ, hσ⟩
    simp only [Finset.smul_sum, smul_mul', smul_inv_smul, hc] at h1
    simpa [mul_comm] using h1
  · intro σ hσ
    have h1 := congrArg (σ • ·) (h.sum_out σ⁻¹ (fun h' => hσ (by simpa using inv_mem h')))
    simp only [Finset.smul_sum, smul_mul', smul_inv_smul, smul_zero] at h1
    simpa [mul_comm] using h1

end Sep

section Tower

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

def fixInt {H : Subgroup (Gal p Ω)} (V : Subgroup H) :
    Subalgebra (O0 p) (integralClosure (O0 p) Ω) where
  carrier := {s | ∀ g : V, g • (s : Ω) = s}
  mul_mem' {x y} hx hy g := by
    simp only [Set.mem_setOf_eq, Subalgebra.coe_mul] at *
    rw [smul_mul', hx g, hy g]
  add_mem' {x y} hx hy g := by
    simp only [Set.mem_setOf_eq, Subalgebra.coe_add] at *
    rw [smul_add, hx g, hy g]
  algebraMap_mem' r g := by
    show g • (algebraMap (O0 p) Ω r) = _
    exact ((g : H) : Gal p Ω).commutes r

theorem towerAlg_fixed (T : Tower p Ω) {s : integralClosure (O0 p) Ω} (hs : s ∈ towerAlg T)
    (g : ↥(⨅ n, Gn T n)) : g • (s : Ω) = s := by
  have hle : towerAlg T ≤ fixInt (⊤ : Subgroup ↥(⨅ n, Gn T n)) := by
    refine Algebra.adjoin_le ?_
    rintro x (⟨m, rfl⟩ | ⟨m, rfl⟩) g
    · exact ((GlobalTheory.K5.Basic.mem_gn T m _).1 (Subgroup.mem_iInf.1 (g : ↥(⨅ n, Gn T n)).2 m)).1
    · exact ((GlobalTheory.K5.Basic.mem_gn T m _).1 (Subgroup.mem_iInf.1 (g : ↥(⨅ n, Gn T n)).2 m)).2
  exact hle hs ⟨g, trivial⟩

end Tower

end GlobalTheory.AlmostEt.TrTower

namespace GlobalTheory.AlmostEt.TrTower

theorem exists_trData_towerAlg : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω) (F : Finset (integralClosure (O0 p) Ω)),
    ∃ (C : Subalgebra (O0 p) (integralClosure (O0 p) Ω))
      (tr : (integralClosure (O0 p) Ω) → (integralClosure (O0 p) Ω)) (n : ℕ)
      (a b : Fin n → (integralClosure (O0 p) Ω)),
      (↑F : Set (integralClosure (O0 p) Ω)) ⊆ C ∧
        IsTrData (towerAlg T) C tr a b (p : (integralClosure (O0 p) Ω)) := by
  intro p _ Ω _ _ hp2 hclo T F
  classical
  have hpcoe : ((p : integralClosure (O0 p) Ω) : Ω) = p := map_natCast (integralClosure (O0 p) Ω).val p
  obtain ⟨v, hvint, hvinv, hp0, hp1, hS⟩ := GlobalTheory.T.exists_valuation_almostEtale_towerFixer p Ω hp2 hclo T
  obtain ⟨U, -, hUfin, hUfix, hUsep⟩ := hS (F.image Subtype.val)
  obtain ⟨n, a, b, c, hsep, hc⟩ := hUsep (v p) hp1
  haveI := hUfin
  haveI : Fintype (↥(⨅ n, Gn T n) ⧸ U) := Fintype.ofFinite _
  have hvinv' : ∀ (g : ↥(⨅ n, Gn T n)) (x : Ω), v (g • x) = v x := fun g x => hvinv g x
  have hc0 : c ≠ 0 := by
    rintro rfl; rw [map_zero] at hc; exact (not_lt_zero' hc)
  have hvc : 0 < v c := lt_of_le_of_lt (by positivity) hc

  have hpfix : ∀ (g : ↥(⨅ n, Gn T n)), g • (p : Ω) = p := fun g => by
    change ((g : Gal p Ω)) (p : Ω) = p
    exact map_natCast _ p
  have hd : (p : Ω) / c ∈ Fix Ω U := div_mem (fun g => hpfix g) hsep.c_mem
  have hdv : v ((p : Ω) / c) ≤ 1 := by
    rw [map_div₀]; exact div_le_one_of_le₀ hc.le (by positivity)
  have hsep' : IsSep v U (fun i => a i * ((p : Ω) / c)) b (p : Ω) := by
    have := isSep_mul_right hsep hd hdv (by rw [mul_div_cancel₀ _ hc0]; exact hp1.le)
    rwa [mul_div_cancel₀ _ hc0] at this
  have hsw := isSep_swap hsep'
  have hint : ∀ x : Ω, v x ≤ 1 → x ∈ integralClosure (O0 p) Ω := fun x hx => (hvint x).1 hx
  let a' : Fin n → integralClosure (O0 p) Ω := fun i => ⟨_, hint _ (hsep'.a_le i)⟩
  let b' : Fin n → integralClosure (O0 p) Ω := fun i => ⟨_, hint _ (hsep'.b_le i)⟩
  have htrint : ∀ s : integralClosure (O0 p) Ω, cosetTrace U (s : Ω) ∈ integralClosure (O0 p) Ω :=
    fun s => Subalgebra.sum_mem _ fun q _ => GlobalTheory.K5.Basic.isInt_gal _ s.2
  let tr : integralClosure (O0 p) Ω → integralClosure (O0 p) Ω := fun s => ⟨_, htrint s⟩
  have htr : ∀ s, (tr s : Ω) = cosetTrace U (s : Ω) := fun s => rfl
  have hle : towerAlg T ≤ fixInt U := fun s hs g => towerAlg_fixed T hs (g : ↥(⨅ n, Gn T n))
  refine ⟨fixInt U, tr, n, a', b', ?_, ?_⟩
  · intro s hs
    exact hUfix _ (Finset.mem_image_of_mem _ hs)
  refine
    { le := hle
      e_mem := Subalgebra.natCast_mem _ p
      a_mem := fun i => hsep'.a_mem i
      b_mem := fun i => hsep'.b_mem i
      tr_mem := ?_
      tr_add := ?_
      tr_mul := ?_
      left := ?_
      right := ?_
      sum := ?_ }
  · intro x hx
    apply GlobalTheory.T.mem_towerUnionAdjoin_of_galois_fixed p Ω hclo T
    intro g hg
    exact (cosetTrace_fixed_props Ω v _ hvinv' U _ hx).1 ⟨g, hg⟩
  · intro x _ y _
    apply Subtype.ext
    simp only [htr, Subalgebra.coe_add, cosetTrace, smul_add, Finset.sum_add_distrib]
  · intro β hβ x hx
    apply Subtype.ext
    simp only [htr, Subalgebra.coe_mul]
    exact (cosetTrace_fixed_props Ω v _ hvinv' U _ hx).2.2 _ (towerAlg_fixed T hβ)
  · intro x hx
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, hpcoe, AddSubmonoidClass.coe_finsetSum, htr]
    exact GlobalTheory.T.sum_mul_cosetRepresentativeTrace_eq Ω v _ U n _ _ _ hsep' _ hx
  · intro x hx
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, hpcoe, AddSubmonoidClass.coe_finsetSum, htr]
    exact GlobalTheory.T.sum_mul_cosetRepresentativeTrace_eq Ω v _ U n _ _ _ hsw _ hx
  · apply Subtype.ext
    simp only [Subalgebra.coe_mul, hpcoe, AddSubmonoidClass.coe_finsetSum]
    simpa using hsep'.sum_in 1 (one_mem _)

end GlobalTheory.AlmostEt.TrTower
end
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisForm

lemma sum_shift (L : ℕ) [NeZero L] (φ : ZMod L → ℂ) (u e : ZMod L) (he : IsUnit e) :
    ∑ r ∈ Finset.range L, φ (u + (r : ZMod L) * e) = ∑ y, φ y := by
  rw [Finset.sum_range (fun r => φ (u + (r : ZMod L) * e))]
  refine Fintype.sum_bijective (fun i : Fin L => u + ((i : ℕ) : ZMod L) * e) ?_ _ _ (fun _ => rfl)
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp [ZMod.card]⟩
  intro i i' h
  simp only [add_right_inj] at h
  have h' := he.mul_right_cancel h
  rw [ZMod.natCast_eq_natCast_iff'] at h'
  ext
  rwa [Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt i'.2] at h'

lemma hat_zero (L : ℕ) [NeZero L] (φ : ZMod L → ℂ) : hat φ 0 = ∑ y, φ y := by
  have := sum_shift L φ 0 1 isUnit_one
  simp only [zero_add, mul_one] at this
  rw [← this]; simp [hat]

lemma bdd_of_periodic (L₂ : ℕ) (hL : 0 < L₂) (b : ℤ → ℂ) (hb : ∀ x, b (x + L₂) = b x) :
    ∃ C : ℝ, ∀ x, ‖b x‖ ≤ C := by
  have hp : Function.Periodic b (L₂ : ℤ) := hb
  have hpz : ∀ y n : ℤ, b (y + n * L₂) = b y := fun y n => by simpa using hp.int_mul n y
  refine ⟨∑ i ∈ Finset.range L₂, ‖b i‖, fun x => ?_⟩
  have h1 := Int.emod_nonneg x (by omega : (L₂ : ℤ) ≠ 0)
  have h2 := Int.emod_lt_of_pos x (by omega : (0 : ℤ) < L₂)
  have e : b x = b (((x % L₂).toNat : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg h1, ← hpz (x % L₂) (x / L₂)]
    congr 1
    rw [Int.emod_def]; ring
  rw [e]
  exact Finset.single_le_sum (f := fun i : ℕ => ‖b i‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_range.mpr (by omega))

lemma latF_trans (L₁ L₂ : ℕ) (hL₁ : 0 < L₁) (b χ₁ χ₂ : ℤ → ℂ) (φ : ZMod L₁ → ℂ)
    (hb : ∀ x, b (x + L₂) = b x)
    (hχ : ∀ d : ℤ, IsCoprime d (L₁ * L₂ : ℕ) → (∀ y, φ y = χ₁ d * φ (y * d)) ∧ ∀ x, b (x * d) = χ₂ d * b x)
    (a b' k d : ℤ) (hdet : a * d - b' * (L₁ * L₂ * k) = 1) (x : ℤ × ℤ) :
    latF L₁ b φ x = χ₁ d * χ₂ d * latF L₁ b φ (x.1 * a + x.2 * (L₁ * L₂ * k), x.1 * b' + x.2 * d) := by
  have hp : Function.Periodic b (L₂ : ℤ) := hb
  have hpz : ∀ y n : ℤ, b (y + n * L₂) = b y := fun y n => by simpa using hp.int_mul n y
  have hL : (L₁ : ℤ) ≠ 0 := by exact_mod_cast hL₁.ne'
  have hcop : IsCoprime d ((L₁ * L₂ : ℕ) : ℤ) := ⟨a, -(b' * k), by push_cast; linear_combination hdet⟩
  obtain ⟨hφ, hbχ⟩ := hχ d hcop
  have hcopa : IsCoprime (L₁ : ℤ) a := ⟨-(b' * L₂ * k), d, by linear_combination hdet⟩
  unfold latF
  by_cases h : (L₁ : ℤ) ∣ x.1
  · obtain ⟨m, hm⟩ := h
    have h2 : (L₁ : ℤ) ∣ x.1 * a + x.2 * (L₁ * L₂ * k) := ⟨m * a + x.2 * L₂ * k, by rw [hm]; ring⟩
    rw [if_pos ⟨m, hm⟩, if_pos h2]
    have e1 : x.1 / L₁ = m := by rw [hm, Int.mul_ediv_cancel_left _ hL]
    have e2 : (x.1 * a + x.2 * (L₁ * L₂ * k)) / L₁ = m * a + (x.2 * k) * L₂ := by
      rw [show x.1 * a + x.2 * (L₁ * L₂ * k) = L₁ * (m * a + (x.2 * k) * L₂) by rw [hm]; ring,
        Int.mul_ediv_cancel_left _ hL]
    have e3 : (((x.1 * b' + x.2 * d : ℤ)) : ZMod L₁) = (x.2 : ZMod L₁) * (d : ZMod L₁) := by
      rw [hm]; push_cast; rw [ZMod.natCast_self]; ring
    rw [e1, e2, e3, hpz]
    have e4 : b m = χ₂ d * b (m * a) := by
      rw [← hbχ, ← hpz m (m * b' * L₁ * k)]
      congr 1
      linear_combination (-m) * hdet
    rw [e4, hφ (x.2 : ZMod L₁)]; ring
  · have h2 : ¬ (L₁ : ℤ) ∣ x.1 * a + x.2 * (L₁ * L₂ * k) := by
      intro h2; apply h
      have h3 : (L₁ : ℤ) ∣ x.2 * (L₁ * L₂ * k) := ⟨x.2 * L₂ * k, by ring⟩
      exact hcopa.dvd_of_dvd_mul_right ((dvd_add_left h3).mp h2)
    rw [if_neg h, if_neg h2, mul_zero]

lemma latF_kills (L₁ L₂ : ℕ) (hL₁ : 0 < L₁) (b : ℤ → ℂ) (φ : ZMod L₁ → ℂ)
    (hb : ∀ x, b (x + L₂) = b x) (hhat : hat φ 0 = 0) (k d : ℤ) (hd : IsUnit (d : ZMod L₁)) :
    Kills L₁ (L₁ * L₂ * k, d) (latF L₁ b φ) := by
  haveI : NeZero L₁ := ⟨hL₁.ne'⟩
  have hp : Function.Periodic b (L₂ : ℤ) := hb
  have hpz : ∀ y n : ℤ, b (y + n * L₂) = b y := fun y n => by simpa using hp.int_mul n y
  have hL : (L₁ : ℤ) ≠ 0 := by exact_mod_cast hL₁.ne'
  rw [hat_zero] at hhat
  intro x
  by_cases h : (L₁ : ℤ) ∣ x.1
  · obtain ⟨m, hm⟩ := h
    calc ∑ r ∈ Finset.range L₁, latF L₁ b φ (x - (r : ℤ) • ((L₁ : ℤ) * L₂ * k, d))
        = ∑ r ∈ Finset.range L₁, b m * φ ((x.2 : ZMod L₁) + (r : ZMod L₁) * (-(d : ZMod L₁))) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          simp only [latF, Prod.fst_sub, Prod.snd_sub, Prod.smul_mk, smul_eq_mul]
          rw [if_pos ⟨m - r * L₂ * k, by rw [hm]; ring⟩,
            show x.1 - (r : ℤ) * (L₁ * L₂ * k) = L₁ * (m + (-(r * k)) * L₂) by rw [hm]; ring,
            Int.mul_ediv_cancel_left _ hL, hpz]
          congr 2; push_cast; ring
      _ = 0 := by rw [← Finset.mul_sum, sum_shift L₁ φ _ _ hd.neg, hhat, mul_zero]
  · refine Finset.sum_eq_zero fun r _ => ?_
    simp only [latF, Prod.fst_sub, Prod.snd_sub, Prod.smul_mk, smul_eq_mul]
    rw [if_neg]
    intro h2; apply h
    have h3 : (L₁ : ℤ) ∣ (r : ℤ) * (L₁ * L₂ * k) := ⟨r * L₂ * k, by ring⟩
    simpa using dvd_add h2 h3

end GlobalTheory.EisForm

namespace GlobalTheory.EisForm

theorem eis_latF_mf : ∀ (j L₁ L₂ : ℕ) (b χ₁ χ₂ : ℤ → ℂ) (φ : ZMod L₁ → ℂ), 1 ≤ j → 0 < L₁ → 0 < L₂ → hat φ 0 = 0 →
    (∀ x, b (x + L₂) = b x) →
    (∀ d : ℤ, IsCoprime d (L₁ * L₂ : ℕ) → (∀ y, φ y = χ₁ d * φ (y * d)) ∧ ∀ x, b (x * d) = χ₂ d * b x) →
    χ₁ (-1) * χ₂ (-1) = (-1) ^ j →
    ∃ c : ℂ, MF j (L₁ * L₂) (fun d => χ₁ d * χ₂ d) (eis j c (hat φ) b) ∧
      ∀ τ : ℍ, lat j 0 L₁ (0, 1) (latF L₁ b φ) τ = 2 * (-2 * π * Complex.I / L₁) ^ j / (j - 1).factorial * qs (eis j c (hat φ) b) τ := by
  intro j L₁ L₂ b χ₁ χ₂ φ hj hL₁ hL₂ hhat hb hχ hpar
  haveI : NeZero L₁ := ⟨hL₁.ne'⟩
  obtain ⟨Cb, hCb⟩ := bdd_of_periodic L₂ hL₂ b hb
  have hparity : ∀ x y : ℤ, b (-x) * φ (-(y : ZMod L₁)) = (-1) ^ j * (b x * φ y) := by
    intro x y
    obtain ⟨hφ, hbb⟩ := hχ (-1) ⟨-1, 0, by ring⟩
    have h1 := hφ (-(y : ZMod L₁))
    have h2 := hbb x
    rw [show -(y : ZMod L₁) * ((-1 : ℤ) : ZMod L₁) = y by push_cast; ring] at h1
    rw [mul_neg_one] at h2
    rw [h1, h2, ← hpar]; ring
  obtain ⟨c, hP, hq⟩ := GlobalTheory.T.regularizedEisensteinLatticeSum_qExpansion j L₁ b φ hj hL₁ ⟨Cb, hCb⟩ hhat hparity
  refine ⟨c, ⟨hP, ?_⟩, hq⟩
  set K : ℂ := 2 * (-2 * π * Complex.I / L₁) ^ j / (j - 1).factorial with hKdef
  have hK : K ≠ 0 := by
    have hL : (L₁ : ℂ) ≠ 0 := by exact_mod_cast hL₁.ne'
    simp [hKdef, Real.pi_ne_zero, Complex.I_ne_zero, hL, Nat.factorial_ne_zero]
  set Φ := latF L₁ b φ with hΦ
  have hq' : ∀ τ, qs (eis j c (hat φ) b) τ = K⁻¹ * lat j 0 L₁ (0, 1) Φ τ := fun τ => by
    rw [hq τ, ← mul_assoc, inv_mul_cancel₀ hK, one_mul]
  have hΦb : ∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C := by
    have hC0 : 0 ≤ Cb := le_trans (norm_nonneg _) (hCb 0)
    refine ⟨Cb * ∑ y, ‖φ y‖, fun x => ?_⟩
    simp only [hΦ, latF]
    split_ifs
    · rw [norm_mul]
      exact mul_le_mul (hCb _) (Finset.single_le_sum (f := fun y => ‖φ y‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ _)) (norm_nonneg _) hC0
    · simpa using mul_nonneg hC0 (Finset.sum_nonneg fun y _ => norm_nonneg (φ y))
  intro γ hc τ
  obtain ⟨k, hk⟩ := hc
  push_cast at hk
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * ((L₁ : ℤ) * L₂ * k) = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    rw [← hk]; exact this
  have hunit : IsUnit ((γ 1 1 : ℤ) : ZMod L₁) := by
    refine isUnit_iff_exists_inv.mpr ⟨((γ 0 0 : ℤ) : ZMod L₁), ?_⟩
    have := congrArg (fun z : ℤ => (z : ZMod L₁)) hdet
    push_cast at this
    rw [ZMod.natCast_self] at this
    linear_combination this
  set χd := χ₁ (γ 1 1) * χ₂ (γ 1 1) with hχd
  have htr : ∀ x : ℤ × ℤ, (fun y => χd * Φ y) (x.1 * γ 0 0 + x.2 * γ 1 0, x.1 * γ 0 1 + x.2 * γ 1 1) = Φ x := by
    intro x
    have := latF_trans L₁ L₂ hL₁ b χ₁ χ₂ φ hb hχ (γ 0 0) (γ 0 1) k (γ 1 1) hdet x
    rw [← hk] at this
    exact this.symm
  have hlin : ∀ w, lat j 0 L₁ w (fun y => χd * Φ y) τ = χd * lat j 0 L₁ w Φ τ := by
    intro w
    unfold lat
    rw [← tsum_mul_left]
    congr 1; ext x; ring
  have hw : ((0 : ℤ) * γ 0 0 + 1 * γ 1 0, (0 : ℤ) * γ 0 1 + 1 * γ 1 1) = ((L₁ : ℤ) * L₂ * k, γ 1 1) := by
    simp [hk]
  have hk1 : Kills L₁ ((L₁ : ℤ) * L₂ * k, γ 1 1) Φ := latF_kills L₁ L₂ hL₁ b φ hb hhat k (γ 1 1) hunit
  have hk0 : Kills L₁ (0, 1) Φ := by
    simpa using latF_kills L₁ L₂ hL₁ b φ hb hhat 0 1 (by simp)
  rw [hq', hq', GlobalTheory.T.regularizedEisensteinLatticeSum_slTwo_smul j L₁ (0, 1) Φ (fun y => χd * Φ y) γ τ htr, hlin]
  simp only [Prod.fst, Prod.snd]
  rw [hw, GlobalTheory.T.regularizedEisensteinLatticeSum_direction_indep j L₁ _ (0, 1) Φ τ hj hL₁ hΦb hk1 hk0]
  ring

end GlobalTheory.EisForm
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

open Matrix.SpecialLinearGroup
open scoped Pointwise

theorem norm_petersson_self_eq (k : ℕ) (f : ℍ → ℂ) (z : ℍ) :
    ‖UpperHalfPlane.petersson (k : ℤ) f f z‖ = ‖f z‖ ^ 2 * z.im ^ k := by
  simp only [UpperHalfPlane.petersson, norm_mul, Complex.norm_conj, zpow_natCast, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg z.im_pos.le]
  ring

theorem cusp_decay : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ) (γ : SL(2, ℤ)), 1 ≤ k → 0 < L → N ∣ L →
    CF k L (ch ε) a → ∃ C δ : ℝ, 0 < δ ∧ ∀ τ : ℍ, 1 / 2 ≤ τ.im →
      ‖qs a (γ • τ)‖ ^ 2 * (γ • τ).im ^ k ≤ C * Real.exp (-δ * τ.im) := by
  intro k L N ε a γ hk hL hN hcf
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_cuspForm_gamma1_of_isCuspFormCoeffSeq k L N ε a hk hL hN hcf
  obtain ⟨C₀, hC₀⟩ := hcf.2
  haveI : NeZero L := ⟨hL.ne'⟩
  have : ((ConjAct.toConjAct (γ : GL (Fin 2) ℝ)⁻¹) • (Gamma1 L : Subgroup (GL (Fin 2) ℝ))).IsArithmetic := by
    simpa [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl), map_inv, map_mapGL]
      using! Subgroup.IsArithmetic.conj (Gamma1 L : Subgroup (GL (Fin 2) ℝ)) (mapGL ℚ γ)⁻¹
  obtain ⟨δ, hδ, hd⟩ := (CuspFormClass.zero_at_infty (CuspForm.translate f γ)).petersson_exp_decay_left (k : ℤ) _
      (CuspForm.translate f γ)
  obtain ⟨D, hD, h⟩ := hd.exists_pos
  rw [Asymptotics.isBigOWith_iff, atImInfty, eventually_comap, eventually_atTop] at h
  obtain ⟨y, hy⟩ := h
  have hC₀0 : 0 ≤ C₀ := le_trans (by positivity) (hC₀ UpperHalfPlane.I)
  refine ⟨max D (C₀ * Real.exp (δ * |y|)), δ, hδ, fun τ hτ => ?_⟩
  have key : ‖qs a (γ • τ)‖ ^ 2 * (γ • τ).im ^ k =
      ‖UpperHalfPlane.petersson (k : ℤ) (CuspForm.translate f γ) (CuspForm.translate f γ) τ‖ := by
    rw [show ((CuspForm.translate f γ : CuspForm _ _) : ℍ → ℂ) = (⇑f) ∣[(k : ℤ)] γ from rfl,
      UpperHalfPlane.petersson_slash_SL, norm_petersson_self_eq, hf]
  rw [key]
  rcases le_total y τ.im with h1 | h1
  · have h2 := hy _ h1 τ rfl
    rw [Real.norm_of_nonneg (Real.exp_pos _).le] at h2
    exact h2.trans (by gcongr; exact le_max_left _ _)
  · rw [← key]
    have h3 : 1 ≤ Real.exp (δ * |y|) * Real.exp (-δ * τ.im) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith [le_abs_self y]
    calc ‖qs a (γ • τ)‖ ^ 2 * (γ • τ).im ^ k ≤ C₀ := hC₀ _
      _ ≤ C₀ * (Real.exp (δ * |y|) * Real.exp (-δ * τ.im)) := le_mul_of_one_le_right hC₀0 h3
      _ = C₀ * Real.exp (δ * |y|) * Real.exp (-δ * τ.im) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

end GlobalTheory.EisM
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

theorem _root_.GlobalTheory.T.reduces_of_det_evM_eq_zero' : ∀ (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ) (τ₀ : ℍ), IsReps Γ s → (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (evM s w F τ₀).det = 0 → Reduces Γ w F := by
  first | exact @GlobalTheory.OddFrame.reduces_of_det_evM_eq_zero | exact GlobalTheory.OddFrame.reduces_of_det_evM_eq_zero | (intros; apply GlobalTheory.OddFrame.reduces_of_det_evM_eq_zero <;> assumption)
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_central_circle_distinct_graded_eigen : ∀ (p q : ℕ) (T : GrpData p q) (σ : URep T) (M : GKMod p q) (j : M.V →ₗ[ℂ] σ.H), (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0) → ∀ (N : ℕ → Submodule ℂ M.V) (c : ℚ), (∀ m : ℕ, ∀ x ∈ N m, ∑ i : Fin p, M.act (Eab (Sum.inl i) (Sum.inl i)) x = ((c : ℂ) + m) • x) → ∃ k ∈ T.Kset, ∃ lam : ℕ → ℂ, Function.Injective lam ∧ ∀ m, ∀ x ∈ N m, σ.π k (j x) = lam m • j x := by
  first | exact @GlobalTheory.GradedCentralCircle.exists_central_eigen | exact GlobalTheory.GradedCentralCircle.exists_central_eigen | (intros; apply GlobalTheory.GradedCentralCircle.exists_central_eigen <;> assumption)
end
