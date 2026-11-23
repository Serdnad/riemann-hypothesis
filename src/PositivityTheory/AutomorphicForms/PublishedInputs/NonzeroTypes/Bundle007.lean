module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_V0fin

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def lift {n : ℕ} (g : ↥(KO k (Fin n))) : GL (Fin n) 𝒪[k] := Classical.choose g.2

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
lemma lift_spec {n : ℕ} (g : ↥(KO k (Fin n))) :
    Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) (lift g) = (g : GL (Fin n) k) :=
  Classical.choose_spec g.2

def red {n : ℕ} (r : ℕ) (g : ↥(KO k (Fin n))) :
    Matrix (Fin n) (Fin n) (𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k] ^ r) :=
  ((lift g : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]).map (Ideal.Quotient.mk _)

instance finQuot (r : ℕ) : Finite (𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k] ^ r) :=
  IsLocalRing.finite_quotient_iff.mpr ⟨r, le_rfl⟩

instance finRed (n r : ℕ) : Finite (Matrix (Fin n) (Fin n) (𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k] ^ r)) :=
  inferInstanceAs (Finite (Fin n → Fin n → (𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k] ^ r)))

lemma mem_KC_of_red_eq {n : ℕ} (r : ℕ) (g g' : ↥(KO k (Fin n))) (h : red r g = red r g') :
    ((g⁻¹ * g' : ↥(KO k (Fin n))) : GL (Fin n) k) ∈ KC k n r := by
  refine ⟨(g⁻¹ * g').2, fun i j => ?_⟩
  have hu : ((g⁻¹ * g' : ↥(KO k (Fin n))) : GL (Fin n) k) =
      Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) ((lift g)⁻¹ * lift g') := by
    rw [map_mul, map_inv, lift_spec, lift_spec]; rfl
  have hd : ∀ l m, ((lift g' : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) l m -
      ((lift g : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) l m ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ r := by
    intro l m
    have := congrFun (congrFun h l) m
    simp only [red, Matrix.map_apply] at this
    exact Ideal.Quotient.eq.mp this.symm
  have hM : (((lift g)⁻¹ * lift g' : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) =
      1 + ((lift g)⁻¹ : GL (Fin n) 𝒪[k]).val *
        ((lift g' : GL (Fin n) 𝒪[k]).val - (lift g : GL (Fin n) 𝒪[k]).val) := by
    rw [Units.val_mul, Matrix.mul_sub, Units.inv_mul]; abel
  refine ⟨(((lift g)⁻¹ * lift g' : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) i j -
      if i = j then 1 else 0, ?_, ?_⟩
  · rw [hM, Matrix.add_apply, Matrix.one_apply, add_sub_cancel_left, Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hd l j)
  · rw [hu]
    change _ = ((((lift g)⁻¹ * lift g' : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]).map
      (algebraMap 𝒪[k] k)) i j - _
    simp only [Matrix.map_apply, map_sub, apply_ite (algebraMap 𝒪[k] k), map_one, map_zero]

end P_V0fin

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_V0fin {n : ℕ} (G : Grp k n) : FixedSubspaceFiniteProp G := by
  intro _ _
  let φ := P_V0fin.red (k := k) (n := n) G.lev
  have hle : G.V0sp ≤ LinearMap.range (LinearMap.funLeft ℂ ℂ φ) := by
    intro f hf
    refine ⟨fun q => if hq : ∃ g, φ g = q then f (Classical.choose hq) else 0, ?_⟩
    funext g
    have hq : ∃ g', φ g' = φ g := ⟨g, rfl⟩
    simp only [LinearMap.funLeft_apply, dif_pos hq]
    have hk := P_V0fin.mem_KC_of_red_eq G.lev (Classical.choose hq) g (Classical.choose_spec hq)
    have := hf.2 (Classical.choose hq) ((Classical.choose hq)⁻¹ * g) hk
    rw [mul_inv_cancel_left] at this
    exact this.symm
  have : FiniteDimensional ℂ (LinearMap.range (LinearMap.funLeft ℂ ℂ φ)) :=
    LinearMap.finiteDimensional_range _
  exact Submodule.finiteDimensional_of_le hle

end UpperTheory.TNZ.Grp
end
end

section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

namespace Grp

namespace P_V0stable

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem alg_inj : Function.Injective (algebraMap 𝒪[k] k) := Subtype.val_injective

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem coe_map_apply {n : ℕ} (A : GL (Fin n) 𝒪[k]) (i j : Fin n) :
    ((Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k) A : GL (Fin n) k) :
      Matrix (Fin n) (Fin n) k) i j = algebraMap 𝒪[k] k ((A : Matrix (Fin n) (Fin n) 𝒪[k]) i j) := rfl

theorem conj_mem_KC {n r : ℕ} (g u : GL (Fin n) k) (hg : g ∈ KO k (Fin n)) (hu : u ∈ KC k n r) :
    g⁻¹ * u * g ∈ KC k n r := by
  obtain ⟨A, rfl⟩ := hg
  obtain ⟨⟨B, rfl⟩, hB⟩ := hu
  have hB' : ∀ i j, (B : Matrix (Fin n) (Fin n) 𝒪[k]) i j - (1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j ∈ 𝓂[k] ^ r := by
    intro i j
    obtain ⟨y, hy, hyx⟩ := hB i j
    have hyeq : y = (B : Matrix (Fin n) (Fin n) 𝒪[k]) i j - (1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j := by
      apply alg_inj
      rw [hyx, coe_map_apply, map_sub, Matrix.one_apply]
      split_ifs <;> simp
    exact hyeq ▸ hy
  have key : ∀ i j, ((A⁻¹ * B * A : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) i j
      - (1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j ∈ 𝓂[k] ^ r := by
    intro i j
    have h : ((A⁻¹ * B * A : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) - 1
        = ((A⁻¹ : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k])
          * ((B : Matrix (Fin n) (Fin n) 𝒪[k]) - 1) * (A : Matrix (Fin n) (Fin n) 𝒪[k]) := by
      rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.inv_mul]
    rw [← Matrix.sub_apply, h, Matrix.mul_apply]
    refine Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ ?_
    rw [Matrix.mul_apply]
    refine Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _ ?_
    rw [Matrix.sub_apply]
    exact hB' m l
  rw [← map_inv, ← map_mul, ← map_mul]
  refine ⟨⟨_, rfl⟩, fun i j => ⟨_, key i j, ?_⟩⟩
  rw [coe_map_apply, map_sub, Matrix.one_apply]
  split_ifs <;> simp

end P_V0stable

theorem step_V0stable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (G : Grp k n) : FixedSubspaceStableProp G := by
  intro _ _ g φ hφ
  obtain ⟨h1, h2⟩ : (∀ p : ↥(KO k (Fin n)), (p : GL (Fin n) k) ∈ G.PO → ∀ x, φ (p * x) = G.lam p * φ x) ∧
      ∀ x (u : ↥(KO k (Fin n))), (u : GL (Fin n) k) ∈ KC k n G.lev → φ (x * u) = φ x := hφ
  show (∀ p : ↥(KO k (Fin n)), (p : GL (Fin n) k) ∈ G.PO →
      ∀ x, Rreg (k := k) (n := n) g φ (p * x) = G.lam p * Rreg (k := k) (n := n) g φ x) ∧
    ∀ x (u : ↥(KO k (Fin n))), (u : GL (Fin n) k) ∈ KC k n G.lev →
      Rreg (k := k) (n := n) g φ (x * u) = Rreg (k := k) (n := n) g φ x
  refine ⟨fun p hp x => ?_, fun x u hu => ?_⟩
  · show φ (p * x * g) = G.lam p * φ (x * g)
    rw [mul_assoc]
    exact h1 p hp (x * g)
  · show φ (x * u * g) = φ (x * g)
    have hc : ((g⁻¹ * u * g : ↥(KO k (Fin n))) : GL (Fin n) k) ∈ KC k n G.lev := by
      change ((g : GL (Fin n) k))⁻¹ * (u : GL (Fin n) k) * (g : GL (Fin n) k) ∈ KC k n G.lev
      exact P_V0stable.conj_mem_KC _ _ g.2 hu
    have e : x * u * g = x * g * (g⁻¹ * u * g) := by group
    rw [e]
    exact h2 _ _ hc

end Grp

end UpperTheory.TNZ
end
end

section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

namespace Grp

namespace CharacterConductor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def CS (ψ : 𝒪[k]ˣ →* ℂˣ) : Set ℕ :=
  {c | ∀ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c → ψ u = 1}

theorem cond_eq (ψ : 𝒪[k]ˣ →* ℂˣ) : cond ψ = sInf (CS ψ) := rfl

theorem CS_mono (ψ : 𝒪[k]ˣ →* ℂˣ) {c d : ℕ} (hc : c ∈ CS ψ) (hcd : c ≤ d) : d ∈ CS ψ := by
  intro u hu
  exact hc u (Ideal.pow_le_pow_right hcd hu)

theorem CS_inv (ψ : 𝒪[k]ˣ →* ℂˣ) : CS ψ⁻¹ = CS ψ := by
  ext c
  simp only [CS, Set.mem_setOf_eq, MonoidHom.inv_apply, inv_eq_one]

theorem cond_one : cond (1 : 𝒪[k]ˣ →* ℂˣ) = 0 := by
  rw [cond_eq]
  apply Nat.sInf_eq_zero.mpr
  left
  intro u _
  rfl

theorem res_div_swap {s : ℕ} (μ : Fin s → kˣ →* ℂˣ) (a b : Fin s) :
    res (μ b / μ a) = (res (μ a / μ b))⁻¹ := by
  ext u
  simp [res, MonoidHom.div_apply, MonoidHom.inv_apply, inv_div]

theorem res_div_mul {s : ℕ} (μ : Fin s → kˣ →* ℂˣ) (a b c : Fin s) (u : 𝒪[k]ˣ) :
    res (μ a / μ c) u = res (μ a / μ b) u * res (μ b / μ c) u := by
  simp [res, MonoidHom.div_apply, div_mul_div_cancel₀]

theorem cc_self {s : ℕ} (μ : Fin s → kˣ →* ℂˣ) (a : Fin s) : cc μ a a = 0 := by
  unfold cc
  rw [div_self']
  exact cond_one

theorem cc_comm {s : ℕ} (μ : Fin s → kˣ →* ℂˣ) (a b : Fin s) : cc μ a b = cc μ b a := by
  unfold cc
  rw [res_div_swap μ a b, cond_eq, cond_eq, CS_inv]

theorem cc_ultra {s : ℕ} (μ : Fin s → kˣ →* ℂˣ) (a b c : Fin s)
    (hab : (CS (res (μ a / μ b))).Nonempty) (hbc : (CS (res (μ b / μ c))).Nonempty) :
    cc μ a c ≤ max (cc μ a b) (cc μ b c) := by
  have h1 : cc μ a b ∈ CS (res (μ a / μ b)) := Nat.sInf_mem hab
  have h2 : cc μ b c ∈ CS (res (μ b / μ c)) := Nat.sInf_mem hbc
  have h3 : max (cc μ a b) (cc μ b c) ∈ CS (res (μ a / μ c)) := by
    intro u hu
    rw [res_div_mul μ a b c u,
      CS_mono _ h1 (le_max_left _ _) u hu, CS_mono _ h2 (le_max_right _ _) u hu, one_mul]
  exact Nat.sInf_le h3

theorem step_ccBasic_of_cond :
    ∀ (s : ℕ) (μ : Fin s → kˣ →* ℂˣ),
      (∀ a b : Fin s, ∃ c : ℕ, ∀ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c →
        res (μ a / μ b) u = 1) →
      ∀ a b c : Fin s, cc μ a a = 0 ∧ cc μ a b = cc μ b a ∧ cc μ a c ≤ max (cc μ a b) (cc μ b c) := by
  intro s μ hμ a b c
  refine ⟨cc_self μ a, cc_comm μ a b, cc_ultra μ a b c ?_ ?_⟩
  · obtain ⟨c0, h⟩ := hμ a b
    exact ⟨c0, h⟩
  · obtain ⟨c0, h⟩ := hμ b c
    exact ⟨c0, h⟩

end CharacterConductor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_ccBasic : CompactConductorBasicProp (k := k) :=
  CharacterConductor.step_ccBasic_of_cond

end Grp

end UpperTheory.TNZ
end
end

section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Grp

namespace CharacterConductorBound

def Lv (ψ : 𝒪[k]ˣ →* ℂˣ) : Set ℕ :=
  {c | ∀ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c → ψ u = 1}

theorem exists_level (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ) : (Lv (res μ)).Nonempty := by
  have hopen : IsOpen (μ.ker : Set kˣ) := hμ
  obtain ⟨V, hVo, hV⟩ := (Units.isEmbedding_val₀ (G₀ := k)).isInducing.isOpen_iff.mp hopen
  have h1 : (1 : k) ∈ V := by
    have : (1 : kˣ) ∈ (Units.val ⁻¹' V) := by rw [hV]; exact μ.ker.one_mem
    simpa using this
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_iff' (R := k)).mp (hVo.mem_nhds h1)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have hlt : valuation k (algebraMap 𝒪[k] k ϖ) < 1 :=
    (Valuation.integer.integers (valuation k)).valuation_irreducible_lt_one hϖ
  have : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨c, hc⟩ := exists_pow_lt₀ hlt γ
  refine ⟨c, fun u hu => ?_⟩
  have hm : IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hu
  obtain ⟨t, ht⟩ := hu
  have e : ((u : 𝒪[k]) : k) - 1 = (algebraMap 𝒪[k] k ϖ) ^ c * algebraMap 𝒪[k] k t := by
    have := congrArg (algebraMap 𝒪[k] k) ht
    simp only [map_sub, map_mul, map_pow, map_one] at this
    exact this
  have ht1 : valuation k (algebraMap 𝒪[k] k t) ≤ 1 := t.2
  have hv : valuation k (((u : 𝒪[k]) : k) - 1) < γ := by
    rw [e, map_mul, map_pow]
    calc valuation k (algebraMap 𝒪[k] k ϖ) ^ c * valuation k (algebraMap 𝒪[k] k t)
        ≤ valuation k (algebraMap 𝒪[k] k ϖ) ^ c * 1 := by gcongr
      _ < γ := by rw [mul_one]; exact hc
  have hmem : unitIncl k u ∈ (Units.val ⁻¹' V : Set kˣ) := hγ hv
  rw [hV] at hmem
  exact (MonoidHom.mem_ker).mp hmem

theorem max_mem (μ ν : kˣ →* ℂˣ) {c c' : ℕ} (hc : c ∈ Lv (res μ)) (hc' : c' ∈ Lv (res ν)) :
    max c c' ∈ Lv (res (μ / ν)) := by
  intro u hu
  have h1 := hc u (Ideal.pow_le_pow_right (le_max_left c c') hu)
  have h2 := hc' u (Ideal.pow_le_pow_right (le_max_right c c') hu)
  simp only [MonoidHom.comp_apply, MonoidHom.div_apply] at h1 h2 ⊢
  rw [h1, h2, div_one]

theorem cond_mem (ψ : 𝒪[k]ˣ →* ℂˣ) (h : (Lv ψ).Nonempty) : cond ψ ∈ Lv ψ := Nat.sInf_mem h

variable {n : ℕ} (G : Grp k n)

theorem lv_a (a : Fin G.s) : cond (res (G.μ a)) ∈ Lv (res (G.μ a)) :=
  cond_mem _ (exists_level _ (G.smooth a))

theorem lv_ab (a b : Fin G.s) :
    max (cond (res (G.μ a))) (cond (res (G.μ b))) ∈ Lv (res (G.μ a / G.μ b)) :=
  max_mem _ _ (lv_a G a) (lv_a G b)

theorem cc_le (a b : Fin G.s) : cc G.μ a b ≤ max (cond (res (G.μ a))) (cond (res (G.μ b))) :=
  Nat.sInf_le (lv_ab G a b)

theorem cc_mem (a b : Fin G.s) : cc G.μ a b ∈ Lv (res (G.μ a / G.μ b)) :=
  Nat.sInf_mem ⟨_, lv_ab G a b⟩

theorem cond_le_sum (a : Fin G.s) : cond (res (G.μ a)) ≤ ∑ b, cond (res (G.μ b)) :=
  Finset.single_le_sum (f := fun b => cond (res (G.μ b))) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

theorem one_le_cc (a b : Fin G.s) (hab : a ≠ b) : 1 ≤ cc G.μ a b := by
  by_contra h0
  have h0' : cc G.μ a b = 0 := by omega
  have hm := cc_mem G a b
  rw [h0'] at hm
  apply G.dist a b hab
  ext u
  have := hm u (by simp)
  simp only [MonoidHom.comp_apply, MonoidHom.div_apply, div_eq_one] at this
  simp only [MonoidHom.comp_apply, this]

end CharacterConductorBound

theorem step_ccBound {n : ℕ} (G : Grp k n) : CompactConductorBoundProp G := by
  have hlev : G.lev = 1 + ∑ b, cond (res (G.μ b)) := rfl
  refine ⟨fun a b hab => CharacterConductorBound.one_le_cc G a b hab, fun a b => ?_, fun a => ?_,
    fun a b u hu => CharacterConductorBound.cc_mem G a b u hu⟩
  · have h1 := CharacterConductorBound.cc_le G a b
    have h2 := CharacterConductorBound.cond_le_sum G a
    have h3 := CharacterConductorBound.cond_le_sum G b
    rw [hlev]
    omega
  · have h2 := CharacterConductorBound.cond_le_sum G a
    rw [hlev]
    omega

end Grp

end UpperTheory.TNZ
end
end

section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.LeviEigenvectorMembership

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} (G : Grp k n)

theorem mem_left_iff (hmul : ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, g * h ∈ G.JSet) (hinv : ∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet)
    {g : GL (Fin n) k} (hg : g ∈ G.JSet) (h : GL (Fin n) k) : g * h ∈ G.JSet ↔ h ∈ G.JSet := by
  refine ⟨fun hgh => ?_, fun hh => hmul g hg h hh⟩
  have := hmul _ (hinv g hg) _ hgh
  simpa [← mul_assoc] using this

theorem mem_right_iff (hmul : ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, g * h ∈ G.JSet) (hinv : ∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet)
    {h : GL (Fin n) k} (hh : h ∈ G.JSet) (g : GL (Fin n) k) : g * h ∈ G.JSet ↔ g ∈ G.JSet := by
  refine ⟨fun hgh => ?_, fun hg => hmul g hg h hh⟩
  have := hmul _ hgh _ (hinv h hh)
  simpa [mul_assoc] using this

theorem levi_eigenvector_of_conditions (hcb : CompactConductorBasicProp (k := k)) (hccB : CompactConductorBoundProp G) (hΔU : ModulusOnUnitsProp G) (hΔM : ModulusMultiplicativeProp G)
    (hJone : JacquetOneProp G) (hJmul : JacquetMultiplicativeProp G) (hJinv : JacquetInverseProp G) (hlM : LambdaMultiplicativeProp G)
    (hlB : LambdaBasicProp G) (hKC : CompactOpenKernelProp G) :
    G.v0 ∈ G.V0sp ∧ G.v0 ≠ 0 ∧ ∀ j : ↥(KO k (Fin n)), (j : GL (Fin n) k) ∈ G.JSet →
      Rreg (k := k) (n := n) j G.v0 = G.lam j • G.v0 := by
  have hmul := hJmul hcb hccB
  have hinv := hJinv hcb hccB
  have hlam := hlM hcb hΔU hΔM hccB
  obtain ⟨hl1, -, hlK⟩ := hlB hccB
  have hKJ : KC k n G.lev ⊆ G.JSet := (hKC hccB G.lev).2.2.2.2 le_rfl

  have hright : ∀ (g j : ↥(KO k (Fin n))), (j : GL (Fin n) k) ∈ G.JSet →
      G.v0 (g * j) = G.lam j * G.v0 g := by
    intro g j hj
    simp only [Grp.v0, Subgroup.coe_mul, mem_right_iff G hmul hinv hj]
    split_ifs with hg
    · rw [hlam _ hg _ hj, mul_comm]
    · simp
  refine ⟨⟨fun p hp g => ?_, fun g u hu => ?_⟩, ?_, fun j hj => ?_⟩
  · have hpJ : (p : GL (Fin n) k) ∈ G.JSet := hJone.2 hp
    simp only [Grp.v0, Subgroup.coe_mul, mem_left_iff G hmul hinv hpJ]
    split_ifs with hg
    · rw [hlam _ hpJ _ hg]
    · simp
  · rw [hright g u (hKJ hu), hlK _ hu, one_mul]
  · intro h0
    have := congrFun h0 1
    simp only [Grp.v0, OneMemClass.coe_one, if_pos hJone.1, hl1, Pi.zero_apply] at this
    exact one_ne_zero this
  · funext g
    rw [Pi.smul_apply, smul_eq_mul, ← hright g j hj]
    rfl

end UpperTheory.TNZ.Grp.LeviEigenvectorMembership

namespace UpperTheory.TNZ.Grp

theorem leviEigenvector_holds {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (G : Grp k n) : NonzeroLeviEigenvectorExists G :=
  fun hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC =>
    LeviEigenvectorMembership.levi_eigenvector_of_conditions G hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC

end UpperTheory.TNZ.Grp
end
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TNZ

theorem step_sphOfUnr : SphericalOfUnramifiedProp := by
  intro E Ω _ _ _ _ _ A w h a ha ε rc H d v hv hd
  obtain ⟨⟨n, c⟩, rfl⟩ := H.bij.2 v
  have hn : n = d := by rw [← hd, H.dim]
  subst hn
  exact ⟨c.rep.V, inferInstance, inferInstance, c.rep.ρ, c.rep.smooth, c.rep.irr, (H.sph ⟨n, c⟩).2 hv,
    congrArg rc (IrrGL.of_rep ⟨n, c⟩)⟩

end UpperTheory.TNZ
end
end
