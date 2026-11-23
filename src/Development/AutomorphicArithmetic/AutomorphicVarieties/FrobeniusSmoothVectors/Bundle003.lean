module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContinuousCoboundaries2
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle045
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.Sylow

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_count :
    ∀ {K G W V T : Type} [Field K] [Group G] [TopologicalSpace G] [AddCommGroup W] [Module K W] [Module.Finite K W] [AddCommGroup T] [Module K T] [Module.Finite K T] {Gv : V → Type} [∀ v, Group (Gv v)] (loc : ∀ v, Gv v →* G) (ρ : Representation K G W) (b : V → Submodule K W) (φ : T →ₗ[K] (G → W)), (∀ v Y, (∀ s, ρ (loc v s) Y - Y ∈ b v) → Y ∈ b v) → (∀ x ∈ Z1C loc ρ b, ∃ D X, ∀ s, φ D s = x.1 s + (ρ s X - X)) → Module.finrank K (H1C loc ρ b) ≤ Module.finrank K T ∧ ∀ (X₀ : W) (D₀ : T), X₀ ≠ 0 → (∀ s, φ D₀ s = ρ s X₀ - X₀) → Module.finrank K (H1C loc ρ b) + 1 ≤ Module.finrank K T + Module.finrank K (coneH0 ρ b) := by
  intro K G W V T _ _ _ _ _ _ _ _ _ Gv _ loc ρ b φ hA hB
  let cob : W →ₗ[K] (G → W) := LinearMap.pi (fun s => ρ s - LinearMap.id)
  have hcob : ∀ X s, cob X s = ρ s X - X := fun X s => rfl
  let C := LinearMap.range cob
  let f : T →ₗ[K] (G → W) ⧸ C := C.mkQ ∘ₗ φ
  let Ψ : Z1C loc ρ b →ₗ[K] (G → W) ⧸ C :=
    C.mkQ ∘ₗ (LinearMap.fst K (G → W) (V → W)) ∘ₗ (Z1C loc ρ b).subtype
  have hle : Submodule.comap (Z1C loc ρ b).subtype (continuousCoboundaries1 ρ b) ≤ LinearMap.ker Ψ := by
    rintro ⟨x, hx⟩ hxB
    rw [Submodule.mem_comap] at hxB
    obtain ⟨X, hX, -⟩ := hxB
    rw [LinearMap.mem_ker]
    show C.mkQ x.1 = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨X, funext fun s => ((hX s).trans (hcob X s).symm).symm⟩
  have hker : LinearMap.ker Ψ ≤ Submodule.comap (Z1C loc ρ b).subtype (continuousCoboundaries1 ρ b) := by
    rintro ⟨x, hx⟩ hk
    rw [LinearMap.mem_ker] at hk
    change C.mkQ x.1 = 0 at hk
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hk
    obtain ⟨X, hX⟩ := hk
    obtain ⟨-, -, hloc⟩ := hx
    rw [Submodule.mem_comap]
    refine ⟨X, fun s => (congrFun hX s).symm, fun v => ?_⟩
    have hmem : X - x.2 v ∈ b v := by
      refine hA v _ (fun s => ?_)
      have h1 := hloc v s
      convert h1 using 1
      rw [← hX, hcob, map_sub]
      abel
    have h2 := (b v).neg_mem hmem
    rwa [neg_sub] at h2
  let L := (Submodule.comap (Z1C loc ρ b).subtype (continuousCoboundaries1 ρ b)).liftQ Ψ hle
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hker
  have hrange : ∀ y, L y ∈ LinearMap.range f := by
    intro y
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨D, X, hD⟩ := hB z.1 z.2
    refine ⟨D, ?_⟩
    show C.mkQ (φ D) = C.mkQ z.1.1
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    refine ⟨X, funext fun s => ?_⟩
    show cob X s = φ D s - z.1.1 s
    rw [hcob, hD]
    abel
  let L' : H1C loc ρ b →ₗ[K] LinearMap.range f := L.codRestrict _ hrange
  have hinj' : Function.Injective L' := fun a c h => hinj (congrArg Subtype.val h)
  have h1 : Module.finrank K (H1C loc ρ b) ≤ Module.finrank K (LinearMap.range f) :=
    LinearMap.finrank_le_finrank_of_injective hinj'
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  have h3 := LinearMap.finrank_range_le f
  refine ⟨h1.trans h3, ?_⟩
  intro X₀ D₀ hX₀ hD₀
  by_cases hinv : ∀ s, ρ s X₀ = X₀
  · have hH0 : X₀ ∈ coneH0 ρ b := by
      show (∀ g, ρ g X₀ = X₀) ∧ ∀ v, X₀ ∈ b v
      exact ⟨hinv, fun v => hA v X₀ (fun s => by rw [hinv, sub_self]; exact (b v).zero_mem)⟩
    have h4 : Module.finrank K (coneH0 ρ b) ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero]
      intro h
      rw [h] at hH0
      exact hX₀ ((Submodule.mem_bot K).1 hH0)
    omega
  · push_neg at hinv
    obtain ⟨s, hs⟩ := hinv
    have hD0 : D₀ ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker]
      show C.mkQ (φ D₀) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨X₀, funext fun t => (hcob X₀ t).trans (hD₀ t).symm⟩
    have hne : D₀ ≠ 0 := by
      rintro rfl
      apply hs
      have h5 := hD₀ s
      rw [map_zero, Pi.zero_apply] at h5
      exact (sub_eq_zero.1 h5.symm)
    have h4 : Module.finrank K (LinearMap.ker f) ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero]
      intro h
      rw [h] at hD0
      exact hne ((Submodule.mem_bot K).1 hD0)
    omega
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.smooth_vector_fixed_by_open_subgroup :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ χ : F.Γ →* kˣ, χ F.c = -1 → (∀ v, ∃ s, χ (F.loc v s) ≠ 1) → Nontrivial (H1C F.loc (chRep χ) fun _ => ⊥) → ∃ x : F.Γ → k, IsLocallyConstant x ∧ (∀ g h, x (g * h) = x g + χ g * x h) ∧ x F.c = 0 ∧ (∀ v, ∃ Y : k, ∀ s, x (F.loc v s) = χ (F.loc v s) * Y - Y) ∧ ∃ g : F.G0, x g ≠ 0 := by
  intro l _ k _ _ F C₀ hok χ hc hloc hnt
  obtain ⟨q, hq⟩ := exists_ne (0 : H1C F.loc (chRep χ) fun _ => ⊥)
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [Ne, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hq
  obtain ⟨⟨x, y⟩, hz⟩ := z
  obtain ⟨hlc, hcoc, hlocz⟩ := hz
  simp only [chRep_apply] at hcoc
  simp only [chRep_apply, Submodule.mem_bot] at hlocz
  have h2 : (2 : k) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : k) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff k l] at h'
    exact hok.l_odd ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 h')
  have hx1 : x 1 = 0 := by
    have e := hcoc 1 1
    rw [mul_one, map_one, Units.val_one, one_mul] at e
    linear_combination -e
  have hχ : ∀ s, (χ s : k) * x F.c = x (s * F.c) - x s := by
    intro s
    rw [hcoc]
    ring
  set X : k := -(x F.c) / 2 with hX
  set x' : F.Γ → k := fun s => x s - ((χ s : k) * X - X) with hx'
  have hform : x' = fun s => (x s + x (s * F.c) - x F.c) / 2 := by
    funext s
    simp only [hx', hX]
    rw [show x (s * F.c) = (χ s : k) * x F.c + x s by rw [hχ]; ring]
    field_simp
    ring
  have hcoc' : ∀ g h, x' (g * h) = x' g + (χ g : k) * x' h := by
    intro g h
    simp only [hx']
    rw [hcoc, map_mul, Units.val_mul]
    ring
  have hc' : x' F.c = 0 := by
    rw [hform]
    simp only
    rw [hok.c_sq, hx1]
    ring
  have hloc' : ∀ v s, x' (F.loc v s) = (χ (F.loc v s) : k) * (y v - X) - (y v - X) := by
    intro v s
    simp only [hx']
    have e := hlocz v s
    linear_combination e
  refine ⟨x', ?_, hcoc', hc', fun v => ⟨y v - X, hloc' v⟩, ?_⟩
  · rw [hform]
    exact IsLocallyConstant.comp₂ hlc (hlc.comp_continuous (continuous_mul_const F.c))
      (fun a b => (a + b - x F.c) / 2)
  · by_contra hall
    push_neg at hall
    have hzero : ∀ γ, x' γ = 0 := by
      intro γ
      rcases Int.units_eq_one_or (F.del γ) with hd | hd
      · exact hall ⟨γ, hd⟩
      · have hm : γ * F.c ∈ F.del.ker := by
          rw [MonoidHom.mem_ker, map_mul, hd, hok.del_c]
          rfl
        have e : γ = (γ * F.c) * F.c := by
          rw [mul_assoc, hok.c_sq, mul_one]
        rw [e, hcoc', hc', mul_zero, add_zero]
        exact hall ⟨_, hm⟩
    have hy : ∀ v, y v - X = 0 := by
      intro v
      obtain ⟨s, hs⟩ := hloc v
      have e := hloc' v s
      rw [hzero] at e
      have e' : ((χ (F.loc v s) : k) - 1) * (y v - X) = 0 := by
        linear_combination -e
      rcases mul_eq_zero.1 e' with h | h
      · exact absurd (by
          have : (χ (F.loc v s) : k) = 1 := sub_eq_zero.1 h
          exact Units.val_eq_one.1 this) hs
      · exact h
    apply hq
    refine ⟨X, fun s => ?_, fun v => ?_⟩
    · have e := hzero s
      simp only [hx'] at e
      show x s = (chRep χ s) X - X
      rw [chRep_apply]
      linear_combination e
    · show y v - X ∈ (⊥ : Submodule k k)
      rw [Submodule.mem_bot]
      exact hy v
end

section

noncomputable section

namespace UpperTheory.V.Fr.Frame

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] (F : Frame l k) (M : Type) [AddCommGroup M] [Module k M]

def strY : Submodule k (F.G0 → M) where
  carrier := {y | IsLocallyConstant y ∧ (∀ g h : F.G0, y (g * h) = (F.Ψ h : k) • y g + y h) ∧
    y F.g0 = y (F.star F.g0) ∧
    (∀ v, ∃ α : M, ∀ s, y (F.loc0 v s) = ((F.Ψ (F.loc v s) : k) - 1) • α) ∧
    ∀ v, ∃ β : M, ∀ s, y (F.star (F.loc0 v s)) = (1 - (((F.Ψ (F.loc v s))⁻¹ : kˣ) : k)) • β}
  add_mem' := by
    rintro x y ⟨a1, a2, a3, a4, a5⟩ ⟨b1, b2, b3, b4, b5⟩
    refine ⟨a1.add b1, fun g h => ?_, by simp [a3, b3], fun v => ?_, fun v => ?_⟩
    · simp only [Pi.add_apply, a2, b2, smul_add]; abel
    · obtain ⟨α, h⟩ := a4 v
      obtain ⟨α', h'⟩ := b4 v
      exact ⟨α + α', fun s => by rw [Pi.add_apply, h, h', smul_add]⟩
    · obtain ⟨α, h⟩ := a5 v
      obtain ⟨α', h'⟩ := b5 v
      exact ⟨α + α', fun s => by rw [Pi.add_apply, h, h', smul_add]⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, by simp, rfl, fun _ => ⟨0, by simp⟩, fun _ => ⟨0, by simp⟩⟩
  smul_mem' := by
    rintro c x ⟨a1, a2, a3, a4, a5⟩
    refine ⟨a1.comp (c • ·), fun g h => ?_, by simp [a3], fun v => ?_, fun v => ?_⟩
    · simp only [Pi.smul_apply, a2, smul_add, smul_comm c]
    · obtain ⟨α, h⟩ := a4 v
      exact ⟨c • α, fun s => by rw [Pi.smul_apply, h, smul_comm]⟩
    · obtain ⟨α, h⟩ := a5 v
      exact ⟨c • α, fun s => by rw [Pi.smul_apply, h, smul_comm]⟩

def strS : Submodule k (F.G0 → M) where
  carrier := {a | IsLocallyConstant a ∧
    (∀ g h : F.G0, a (g * h) = (F.Ψ h : k) • a g + (((F.Ψ g)⁻¹ : kˣ) : k) • a h) ∧ (∀ g, a (F.star g) = a g) ∧
    ∀ v, ∃ γ : M, ∀ s, a (F.loc0 v s) = ((F.Ψ (F.loc v s) : k) - (((F.Ψ (F.loc v s))⁻¹ : kˣ) : k)) • γ}
  add_mem' := by
    rintro x y ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩
    refine ⟨a1.add b1, fun g h => ?_, fun g => by simp [a3, b3], fun v => ?_⟩
    · simp only [Pi.add_apply, a2, b2, smul_add]; abel
    · obtain ⟨α, h⟩ := a4 v
      obtain ⟨α', h'⟩ := b4 v
      exact ⟨α + α', fun s => by rw [Pi.add_apply, h, h', smul_add]⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, by simp, fun _ => rfl, fun _ => ⟨0, by simp⟩⟩
  smul_mem' := by
    rintro c x ⟨a1, a2, a3, a4⟩
    refine ⟨a1.comp (c • ·), fun g h => ?_, fun g => by simp [a3], fun v => ?_⟩
    · simp only [Pi.smul_apply, a2, smul_add, smul_comm c]
    · obtain ⟨α, h⟩ := a4 v
      exact ⟨c • α, fun s => by rw [Pi.smul_apply, h, smul_comm]⟩

variable {F M} {M' : Type} [AddCommGroup M'] [Module k M']

theorem strY_map (f : M →ₗ[k] M') {y : F.G0 → M} (hy : y ∈ F.strY M) : (fun g => f (y g)) ∈ F.strY M' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hy
  refine ⟨h1.comp f, fun g h => ?_, congrArg f h3, fun v => ?_, fun v => ?_⟩
  · simp only [h2, map_add (f := _), map_smul]
  · obtain ⟨α, hα⟩ := h4 v
    exact ⟨f α, fun s => by simp only [hα, map_smul]⟩
  · obtain ⟨β, hβ⟩ := h5 v
    exact ⟨f β, fun s => by simp only [hβ, map_smul]⟩

theorem strS_map (f : M →ₗ[k] M') {a : F.G0 → M} (ha : a ∈ F.strS M) : (fun g => f (a g)) ∈ F.strS M' := by
  obtain ⟨h1, h2, h3, h4⟩ := ha
  refine ⟨h1.comp f, fun g h => ?_, fun g => congrArg f (h3 g), fun v => ?_⟩
  · simp only [h2, map_add (f := _), map_smul]
  · obtain ⟨γ, hγ⟩ := h4 v
    exact ⟨f γ, fun s => by simp only [hγ, map_smul]⟩

end UpperTheory.V.Fr.Frame
end
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

namespace UpperTheory.V.Fr

private theorem ab_eval {k X : Type} [Field k] [Inhabited X] (r : ℕ) :
    ∀ H : Submodule k (X → k), Module.Finite k H → Module.finrank k H ≤ r →
      ∃ t : Fin r → X, ∀ φ ∈ H, (∀ a, φ (t a) = 0) → φ = 0 :=
  _root_.UpperTheory.Reformulated.B.Ra1.ab_eval r

private theorem ab_eval' {k X : Type} [Field k] [Inhabited X] (r : ℕ) (H : Submodule k (X → k))
    (hr : Module.rank k H ≤ r) : ∃ t : Fin r → X, ∀ φ ∈ H, (∀ a, φ (t a) = 0) → φ = 0 :=
  haveI : Module.Free k H := Module.Free.of_divisionRing k H
  ab_eval r H (Module.rank_lt_aleph0_iff.1 (hr.trans_lt Cardinal.natCast_lt_aleph0)) (Module.finrank_le_of_rank_le hr)

private theorem ab_char {l : ℕ} [Fact l.Prime] (k : Type) [Field k] [CharP k l] {B : Type} [CommGroup B] [Finite B]
    [Nontrivial B] (hB : IsPGroup l B) : ∃ ψ : B →* Multiplicative k, ∃ b, ψ b ≠ 1 := by
  obtain ⟨n, hn0, hn⟩ := hB.nontrivial_iff_card.1 inferInstance
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0.ne'
  have hl : l.Prime := Fact.out
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := B) l (n := n) (hn ▸ pow_dvd_pow l n.le_succ)
  have hq : Nat.card (B ⧸ K) = l := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup K
    rw [hn, hK, pow_succ'] at this
    exact (Nat.eq_of_mul_eq_mul_right (pow_pos hl.pos n) this).symm
  have hz : Nat.card (Multiplicative (ZMod l)) = l := by simp
  let e := mulEquivOfPrimeCardEq hq hz
  let j : Multiplicative (ZMod l) →* Multiplicative k :=
    AddMonoidHom.toMultiplicative (ZMod.castHom (dvd_refl l) k).toAddMonoidHom
  have hj : Function.Injective j := (ZMod.castHom (dvd_refl l) k).injective
  haveI : Nontrivial (B ⧸ K) := Finite.one_lt_card_iff_nontrivial.1 (hq.symm ▸ hl.one_lt)
  obtain ⟨q, hq1⟩ := exists_ne (1 : B ⧸ K)
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨j.comp (e.toMonoidHom.comp (QuotientGroup.mk' K)), b, fun h => hq1 ?_⟩
  exact e.injective (hj (h.trans (by simp)))

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}

private theorem ab_plus (hF : F.Ok C₀) : ∃ t : Fin (1 + C₀) → F.Γ,
    ∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ φ : F.Γ →* A, IsOpen (φ.ker : Set F.Γ) →
      (∀ a, φ (t a) = 1) → ∀ g, φ g = 1 := by
  let L : H1C F.loc (chRep (1 : F.Γ →* kˣ)) (fun _ => ⊤) →ₗ[k] (F.Γ → k) :=
    Submodule.liftQ _ ((LinearMap.fst k _ _).comp (Submodule.subtype _)) (by
      rintro x ⟨X, h, -⟩
      funext s
      simpa using h s)
  have hr : Module.rank k (LinearMap.range L) ≤ ((1 + C₀ : ℕ) : Cardinal) :=
    (rank_range_le L).trans (by exact_mod_cast hF.h1)
  haveI : Inhabited F.Γ := ⟨1⟩
  obtain ⟨t, ht⟩ := ab_eval' (1 + C₀) (LinearMap.range L) hr
  refine ⟨t, fun A _ _ hA φ ho hz g => ?_⟩
  by_contra hg
  haveI : Nontrivial φ.range := ⟨⟨φ.rangeRestrict g, 1, fun e => hg (congrArg Subtype.val e)⟩⟩
  obtain ⟨ψ, b, hb⟩ := ab_char k (hA.to_subgroup φ.range)
  obtain ⟨x, rfl⟩ := φ.rangeRestrict_surjective b
  let f : F.Γ → k := fun s => (ψ (φ.rangeRestrict s)).toAdd
  have hlc : IsLocallyConstant f := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun s => ⟨(fun y => s⁻¹ * y) ⁻¹' φ.ker, ho.preimage (by fun_prop),
      by simp, fun y hy => ?_⟩
    have : φ.rangeRestrict y = φ.rangeRestrict s := by
      apply Subtype.ext
      have h : φ (s⁻¹ * y) = 1 := hy
      rw [map_mul, map_inv, inv_mul_eq_one] at h
      exact h.symm
    simp only [f, this]
  have hm : f ∈ LinearMap.range L :=
    ⟨Submodule.Quotient.mk ⟨(f, 0), hlc, fun s u => by simp [f], fun _ _ => trivial⟩, rfl⟩
  have := ht f hm fun a => by
    have : φ.rangeRestrict (t a) = 1 := Subtype.ext (hz a)
    simp [f, this]
  exact hb (congrFun this x)

private theorem ab_minus (hF : F.Ok C₀) : ∃ (s' : Fin F.d → F.G0) (h : ℕ), h ≠ 0 ∧
    (∀ a, ∃ v g, g ∈ F.Iv v ∧ F.Ψ (F.loc v g) = 1 ∧ s' a = F.loc0 v g) ∧
    ∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ χ : F.G0 →* A, IsOpen (χ.ker : Set F.G0) →
      (∀ g, χ (F.star g) = χ g) → (∀ a, χ (s' a) = 1) → ∀ g, χ g ^ h = 1 := by
  choose u a₀ hu _ hgen using hF.gen
  obtain ⟨h, h0, hcl⟩ := hF.cl
  let e : (Σ v, Fin (F.dv v)) ≃ Fin F.d := Fintype.equivFinOfCardEq (by simp [Frame.d])
  refine ⟨fun a => F.loc0 (e.symm a).1 (u _ (e.symm a).2), h, h0,
    fun a => ⟨_, _, (hu _ _).1, (hu _ _).2, rfl⟩, fun A _ _ hA χ ho hs hz => hcl A hA χ ho ?_⟩
  have key : ∀ v, ∀ g ∈ F.Iv v, χ (F.loc0 v g) = 1 := fun v =>
    hgen v A hA (χ.comp (F.loc0 v)) (ho.preimage (hF.loc_cont v)) fun a => by
      have := hz (e ⟨v, a⟩)
      beta_reduce at this
      rw [e.symm_apply_apply] at this
      exact this
  rintro ⟨v, _ | _⟩ g hg
  · exact key v g hg
  · have := hs (F.loc0 v g)⁻¹
    rw [Frame.star, inv_inv, map_inv, key v g hg, inv_one] at this
    exact this

private theorem ab_ext (hF : F.Ok C₀) : ∃ π : F.Γ → F.G0, (∀ g : F.G0, π g = g) ∧
    ∀ (A : Type) [CommGroup A] (χ : F.G0 →* A), (∀ g, χ (F.conj g) = χ g) → ∃ φ : F.Γ →* A, ∀ γ, φ γ = χ (π γ) := by
  classical
  have hc : ∀ γ : F.Γ, γ ∉ F.del.ker → γ * F.c ∈ F.del.ker := fun γ h => by
    rw [MonoidHom.mem_ker] at h ⊢
    rw [map_mul, hF.del_c, (Int.units_eq_one_or _).resolve_left h]; simp
  have hci : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hF.c_sq
  have hcj : ∀ g : F.G0, (F.conj g : F.Γ) = F.c * g * F.c := fun g => by
    show F.c * g * F.c⁻¹ = _
    rw [hci]
  let π : F.Γ → F.G0 := fun γ => if h : γ ∈ F.del.ker then ⟨γ, h⟩ else ⟨γ * F.c, hc γ h⟩
  have p1 : ∀ γ, γ ∈ F.del.ker → (π γ : F.Γ) = γ := fun γ h => by simp only [π, dif_pos h]
  have p2 : ∀ γ, γ ∉ F.del.ker → (π γ : F.Γ) = γ * F.c := fun γ h => by simp only [π, dif_neg h]
  refine ⟨π, fun g => Subtype.ext (p1 g g.2), fun A _ χ hχ => ⟨MonoidHom.mk' (fun γ => χ (π γ)) fun a b => ?_, fun _ => rfl⟩⟩
  by_cases ha : a ∈ F.del.ker
  · rw [← map_mul]
    congr 1
    apply Subtype.ext
    by_cases hb : b ∈ F.del.ker
    · rw [Subgroup.coe_mul, p1 _ ha, p1 _ hb, p1 _ (mul_mem ha hb)]
    · rw [Subgroup.coe_mul, p1 _ ha, p2 _ hb, p2 _ fun h => hb ((Subgroup.mul_mem_cancel_left _ ha).1 h), mul_assoc]
  · show χ _ = χ _ * χ _
    rw [← hχ (π b), ← map_mul]
    congr 1
    apply Subtype.ext
    by_cases hb : b ∈ F.del.ker
    · rw [Subgroup.coe_mul, hcj, p2 _ ha, p1 _ hb, p2 _ fun h => ha ((Subgroup.mul_mem_cancel_right _ hb).1 h)]
      simp only [mul_assoc]
      rw [← mul_assoc F.c F.c, hF.c_sq, one_mul]
    · have hab : a * b ∈ F.del.ker := by
        rw [MonoidHom.mem_ker] at ha hb ⊢
        rw [map_mul, (Int.units_eq_one_or _).resolve_left ha, (Int.units_eq_one_or _).resolve_left hb]; simp
      rw [Subgroup.coe_mul, hcj, p2 _ ha, p2 _ hb, p1 _ hab]
      simp only [mul_assoc]
      rw [← mul_assoc F.c F.c, hF.c_sq, one_mul, mul_one]

end UpperTheory.V.Fr

theorem UpperTheory.V.Fr.ab_gen :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∃ (s : Fin (1 + C₀ + F.d) → F.G0) (s' : Fin F.d → F.G0) (h : ℕ), h ≠ 0 ∧ (∀ a, F.Ψ (s a) = 1) ∧ (∀ a, ∃ v g, g ∈ F.Iv v ∧ F.Ψ (F.loc v g) = 1 ∧ s' a = F.loc0 v g) ∧ ∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ χ : F.G0 →* A, IsOpen (χ.ker : Set F.G0) → ((∀ a, χ (s a) = 1) → ∀ g, χ g ^ h = 1) ∧ ((∀ g, χ (F.star g) = χ g) → (∀ a, χ (s' a) = 1) → ∀ g, χ g ^ h = 1) := by
  intro l _ k _ _ F C₀ hF
  obtain ⟨t, ht⟩ := ab_plus hF
  obtain ⟨s', h, h0, hs', hm⟩ := ab_minus hF
  obtain ⟨π, hπ, hext⟩ := ab_ext hF
  haveI := hF.fin
  have hcop : (Nat.card kˣ).Coprime l := by
    haveI := Fintype.ofFinite k
    obtain ⟨n, hl, hn⟩ := FiniteField.card k l
    rw [Nat.card_units, Nat.card_eq_fintype_card, hn]
    refine Nat.Coprime.coprime_dvd_right (dvd_pow_self l n.ne_zero) ?_
    exact (Nat.coprime_self_sub_left (Nat.one_le_pow _ _ hl.pos)).2 (Nat.coprime_one_left _)
  have hcc : ∀ g, F.conj (F.conj g) = g := fun g => Subtype.ext (by
    show F.c * (F.c * g * F.c⁻¹) * F.c⁻¹ = g
    rw [inv_eq_of_mul_eq_one_right hF.c_sq]
    simp only [mul_assoc]
    rw [← mul_assoc F.c F.c, hF.c_sq, one_mul, mul_one])
  have hcont : Continuous F.conj := by
    refine Continuous.subtype_mk (f := fun g : F.G0 => F.c * g * F.c⁻¹) (by fun_prop) _
  refine ⟨Fin.append (fun a => (π (t a) * F.conj (π (t a))) ^ Nat.card kˣ) s', s', h, h0, fun a => ?_, hs',
    fun A _ _ hA χ ho => ⟨fun hz => hm A hA χ ho ?_ fun a => by simpa using hz (Fin.natAdd _ a), hm A hA χ ho⟩⟩
  · refine Fin.addCases (fun a => ?_) (fun a => ?_) a
    · rw [Fin.append_left, Subgroup.coe_pow, map_pow, pow_card_eq_one']
    · rw [Fin.append_right]
      obtain ⟨v, g, -, h1, h2⟩ := hs' a
      rw [h2]; exact h1
  · obtain ⟨φ, hφ⟩ := hext A (χ * χ.comp F.conj) fun g => by simp [hcc, mul_comm]
    have hop : IsOpen (φ.ker : Set F.Γ) := by
      refine Subgroup.isOpen_mono (H₁ := (χ.ker ⊓ χ.ker.comap F.conj).map F.del.ker.subtype) ?_ ?_
      · rintro _ ⟨g, ⟨h1, h2⟩, rfl⟩
        show φ g = 1
        rw [hφ, hπ]
        exact (congrArg₂ (· * ·) h1 h2).trans (mul_one 1)
      · exact hF.del_open.isOpenMap_subtype_val _ (ho.inter (ho.preimage hcont))
    have h1 := ht A hA φ hop fun a => by
      have := hz (Fin.castAdd _ a)
      rw [Fin.append_left, map_pow, map_mul] at this
      obtain ⟨n, hn⟩ := hA (χ (π (t a)) * χ (F.conj (π (t a))))
      rw [hφ]
      exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (hcop.pow_right n) (orderOf_dvd_of_pow_eq_one this)
        (orderOf_dvd_of_pow_eq_one hn))
    intro g
    have := h1 (g⁻¹ : F.G0)
    rw [hφ, hπ] at this
    have h2 : χ g⁻¹ * χ (F.star g) = 1 := this
    rw [map_inv, inv_mul_eq_one] at h2
    exact h2.symm
end
