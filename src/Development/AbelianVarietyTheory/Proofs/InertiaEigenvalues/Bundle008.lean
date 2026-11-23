module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Nakayama
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Analysis.Normed.Ring.Basic

@[expose] public section

section

namespace GlobalTheory

private theorem exists_equivariant_projection_onto_invariant_submodule {G M : Type} [Group G] [Fintype G] [AddCommGroup M]
    [Module ℂ M] (S W : Submodule ℂ M) (π : G → Module.End ℂ M)
    (h1 : ∀ v ∈ S, π 1 v = v)
    (hmul : ∀ g h, ∀ v ∈ S, π (g * h) v = π h (π g v))
    (hWS : W ≤ S) (hW : ∀ g, ∀ w ∈ W, π g w ∈ W) :
    ∃ P : M →ₗ[ℂ] M, (∀ x, P x ∈ W) ∧ (∀ w ∈ W, P w = w) ∧
      (∀ g, ∀ x ∈ S, P (π g x) = π g (P x)) := by
  classical
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl W
  refine ⟨(Fintype.card G : ℂ)⁻¹ • ∑ g, π g⁻¹ ∘ₗ W.projection q hq ∘ₗ π g,
    ?_, ?_, ?_⟩
  · intro x
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]
    exact W.smul_mem _ (W.sum_mem fun g _ => hW _ _ (Submodule.projection_apply_mem _ _))
  · intro w hw
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]
    have key : ∀ g : G, π g⁻¹ (W.projection q hq (π g w)) = w := by
      intro g
      rw [Submodule.projection_apply_of_mem_left hq (hW g w hw), ← hmul _ _ w (hWS hw)]
      simp [h1 w (hWS hw)]
    simp only [key, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]
    rw [smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero), one_smul]
  · intro h x hx

    simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply, map_smul, map_sum]
    refine congrArg (fun y => (Fintype.card G : ℂ)⁻¹ • y) ?_
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
    simp only [Equiv.coe_mulLeft]
    rw [← hmul _ _ x hx, ← hmul _ h _ (hWS (Submodule.projection_apply_mem _ _))]
    simp only [mul_inv_rev, inv_mul_cancel_right]

theorem mem_span_killed_union_averages {G M : Type} [Group G] [Fintype G] [AddCommGroup M]
    [Module ℂ M] (S : Submodule ℂ M) (π : G → Module.End ℂ M)
    (hS : ∀ g, ∀ v ∈ S, π g v ∈ S) (h1 : ∀ v ∈ S, π 1 v = v)
    (hmul : ∀ g h, ∀ v ∈ S, π (g * h) v = π h (π g v))
    (C : Set (G → ℂ)) (hC : ∀ c ∈ C, ∀ x : G, (fun g => c (x * g * x⁻¹)) ∈ C)
    (v : M) (hv : v ∈ S) :
    v ∈ Submodule.span ℂ ({w | w ∈ S ∧ ∀ c ∈ C, ∑ g, c g • π g w = 0} ∪
      {u | ∃ c ∈ C, ∃ w ∈ S, u = ∑ g, c g • π g w}) := by
  classical
  have hAS : ∀ (c : G → ℂ), ∀ w ∈ S, ∑ g, c g • π g w ∈ S := fun c w hw =>
    S.sum_mem fun g _ => S.smul_mem _ (hS g w hw)
  have hWS : Submodule.span ℂ {u | ∃ c ∈ C, ∃ w ∈ S, u = ∑ g, c g • π g w} ≤ S :=
    Submodule.span_le.2 (by rintro u ⟨c, -, w, hw, rfl⟩; exact hAS c w hw)
  have hWst : ∀ h, ∀ u ∈ Submodule.span ℂ {u | ∃ c ∈ C, ∃ w ∈ S, u = ∑ g, c g • π g w},
      π h u ∈ Submodule.span ℂ {u | ∃ c ∈ C, ∃ w ∈ S, u = ∑ g, c g • π g w} := by
    intro h u hu
    have hle : Submodule.span ℂ {u | ∃ c ∈ C, ∃ w ∈ S, u = ∑ g, c g • π g w} ≤
        (Submodule.span ℂ {u | ∃ c ∈ C, ∃ w ∈ S, u = ∑ g, c g • π g w}).comap (π h) := by
      refine Submodule.span_le.2 ?_
      rintro u ⟨c, hc, w, hw, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      refine Submodule.subset_span ⟨fun k => c (h * k * h⁻¹), hC c hc h, π h w, hS h w hw, ?_⟩

      rw [map_sum]
      refine Fintype.sum_equiv (MulAut.conj h⁻¹).toEquiv _ _ fun g => ?_
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv,
        map_smul]
      rw [show h * (h⁻¹ * g * h) * h⁻¹ = g by group, ← hmul _ _ w hw, ← hmul _ _ w hw,
        show g * h = h * (h⁻¹ * g * h) by group]
    exact hle hu
  obtain ⟨P, hPW, hPid, hPc⟩ := exists_equivariant_projection_onto_invariant_submodule S _ π h1 hmul hWS hWst
  have hPv : P v ∈ S := hWS (hPW v)
  have hPc' : ∀ g, P (π g v) = π g (P v) := fun g => hPc g v hv
  have hkill : v - P v ∈ {w | w ∈ S ∧ ∀ c ∈ C, ∑ g, c g • π g w = 0} := by
    refine ⟨S.sub_mem hv hPv, fun c hc => ?_⟩
    have hA : ∑ g, c g • π g (P v) = P (∑ g, c g • π g v) := by

      simp only [map_sum, map_smul, hPc']
    simp only [map_sub, smul_sub, Finset.sum_sub_distrib, hA]
    rw [hPid _ (Submodule.subset_span ⟨c, hc, v, hv, rfl⟩), sub_self]
  have hsum := Submodule.add_mem _ (Submodule.subset_span (Set.mem_union_left _ hkill))
    (Submodule.span_mono Set.subset_union_right (hPW v))
  rwa [sub_add_cancel] at hsum

end GlobalTheory
end

section

namespace GlobalTheory.DownLift

theorem abstract_irreducible_of_highestWeight (V : Type) [AddCommGroup V] [Module ℂ V]
    (U : Submodule ℂ V) (hfin : FiniteDimensional ℂ U) (J : Type) (E : J → Module.End ℂ V)
    (st : J → J) (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (Hw : V → Prop)
    (hU : ∀ j, ∀ x ∈ U, E j x ∈ U) (han : ∀ x ∈ U, B x x = 0 → x = 0)
    (hadj : ∀ j x y, B (E j x) y = B x (E (st j) y)) (hst : ∀ j, st (st j) = j)
    (hex : ∀ T : Submodule ℂ V, T ≤ U → T ≠ ⊥ → (∀ j, ∀ x ∈ T, E j x ∈ T) →
      ∃ x ∈ T, x ≠ 0 ∧ Hw x)
    (hprop : ∀ x y, x ∈ U → y ∈ U → Hw x → Hw y → x ≠ 0 → ∃ c : ℂ, y = c • x)
    (S : Submodule ℂ V) (hSU : S ≤ U) (hS : S ≠ ⊥) (hSE : ∀ j, ∀ x ∈ S, E j x ∈ S) :
    S = U := by
  classical
  let P : Submodule ℂ V := U ⊓ ⨅ s : S, LinearMap.ker (B (s : V))
  have hP : ∀ y, y ∈ P ↔ y ∈ U ∧ ∀ s ∈ S, B s y = 0 := by
    intro y
    simp [P, Submodule.mem_iInf]
  have hPbot : P = ⊥ := by
    by_contra hne
    have hPE : ∀ j, ∀ x ∈ P, E j x ∈ P := by
      intro j y hy
      rw [hP] at hy ⊢
      refine ⟨hU j y hy.1, fun s hs => ?_⟩
      have h := hadj (st j) s y
      rw [hst] at h
      rw [← h]
      exact hy.2 _ (hSE _ _ hs)
    obtain ⟨y, hyP, hy0, hyw⟩ := hex P inf_le_left hne hPE
    obtain ⟨x, hxS, hx0, hxw⟩ := hex S hSU hS hSE
    rw [hP] at hyP
    obtain ⟨c, hc⟩ := hprop x y (hSU hxS) hyP.1 hxw hyw hx0
    have hyS : y ∈ S := hc ▸ S.smul_mem c hxS
    exact hy0 (han y hyP.1 (hyP.2 y hyS))
  haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSU
  let b := Module.finBasis ℂ S
  let φ : U →ₗ[ℂ] (Fin (Module.finrank ℂ S) → ℂ) :=
    LinearMap.pi fun i => (B (b i : V)).comp U.subtype
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    have hy' : ∀ i, B (b i : V) (y : V) = 0 := fun i => congrFun (LinearMap.mem_ker.mp hy) i
    have hyP : (y : V) ∈ P := by
      rw [hP]
      refine ⟨y.2, fun s hs => ?_⟩
      have h := congrArg (fun z : S => (z : V)) (b.sum_repr ⟨s, hs⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h

      rw [← h, map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy', smul_zero]
    rw [hPbot, Submodule.mem_bot] at hyP
    rw [Submodule.mem_bot]
    exact Subtype.ext hyP
  have hle := LinearMap.finrank_le_finrank_of_injective hφ
  rw [Module.finrank_fin_fun] at hle
  exact Submodule.eq_of_le_of_finrank_le hSU hle

end GlobalTheory.DownLift
end

section

namespace GlobalTheory.OrthogonalProjection

open Module

theorem exists_orthogonal_projection_finite {W : Type} [AddCommGroup W] [Module ℂ W] (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (hB : ∀ v : W, B v v = 0 → v = 0) (M : Submodule ℂ W) [FiniteDimensional ℂ M] (v : W) :
    ∃ m ∈ M, ∀ z ∈ M, B z (v - m) = 0 := by
  classical
  let b : Basis (Fin (finrank ℂ M)) ℂ M := Module.finBasis ℂ M
  let T : M →ₗ[ℂ] (Fin (finrank ℂ M) → ℂ) :=
    LinearMap.pi (fun i => (B (b i : W)).comp M.subtype)
  have key : ∀ w : W, (∀ i, B (b i : W) w = 0) → ∀ z ∈ M, B z w = 0 := by
    intro w hw z hz
    have h0 : (B.flip w).comp M.subtype = 0 := by
      apply b.ext
      intro i
      simpa using hw i
    have := LinearMap.congr_fun h0 ⟨z, hz⟩
    simpa using this
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    have h1 : ∀ i, B (b i : W) (m : W) = 0 := by
      intro i
      have := congr_fun hm i
      simpa [T] using this
    have h2 := key m h1 m m.2
    exact Subtype.ext (hB _ h2)
  have hsurj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Module.finrank_fin_fun])).mp hinj
  obtain ⟨m, hm⟩ := hsurj (fun i => B (b i : W) v)
  refine ⟨m, m.2, ?_⟩
  apply key
  intro i
  have := congr_fun hm i
  simp [T] at this
  simp [map_sub, this]

theorem exists_orth_proj : ∀ {W : Type} [inst : AddCommGroup W] [inst_1 : Module ℂ W] (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), (∀ (v : W), ((B : W → W →ₗ[ℂ] ℂ) v : W → ℂ) v = (0 : ℂ) → v = (0 : W)) → ∀ (M : Submodule ℂ W) [FiniteDimensional ℂ ↥M] (v : W), ∃ m ∈ M, ∀ z ∈ M, ((B : W → W →ₗ[ℂ] ℂ) z : W → ℂ) (v - m) = (0 : ℂ) := by
  intro W _ _ B hB M _ v
  exact exists_orthogonal_projection_finite B hB M v

end GlobalTheory.OrthogonalProjection
end

section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem mem_span_indicator_lowerSets :
    ∀ (X L : Type) [Fintype L] [PartialOrder L] (ρ : X → Option L) (Φ : X → ℂ),
      (∀ x, ρ x = none → Φ x = 0) → (∀ x x', ρ x = ρ x' → Φ x = Φ x') →
      Φ ∈ Submodule.span ℂ {Ψ | ∃ l : L, Ψ = Set.indicator {x | ∃ l', ρ x = some l' ∧ l' ≤ l}
        (fun _ => (1 : ℂ))} := by
  classical
  intro X L _ _ ρ Φ h0 hΦ
  set S := Submodule.span ℂ {Ψ : X → ℂ | ∃ l : L, Ψ = Set.indicator
    {x | ∃ l', ρ x = some l' ∧ l' ≤ l} (fun _ => (1 : ℂ))} with hS
  have key : ∀ l : L, Set.indicator {x | ρ x = some l} (fun _ => (1 : ℂ)) ∈ S := by
    intro l
    induction l using WellFoundedLT.induction with
    | ind l ih =>
      have hsum : Set.indicator {x | ρ x = some l} (fun _ => (1 : ℂ)) =
          Set.indicator {x | ∃ l', ρ x = some l' ∧ l' ≤ l} (fun _ => (1 : ℂ)) -
            ∑ l' ∈ Finset.univ.filter (· < l),
              Set.indicator {x | ρ x = some l'} (fun _ => (1 : ℂ)) := by
        funext x
        simp only [Pi.sub_apply, Finset.sum_apply, Set.indicator_apply, Set.mem_setOf_eq]
        cases hx : ρ x with
        | none => simp
        | some m =>
          have h1 : (∃ l', some m = some l' ∧ l' ≤ l) ↔ m ≤ l := by simp
          simp only [Option.some.injEq, h1]
          rw [Finset.sum_ite_eq]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases hml : m = l
          · subst hml; simp
          · by_cases hle : m ≤ l
            · have hlt : m < l := lt_of_le_of_ne hle hml
              simp [hml, hle, hlt]
            · have hlt : ¬ m < l := fun h => hle h.le
              simp [hml, hle, hlt]
      rw [hsum]
      exact S.sub_mem (Submodule.subset_span ⟨l, rfl⟩)
        (S.sum_mem fun l' hl' => ih l' (by simpa using hl'))
  let c : L → ℂ := fun l => if h : ∃ x, ρ x = some l then Φ h.choose else 0
  have hdecomp : Φ = ∑ l, c l • Set.indicator {x | ρ x = some l} (fun _ => (1 : ℂ)) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, Set.indicator_apply, Set.mem_setOf_eq,
      smul_eq_mul, mul_ite, mul_one, mul_zero]
    cases hx : ρ x with
    | none => simpa using h0 x hx
    | some m =>
      simp only [Option.some.injEq, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      have hex : ∃ y, ρ y = some m := ⟨x, hx⟩
      simp only [c, dif_pos hex]
      exact hΦ _ _ (hx.trans hex.choose_spec.symm)
  rw [hdecomp]
  exact S.sum_mem fun l _ => S.smul_mem _ (key l)

end GlobalTheory
end

section

open TensorProduct

namespace GlobalTheory.BSP

open TensorProduct in
private theorem exists_eq_one_tmul_quotient {A : Type} [CommRing A] (I : Ideal A) {M : Type}
    [AddCommGroup M] [Module A M] (z : (A ⧸ I) ⊗[A] M) : ∃ x : M, z = (1 : A ⧸ I) ⊗ₜ[A] x := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul t x =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective t
    refine ⟨r • x, ?_⟩
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    rfl
  | add z z' hz hz' =>
    obtain ⟨x, rfl⟩ := hz
    obtain ⟨x', rfl⟩ := hz'
    exact ⟨x + x', by rw [TensorProduct.tmul_add]⟩

open TensorProduct in
private theorem one_tmul_quotient_eq_zero_iff_mem_smul {A : Type} [CommRing A] (I : Ideal A) {M : Type}
    [AddCommGroup M] [Module A M] (y : M) :
    (1 : A ⧸ I) ⊗ₜ[A] y = 0 ↔ y ∈ I • (⊤ : Submodule A M) := by
  have h := quotTensorEquivQuotSMul_mk_tmul (M := M) I 1 y
  rw [map_one, one_smul] at h
  rw [← (quotTensorEquivQuotSMul M I).map_eq_zero_iff, h, Submodule.Quotient.mk_eq_zero]


open TensorProduct in
theorem _root_.GlobalTheory.BSP.bijective_of_bijective_baseChange_quotient :
    ∀ (A : Type) [CommRing A] (𝔞 : Ideal A), 𝔞 ≤ Ideal.jacobson ⊥ → ∀ (P : Type) [AddCommGroup P] [Module A P] [Module.Finite A P] (P' : Type) [AddCommGroup P'] [Module A P'] [Module.Finite A P'] [Module.Projective A P'] (w : P →ₗ[A] P'), Function.Bijective (w.baseChange (A ⧸ 𝔞)) → Function.Bijective w := by
  intro A _ 𝔞 h𝔞 P _ _ _ P' _ _ _ _ w hw
  have surj : Function.Surjective w := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top h𝔞 ?_
    intro y _
    obtain ⟨z, hz⟩ := hw.2 ((1 : A ⧸ 𝔞) ⊗ₜ[A] y)
    obtain ⟨x, rfl⟩ := exists_eq_one_tmul_quotient 𝔞 z
    rw [LinearMap.baseChange_tmul] at hz
    have hmem : w x - y ∈ 𝔞 • (⊤ : Submodule A P') := by
      rw [← one_tmul_quotient_eq_zero_iff_mem_smul, TensorProduct.tmul_sub, hz, sub_self]
    have : y = w x - (w x - y) := by abel
    rw [this]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨x, rfl⟩) (Submodule.mem_sup_right hmem)
  refine ⟨?_, surj⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property w LinearMap.id surj
  set π : P →ₗ[A] P := LinearMap.id - s ∘ₗ w with hπ
  have hwπ : ∀ p, w (π p) = 0 := fun p => by
    have := LinearMap.congr_fun hs (w p)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp [hπ, this]
  have hπw : ∀ p, w p = 0 → π p = p := fun p hp => by simp [hπ, hp]
  have hbot : LinearMap.range π = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot 𝔞 _ ?_ ?_ h𝔞
    · rw [LinearMap.range_eq_map]
      exact Module.Finite.fg_top.map _
    · rintro _ ⟨p, rfl⟩
      have h0 : (1 : A ⧸ 𝔞) ⊗ₜ[A] π p = 0 := by
        apply hw.1
        rw [LinearMap.baseChange_tmul, hwπ, TensorProduct.tmul_zero, map_zero]
      rw [one_tmul_quotient_eq_zero_iff_mem_smul] at h0
      rw [LinearMap.range_eq_map, ← Submodule.map_smul'', ← hπw _ (hwπ p)]
      exact Submodule.mem_map_of_mem h0
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro p hp
  have : π p ∈ LinearMap.range π := ⟨p, rfl⟩
  rw [hbot, Submodule.mem_bot, hπw p hp] at this
  exact this

end GlobalTheory.BSP
end

section

namespace GlobalTheory.WeightSum

theorem scalar_weight_sum {ι : Type} (S : Finset ι) (w : ι → ℤ) (a : ι → ℂ)
    (h : ∀ z : ℂ, ‖z‖ = 1 → ∑ s ∈ S, z ^ w s * a s = 0) :
    ∑ s ∈ S, (w s : ℂ) * a s = 0 := by
  have hG : HasDerivAt (fun u : ℂ => ∑ s ∈ S, Complex.exp ((w s : ℂ) * (u * Complex.I)) * a s)
      (∑ s ∈ S, ((w s : ℂ) * Complex.I) * a s) ((0 : ℝ) : ℂ) := by
    apply HasDerivAt.fun_sum
    intro s _
    have h1 : HasDerivAt (fun u : ℂ => (w s : ℂ) * (u * Complex.I)) ((w s : ℂ) * Complex.I)
        ((0 : ℝ) : ℂ) := by
      simpa using ((hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const Complex.I).const_mul (w s : ℂ)
    have h2 := h1.cexp.mul_const (a s)
    simpa using h2
  have hg := hG.comp_ofReal
  have hz : (fun t : ℝ => ∑ s ∈ S, Complex.exp ((w s : ℂ) * ((t : ℂ) * Complex.I)) * a s)
      = fun _ => (0 : ℂ) := by
    funext t
    have := h (Complex.exp (t * Complex.I)) (Complex.norm_exp_ofReal_mul_I t)
    simpa only [← Complex.exp_int_mul] using this
  rw [hz] at hg
  have h0 := hg.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
  have h3 : (∑ s ∈ S, (w s : ℂ) * a s) * Complex.I = 0 := by
    rw [← h0, Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ => by ring
  exact (mul_eq_zero.mp h3).resolve_right Complex.I_ne_zero

theorem weight_sum_mem {E : Type} [AddCommGroup E] [Module ℂ E] (V : Submodule ℂ E) {ι : Type}
    (S : Finset ι) (w : ι → ℤ) (f : ι → E)
    (h : ∀ z : ℂ, ‖z‖ = (1 : ℝ) → ∑ s ∈ S, z ^ w s • f s ∈ V) :
    ∑ s ∈ S, ((w s : ℤ) : ℂ) • f s ∈ V := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  rw [Submodule.mem_dualAnnihilator] at hφ
  have := scalar_weight_sum S w (fun s => φ (f s)) fun z hz => by

    simpa [map_sum] using hφ _ (h z hz)

  simpa [map_sum] using this

end GlobalTheory.WeightSum
end

section

namespace GlobalTheory.EvalNormCoefficientBound

theorem norm_eval_le_sum_norm_coeff {σ : Type} (P : MvPolynomial σ ℂ) (v : σ → ℂ)
    (hv : ∀ (s : σ), ‖v s‖ ≤ (1 : ℝ)) :
    ‖(MvPolynomial.eval v : MvPolynomial σ ℂ → ℂ) P‖ ≤
      ∑ d ∈ MvPolynomial.support P, ‖AddMonoidAlgebra.coeff P d‖ := by
  rw [MvPolynomial.eval_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun d _ => ?_))
  rw [norm_mul]
  have h1 : ‖∏ s ∈ d.support, v s ^ d s‖ ≤ 1 := by
    rw [norm_prod]
    refine Finset.prod_le_one₀ (fun s _ => norm_nonneg _) (fun s _ => ?_)
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (hv s)
  exact mul_le_of_le_one_right (norm_nonneg _) h1

end GlobalTheory.EvalNormCoefficientBound
end

section

namespace GlobalTheory.OneAddPowSquareZero

theorem one_add_pow_of_mul_self_eq_zero :
    ∀ {S : Type} [inst : Ring S] (X : S), X * X = (0 : S) →
      ∀ (N : ℕ), ((1 : S) + X) ^ N = (1 : S) + (↑N : S) * X := by
  intro S _ X hX N
  induction N with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.cast_succ, mul_add, mul_one, add_mul, one_mul, mul_assoc, hX,
      mul_zero, add_zero, add_mul, one_mul, add_assoc]

end GlobalTheory.OneAddPowSquareZero
end
