module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.FieldTheory.PrimitiveElement

@[expose] public section

section

noncomputable section

namespace SheetDecomposition.PF

open MvPolynomial

theorem ker_baseChange {k B K σ Φ Φ' : Type} [Field k] [CommRing B] [Algebra k B] [Field Φ] [Field Φ']
    [Algebra (MvPolynomial K k) Φ] [IsFractionRing (MvPolynomial K k) Φ] (a : k →+* Φ)
    (ha : ∀ c, a c = algebraMap (MvPolynomial K k) Φ (C c)) (ν : MvPolynomial K B →+* Φ') (hν : Function.Injective ν)
    (L : Φ →+* Φ') (hL : ∀ r, L (algebraMap (MvPolynomial K k) Φ r) = ν (map (algebraMap k B) r))
    (ψ : MvPolynomial σ k →ₐ[k] B) :
    RingHom.ker (eval₂Hom L fun s => ν (C (ψ (X s)))) = (RingHom.ker ψ).map (map a) := by
  classical
  obtain ⟨Θ, hΘ⟩ : ∃ f : MvPolynomial σ Φ →+* Φ', f = eval₂Hom L fun s => ν (C (ψ (X s))) :=
    ⟨_, rfl⟩
  suffices main : RingHom.ker Θ = (RingHom.ker ψ).map (map a) by
    subst hΘ
    exact main
  have hΘC : ∀ f : Φ, Θ (C f) = L f := fun f => by rw [hΘ, eval₂Hom_C]
  have hΘX : ∀ s : σ, Θ (X s) = ν (C (ψ (X s))) := fun s => by rw [hΘ, eval₂Hom_X']
  obtain ⟨α, hα⟩ : ∃ f : MvPolynomial K (MvPolynomial σ k) →+* MvPolynomial σ Φ,
      f = eval₂Hom (map a) fun i => C (algebraMap (MvPolynomial K k) Φ (X i)) := ⟨_, rfl⟩
  have hαC : ∀ p : MvPolynomial σ k, α (C p) = map a p := fun p => by rw [hα, eval₂Hom_C]
  have hαX : ∀ i : K, α (X i) = C (algebraMap (MvPolynomial K k) Φ (X i)) := fun i => by
    rw [hα, eval₂Hom_X']
  have hΘa : ∀ p : MvPolynomial σ k, Θ (map a p) = ν (C (ψ p)) := by
    have h : Θ.comp (map a) =
        ν.comp ((C : B →+* MvPolynomial K B).comp (ψ : MvPolynomial σ k →+* B)) := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, map_C, hΘC, ha, hL, RingHom.coe_coe, algHom_C]
      · intro s
        simp only [RingHom.comp_apply, map_X, hΘX, RingHom.coe_coe]
    intro p
    exact DFunLike.congr_fun h p
  have hΘα : ∀ Q, Θ (α Q) = ν (map (ψ : MvPolynomial σ k →+* B) Q) := by
    have h : Θ.comp α = ν.comp (map (ψ : MvPolynomial σ k →+* B)) := by
      apply MvPolynomial.ringHom_ext
      · intro p
        simp only [RingHom.comp_apply, hαC, hΘa, map_C, RingHom.coe_coe]
      · intro i
        simp only [RingHom.comp_apply, hαX, hΘC, hL, map_X]
    intro Q
    exact DFunLike.congr_fun h Q
  have hαmapC : ∀ p : MvPolynomial K k, α (map (C : k →+* MvPolynomial σ k) p) =
      C (algebraMap (MvPolynomial K k) Φ p) := by
    have h : α.comp (map (C : k →+* MvPolynomial σ k)) =
        (C : Φ →+* MvPolynomial σ Φ).comp (algebraMap (MvPolynomial K k) Φ) := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, map_C, hαC, ha]
      · intro i
        simp only [RingHom.comp_apply, map_X, hαX]
    intro p
    exact DFunLike.congr_fun h p
  have hCmem : ∀ q : MvPolynomial K k, C (algebraMap (MvPolynomial K k) Φ q) ∈ α.range :=
    fun q => RingHom.mem_range.mpr ⟨_, hαmapC q⟩
  have hXmem : ∀ s : σ, (X s : MvPolynomial σ Φ) ∈ α.range := fun s =>
    RingHom.mem_range.mpr ⟨C (X s), by rw [hαC, map_X]⟩
  have hden : ∀ P : MvPolynomial σ Φ, ∃ q : MvPolynomial K k, q ≠ 0 ∧
      C (algebraMap (MvPolynomial K k) Φ q) * P ∈ α.range := by
    intro P
    refine MvPolynomial.induction_on (motive := fun P => ∃ q : MvPolynomial K k, q ≠ 0 ∧
      C (algebraMap (MvPolynomial K k) Φ q) * P ∈ α.range) P ?_ ?_ ?_
    · intro f
      try dsimp only
      obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial K k) f
      refine ⟨q, nonZeroDivisors.ne_zero hq, ?_⟩
      rw [← C_mul, mul_div_cancel₀ _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq)]
      exact hCmem p
    · intro P₁ P₂ h₁ h₂
      try dsimp only at h₁ h₂ ⊢
      obtain ⟨q₁, hq₁, h₁⟩ := h₁
      obtain ⟨q₂, hq₂, h₂⟩ := h₂
      refine ⟨q₁ * q₂, mul_ne_zero hq₁ hq₂, ?_⟩
      have e : C (algebraMap (MvPolynomial K k) Φ (q₁ * q₂)) * (P₁ + P₂) =
          C (algebraMap (MvPolynomial K k) Φ q₂) * (C (algebraMap (MvPolynomial K k) Φ q₁) * P₁) +
            C (algebraMap (MvPolynomial K k) Φ q₁) * (C (algebraMap (MvPolynomial K k) Φ q₂) * P₂) := by
        rw [map_mul, C_mul]
        ring
      rw [e]
      exact add_mem (mul_mem (hCmem q₂) h₁) (mul_mem (hCmem q₁) h₂)
    · intro P s h
      try dsimp only at h ⊢
      obtain ⟨q, hq, h⟩ := h
      refine ⟨q, hq, ?_⟩
      rw [← mul_assoc]
      exact mul_mem h (hXmem s)
  apply le_antisymm
  · intro P hP
    rw [RingHom.mem_ker] at hP
    obtain ⟨q, hq, hmem⟩ := hden P
    obtain ⟨Q, hQ⟩ := RingHom.mem_range.mp hmem
    have hQ0 : map (ψ : MvPolynomial σ k →+* B) Q = 0 := by
      apply hν
      rw [map_zero, ← hΘα, hQ, map_mul, hP, mul_zero]
    have hJ : α Q ∈ (RingHom.ker ψ).map (map a) := by

      rw [Q.as_sum, map_sum]
      refine Ideal.sum_mem _ fun v _ => ?_
      rw [monomial_eq, map_mul, hαC]
      refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
      rw [RingHom.mem_ker]
      have hv := congrArg (AddMonoidAlgebra.coeff · v) hQ0
      rw [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hv
      exact hv
    have hqne : algebraMap (MvPolynomial K k) Φ q ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hq)
    have hP' : P = C (algebraMap (MvPolynomial K k) Φ q)⁻¹ * α Q := by
      rw [hQ, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hqne, C_1, one_mul]
    rw [hP']
    exact Ideal.mul_mem_left _ _ hJ
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [RingHom.mem_ker] at hp
    rw [Ideal.mem_comap, RingHom.mem_ker, hΘa, hp, map_zero, map_zero]

end SheetDecomposition.PF
end
end

section

noncomputable section

namespace SheetDecomposition.ChartAlg

open MvPolynomial Filter Topology

theorem exists_coords {σ : Type} [Fintype σ] {E : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (L : E →ₗ[ℂ] (σ → ℂ)) (hL : Function.Injective L) :
    ∃ (κ : Type) (_ : Fintype κ) (a : κ → σ), Fintype.card κ = Module.finrank ℂ E ∧
      Function.Surjective (fun (x : E) (k : κ) => L x (a k)) := by
  classical
  let f : σ → Module.Dual ℂ E := fun s => (LinearMap.proj s).comp L
  have hproj : Submodule.span ℂ (Set.range fun s : σ => (LinearMap.proj s : (σ → ℂ) →ₗ[ℂ] ℂ)) = ⊤ := by
    refine eq_top_iff.2 fun φ _ => ?_
    have hφ : φ = ∑ s, φ (Pi.single s 1) • (LinearMap.proj s : (σ → ℂ) →ₗ[ℂ] ℂ) := by
      refine LinearMap.pi_ext fun i c => ?_
      have hsc : (Pi.single i c : σ → ℂ) = c • Pi.single i 1 := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      simp [hsc, Pi.single_apply, mul_comm]
    rw [hφ]
    exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  have htop : Submodule.span ℂ (Set.range f) = ⊤ := by
    have hr : Set.range f = L.dualMap '' Set.range fun s : σ => (LinearMap.proj s : (σ → ℂ) →ₗ[ℂ] ℂ) := by
      rw [← Set.range_comp]; rfl
    rw [hr, Submodule.span_image, hproj, Submodule.map_top, LinearMap.range_dualMap_eq_dualAnnihilator_ker,
      LinearMap.ker_eq_bot.2 hL, Submodule.dualAnnihilator_bot]
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent ℂ (Set.range f)
  have : Finite b := hli.finite
  let _ : Fintype b := Fintype.ofFinite b
  have hbtop : Submodule.span ℂ b = ⊤ := hspan.trans htop
  let a : b → σ := fun k => (hb k.2).choose
  have ha : ∀ k : b, f (a k) = k := fun k => (hb k.2).choose_spec
  refine ⟨b, inferInstance, a, ?_, ?_⟩
  · have B := Module.Basis.mk hli (by rw [Subtype.range_coe, hbtop])
    rw [← Module.finrank_eq_card_basis B, Subspace.dual_finrank_eq]
  · let T : E →ₗ[ℂ] (b → ℂ) := LinearMap.pi fun k => (k : Module.Dual ℂ E)
    have hT : ∀ x, T x = fun k => L x (a k) := by
      intro x; funext k
      show (k : Module.Dual ℂ E) x = L x (a k)
      rw [← ha k]; rfl
    have hinj : Function.Injective T := by
      refine (injective_iff_map_eq_zero T).2 fun x hx => ?_
      have h0 : ∀ φ : Module.Dual ℂ E, φ x = 0 := by
        intro φ
        have hφ : φ ∈ Submodule.span ℂ b := hbtop ▸ Submodule.mem_top
        induction hφ using Submodule.span_induction with
        | mem ψ hψ => exact congrFun hx ⟨ψ, hψ⟩
        | zero => rfl
        | add ψ χ _ _ h1 h2 => rw [LinearMap.add_apply, h1, h2, add_zero]
        | smul c ψ _ h => rw [LinearMap.smul_apply, h, smul_zero]
      exact (Module.forall_dual_apply_eq_zero_iff ℂ x).1 h0
    have hsurjT : Function.Surjective T := by
      refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj
      have B := Module.Basis.mk hli (by rw [Subtype.range_coe, hbtop])
      rw [Module.finrank_fintype_fun_eq_card, ← Module.finrank_eq_card_basis B, Subspace.dual_finrank_eq]
    intro y
    obtain ⟨x, hx⟩ := hsurjT y
    exact ⟨x, (hT x).symm.trans hx⟩

theorem eq_zero_of_eventually {κ : Type} [Fintype κ] (q : MvPolynomial κ ℤ) (u : κ → ℂ)
    (h : ∀ᶠ v in 𝓝 u, aeval v q = 0) : q = 0 := by
  classical
  have he : ∀ v, aeval v q = eval v (MvPolynomial.map (Int.castRingHom ℂ) q) := by
    intro v
    rw [MvPolynomial.eval_map, MvPolynomial.aeval_def,
      Subsingleton.elim (algebraMap ℤ ℂ) (Int.castRingHom ℂ)]
  have han := AnalyticOnNhd.eval_continuousLinearMap (ContinuousLinearMap.id ℂ (κ → ℂ))
    (MvPolynomial.map (Int.castRingHom ℂ) q)
  have hz : ∀ v, eval v (MvPolynomial.map (Int.castRingHom ℂ) q) = 0 := by
    intro v
    have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ u)
      (h.mono fun w hw => by
        show eval w (MvPolynomial.map (Int.castRingHom ℂ) q) = 0
        rw [← he]; exact hw) (Set.mem_univ v)
    simpa using this
  have hp0 : MvPolynomial.map (Int.castRingHom ℂ) q = MvPolynomial.map (Int.castRingHom ℂ) 0 :=
    MvPolynomial.funext fun v => by rw [hz v, map_zero, map_zero]
  exact MvPolynomial.map_injective _ Int.cast_injective hp0

theorem not_eventually_zero {σ : Type} [Fintype σ] {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (P : Ideal (MvPolynomial σ ℤ)) [P.IsPrime]
    (hP : Algebra.trdeg ℤ (MvPolynomial σ ℤ ⧸ P) ≤ (Module.finrank ℂ E : Cardinal))
    (Γ : E → σ → ℂ) (w₀ : E) (L : E →L[ℂ] (σ → ℂ)) (hΓ : HasStrictFDerivAt Γ L w₀) (hL : Function.Injective L)
    (hv : ∀ f ∈ P, ∀ᶠ w in 𝓝 w₀, aeval (Γ w) f = 0) (g : MvPolynomial σ ℤ) (hg : g ∉ P) :
    ¬ ∀ᶠ w in 𝓝 w₀, aeval (Γ w) g = 0 := by
  classical
  intro hg0
  obtain ⟨κ, _, a, hcard, hsurj⟩ := exists_coords L.toLinearMap hL
  let Pa : (σ → ℂ) →L[ℂ] (κ → ℂ) := ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (a k)
  have hφ : HasStrictFDerivAt (fun w => fun k => Γ w (a k)) (Pa.comp L) w₀ :=
    Pa.hasStrictFDerivAt.comp w₀ hΓ
  have hrange : (Pa.comp L).range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hmap := hφ.map_nhds_eq_of_surj hrange
  have htr : ∀ q : MvPolynomial κ ℤ, (∀ᶠ w in 𝓝 w₀, aeval (Γ w) (rename a q) = 0) → q = 0 := by
    intro q hq
    refine eq_zero_of_eventually q (fun k => Γ w₀ (a k)) ?_
    rw [← hmap, Filter.eventually_map]
    exact hq.mono fun w hw => by rw [aeval_rename] at hw; exact hw
  let x : κ → MvPolynomial σ ℤ ⧸ P := fun k => Ideal.Quotient.mk P (X (a k))
  have hx : ∀ q : MvPolynomial κ ℤ, aeval x q = Ideal.Quotient.mk P (rename a q) := by
    intro q
    have hh : (aeval x : MvPolynomial κ ℤ →ₐ[ℤ] MvPolynomial σ ℤ ⧸ P) =
        (Ideal.Quotient.mkₐ ℤ P).comp (rename a) := by
      ext k
      simp [x]
    rw [hh]
    rfl
  have hind : AlgebraicIndependent ℤ x := by
    rw [algebraicIndependent_iff_injective_aeval]
    refine (injective_iff_map_eq_zero _).2 fun q hq => htr q ?_
    rw [hx, Ideal.Quotient.eq_zero_iff_mem] at hq
    exact hv _ hq
  have hgbar : Ideal.Quotient.mk P g ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have htrans : Transcendental (Algebra.adjoin ℤ (Set.range x)) (Ideal.Quotient.mk P g) := by
    intro halg
    obtain ⟨r, hr0, t, ht⟩ := halg.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hgbar)
    have ht' : (r : MvPolynomial σ ℤ ⧸ P) = Ideal.Quotient.mk P g * t := ht
    have hr : (r : MvPolynomial σ ℤ ⧸ P) ∈ (aeval (R := ℤ) x).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval]
      exact r.2
    obtain ⟨q, hq⟩ := hr
    have hq' : aeval x q = (r : MvPolynomial σ ℤ ⧸ P) := hq
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective t
    have hmem : rename a q - g * h ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ← hx, hq', ht', sub_self]
    have hq0 : q = 0 := htr q (((hv _ hmem).and hg0).mono fun w hw => by
      have h1 := hw.1
      rw [map_sub, map_mul, hw.2, zero_mul, sub_zero] at h1
      exact h1)
    apply hr0
    rw [hq0, map_zero] at hq'
    exact Subtype.ext (by simpa using hq'.symm)
  have hc := ((hind.option_iff_transcendental _).2 htrans).cardinalMk_le_trdeg
  rw [Cardinal.mk_option, Cardinal.mk_fintype, hcard] at hc
  have hlt := hc.trans hP
  exact absurd hlt (by norm_cast; omega)

end SheetDecomposition.ChartAlg
end
end

section

noncomputable section

namespace SheetDecomposition.CovAlg

open Polynomial

def mon {R : Type} [CommRing R] {d : ℕ} (a : Fin d → R) : R[X] := X ^ d + ∑ j, C (a j) * X ^ (j : ℕ)

def low {R : Type} [CommRing R] {d : ℕ} (a : Fin d → R) : R[X] := ∑ j, C (a j) * X ^ (j : ℕ)

theorem mon_map {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (a : Fin d → R) (f : R →+* S) :
    (mon a).map f = mon fun j => f (a j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [mon, Polynomial.map_sum]

theorem eval₂_low {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (a : Fin d → R) (f : R →+* S) (x : S) :
    eval₂ f x (low a) = ∑ j, f (a j) * x ^ (j : ℕ) := by
  simp [low, eval₂_finsetSum]

theorem mon_monic {R : Type} [CommRing R] {d : ℕ} (a : Fin d → R) : (mon a).Monic :=
  monic_X_pow_add (degree_sum_fin_lt a)

theorem exists_prim (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω] [Algebra Ω₀ Ω] (d : ℕ) (hd : 0 < d)
    (hfin : Module.finrank Ω₀ Ω = d) {σ : Type} [Fintype σ] (t : σ → Ω)
    (ht : Algebra.adjoin Ω₀ (Set.range t) = ⊤) (γ : Ω) :
    ∃ (θ : Ω) (T : Set Ω₀), T.Finite ∧ ∀ (R : Type) [CommRing R] (i : R →+* Ω₀), Function.Injective i →
      T ⊆ Set.range i → ∃ (a : Fin d → R) (cf : σ → Fin d → R) (G : R[X]) (Q : MvPolynomial σ R),
        (mon a).Separable ∧ (∀ F : R[X], eval₂ ((algebraMap Ω₀ Ω).comp i) θ F = 0 ↔ mon a ∣ F) ∧
        (∀ s, eval₂ ((algebraMap Ω₀ Ω).comp i) θ (low (cf s)) = t s) ∧
        eval₂ ((algebraMap Ω₀ Ω).comp i) θ G = γ ∧ MvPolynomial.eval₂ ((algebraMap Ω₀ Ω).comp i) t Q = θ := by
  classical
  haveI : FiniteDimensional Ω₀ Ω := Module.finite_of_finrank_pos (hfin ▸ hd)
  haveI : CharZero Ω₀ := (algebraMap Ω₀ Ω).charZero
  let pb := Field.powerBasisOfFiniteOfSeparable Ω₀ Ω
  obtain rfl : pb.dim = d := pb.finrank.symm.trans hfin
  have hint : IsIntegral Ω₀ pb.gen := pb.isIntegral_gen
  let a₀ : Fin pb.dim → Ω₀ := fun j => (minpoly Ω₀ pb.gen).coeff j
  have hP : mon a₀ = minpoly Ω₀ pb.gen := by
    conv_rhs => rw [(minpoly.monic hint).as_sum, pb.natDegree_minpoly, Finset.sum_range]
    rfl
  let cf₀ : σ → Fin pb.dim → Ω₀ := fun s j => pb.basis.repr (t s) j
  have hcf : ∀ s, ∑ j, algebraMap Ω₀ Ω (cf₀ s j) * pb.gen ^ (j : ℕ) = t s := fun s => by
    conv_rhs => rw [← pb.basis.sum_repr (t s)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pb.basis_eq_pow, Algebra.smul_def]
  obtain ⟨G₀, hG₀⟩ := pb.exists_eq_aeval' γ
  obtain ⟨Q₀, hQ₀⟩ : ∃ Q₀ : MvPolynomial σ Ω₀, MvPolynomial.aeval t Q₀ = pb.gen := by
    have : pb.gen ∈ Algebra.adjoin Ω₀ (Set.range t) := ht ▸ Algebra.mem_top
    rw [Algebra.adjoin_range_eq_range_aeval] at this
    exact this
  obtain ⟨u₀, v₀, huv⟩ : (minpoly Ω₀ pb.gen).Separable := Algebra.IsSeparable.isSeparable Ω₀ pb.gen
  refine ⟨pb.gen, Set.range a₀ ∪ Set.range (fun q : σ × Fin pb.dim => cf₀ q.1 q.2) ∪ G₀.coeffs ∪ Q₀.coeffs ∪
    u₀.coeffs ∪ v₀.coeffs, by
      simp only [Set.finite_union, Set.finite_range, Finset.finite_toSet, and_self], ?_⟩
  intro R _ i hi hT
  simp only [Set.union_subset_iff] at hT
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hT
  choose a ha using fun j => h1 ⟨j, rfl⟩
  choose cf hcf' using fun s j => h2 ⟨(s, j), rfl⟩
  obtain ⟨G, hG⟩ := (mem_lifts _).1 ((lifts_iff_coeffs_subset_range _).2 h3)
  obtain ⟨u, hu⟩ := (mem_lifts _).1 ((lifts_iff_coeffs_subset_range _).2 h5)
  obtain ⟨v, hv⟩ := (mem_lifts _).1 ((lifts_iff_coeffs_subset_range _).2 h6)
  obtain ⟨Q, hQ⟩ := MvPolynomial.mem_range_map_iff_coeffs_subset.2 h4
  have hm : (mon a).map i = minpoly Ω₀ pb.gen := by
    rw [mon_map, ← hP]
    exact congrArg mon (funext ha)
  have hev : ∀ F : R[X], eval₂ ((algebraMap Ω₀ Ω).comp i) pb.gen F = aeval pb.gen (F.map i) := fun F => by
    rw [aeval_def, eval₂_map]
  refine ⟨a, cf, G, Q, ⟨u, v, ?_⟩, fun F => ?_, fun s => ?_, ?_, ?_⟩
  · apply map_injective i hi
    rw [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_mul, ← derivative_map, hm, hu, hv, huv,
      Polynomial.map_one]
  · rw [hev, ← map_dvd_map i hi (mon_monic a), hm, minpoly.dvd_iff]
  · rw [eval₂_low, ← hcf s]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [RingHom.comp_apply, hcf']
  · rw [hev, hG, hG₀]
  · rw [← MvPolynomial.eval₂_map, hQ, ← hQ₀, MvPolynomial.aeval_def]

end SheetDecomposition.CovAlg
end
end
