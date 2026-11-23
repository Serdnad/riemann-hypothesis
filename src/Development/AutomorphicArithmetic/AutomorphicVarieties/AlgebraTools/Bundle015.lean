module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle004
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle005
public import Mathlib.Data.Matrix.Basis
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle007
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IrreducibleSpans.Burnside
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle008
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
public import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

@[expose] public section

section

open IsLocalRing UpperTheory.V.AlgebraTools

private theorem level_map {R : Type} [CommRing R] {p : Ideal R} {B : Type} [CommRing B]
    [IsLocalRing B] [Algebra R B] (h : IsCplAt R p B) (n : ℕ) {D : Type} [CommRing D]
    (g : R →+* D) (hu : ∀ s, s ∉ p → IsUnit (g s)) (hz : ∀ a, a ∈ p ^ n → g a = 0) :
    ∃ f : B →+* D, ∀ (b : B) (a s : R), s ∉ p →
      algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n → g s * f b = g a := by
  have hP := h.isPrime
  choose A S hS hAS using h.dense n
  have wd : ∀ (b : B) (a s a' s' : R), s ∉ p → s' ∉ p →
      algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n →
      algebraMap R B s' * b - algebraMap R B a' ∈ maximalIdeal B ^ n → g s * g a' = g s' * g a := by
    intro b a s a' s' _ hs' h1 h2
    have hm : algebraMap R B (s * a' - s' * a) ∈ maximalIdeal B ^ n := by
      have hid : algebraMap R B (s * a' - s' * a) = algebraMap R B s' *
          (algebraMap R B s * b - algebraMap R B a) - algebraMap R B s *
          (algebraMap R B s' * b - algebraMap R B a') := by
        simp only [map_sub, map_mul]
        ring
      rw [hid]
      exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)
    obtain ⟨t, ht, hta⟩ := h.strict n _ hm
    have h0 := hz _ hta
    rw [map_mul, (hu t ht).mul_right_eq_zero, map_sub, map_mul, map_mul, sub_eq_zero] at h0
    exact h0
  let F : B → D := fun b => ↑(hu _ (hS b)).unit⁻¹ * g (A b)
  have hF0 : ∀ b, g (S b) * F b = g (A b) := by
    intro b
    simp only [F, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
  have spec : ∀ (b : B) (a s : R), s ∉ p →
      algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n → g s * F b = g a := by
    intro b a s hs hb
    apply (hu _ (hS b)).mul_left_cancel
    rw [← mul_assoc, mul_comm (g (S b)), mul_assoc, hF0, wd b (A b) (S b) a s (hS b) hs (hAS b) hb]
  have eq_of : ∀ (b : B) (y : D) (a s : R), s ∉ p →
      algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n → g a = g s * y → F b = y := by
    intro b y a s hs hb hy
    exact (hu s hs).mul_left_cancel ((spec b a s hs hb).trans hy)
  have hprod : ∀ x y : B, S x * S y ∉ p := fun x y hm => (hP.mem_or_mem hm).elim (hS x) (hS y)
  refine ⟨{ toFun := F, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, spec⟩
  · refine eq_of 1 1 1 1 ?_ ?_ (by simp)
    · intro h1
      exact hP.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    · simp
  · intro x y
    refine eq_of (x * y) _ (A x * A y) (S x * S y) (hprod x y) ?_ ?_
    · have hid : algebraMap R B (S x * S y) * (x * y) - algebraMap R B (A x * A y) =
          algebraMap R B (S x) * x * (algebraMap R B (S y) * y - algebraMap R B (A y)) +
          algebraMap R B (A y) * (algebraMap R B (S x) * x - algebraMap R B (A x)) := by
        simp only [map_mul]
        ring
      rw [hid]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hAS y)) (Ideal.mul_mem_left _ _ (hAS x))
    · show g (A x * A y) = g (S x * S y) * (F x * F y)
      rw [map_mul, map_mul, ← hF0 x, ← hF0 y]
      ring
  · refine eq_of 0 0 0 1 ?_ ?_ (by simp)
    · intro h1
      exact hP.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    · simp
  · intro x y
    refine eq_of (x + y) _ (S y * A x + S x * A y) (S x * S y) (hprod x y) ?_ ?_
    · have hid : algebraMap R B (S x * S y) * (x + y) - algebraMap R B (S y * A x + S x * A y) =
          algebraMap R B (S y) * (algebraMap R B (S x) * x - algebraMap R B (A x)) +
          algebraMap R B (S x) * (algebraMap R B (S y) * y - algebraMap R B (A y)) := by
        simp only [map_mul, map_add (f := _)]
        ring
      rw [hid]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hAS x)) (Ideal.mul_mem_left _ _ (hAS y))
    · show g (S y * A x + S x * A y) = g (S x * S y) * (F x + F y)
      rw [map_add (f := _), map_mul, map_mul, map_mul, ← hF0 x, ← hF0 y]
      ring

theorem UpperTheory.V.AlgebraTools.IsCplAt.existsUnique_lift :
    ∀ (R : Type) [CommRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B], IsCplAt R p B →
      ∀ (C : Type) [CommRing C] [IsLocalRing C] [IsAdicComplete (maximalIdeal C) C] (φ : R →+* C),
      (maximalIdeal C).comap φ = p → ∃! ψ : B →+* C, ψ.comp (algebraMap R B) = φ := by
  intro R _ p B _ _ _ hB C _ _ _ φ hφ
  have hpI : ∀ n, ∀ a ∈ p ^ n, φ a ∈ maximalIdeal C ^ n := by
    intro n a ha
    have hle : Ideal.map φ p ≤ maximalIdeal C := by
      rw [← hφ]
      exact Ideal.map_comap_le
    have hmap : Ideal.map φ (p ^ n) ≤ maximalIdeal C ^ n := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono hle n
    exact hmap (Ideal.mem_map_of_mem φ ha)
  have hunit : ∀ s, s ∉ p → IsUnit (φ s) := by
    intro s hs
    by_contra hn
    apply hs
    rw [← hφ, Ideal.mem_comap]
    exact (IsLocalRing.mem_maximalIdeal _).2 hn
  let g : ∀ n, R →+* C ⧸ maximalIdeal C ^ n := fun n => (Ideal.Quotient.mk (maximalIdeal C ^ n)).comp φ
  have hu : ∀ n s, s ∉ p → IsUnit (g n s) := fun n s hs =>
    (hunit s hs).map (Ideal.Quotient.mk (maximalIdeal C ^ n))
  have hz : ∀ n a, a ∈ p ^ n → g n a = 0 := fun n a ha => Ideal.Quotient.eq_zero_iff_mem.2 (hpI n a ha)
  choose f hf using fun n => level_map hB n (g n) (hu n) (hz n)
  have lvl : ∀ n (k : B → C ⧸ maximalIdeal C ^ n), (∀ (b : B) (a s : R), s ∉ p →
      algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n → g n s * k b = g n a) →
      ∀ b, k b = f n b := by
    intro n k hk b
    obtain ⟨a, s, hs, hb⟩ := hB.dense n b
    exact (hu n s hs).mul_left_cancel ((hk b a s hs hb).trans (hf n b a s hs hb).symm)
  have compat : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (maximalIdeal C) hle).comp (f n) = f m := by
    intro m n hle
    ext b
    obtain ⟨a, s, hs, hb⟩ := hB.dense n b
    have hbm : algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ m :=
      Ideal.pow_le_pow_right hle hb
    apply (hu m s hs).mul_left_cancel
    show g m s * Ideal.Quotient.factorPow (maximalIdeal C) hle (f n b) = g m s * f m b
    rw [hf m b a s hs hbm]
    have hc := congrArg (Ideal.Quotient.factorPow (maximalIdeal C) hle) (hf n b a s hs hb)
    rw [map_mul] at hc
    have hg : ∀ x, Ideal.Quotient.factorPow (maximalIdeal C) hle (g n x) = g m x := by
      intro x
      simp [g]
    rw [hg, hg] at hc
    exact hc
  have h1p : (1 : R) ∉ p := fun h1 => hB.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hmk : ∀ n b, Ideal.Quotient.mk (maximalIdeal C ^ n)
      (IsAdicComplete.liftRingHom (maximalIdeal C) f compat b) = f n b :=
    fun n b => IsAdicComplete.mk_liftRingHom (maximalIdeal C) f compat n b
  refine ⟨IsAdicComplete.liftRingHom (maximalIdeal C) f compat, ?_, ?_⟩
  · apply DFunLike.coe_injective
    apply IsHausdorff.funext' (maximalIdeal C)
    intro n r
    rw [RingHom.comp_apply, hmk]
    apply (hu n 1 h1p).mul_left_cancel
    rw [hf n (algebraMap R B r) r 1 h1p (by simp), map_one, one_mul]
    rfl
  · intro ψ' hψ'
    apply IsAdicComplete.eq_liftRingHom (maximalIdeal C) f compat ψ'
    intro n
    ext b
    rw [RingHom.comp_apply]
    refine lvl n (fun b => Ideal.Quotient.mk (maximalIdeal C ^ n) (ψ' b)) ?_ b
    intro b a s hs hb
    have hmap : Ideal.map ψ' (maximalIdeal B ^ n) ≤ maximalIdeal C ^ n := by
      rw [← IsCplAt.map_pow_eq R p B hB n, Ideal.map_map, hψ', Ideal.map_le_iff_le_comap]
      intro c hc
      exact hpI n c hc
    have h0 := Ideal.Quotient.eq_zero_iff_mem.2 (hmap (Ideal.mem_map_of_mem _ hb))
    have e : ∀ x, ψ' (algebraMap R B x) = φ x := fun x => by rw [← RingHom.comp_apply, hψ']
    rw [map_sub, map_mul, e, e, map_sub, map_mul, sub_eq_zero] at h0
    exact h0
end

section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.IsCplAt.dvr :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (π : R), Prime π →
      ∀ (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B], IsCplAt R (Ideal.span {π}) B →
      ∃ _ : IsDomain B, IsDiscreteValuationRing B ∧ Irreducible (algebraMap R B π) := by
  intro R _ _ _ π hπ B _ _ _ h
  haveI : IsNoetherianRing B := h.noeth
  set f := algebraMap R B with hf
  have hm : maximalIdeal B = Ideal.span {f π} := by
    have h1 := UpperTheory.V.AlgebraTools.IsCplAt.map_pow_eq R _ B h 1
    simpa [Ideal.map_span] using h1.symm
  have hpow : ∀ n : ℕ, maximalIdeal B ^ n = Ideal.span {f π ^ n} := by
    intro n
    rw [hm, Ideal.span_singleton_pow]
  have hnil : ∀ n : ℕ, f π ^ n ≠ 0 := by
    intro n hn
    have hmem : f (π ^ n) ∈ maximalIdeal B ^ (n + 1) := by
      rw [map_pow, hn]
      exact zero_mem _
    obtain ⟨s, hs, hs'⟩ := h.strict (n + 1) (π ^ n) hmem
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hs'
    obtain ⟨t, ht⟩ := hs'
    apply hs
    rw [Ideal.mem_span_singleton]
    refine ⟨t, ?_⟩
    have hπn : π ^ n ≠ 0 := pow_ne_zero _ hπ.ne_zero
    apply mul_right_cancel₀ hπn
    rw [ht]
    ring
  have hK := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal B) (Ideal.IsMaximal.ne_top inferInstance)
  have hfac : ∀ x : B, x ≠ 0 → ∃ (k : ℕ) (u : B), IsUnit u ∧ x = f π ^ k * u := by
    intro x hx
    classical
    have hex : ∃ n : ℕ, x ∉ maximalIdeal B ^ n := by
      by_contra hc
      push_neg at hc
      apply hx
      have hin : x ∈ ⨅ i : ℕ, maximalIdeal B ^ i := Submodule.mem_iInf _ |>.mpr hc
      rw [hK] at hin
      exact (Submodule.mem_bot _).mp hin
    have hn : x ∉ maximalIdeal B ^ Nat.find hex := Nat.find_spec hex
    have n0 : Nat.find hex ≠ 0 := by
      intro h0
      apply hn
      rw [h0, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hxk : x ∈ maximalIdeal B ^ k := by
      by_contra hc
      have := Nat.find_min' hex hc
      omega
    rw [hpow, Ideal.mem_span_singleton'] at hxk
    obtain ⟨u, rfl⟩ := hxk
    refine ⟨k, u, ?_, by ring⟩
    by_contra hu
    apply hn
    have hum : u ∈ maximalIdeal B := (IsLocalRing.mem_maximalIdeal u).mpr hu
    rw [hm, Ideal.mem_span_singleton'] at hum
    obtain ⟨c, rfl⟩ := hum
    rw [hk, hpow, Ideal.mem_span_singleton']
    exact ⟨c, by ring⟩
  haveI : IsDomain B := by
    have hnzd : NoZeroDivisors B := ⟨fun {a b} hab => by
      by_contra hc
      push_neg at hc
      obtain ⟨i, u, hu, rfl⟩ := hfac a hc.1
      obtain ⟨j, v, hv, rfl⟩ := hfac b hc.2
      apply hnil (i + j)
      have hz : f π ^ (i + j) * (u * v) = 0 := by
        rw [← hab]
        ring
      exact (hu.mul hv).mul_left_eq_zero.mp hz⟩
    exact NoZeroDivisors.to_isDomain B
  have hirr : Irreducible (f π) :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal (f π) (by simpa using hnil 1) hm
  refine ⟨inferInstance, ?_, hirr⟩
  apply IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
  refine ⟨f π, hirr, fun {x} hx => ?_⟩
  obtain ⟨n, u, hu, rfl⟩ := hfac x hx
  exact ⟨n, hu.unit, by simp⟩
end

section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private def UpperTheory.V.AlgebraTools.spIdx (n d : ℕ) (hd : d = n + 1) :
    (Fin d × ∀ i : Fin n, Fin (n - i)) ≃ (∀ i : Fin (n + 1), Fin (n + 1 - i)) where
  toFun p := fun i => Fin.cases (motive := fun i : Fin (n + 1) => Fin (n + 1 - i))
    ⟨p.1, by have := p.1.2; simp; omega⟩
    (fun j => ⟨p.2 j, by have := (p.2 j).2; simp only [Fin.val_succ]; omega⟩) i
  invFun c := (⟨c 0, by have := (c 0).2; simp at this; omega⟩,
    fun j => ⟨c j.succ, by have := (c j.succ).2; simp only [Fin.val_succ] at this; omega⟩)
  left_inv p := by
    ext <;> rfl
  right_inv c := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private theorem UpperTheory.V.AlgebraTools.spCard (n : ℕ) :
    Fintype.card (∀ i : Fin n, Fin (n - i)) = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Fintype.card_congr (UpperTheory.V.AlgebraTools.spIdx n (n + 1) rfl), Fintype.card_prod,
      Fintype.card_fin, ih, Nat.factorial_succ]

theorem UpperTheory.V.AlgebraTools.splitAlg_basis :
    ∀ (n : ℕ) (R : Type) [CommRing R] (P : Polynomial R), P.Monic → P.natDegree = n →
      (∃ b : Module.Basis (∀ i : Fin n, Fin (n - i)) R (SplitAlg P n), ∀ c, b c = ∏ i, SplitAlg.root P n i ^ (c i : ℕ)) ∧
      Fintype.card (∀ i : Fin n, Fin (n - i)) = n.factorial := by
  intro n
  induction n with
  | zero =>
    intro R _ P hm hd
    refine ⟨?_, UpperTheory.V.AlgebraTools.spCard 0⟩
    have hP : P = 1 := Polynomial.eq_one_of_monic_natDegree_zero hm hd
    let f : SplitAlg P 0 →ₐ[R] R :=
      SplitAlg.lift P 0 (A := R) (fun i => i.elim0) (by simp [hP])
    have hfg : (Algebra.ofId R (SplitAlg P 0)).comp f = AlgHom.id R _ :=
      SplitAlg.hom_ext P 0 (fun i => i.elim0)
    have hgf : f.comp (Algebra.ofId R (SplitAlg P 0)) = AlgHom.id R R := Algebra.ext_id _ _ _
    let e : R ≃ₐ[R] SplitAlg P 0 := AlgEquiv.ofAlgHom (Algebra.ofId R _) f hfg hgf
    refine ⟨(Module.Basis.singleton (∀ i : Fin 0, Fin (0 - i)) R).map e.toLinearEquiv, fun c => ?_⟩
    simp [Module.Basis.singleton_apply]
  | succ n ih =>
    intro R _ P hm hd
    refine ⟨?_, UpperTheory.V.AlgebraTools.spCard (n + 1)⟩
    obtain ⟨inst1, inst2, h3, e, he⟩ := splitAlg_succ_equiv R n P hm hd
    have hroot : (Polynomial.map (algebraMap R (AdjoinRoot P)) P).IsRoot (AdjoinRoot.root P) := by
      rw [AdjoinRoot.algebraMap_eq]
      exact AdjoinRoot.isRoot_root P
    have hmul := (Polynomial.mul_divByMonic_eq_iff_isRoot).2 hroot
    have hQm : (Polynomial.map (algebraMap R (AdjoinRoot P)) P /ₘ
        (Polynomial.X - Polynomial.C (AdjoinRoot.root P))).Monic := by
      refine Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C (AdjoinRoot.root P)) ?_
      rw [hmul]
      exact hm.map _
    have hQd : (Polynomial.map (algebraMap R (AdjoinRoot P)) P /ₘ
        (Polynomial.X - Polynomial.C (AdjoinRoot.root P))).natDegree = n := by
      rcases subsingleton_or_nontrivial (AdjoinRoot P) with hs | hs
      · exfalso
        have hR : Nontrivial R := by
          rcases subsingleton_or_nontrivial R with hR | hR
          · rw [Subsingleton.elim P 0, Polynomial.natDegree_zero] at hd
            omega
          · exact hR
        have hne := (AdjoinRoot.powerBasis' hm).basis.ne_zero
          ⟨0, by rw [AdjoinRoot.powerBasis'_dim, hd]; omega⟩
        exact hne (Subsingleton.elim _ _)
      · rw [Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C _),
          hm.natDegree_map, hd, Polynomial.natDegree_X_sub_C]
        rfl
    obtain ⟨c, hc⟩ := (ih (AdjoinRoot P) _ hQm hQd).1
    let b := (AdjoinRoot.powerBasis' hm).basis.reindex
      (finCongr (by rw [AdjoinRoot.powerBasis'_dim, hd]))
    let c' := c.map e.symm.toLinearEquiv
    refine ⟨(b.smulTower c').reindex (UpperTheory.V.AlgebraTools.spIdx n (n + 1) rfl), fun k => ?_⟩
    rw [Module.Basis.reindex_apply, Module.Basis.smulTower_apply, Fin.prod_univ_succ]
    have hb : ∀ j, b j = AdjoinRoot.root P ^ (j : ℕ) := by
      intro j
      simp only [b, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, AdjoinRoot.powerBasis'_gen]
      rfl
    have hinv : ∀ i : Fin n, e.symm (SplitAlg.root _ n i) = SplitAlg.root P (n + 1) i.succ := by
      intro i
      rw [AlgEquiv.symm_apply_eq, he]
    simp only [c', Module.Basis.map_apply, hb, hc, Algebra.smul_def, map_pow, h3, map_prod,
      AlgEquiv.toLinearEquiv_apply, hinv]
    rfl
end

section

open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.vr_reduction :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (U : T.Units ι o) {F : Type} [CommRing F] [Algebra B F] (r : E →ₐ[B] Matrix ι ι F) (p q : ι), (∀ y, r (T.st y) = (r y)ᵀ) → (∀ i, r (U.x i) = single (o i) i 1) → (∀ y i j, o i ≠ o j → r y i j = 0) → (∀ y i j, algebraMap B F (U.vr p q y i j).ev = r y i j) ∧ (o p = p → o q = q → p ≠ q → (U.oddForm p q).red ≤ RingHom.ker (algebraMap B F)) := by
  intro B E _ _ _ T ι _ _ o U F _ _ r p q hst hx hr
  obtain ⟨-, -, h3, h4, h5, -, h7⟩ := units_basic T o U
  have hep : ∀ k, r (U.ep (o k)) = Matrix.single (o k) (o k) 1 := by
    intro k
    rw [← U.x_base k, hx, U.o_o]
  have hz : ∀ w i j, r (U.x i * w * T.st (U.x j)) = Matrix.single (o i) (o j) (r w i j) := by
    intro w i j
    rw [map_mul, map_mul, hst, hx, hx, Matrix.transpose_single, Matrix.single_mul_mul_single, one_mul, mul_one]
  have key : ∀ w i j, algebraMap B F (T.tr (U.x i * w * T.st (U.x j))) = r w i j := by
    intro w i j
    by_cases hij : o i = o j
    · have e := congrArg (fun M => M (o i) (o j)) (hz w i j)
      simp only [Matrix.single_apply_same] at e
      rw [← e]
      conv_rhs => rw [h5 i j w hij, map_smul, hep i, ← hij]
      simp [Matrix.smul_apply, Algebra.smul_def]
    · rw [hr w i j hij, ← h7 i j w, h3 _ _ _ hij, map_zero]
  refine ⟨fun y i j => ?_, ?_⟩
  · show algebraMap B F (T.tr (U.x i * y * T.st (U.x j))) = _
    exact key y i j
  · intro hp hq hpq
    refine Ideal.span_le.mpr ?_
    rintro c ⟨b, b', rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    show algebraMap B F (T.tr ((b : E) * T.st (b' : E))) = 0
    obtain ⟨z, hz'⟩ := b.2
    have hb : r (b : E) = 0 := by
      rw [← hz']
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, map_mul]
      have hpp := hep p
      rw [hp] at hpp
      have hqq := hep q
      rw [hq] at hqq
      rw [hpp, hqq, ← mul_assoc, Matrix.single_mul_mul_single, hr z p q (by rw [hp, hq]; exact hpq)]
      simp

    rw [h4, map_sum]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [key, map_mul, hb, zero_mul, Matrix.zero_apply]
end

section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.isQuasiRegularSeq_of_tower :
    ∀ (R σ : Type) [CommRing R] [Finite σ] (y : σ → R) (M : Type) [AddCommGroup M] [Module R M] (P : ℕ → Type) [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)] (q : ∀ k, M →ₗ[R] P k),
      (∀ k, Function.Surjective (q k)) → (∀ k, LinearMap.ker (q k) = Ideal.span (Set.range y) ^ k • ⊤) →
      (∀ a k, a < k → QRegAt (P k) y ⊥ a) → GlobalTheory.IsQuasiRegularSeq M y := by
  intro R σ _ _ y M _ _ P _ _ q hs hk hq
  rw [isQuasiRegularSeq_iff_qRegAt]
  intro a c hc α
  simp only [sup_bot_eq] at hc ⊢
  have h := hq a (a + 1) (Nat.lt_succ_self a) (fun β => q (a + 1) (c β)) (by

    rw [← hk, LinearMap.mem_ker, map_sum] at hc
    simp only [map_smul] at hc
    rw [hc]
    exact zero_mem _) α
  simp only [sup_bot_eq] at h
  have htop : (⊤ : Submodule R (P (a + 1))) = Submodule.map (q (a + 1)) ⊤ := by
    rw [Submodule.map_top, LinearMap.range_eq_top.2 (hs _)]
  rw [htop, ← Submodule.map_smul''] at h
  have h2 : c α ∈ Submodule.comap (q (a + 1))
      (Submodule.map (q (a + 1)) (Ideal.span (Set.range y) • ⊤ : Submodule R M)) := h
  rw [Submodule.comap_map_eq, hk] at h2
  have hle : (Ideal.span (Set.range y) ^ (a + 1) • ⊤ : Submodule R M) ≤ Ideal.span (Set.range y) • ⊤ :=
    Submodule.smul_mono_left (Ideal.pow_le_self (Nat.succ_ne_zero a))
  rwa [sup_eq_left.2 hle] at h2
end

section

open Polynomial Matrix IsLocalRing TensorProduct

private theorem irreducible_of_span_eq_top {K G ι : Type} [Field K] [Fintype ι] [DecidableEq ι]
    (f : G → Matrix ι ι K) (h : Submodule.span K (Set.range f) = ⊤) (N : Submodule K (ι → K))
    (hN : ∀ g, ∀ v ∈ N, (f g).mulVec v ∈ N) : N = ⊥ ∨ N = ⊤ :=
  _root_.UpperTheory.Reformulated.B.IrreducibleOfSpanningMatrices.irreducible_of_span_eq_top f h N hN

private theorem span_map_ringHom_eq_top {k K G ι : Type} [Field k] [Field K] [Fintype ι] [DecidableEq ι]
    (φ : k →+* K) (f : G → Matrix ι ι k) (h : Submodule.span k (Set.range f) = ⊤) :
    Submodule.span K (Set.range fun g => (f g).map φ) = ⊤ :=
  _root_.UpperTheory.Reformulated.B.Qe1.span_map_ringHom_eq_top φ f h

theorem UpperTheory.V.AlgebraTools.irred_iff_span :
    ∀ {k K G : Type} [Field k] [IsAlgClosed k] [Field K] [Group G] {ι : Type} [Fintype ι] [DecidableEq ι] (φ : k →+* K) (ρ : G →* Matrix ι ι k), ((∀ N : Submodule k (ι → k), (∀ g, ∀ v ∈ N, (ρ g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤) ↔ Submodule.span k (Set.range ρ) = ⊤) ∧ (Submodule.span k (Set.range ρ) = ⊤ ↔ Submodule.span K (Set.range fun g => (ρ g).map φ) = ⊤) ∧ (Submodule.span K (Set.range fun g => (ρ g).map φ) = ⊤ → ∀ N : Submodule K (ι → K), (∀ g, ∀ v ∈ N, ((ρ g).map φ).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤) := by
  intro k K G _ _ _ _ ι _ _ φ ρ
  refine ⟨⟨KStar.Schema.span_eq_top_of_irreducible ρ, fun h N hN => irreducible_of_span_eq_top ρ h N hN⟩,
    ⟨span_map_ringHom_eq_top φ ρ, fun h => ?_⟩, fun h N hN => irreducible_of_span_eq_top _ h N hN⟩
  refine KStar.Schema.span_eq_top_of_residue φ ?_ _ ?_
  · rw [IsLocalRing.maximalIdeal_eq_bot]
    exact (RingHom.injective_iff_ker_eq_bot φ).mp φ.injective
  · rw [← Set.range_comp]
    exact h
end
