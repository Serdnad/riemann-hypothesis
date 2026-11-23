module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Flat.Basic
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.ModEq
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle001
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalRing.Module

@[expose] public section

section

namespace GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj

open GlobalTheory.CompanionTheory.Ar.Num TensorProduct

variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {R : Subalgebra o Ω}
  {E : Type*} [AddCommGroup E] [Module Ω E]

theorem exists_pow_cover {k : ℕ} (f c : Fin k → R) (h : ∑ l, c l * f l = 1) (n : ℕ) :
    ∃ d : Fin k → R, ∑ l, d l * f l ^ n = 1 := by
  have h1 : Ideal.span (Set.range f) = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← h]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)
  have h2 := Ideal.span_pow_eq_top _ h1 n
  rw [← Set.range_comp, Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun] at h2
  exact h2

theorem exists_charts {r : ℕ} {L : Submodule R E} (h : LocFree R r L.toAddSubgroup) :
    ∃ (k : ℕ) (f c : Fin k → R) (B : Fin k → Module.Basis (Fin r) Ω E), ∑ l, c l * f l = 1 ∧
      (∀ l q, ∃ n : ℕ, (f l : Ω) ^ n • B l q ∈ L) ∧
      ∀ l q, ∀ e ∈ L, ∃ n : ℕ, (f l : Ω) ^ n * (B l).repr e q ∈ R := by
  classical
  obtain ⟨-, k, f, c, hf, hc, hs, hb⟩ := h
  choose b hli hsp hiff using hb
  refine ⟨k, fun l => ⟨f l, hf l⟩, fun l => ⟨c l, hc l⟩,
    fun l => Module.Basis.mk (hli l) (hsp l).ge, ?_, ?_, ?_⟩
  · apply Subtype.ext
    simpa using hs
  · intro l q
    rw [Module.Basis.mk_apply]
    refine (hiff l (b l q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩
    · by_cases hq : q' = q
      · subst hq; simp
      · simp [hq]
    · simp [Pi.single_apply]
  · intro l q e he
    obtain ⟨a, ha, rfl⟩ := (hiff l e).1 ⟨0, by simpa using he⟩
    obtain ⟨n, hn⟩ := ha q
    refine ⟨n, ?_⟩
    have : (Module.Basis.mk (hli l) (hsp l).ge).repr (∑ q, a q • b l q) q = a q := by
      have h2 : (∑ q, a q • b l q) = ∑ q, a q • (Module.Basis.mk (hli l) (hsp l).ge) q := by
        simp [Module.Basis.mk_apply]
      rw [h2, Module.Basis.repr_sum_self]
    rw [this]
    exact hn

theorem pow_smul_mem {L : Submodule R E} (f : R) {n m : ℕ} (hnm : n ≤ m) {e : E}
    (h : (f : Ω) ^ n • e ∈ L) : (f : Ω) ^ m • e ∈ L := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hnm
  have := L.smul_mem (f ^ j) h
  rw [pow_add, mul_smul]
  simpa [Subalgebra.smul_def] using this

theorem pow_mul_mem (f : R) {n m : ℕ} (hnm : n ≤ m) {a : Ω}
    (h : (f : Ω) ^ n * a ∈ R) : (f : Ω) ^ m * a ∈ R := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hnm
  rw [pow_add, mul_assoc]
  exact R.mul_mem (R.pow_mem f.2 j) h

theorem expand {k r : ℕ} (f d : Fin k → R) (B : Fin k → Module.Basis (Fin r) Ω E) (M N : ℕ)
    (hd : ∑ l, d l * f l ^ (M + N) = 1) (e : E) :
    ∑ i : Fin k × Fin r, ((d i.1 : Ω) * ((f i.1 : Ω) ^ M * (B i.1).repr e i.2)) •
      ((f i.1 : Ω) ^ N • B i.1 i.2) = e := by
  have hd' : ∑ l, (d l : Ω) * (f l : Ω) ^ (M + N) = 1 := by
    simpa using congrArg Subtype.val hd
  rw [Fintype.sum_prod_type]
  conv_rhs => rw [← one_smul Ω e, ← hd', Finset.sum_smul]
  refine Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← (B l).sum_repr e, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [smul_smul, smul_smul]
  congr 1
  ring

theorem exists_dualBasis {r : ℕ} {L : Submodule R E} (h : LocFree R r L.toAddSubgroup) :
    ∃ (k : ℕ) (φ : Fin k × Fin r → Module.Dual Ω E) (v : Fin k × Fin r → L),
      (∀ i, ∀ e ∈ L, φ i e ∈ R) ∧ ∀ e, ∑ i, φ i e • (v i : E) = e := by
  classical
  obtain ⟨k, f, c, B, hs, h1, h2⟩ := exists_charts h
  choose n hn using h1
  obtain ⟨N, hN⟩ : ∃ N, ∀ l q, n l q ≤ N := by
    obtain ⟨N, hN⟩ := (Set.finite_range fun i : Fin k × Fin r => n i.1 i.2).bddAbove
    exact ⟨N, fun l q => hN ⟨(l, q), rfl⟩⟩
  let v : Fin k × Fin r → L := fun i =>
    ⟨(f i.1 : Ω) ^ N • B i.1 i.2, pow_smul_mem _ (hN _ _) (hn _ _)⟩

  have hspan : ∀ e ∈ L, e ∈ Submodule.span R (Set.range fun i => (v i : E)) := by
    intro e he
    choose m hm using fun l q => h2 l q e he
    obtain ⟨M, hM⟩ := (Set.finite_range fun i : Fin k × Fin r => m i.1 i.2).bddAbove
    obtain ⟨d, hd⟩ := exists_pow_cover f c hs (M + N)
    rw [← expand f d B M N hd e]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hR : (d i.1 : Ω) * ((f i.1 : Ω) ^ M * (B i.1).repr e i.2) ∈ R :=
      R.mul_mem (d i.1).2 (pow_mul_mem _ (hM ⟨i, rfl⟩) (hm _ _))
    exact Submodule.smul_mem _ (⟨_, hR⟩ : R) (Submodule.subset_span ⟨i, rfl⟩)
  choose m hm using fun (i j : Fin k × Fin r) => h2 i.1 i.2 (v j) (v j).2
  obtain ⟨M, hM⟩ := (Set.finite_range fun i : (Fin k × Fin r) × (Fin k × Fin r) =>
    m i.1 i.2).bddAbove
  obtain ⟨d, hd⟩ := exists_pow_cover f c hs (M + N)
  refine ⟨k, fun i => ((d i.1 : Ω) * (f i.1 : Ω) ^ M) • (B i.1).coord i.2, v, ?_, ?_⟩
  · intro i e he
    have he' := hspan e he
    clear he
    induction he' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      have := R.mul_mem (d i.1).2 (pow_mul_mem _ (hM ⟨(i, j), rfl⟩) (hm i j))
      simpa [mul_assoc] using this
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact R.add_mem hx hy
    | smul a x _ hx =>
      rw [Subalgebra.smul_def, map_smul]
      exact R.mul_mem a.2 hx
  · intro e
    simpa [mul_assoc, v] using expand f d B M N hd e

section DualBasis

variable {ι : Type*} [Fintype ι] {L : Submodule R E} (φ : ι → Module.Dual Ω E) (v : ι → L)
  (hφ : ∀ i, ∀ e ∈ L, φ i e ∈ R) (hv : ∀ e, ∑ i, φ i e • (v i : E) = e)

include hφ hv

theorem sum_eq (x : L) : ∑ i, (⟨φ i x, hφ i x x.2⟩ : R) • v i = x := by
  apply Subtype.ext
  simpa [Subalgebra.smul_def] using hv x

theorem finite_projective : Module.Finite R L ∧ Module.Projective R L := by
  classical
  let s : L →ₗ[R] (ι → R) :=
    { toFun := fun x i => ⟨φ i x, hφ i x x.2⟩
      map_add' := fun x y => by ext i; simp
      map_smul' := fun a x => by ext i; simp [Subalgebra.smul_def] }
  let p : (ι → R) →ₗ[R] L := Fintype.linearCombination R v
  have hps : p ∘ₗ s = LinearMap.id := by
    ext1 x
    exact sum_eq φ v hφ hv x
  exact ⟨Module.Finite.of_surjective p fun x => ⟨s x, LinearMap.congr_fun hps x⟩,
    Module.Projective.of_split s p hps⟩

theorem isBaseChange : IsBaseChange Ω L.subtype := by
  let g : E →ₗ[Ω] Ω ⊗[R] L := ∑ i, (φ i).smulRight ((1 : Ω) ⊗ₜ[R] v i)
  have hg : ∀ e, g e = ∑ i, φ i e • ((1 : Ω) ⊗ₜ[R] v i) := by
    intro e
    simp [g]
  refine IsBaseChange.of_equiv (LinearEquiv.ofLinear (L.subtype.liftBaseChange Ω) g ?_ ?_) ?_
  · ext1 e
    simp [hg, hv]
  · ext x
    have : g x = (1 : Ω) ⊗ₜ[R] x := by
      rw [hg]
      conv_rhs => rw [← sum_eq φ v hφ hv x, tmul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [tmul_smul]
      rfl
    simpa using this
  · intro x
    simp

end DualBasis

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E : Type}
    [AddCommGroup E] [Module Ω E] (r : ℕ) (L : Submodule R E), LocFree R r L.toAddSubgroup →
      Module.Finite R L ∧ Module.Projective R L ∧ Module.finrank Ω E = r ∧
        IsBaseChange Ω L.subtype := by
  intro o Ω _ _ _ R E _ _ r L h
  obtain ⟨k, φ, v, hφ, hv⟩ := exists_dualBasis h
  refine ⟨(finite_projective φ v hφ hv).1, (finite_projective φ v hφ hv).2, ?_,
    isBaseChange φ v hφ hv⟩
  obtain ⟨k, f, c, B, hs, -⟩ := exists_charts h
  rcases k with _ | k
  · simp at hs
  · simpa using Module.finrank_eq_card_basis (B 0)

end GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj
end

section

namespace GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj

open GlobalTheory.CompanionTheory.Ar.Num TensorProduct

theorem exists_local_basis {R L : Type} [CommRing R] [IsDomain R] [AddCommGroup L] [Module R L]
    [Module.Finite R L] [Module.Projective R L] (p : Ideal R) [p.IsPrime] :
    ∃ (n : ℕ) (m : Fin n → L) (s : R), s ∉ p ∧ LinearIndependent R m ∧
      ∀ x : L, s • x ∈ Submodule.span R (Set.range m) := by
  classical
  let Rp := Localization.AtPrime p
  let Lp := LocalizedModule p.primeCompl L
  let f : L →ₗ[R] Lp := LocalizedModule.mkLinearMap p.primeCompl L
  haveI : Module.Free Rp Lp := Module.free_of_flat_of_isLocalRing
  let β := Module.finBasis Rp Lp
  choose ms hms using fun i => IsLocalizedModule.mk'_surjective p.primeCompl f (β i)
  let m : Fin (Module.finrank Rp Lp) → L := fun i => (ms i).1
  let u : Fin (Module.finrank Rp Lp) → Rpˣ := fun i => (IsLocalization.map_units Rp (ms i).2).unit
  have hβ : ∀ i, β.unitsSMul u i = f (m i) := by
    intro i
    rw [Module.Basis.unitsSMul_apply, ← hms i, Units.smul_def]
    simp only [u, IsUnit.unit_spec, algebraMap_smul, Function.uncurry]
    exact IsLocalizedModule.mk'_cancel' f _ _
  have hfun : (β.unitsSMul u : _ → Lp) = f ∘ m := funext hβ
  have hli : LinearIndependent R m := by
    have h1 : LinearIndependent Rp (f ∘ m) := hfun ▸ (β.unitsSMul u).linearIndependent
    have h2 : LinearIndependent R (f ∘ m) := h1.restrict_scalars' R
    exact h2.of_comp f
  have hsp : ∀ x : L, ∃ s : R, s ∉ p ∧ s • x ∈ Submodule.span R (Set.range m) := by
    intro x
    have h1 : f x ∈ (Submodule.span R (Set.range m)).localized' Rp p.primeCompl f := by
      rw [Submodule.localized'_span, ← Set.range_comp, ← hfun, (β.unitsSMul u).span_eq]
      trivial
    obtain ⟨y, hy, s, hs⟩ := (Submodule.mem_localized' _ _ _ _ _).1 h1
    rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, ← map_smul] at hs
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := p.primeCompl) hs
    refine ⟨(c * s : p.primeCompl), (c * s).2, ?_⟩
    rw [Submonoid.coe_mul, mul_smul, ← Submonoid.smul_def, ← hc]
    exact Submodule.smul_mem _ _ hy
  choose s hs hs' using hsp
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := R) (M := L)
  refine ⟨_, m, ∏ t ∈ T, s t, ?_, hli, ?_⟩
  · exact Submonoid.prod_mem p.primeCompl (fun t _ => hs t)
  · intro x
    have hx : x ∈ Submodule.span R (T : Set L) := hT ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem t ht =>
      rw [← Finset.prod_erase_mul T s ht, mul_smul]
      exact Submodule.smul_mem _ _ (hs' t)
    | zero => simp
    | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
    | smul a b _ hb => rw [smul_comm]; exact Submodule.smul_mem _ _ hb

theorem flat_field {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) :
    Module.Flat R Ω := by
  letI : Algebra (FractionRing R) Ω := FractionRing.liftAlgebra R Ω
  haveI : Module.Flat R (FractionRing R) := IsLocalization.flat _ (nonZeroDivisors R)
  haveI : Module.Free (FractionRing R) Ω := Module.Free.of_divisionRing _ _
  haveI : Module.Flat (FractionRing R) Ω := Module.Flat.of_free
  exact Module.Flat.trans R (FractionRing R) Ω

theorem exists_chart {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E : Type}
    [AddCommGroup E] [Module Ω E] (r : ℕ) (L : Submodule R E) [Module.Finite R L] [Module.Projective R L]
    (hr : Module.finrank Ω E = r) (hb : IsBaseChange Ω L.subtype) (p : Ideal R) [p.IsPrime] :
    ∃ s : R, s ∉ p ∧ ∃ b : Fin r → E, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
      ∀ e, (∃ n : ℕ, (s : Ω) ^ n • e ∈ L.toAddSubgroup) ↔
        ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, (s : Ω) ^ n * a q ∈ R) ∧ e = ∑ q, a q • b q := by
  classical
  obtain ⟨n, m, s, hs, hli, hsp⟩ := exists_local_basis (L := L) p
  haveI := flat_field R
  have hs0 : (s : Ω) ≠ 0 := fun h => hs (by
    have : s = 0 := Subtype.ext h
    rw [this]; exact p.zero_mem)
  let b : Fin n → E := fun i => (m i : E)
  have hli' : LinearIndependent Ω b := by
    have h1 := (Module.Flat.linearIndependent_one_tmul (S := Ω) hli).map' hb.equiv.toLinearMap
      (LinearEquiv.ker _)
    have hfun : b = (⇑hb.equiv.toLinearMap ∘ fun x => (1 : Ω) ⊗ₜ[R] m x) := by
      funext i
      simp [b, IsBaseChange.equiv_tmul]
    rw [hfun]
    exact h1
  have key : ∀ x : L, ∃ a : Fin n → R, (s : Ω) • (x : E) = ∑ q, (a q : Ω) • b q := by
    intro x
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (hsp x)
    refine ⟨a, ?_⟩
    have := congrArg (fun z : L => (z : E)) ha
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm
  have hspan : Submodule.span Ω (Set.range b) = ⊤ := by
    rw [eq_top_iff]
    intro e _
    induction e using hb.inductionOn with
    | tmul x =>
      obtain ⟨a, ha⟩ := key x
      rw [← Submodule.smul_mem_iff _ hs0]
      simp only [Submodule.subtype_apply]
      rw [ha]
      exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
    | smul c x hx => exact Submodule.smul_mem _ _ (hx trivial)
    | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
  have hn : n = r := by
    rw [← hr, Module.finrank_eq_card_basis (Module.Basis.mk hli' hspan.ge), Fintype.card_fin]
  subst hn
  refine ⟨s, hs, b, hli', hspan, fun e => ⟨?_, ?_⟩⟩
  · rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := key ⟨_, hk⟩
    refine ⟨fun q => ((s : Ω) ^ (k + 1))⁻¹ * a q, fun q => ⟨k + 1, ?_⟩, ?_⟩
    · rw [mul_inv_cancel_left₀ (pow_ne_zero _ hs0)]; exact (a q).2
    · simp only [mul_smul]
      rw [← Finset.smul_sum, ← ha, smul_smul, smul_smul, mul_assoc, ← pow_succ',
        inv_mul_cancel₀ (pow_ne_zero _ hs0), one_smul]
  · rintro ⟨a, ha, rfl⟩
    choose k hk using ha
    refine ⟨∑ q, k q, ?_⟩
    rw [Finset.smul_sum]
    refine L.toAddSubgroup.sum_mem fun q _ => ?_
    have h1 : (s : Ω) ^ (∑ q, k q) * a q ∈ R := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ q), pow_add, mul_assoc]
      exact R.mul_mem (R.pow_mem s.2 _) (hk q)
    rw [smul_smul]
    exact L.smul_mem (⟨_, h1⟩ : R) (m q).2

theorem locFree_of_projective : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E : Type} [AddCommGroup E] [Module Ω E] (r : ℕ) (L : Submodule R E), Module.Finite R L → Module.Projective R L → Module.finrank Ω E = r → IsBaseChange Ω L.subtype → LocFree R r L.toAddSubgroup := by
  intro o Ω _ _ _ R E _ _ r L _ _ hr hb
  classical
  refine ⟨fun a ha e he => L.smul_mem (⟨a, ha⟩ : R) he, ?_⟩
  let P : R → Prop := fun s => ∃ b : Fin r → E, LinearIndependent Ω b ∧
      Submodule.span Ω (Set.range b) = ⊤ ∧
      ∀ e, (∃ n : ℕ, (s : Ω) ^ n • e ∈ L.toAddSubgroup) ↔
        ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, (s : Ω) ^ n * a q ∈ R) ∧ e = ∑ q, a q • b q
  have htop : Ideal.span {s | P s} = ⊤ := by
    by_contra h
    obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨s, hs, hP⟩ := exists_chart R r L hr hb p
    exact hs (hle (Ideal.subset_span hP))
  have h1 : (1 : R) ∈ Submodule.span R {s | P s} := by
    change (1 : R) ∈ Ideal.span {s | P s}
    rw [htop]; trivial
  obtain ⟨k, c, g, hg⟩ := Submodule.mem_span_set'.1 h1
  refine ⟨k, fun l => ((g l : R) : Ω), fun l => (c l : Ω), fun l => (g l : R).2, fun l => (c l).2, ?_,
    fun l => (g l).2⟩
  have := congrArg (fun z : R => (z : Ω)) hg
  simpa using this

end GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Crv.DegEquiv

open GlobalTheory.CompanionTheory.Ar.Crv

variable {K : Type} [Field K] (C : ACurve K) {V : Type} [AddCommGroup V] [Module K V]
  {V' : Type} [AddCommGroup V'] [Module K V']

def tr (e : V ≃ₗ[K] V') (b : Module.Basis (Fin (Module.finrank K V)) K V) :
    Module.Basis (Fin (Module.finrank K V')) K V' :=
  (b.map e).reindex (finCongr e.finrank_eq)

theorem isLatOf_tr (e : V ≃ₗ[K] V') {i : C.I} {b : Module.Basis (Fin (Module.finrank K V)) K V}
    {L : AddSubgroup V} {L' : AddSubgroup V'} (hb : IsLatOf C i b L)
    (h : ∀ x, x ∈ L ↔ e x ∈ L') : IsLatOf C i (tr e b) L' := by
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [← h, hb]
  simp only [tr, Module.Basis.repr_reindex_apply, Module.Basis.map_repr, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]
  exact ⟨fun H q => H _, fun H q => by simpa using H (finCongr e.finrank_eq q)⟩

theorem det_tr (e : V ≃ₗ[K] V') (a b : Module.Basis (Fin (Module.finrank K V)) K V) :
    (tr e a).det (tr e b) = a.det b := by
  unfold tr
  rw [Module.Basis.coe_reindex, Module.Basis.det_reindex, Module.Basis.det_map]
  congr 1
  funext i
  simp

theorem deg_equiv : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (e : V ≃ₗ[K] V'),
    IsBun C L → (∀ i x, x ∈ L i ↔ e x ∈ L' i) → IsBun C L' ∧ deg C L' = deg C L := by
  intro K _ C V _ _ _ V' _ _ _ L L' e ⟨hl, b0, hb0⟩ h
  choose b hb using hl
  have hb' : ∀ i, IsLatOf C i (tr e (b i)) (L' i) := fun i => isLatOf_tr C e (hb i) (h i)
  refine ⟨⟨fun i => ⟨_, hb' i⟩, tr e b0,
    hb0.subset fun i hi hc => hi (isLatOf_tr C e hc (h i))⟩, ?_⟩
  rw [Inhab.deg_eq C _ hb', Inhab.deg_eq C _ hb]
  set c := (Module.finBasis K V').det (tr e (Module.finBasis K V)) with hc
  have hc0 : c ≠ 0 := ((Module.finBasis K V').isUnit_det _).ne_zero
  have hd0 : ∀ i, (Module.finBasis K V).det (b i) ≠ 0 := fun i =>
    ((Module.finBasis K V).isUnit_det _).ne_zero
  have h1 : ∀ i, (C.w i : ℤ) * WithZero.log (C.v i ((Module.finBasis K V').det (tr e (b i)))) =
      (C.w i : ℤ) * WithZero.log (C.v i c) +
        (C.w i : ℤ) * WithZero.log (C.v i ((Module.finBasis K V).det (b i))) := by
    intro i
    rw [← Module.Basis.det_mul_det _ (tr e (Module.finBasis K V)), det_tr, ← hc, map_mul,
      WithZero.log_mul ((Valuation.ne_zero_iff _).2 hc0) ((Valuation.ne_zero_iff _).2 (hd0 i)),
      mul_add]
  simp only [h1]
  rw [finsum_add_distrib, C.prod c hc0, zero_add]
  · exact (C.fin c hc0).subset fun i hi h1 => hi (by simp [h1])
  · refine (hb0.union (C.fin _ ((Module.finBasis K V).isUnit_det b0).ne_zero)).subset
      fun i hi => ?_
    by_contra hn
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hn
    apply hi
    show (C.w i : ℤ) * WithZero.log (C.v i ((Module.finBasis K V).det (b i))) = 0
    rw [← Module.Basis.det_mul_det _ b0, map_mul, hn.2, Inhab.v_det C hn.1 (hb i)]
    simp

end GlobalTheory.CompanionTheory.Ar.Crv.DegEquiv
end
end

section

open scoped Matrix TensorProduct
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem frobeniusChain_carry : ∀ (p f : ℕ), 2 ≤ p → 0 < f → ∀ (y : ℕ → NNReal), (∀ n, y (n + f) = y n) → (∀ n, y n ≤ 1) → (∀ n, y n ^ p ≤ y (n + 1)) → ∀ (e : Fin f → ℕ) (j : ℕ), 2 ≤ ∑ n, e n → (∑ n : Fin f, e n * p ^ (n : ℕ)) ≡ p ^ (j + 1) [MOD (p ^ f - 1)] → ∏ n : Fin f, y n ^ e n ≤ y j ^ p :=
  PositivityTheory.HtPt.Ra.carry

end GlobalTheory.CompanionTheory.Ar.GR
end

section


theorem _root_.GlobalTheory.T.telescoping_coordinate_difference : ∀ (α : Type) (n : ℕ) (F : (Fin n → α) → ℝ) (a b : Fin n → α), F a - F b = ∑ i : Fin n, (F (fun j => if j < i then b j else a j) - F (fun j => if j ≤ i then b j else a j)) := by
  first | exact @GlobalTheory.CompanionTheory.Telescope.telescope_fin_positions | exact GlobalTheory.CompanionTheory.Telescope.telescope_fin_positions | (intros; apply GlobalTheory.CompanionTheory.Telescope.telescope_fin_positions <;> assumption)
end
