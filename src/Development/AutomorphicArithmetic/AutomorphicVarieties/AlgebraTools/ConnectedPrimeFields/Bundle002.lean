module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
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
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.RingTheory.Regular.Flat
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
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.RingTheory.Filtration
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.KrullDimension.Module

@[expose] public section

section

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem formsAR_embed {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.IsTorsionFree R M] :
    ∃ (ι : Type) (_ : Fintype ι) (f : M →ₗ[R] (ι → R)), Function.Injective f := by
  classical
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  obtain ⟨I, indepI, hI⟩ := exists_maximal_linearIndepOn R s
  have indepI' : LinearIndependent R (fun x : I => s x) := indepI
  let N := Submodule.span R (Set.range fun x : I => s x)
  let b : Module.Basis I R N := Module.Basis.span indepI'
  have exists_a : ∀ i, ∃ a : R, a ≠ 0 ∧ a • s i ∈ N := by
    intro i
    by_cases hi : i ∈ I
    · refine ⟨1, one_ne_zero, ?_⟩
      rw [one_smul]
      exact Submodule.subset_span (Set.mem_range_self (⟨i, hi⟩ : I))
    · obtain ⟨a, ha, ha'⟩ := hI i hi
      refine ⟨a, ha, ?_⟩
      rwa [Set.image_eq_range s I] at ha'
  choose a ha ha' using exists_a
  have hA : (∏ i, a i) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    exact fun i _ => ha i
  let φ : M →ₗ[R] M := LinearMap.lsmul R M (∏ i, a i)
  have hφ : Function.Injective φ := LinearMap.ker_eq_bot.mp (LinearMap.ker_lsmul hA)
  have hle : LinearMap.range φ ≤ N := by
    suffices ∀ i, φ (s i) ∈ N by
      rw [LinearMap.range_eq_map, ← hs, Submodule.map_span_le]
      rintro _ ⟨i, rfl⟩
      apply this
    intro i
    have h1 := N.smul_mem (∏ j ∈ {i}ᶜ, a j) (ha' i)
    rw [← mul_smul, ← Fintype.prod_eq_prod_compl_mul i] at h1
    exact h1
  refine ⟨I, inferInstance,
    b.equivFun.toLinearMap ∘ₗ φ.codRestrict N (fun x => hle ⟨x, rfl⟩), ?_⟩
  intro x y h
  have h2 := b.equivFun.injective h
  exact hφ (congrArg Subtype.val h2)

private theorem formsAR_pi {R ι : Type} [CommRing R] [Fintype ι] (J : Ideal R) (x : ι → R)
    (hx : ∀ i, x i ∈ J) : x ∈ J • (⊤ : Submodule R (ι → R)) := by
  classical
  have : x = ∑ i, x i • (Pi.single i (1 : R) : ι → R) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) trivial

theorem UpperTheory.V.AlgebraTools.Conn.formsAR :
    ∀ {A M : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
      [Module.IsTorsionFree A M] (I : Ideal A), ∃ k : ℕ, ∀ (n : ℕ) (m : M),
        (∀ l : Module.Dual A M, l m ∈ I ^ (n + k)) → m ∈ I ^ n • (⊤ : Submodule A M) := by
  intro A M _ _ _ _ _ _ _ I
  obtain ⟨ι, _, f, hf⟩ := formsAR_embed (R := A) (M := M)
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.range f)
  refine ⟨k, fun n m hm => ?_⟩
  have h1 : f m ∈ I ^ (n + k) • (⊤ : Submodule A (ι → A)) ⊓ LinearMap.range f :=
    ⟨formsAR_pi _ _ fun i => hm ((LinearMap.proj i) ∘ₗ f), ⟨m, rfl⟩⟩
  rw [hk (n + k) (Nat.le_add_left k n), Nat.add_sub_cancel] at h1
  have h2 : f m ∈ I ^ n • LinearMap.range f := Submodule.smul_mono le_rfl inf_le_right h1
  rw [LinearMap.range_eq_map, ← Submodule.map_smul''] at h2
  obtain ⟨y, hy, hym⟩ := h2
  rw [← hf hym]
  exact hy
end

section

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.bidual :
    ∀ {A M : Type} [CommRing A] [IsDomain A] [AddCommGroup M] [Module A M] [Module.Finite A M]
      (a : Module.Dual A (Module.Dual A M)), ∃ (d : A) (r : M), d ≠ 0 ∧ ∀ l : Module.Dual A M, l r = d * a l := by
  intro A M _ _ _ _ _ a
  classical
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule A M).FG)
  let K := FractionRing A
  let ψ : Module.Dual A M → Option S → K := fun l o =>
    o.elim (algebraMap A K (a l)) (fun i => algebraMap A K (l (i : M)))
  have hψs : ∀ (p : A) l o, ψ (p • l) o = algebraMap A K p * ψ l o := by
    intro p l o
    cases o <;> simp [ψ]
  have hψa : ∀ l m o, ψ (l + m) o = ψ l o + ψ m o := by
    intro l m o
    cases o <;> simp [ψ]
  have hψ0 : ∀ o, ψ 0 o = 0 := by
    intro o
    cases o <;> simp [ψ]
  let v : Option S → K := fun j => if none = j then 1 else 0
  have key : ∀ w ∈ Submodule.span K (Set.range ψ),
      ∃ s : A, s ≠ 0 ∧ ∃ l, ∀ o, algebraMap A K s * w o = ψ l o := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      exact ⟨1, one_ne_zero, l, fun o => by simp⟩
    | zero =>
      exact ⟨1, one_ne_zero, 0, fun o => by simp [hψ0]⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, l, hl⟩ := hx
      obtain ⟨t, ht, m, hm⟩ := hy
      refine ⟨s * t, mul_ne_zero hs ht, t • l + s • m, fun o => ?_⟩
      rw [hψa, hψs, hψs, ← hl o, ← hm o, Pi.add_apply, map_mul]
      ring
    | smul c x _ hx =>
      obtain ⟨s, hs, l, hl⟩ := hx
      obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := A) c
      have hq0 : algebraMap A K q ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
      have hc : algebraMap A K q * (algebraMap A K p / algebraMap A K q) = algebraMap A K p :=
        mul_div_cancel₀ _ hq0
      refine ⟨q * s, mul_ne_zero (nonZeroDivisors.ne_zero hq) hs, p • l, fun o => ?_⟩
      rw [hψs, ← hl o, Pi.smul_apply, smul_eq_mul, map_mul]
      linear_combination (algebraMap A K s * x o) * hc
  have hv : v ∉ Submodule.span K (Set.range ψ) := by
    intro hmem
    obtain ⟨s, hs, l, hl⟩ := key v hmem
    have hl0 : l = 0 := by
      apply LinearMap.ext_on hS
      intro i hi
      have h := hl (some ⟨i, hi⟩)
      simp [v, ψ] at h
      rw [LinearMap.zero_apply]
      exact IsFractionRing.injective A K (by rw [map_zero]; exact h.symm)
    subst hl0
    have h := hl none
    simp [v, ψ] at h
    exact hs h
  obtain ⟨f, hf, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
  have hf0 : ∀ l, f (ψ l) = 0 := by
    intro l
    have h : f (ψ l) ∈ (Submodule.span K (Set.range ψ)).map f :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨l, rfl⟩)
    rw [hfW] at h
    exact (Submodule.mem_bot K).mp h
  let c : Option S → K := fun o => f (fun j => if o = j then 1 else 0)
  obtain ⟨Dn, hDc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A) c
  choose b hb using hDc
  have hD0 : algebraMap A K (Dn : A) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors Dn.2
  have hmain : ∀ l : Module.Dual A M, b none * a l + ∑ i : S, b (some i) * l i = 0 := by
    intro l
    have e : ∑ o, ψ l o * c o = 0 := by
      have h := hf0 l
      rw [LinearMap.pi_apply_eq_sum_univ f (ψ l)] at h
      simpa [c, smul_eq_mul] using h
    apply IsFractionRing.injective A K
    rw [map_zero]
    calc algebraMap A K (b none * a l + ∑ i : S, b (some i) * l i)
        = algebraMap A K (Dn : A) * ∑ o, ψ l o * c o := by

          rw [Fintype.sum_option, mul_add, Finset.mul_sum, map_add (f := _), map_mul, map_sum]
          congr 1
          · rw [hb, Algebra.smul_def]
            simp only [ψ, Option.elim_none]
            ring
          · refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [map_mul, hb, Algebra.smul_def]
            simp only [ψ, Option.elim_some]
            ring
      _ = 0 := by rw [e, mul_zero]
  refine ⟨b none, -(∑ i : S, b (some i) • (i : M)), ?_, ?_⟩
  · intro h0
    have h := hb none
    rw [h0, map_zero, Algebra.smul_def] at h
    exact hf ((mul_eq_zero.mp h.symm).resolve_left hD0)
  · intro l
    have h := hmain l

    rw [map_neg, map_sum]
    simp only [map_smul, smul_eq_mul]
    linear_combination -h
end

section

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem UpperTheory.V.AlgebraTools.Conn.drop_one {R : Type} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (I : Ideal R) (y : R) (hy : y ∈ maximalIdeal R)
    (hn : ∀ p ∈ I.minimalPrimes, y ∉ p) :
    ringKrullDim (R ⧸ (I ⊔ Ideal.span {y})) + 1 = ringKrullDim (R ⧸ I) := by
  have hy' : y ∈ (Module.annihilator R (R ⧸ I)).jacobson := by
    rw [Ideal.annihilator_quotient]
    exact (IsLocalRing.maximalIdeal_le_jacobson _) hy
  have hn' : ∀ p ∈ (Module.annihilator R (R ⧸ I)).minimalPrimes, y ∉ p := by
    rw [Ideal.annihilator_quotient]
    exact hn
  have key := Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_jacobson hn' hy'
  rw [Module.supportDim_quotient_eq_ringKrullDim] at key
  rw [← key, ← Module.supportDim_quotient_eq_ringKrullDim]
  have hs : Module.support R (R ⧸ (I ⊔ Ideal.span {y})) = Module.support R (QuotSMulTop y (R ⧸ I)) := by
    rw [Module.support_quotSMulTop, Module.support_eq_zeroLocus, Module.support_eq_zeroLocus,
      Ideal.annihilator_quotient, Ideal.annihilator_quotient, PrimeSpectrum.zeroLocus_sup,
      PrimeSpectrum.zeroLocus_span]
  simp only [Module.supportDim]
  rw [hs]

private theorem UpperTheory.V.AlgebraTools.Conn.max_notMem_minimalPrimes {R : Type} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (h : 0 < ringKrullDim (R ⧸ I)) : maximalIdeal R ∉ I.minimalPrimes := by
  intro hm
  rw [ringKrullDim_quotient, Order.krullDim_pos_iff] at h
  obtain ⟨a, b, hab⟩ := h
  have ha : I ≤ a.1.asIdeal := a.2
  have hma : maximalIdeal R ≤ a.1.asIdeal :=
    hm.2 ⟨a.1.isPrime, ha⟩ (IsLocalRing.le_maximalIdeal a.1.isPrime.ne_top)
  have hbm : b.1.asIdeal ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal b.1.isPrime.ne_top
  have hlt : a.1.asIdeal < b.1.asIdeal := hab
  exact absurd (hbm.trans hma) (not_le_of_gt hlt)

theorem UpperTheory.V.AlgebraTools.Conn.drop :
    ∀ {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra A R]
      [Algebra.IsIntegral A R] (S : Finset (Ideal R)), (∀ I ∈ S, 0 < ringKrullDim (R ⧸ I)) →
      ∃ x ∈ maximalIdeal A, ∀ I ∈ S, ringKrullDim (R ⧸ (I ⊔ Ideal.span {algebraMap A R x})) + 1 = ringKrullDim (R ⧸ I) := by
  intro A R _ _ _ _ _ _ _ S hS
  classical
  let T : Set (Ideal A) := ⋃ I ∈ S, (Ideal.comap (algebraMap A R)) '' I.minimalPrimes
  have hT : T.Finite := Set.Finite.biUnion S.finite_toSet
    (fun I _ => (Ideal.finite_minimalPrimes_of_isNoetherianRing R I).image _)
  have memT : ∀ q, q ∈ T ↔ ∃ I ∈ S, ∃ p ∈ I.minimalPrimes, Ideal.comap (algebraMap A R) p = q := by
    intro q
    simp only [T, Set.mem_iUnion, Set.mem_image, exists_prop]
  have hmA : Ideal.comap (algebraMap A R) (maximalIdeal R) = maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (maximalIdeal R))
  have hTprime : ∀ q ∈ T, q.IsPrime := by
    intro q hq
    obtain ⟨I, _, p, hp, rfl⟩ := (memT q).mp hq
    haveI := hp.1.1
    infer_instance
  have hnot : ¬ ∃ q ∈ hT.toFinset, maximalIdeal A ≤ id q := by
    rintro ⟨q, hq, hle⟩
    obtain ⟨I, hI, p, hp, rfl⟩ := (memT _).mp (hT.mem_toFinset.mp hq)
    haveI := hp.1.1
    have heq : maximalIdeal A = Ideal.comap (algebraMap A R) p :=
      (IsLocalRing.maximalIdeal.isMaximal A).eq_of_le Ideal.IsPrime.ne_top' hle
    haveI : (Ideal.comap (algebraMap A R) p).IsMaximal := heq ▸ IsLocalRing.maximalIdeal.isMaximal A
    have hpm : p = maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_of_isIntegral_of_isMaximal_under p this)
    exact UpperTheory.V.AlgebraTools.Conn.max_notMem_minimalPrimes I (hS I hI) (hpm ▸ hp)
  have hsub := (Ideal.subset_union_prime (s := hT.toFinset) (f := id) ⊥ ⊥
    (fun q hq _ _ => hTprime q (hT.mem_toFinset.mp hq)) (I := maximalIdeal A)).not.mpr hnot
  obtain ⟨x, hxm, hx⟩ := Set.not_subset.mp hsub
  refine ⟨x, hxm, fun I hI => UpperTheory.V.AlgebraTools.Conn.drop_one I _ ?_ ?_⟩
  · have hx' : x ∈ Ideal.comap (algebraMap A R) (maximalIdeal R) := hmA ▸ hxm
    exact hx'
  · intro p hp hxp
    apply hx
    simp only [Set.mem_iUnion, id]
    exact ⟨Ideal.comap (algebraMap A R) p, hT.mem_toFinset.mpr ((memT _).mpr ⟨I, hI, p, hp, rfl⟩), hxp⟩
end

section

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.cmFree :
    ∀ {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [Algebra A B] [Module.Finite A B]
      [Module.Free A B], ReciprocityTheory.CA.IsCM A → ReciprocityTheory.CA.IsCM B := by
  intro A B _ _ _ _ _ _ _ h
  obtain ⟨hN, n, hdim, rs, hlen, hmem, hreg⟩ := h
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have hm : (maximalIdeal B).comap (algebraMap A B) = maximalIdeal A :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal B))
  refine ⟨IsNoetherianRing.of_finite A B, n, ?_, rs.map (algebraMap A B), by simpa using hlen, ?_,
    hreg.of_faithfullyFlat⟩
  · rw [← hdim]
    exact ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hinj
  · intro r hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    have := hmem a ha
    rw [← hm] at this
    exact this
end
