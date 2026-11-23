module

public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle174
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle086
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle117
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle142
public import Mathlib.RingTheory.Smooth.Basic
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle324
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle325
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.LocalRing.Module
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

section

open IsLocalRing



namespace GlobalTheory

open IsLocalRing in


open Polynomial in
private lemma maximalIdeal_eq_span_of_kummer_tower (A W : Type) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing W] [IsLocalRing W] (Φ : A →+* W) (ϖ : A) (u : Aˣ) (m k : ℕ)
    (hϖ : Irreducible ϖ) (hm : IsUnit (m : A)) (hk : 0 < k) (y τ : W) (hy : y ^ m = Φ u)
    (hτ : τ ^ k = Φ ϖ * y) (hτm : τ ∈ maximalIdeal W) (hτnz : τ ∈ nonZeroDivisors W)
    (hfrac : ∀ w : W, ∃ x z, x ∈ Subring.closure (Set.range Φ ∪ {τ}) ∧
      z ∈ Subring.closure (Set.range Φ ∪ {τ}) ∧ z ∈ nonZeroDivisors W ∧ z * w = x) :
    maximalIdeal W = Ideal.span {τ} := by
  obtain ⟨gB, hgB_of, hgB_root⟩ : ∃ gB : AdjoinRoot (X ^ m - C (u : A)) →+* W,
      (∀ a, gB (AdjoinRoot.of _ a) = Φ a) ∧ gB (AdjoinRoot.root _) = y :=
    ⟨AdjoinRoot.lift Φ y (by simp [hy]), fun a => AdjoinRoot.lift_of _, AdjoinRoot.lift_root _⟩
  obtain ⟨g, hg_of, hg_root⟩ : ∃ g : AdjoinRoot (X ^ k - C (AdjoinRoot.of (X ^ m - C (u : A)) ϖ *
        AdjoinRoot.root (X ^ m - C (u : A)))) →+* W,
      (∀ b, g (AdjoinRoot.of _ b) = gB b) ∧ g (AdjoinRoot.root _) = τ :=
    ⟨AdjoinRoot.lift gB τ (by simp [hgB_of, hgB_root, hτ]), fun b => AdjoinRoot.lift_of _,
      AdjoinRoot.lift_root _⟩
  haveI hn : (Ideal.comap g (maximalIdeal W)).IsPrime := Ideal.comap_isPrime g (maximalIdeal W)
  have hTn : AdjoinRoot.root (X ^ k - C (AdjoinRoot.of (X ^ m - C (u : A)) ϖ *
      AdjoinRoot.root (X ^ m - C (u : A)))) ∈ Ideal.comap g (maximalIdeal W) := by
    rw [Ideal.mem_comap, hg_root]
    exact hτm
  have hmaxV := _root_.GlobalTheory.maximalIdeal_localization_eq_span_of_reduced_artinian _ _ (_root_.GlobalTheory.kummerUnit_quotRoot_isReduced A ϖ u m k hϖ hm hk)
    (_root_.GlobalTheory.T.isArtinianRing_kummerAdjoinRoot_quotient_root A ϖ u m k hϖ hm hk) _ hTn
  haveI : IsNoetherianRing (AdjoinRoot (X ^ k - C (AdjoinRoot.of (X ^ m - C (u : A)) ϖ *
      AdjoinRoot.root (X ^ m - C (u : A))))) := inferInstance
  haveI : IsNoetherianRing (Localization.AtPrime (Ideal.comap g (maximalIdeal W))) :=
    IsLocalization.isNoetherianRing (Ideal.comap g (maximalIdeal W)).primeCompl _ inferInstance
  have hunit : ∀ s : (Ideal.comap g (maximalIdeal W)).primeCompl, IsUnit (g s) := by
    intro s
    by_contra h
    exact s.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
  have hlift := fun r => IsLocalization.lift_eq (M := (Ideal.comap g (maximalIdeal W)).primeCompl)
    (S := Localization.AtPrime (Ideal.comap g (maximalIdeal W))) hunit r
  obtain ⟨φ, hφ⟩ : ∃ φ : Localization.AtPrime (Ideal.comap g (maximalIdeal W)) →+* W,
      ∀ r, φ (algebraMap _ _ r) = g r := ⟨IsLocalization.lift hunit, hlift⟩
  have key := _root_.GlobalTheory.maximalIdeal_eq_span_map_of_fractions (Localization.AtPrime (Ideal.comap g (maximalIdeal W))) W φ _ hmaxV (by rw [hφ, hg_root]; exact hτm)
    (by rw [hφ, hg_root]; exact hτnz) ?_
  · rw [key, hφ, hg_root]
  intro w
  obtain ⟨x, z, hx, hz, hznz, hzw⟩ := hfrac w
  have hle : Subring.closure (Set.range Φ ∪ {τ}) ≤ φ.range := by
    rw [Subring.closure_le]
    refine Set.union_subset ?_ ?_
    · rintro _ ⟨a, rfl⟩
      exact ⟨algebraMap _ _ (AdjoinRoot.of _ (AdjoinRoot.of _ a)), by rw [hφ, hg_of, hgB_of]⟩
    · rintro _ rfl
      exact ⟨algebraMap _ _ (AdjoinRoot.root _), by rw [hφ, hg_root]⟩
  obtain ⟨x', rfl⟩ := hle hx
  obtain ⟨z', rfl⟩ := hle hz
  exact ⟨x', z', hznz, hzw⟩


open IsLocalRing in


theorem _root_.GlobalTheory.abhyankar_ramificationIdx_eq_one : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ e) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) →
    ∀ [IsDomain D] [IsDiscreteValuationRing D] (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal],
    Q.ramificationIdx D = 1 := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ π e D _ _ ⟨ψ⟩ hπ he hdiv _ _ _ Q _
  haveI : Q.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  haveI : IsDedekindDomain (integralClosure S L) := integralClosure.isDedekindDomain S K L
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h
      simp at he
    · exact h
  obtain ⟨ht, htnz⟩ := _root_.GlobalTheory.AbhyankarRootUnit.root_mem_maximalIdeal_and_mem_nonZeroDivisors S K L π e D ψ hπ he0 Q
  have hte : (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π))) ^ e = algebraMap S D π := by
    apply ψ.injective
    rw [map_pow, AlgEquiv.apply_symm_apply, AlgEquiv.commutes]
    have h := AdjoinRoot.eval₂_root (Polynomial.X ^ e - Polynomial.C π)
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at h
    rw [sub_eq_zero.1 h]
    rfl
  have htQ : algebraMap D (integralClosure D (TensorProduct S D L))
      (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π))) ∈ Q := by
    rw [IsScalarTower.algebraMap_apply D (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)] at ht
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q _).1 ht
  have hπO : algebraMap S (integralClosure S L) π ≠ 0 := by
    intro h
    have h1 : algebraMap S L π = 0 := by
      rw [IsScalarTower.algebraMap_apply S (integralClosure S L) L, h, map_zero]
    rw [IsScalarTower.algebraMap_apply S K L, map_eq_zero_iff _ (algebraMap K L).injective,
      IsFractionRing.to_map_eq_zero_iff] at h1
    exact hπ.ne_zero h1
  have hπP : algebraMap S (integralClosure S L) π ∈
      Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q := by
    rw [Ideal.mem_comap]
    have hpow : _root_.GlobalTheory.AbhyankarLocal.toNorm S L D (algebraMap S (integralClosure S L) π) =
        (algebraMap D (integralClosure D (TensorProduct S D L))
          (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π)))) ^ e := by
      apply Subtype.ext
      rw [_root_.GlobalTheory.AbhyankarLocal.toNorm_coe, ← map_pow, hte]
      change (1 : D) ⊗ₜ[S] (algebraMap S L π) = algebraMap D (TensorProduct S D L) (algebraMap S D π)
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one π,
        Algebra.algebraMap_eq_smul_one π, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        Algebra.algebraMap_self, RingHom.id_apply]
    rw [hpow]
    exact Ideal.pow_mem_of_mem Q htQ e he0
  haveI hPmax : (Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q).IsMaximal := by
    refine Ideal.IsPrime.isMaximal inferInstance ?_
    intro h
    rw [h] at hπP
    exact hπO hπP
  obtain ⟨ϖ, hϖ, u, hu⟩ := _root_.GlobalTheory.pi_eq_pow_ramificationIdx_mul_unit S K L π e D
    (Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q) hπ hπP
  obtain ⟨k, hk⟩ := hdiv _ hPmax
  obtain ⟨y, hym, hyk⟩ := _root_.GlobalTheory.AbhyankarLocal.exists_kummer_element S K L π e D ψ hπ he0 Q _ k ϖ u hk.symm hu
  have hP0 : Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q ≠ ⊥ := by
    intro h
    rw [h] at hπP
    exact hπO hπP
  haveI : IsDiscreteValuationRing
      (Localization.AtPrime (Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q)) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (integralClosure S L) hP0 _
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hk
      omega
    · exact h
  have hmu : IsUnit (((Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q).ramificationIdx S : ℕ) :
      Localization.AtPrime (Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q)) := by
    have h := he.map (algebraMap S
      (Localization.AtPrime (Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q)))
    rw [map_natCast, hk, Nat.cast_mul] at h
    exact isUnit_of_mul_isUnit_left h
  have hmax := maximalIdeal_eq_span_of_kummer_tower _ (Localization.AtPrime Q)
    (_root_.GlobalTheory.AbhyankarLocal.locHom Q) ϖ u _ k hϖ hmu hk0 y _ hym hyk ht htnz
    (_root_.GlobalTheory.AbhyankarLocal.exists_frac_closure S K L π e D ψ hπ he0 Q)
  have hunder : Ideal.under D Q = maximalIdeal D := by
    refine IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance ?_)
    intro h
    have h1 : ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π)) ∈ Ideal.under D Q := htQ
    rw [h, Ideal.mem_bot] at h1
    rw [h1, map_zero] at htnz
    exact zero_notMem_nonZeroDivisors htnz
  have hmapmax : Ideal.map (algebraMap D (Localization.AtPrime Q)) (Ideal.under D Q) =
      maximalIdeal (Localization.AtPrime Q) := by
    refine le_antisymm ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro d hd
      rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply D (integralClosure D (TensorProduct S D L))
        (Localization.AtPrime Q)]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q _).2 hd
    · rw [hmax, Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ htQ
  rw [Ideal.ramificationIdx_def, hmapmax,
    Module.length_eq_one_iff.2 (isSimpleModule_iff_isCoatom.2 (IsLocalRing.maximalIdeal.isMaximal _).out)]
  rfl

end GlobalTheory
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.PD



open TensorProduct in
theorem exists_notMem_smul_D_mem_span (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K)
    [IsFractionRing B K] [Algebra.Smooth k B] (d : ℕ) (hd : Module.finrank K Ω[K⁄k] = d)
    (P : Ideal B) [P.IsPrime] :
    ∃ (f : B) (u : Fin d → B), f ∉ P ∧
      ∀ v : B, f • D k B v ∈ Submodule.span B (Set.range fun j => D k B (u j)) := by
  haveI : Algebra.FormallyEtale B K := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors B)
  have hinj : Function.Injective (algebraMap B K) := IsFractionRing.injective B K
  haveI : FaithfulSMul B K := (faithfulSMul_iff_algebraMap_injective B K).2 hinj
  have hrk : Module.finrank B Ω[B⁄k] = d := by
    rw [← hd, (KaehlerDifferential.isBaseChange_of_formallyEtale k B K).finrank_eq]
  have hfib : Module.finrank P.ResidueField (P.ResidueField ⊗[B] Ω[B⁄k]) = d := by
    rw [← hrk]; exact Ideal.finrank_fiber_eq_finrank P

  let g : B → P.ResidueField ⊗[B] Ω[B⁄k] := fun v => (1 : P.ResidueField) ⊗ₜ D k B v
  have hg : Submodule.span P.ResidueField (Set.range g) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
    | tmul a m =>
      have h1 : (1 : P.ResidueField) ⊗ₜ[B] m ∈ Submodule.span P.ResidueField (Set.range g) := by
        have hm : m ∈ Submodule.span B (Set.range (D k B)) := by
          rw [KaehlerDifferential.span_range_derivation]; trivial
        induction hm using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨v, rfl⟩ := hy
          exact Submodule.subset_span ⟨v, rfl⟩
        | zero => rw [tmul_zero]; exact zero_mem _
        | add y z _ _ hy hz => rw [tmul_add]; exact add_mem hy hz
        | smul r y _ hy =>
          rw [tmul_smul, ← algebraMap_smul P.ResidueField r]
          exact Submodule.smul_mem _ _ hy
      have : a ⊗ₜ[B] m = a • ((1 : P.ResidueField) ⊗ₜ[B] m) := by
        rw [smul_tmul', smul_eq_mul, mul_one]
      rw [this]; exact Submodule.smul_mem _ _ h1
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent P.ResidueField (Set.range g)
  let bs : Module.Basis s P.ResidueField (P.ResidueField ⊗[B] Ω[B⁄k]) :=
    Module.Basis.mk hli (by rw [Subtype.range_coe, hspan, hg])
  haveI : Finite s := Module.Finite.finite_basis bs
  letI : Fintype s := Fintype.ofFinite s
  have hcard : Fintype.card s = d := by rw [← Module.finrank_eq_card_basis bs, hfib]
  let bF := bs.reindex (Fintype.equivFinOfCardEq hcard)
  have hu : ∀ j, ∃ v, g v = bF j := by
    intro j
    have : bF j ∈ s := by
      rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]; exact Subtype.prop _
    exact hs this
  choose u hu using hu

  let N : Submodule B Ω[B⁄k] := Submodule.span B (Set.range fun j => D k B (u j))
  let φ := (N.mkQ).baseChange P.ResidueField
  have hφ : φ = 0 := by
    refine bF.ext fun j => ?_
    rw [← hu j]
    simp only [φ, g, LinearMap.baseChange_tmul, LinearMap.zero_apply]
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).2 (Submodule.subset_span ⟨j, rfl⟩)]
    exact TensorProduct.tmul_zero _ _
  have hsub : Subsingleton (P.ResidueField ⊗[B] (Ω[B⁄k] ⧸ N)) := by
    have h0 : ∀ x : P.ResidueField ⊗[B] (Ω[B⁄k] ⧸ N), x = 0 := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => rfl
      | add x y hx hy => rw [hx, hy, add_zero]
      | tmul a q =>
        obtain ⟨m, rfl⟩ := N.mkQ_surjective q
        have := LinearMap.congr_fun hφ (a ⊗ₜ m)
        simpa only [φ, LinearMap.baseChange_tmul, LinearMap.zero_apply] using this
    exact ⟨fun x y => by rw [h0 x, h0 y]⟩
  have hnot : (⟨P, inferInstance⟩ : PrimeSpectrum B) ∉ Module.support B (Ω[B⁄k] ⧸ N) := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct, not_nontrivial_iff_subsingleton]
    exact hsub
  rw [Module.mem_support_iff_of_finite] at hnot
  obtain ⟨f, hf, hfP⟩ := Set.not_subset.1 hnot
  have hfN : ∀ v : B, f • D k B v ∈ N := fun v => by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact Module.mem_annihilator.1 hf _
  exact ⟨f, u, hfP, hfN⟩

end GlobalTheory.PD

namespace GlobalTheory.PD

theorem exists_local_dbasis (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K)
    [IsFractionRing B K] [Algebra.Smooth k B] (d : ℕ) (hd : Module.finrank K Ω[K⁄k] = d)
    (P : Ideal B) [P.IsPrime] :
    ∃ (f : B) (u : Fin d → B) (b : Module.Basis (Fin d) K Ω[K⁄k]), f ∉ P ∧ (∀ j, b j = D k K (u j : K)) ∧
      ∀ (v : B) (j : Fin d), ∃ c : B, (f : K) * b.repr (D k K (v : K)) j = c := by
  obtain ⟨f, u, hfP, hfN⟩ := exists_notMem_smul_D_mem_span k K B d hd P
  have hinj : Function.Injective (algebraMap B K) := IsFractionRing.injective B K
  have hf0 : (f : K) ≠ 0 := by
    intro h
    apply hfP
    have : f = 0 := hinj (by rw [map_zero]; exact h)
    rw [this]; exact P.zero_mem
  have hcoef : ∀ v : B, ∃ c : Fin d → B,
      (f : K) • D k K (v : K) = ∑ j, (c j : K) • D k K (u j : K) := by
    intro v
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun B).1 (hfN v)
    refine ⟨c, ?_⟩
    have := congrArg (KaehlerDifferential.map k k B K) hc

    simp only [map_sum, LinearMap.map_smul, KaehlerDifferential.map_D, Subalgebra.smul_def] at this
    exact this.symm
  let W : Submodule K Ω[K⁄k] := Submodule.span K (Set.range fun j => D k K (u j : K))
  have hB : ∀ v : B, D k K (v : K) ∈ W := by
    intro v
    obtain ⟨c, hc⟩ := hcoef v
    have h1 : (f : K) • D k K (v : K) ∈ W := by
      rw [hc]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have := Submodule.smul_mem W (f : K)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hf0, one_smul] at this
  have hK : ∀ w : K, D k K w ∈ W := by
    intro w
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := B) w
    have hy0 : algebraMap B K y ≠ 0 :=
      (map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hy)
    have hx : D k K (algebraMap B K x) = (algebraMap B K x / algebraMap B K y) • D k K (algebraMap B K y)
        + algebraMap B K y • D k K (algebraMap B K x / algebraMap B K y) := by
      conv_lhs => rw [show algebraMap B K x = algebraMap B K x / algebraMap B K y * algebraMap B K y by
        rw [div_mul_cancel₀ _ hy0]]
      rw [Derivation.leibniz, add_comm]
    have h2 : algebraMap B K y • D k K (algebraMap B K x / algebraMap B K y) ∈ W := by
      have e : algebraMap B K y • D k K (algebraMap B K x / algebraMap B K y) =
          D k K (algebraMap B K x) - (algebraMap B K x / algebraMap B K y) • D k K (algebraMap B K y) := by
        rw [hx]; abel
      rw [e]
      exact sub_mem (hB x) (Submodule.smul_mem _ _ (hB y))
    have := Submodule.smul_mem W (algebraMap B K y)⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ hy0, one_smul] at this
  have htop : ⊤ ≤ W := by
    rw [← KaehlerDifferential.span_range_derivation k K]
    exact Submodule.span_le.2 (Set.range_subset_iff.2 hK)
  let b := basisOfTopLeSpanOfCardEqFinrank (fun j => D k K (u j : K)) htop (by rw [Fintype.card_fin, hd])
  have hb : ∀ j, b j = D k K (u j : K) := fun j => by
    simp only [b, coe_basisOfTopLeSpanOfCardEqFinrank]
  refine ⟨f, u, b, hfP, hb, fun v j => ?_⟩
  obtain ⟨c, hc⟩ := hcoef v
  refine ⟨c j, ?_⟩
  have h3 : b.repr ((f : K) • D k K (v : K)) j = (c j : K) := by
    rw [hc]
    simp_rw [← hb]
    rw [b.repr_sum_self (fun j => (c j : K))]
  rw [← h3, map_smul, Finsupp.smul_apply, smul_eq_mul]

end GlobalTheory.PD
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY.LinComb


open Polynomial in
theorem exists_pow_ne_zero {Y : Type} (N : ℕ) (T : Finset Y) (v : Y → Fin N → ℂ)
    (hv : ∀ P ∈ T, v P ≠ 0) : ∃ x : ℂ, ∀ P ∈ T, ∑ k : Fin N, x ^ (k : ℕ) * v P k ≠ 0 := by
  classical
  let q : Y → ℂ[X] := fun P => ∑ k : Fin N, C (v P k) * X ^ (k : ℕ)
  have hcoeff : ∀ P (k : Fin N), (q P).coeff k = v P k := by
    intro P k
    simp only [q, finsetSum_coeff, coeff_C_mul_X_pow, Fin.val_inj]
    simp
  have hq : ∀ P ∈ T, q P ≠ 0 := by
    intro P hP h0
    apply hv P hP
    funext k
    have := hcoeff P k
    rw [h0, coeff_zero] at this
    simpa using this.symm
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (T.biUnion fun P => (q P).roots.toFinset)
  refine ⟨x, fun P hP h => hx ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨P, hP, ?_⟩
  rw [Multiset.mem_toFinset, mem_roots (hq P hP), IsRoot.def]
  simp only [q, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  rw [← h]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

end GlobalTheory.OTY.LinComb

theorem GlobalTheory.OTY.exists_linComb_ne_zero_on_finset : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (L : La) (N : ℕ) (s : Fin N → ι → Y → ℂ) (T : Finset Y), (∀ k, A.IsSec L (s k)) → (∀ P ∈ T, P ∉ A.zeroSet s) → ∃ s' : ι → Y → ℂ, A.IsSec L s' ∧ (∀ P ∈ T, s' (A.pick P) P ≠ 0) ∧ ∃ C : ℝ, 0 < C ∧ ∀ y, A.nsq L s' y ≤ C * A.sqn L s y := by
  intro n Y _ _ _ _ _ ι La _ A L N s T hs hT
  classical
  obtain ⟨x, hx⟩ := GlobalTheory.OTY.LinComb.exists_pow_ne_zero N T (fun P k => s k (A.pick P) P) (by
    intro P hP h0
    apply hT P hP
    intro k
    exact congrFun h0 k)
  refine ⟨fun i y => ∑ k : Fin N, x ^ (k : ℕ) * s k i y, ⟨?_, ?_⟩, fun P hP => hx P hP, ?_⟩
  · intro i
    have : ((fun y => ∑ k : Fin N, x ^ (k : ℕ) * s k i y) ∘ (A.chart i).symm)
        = ∑ k : Fin N, (fun v => x ^ (k : ℕ) * (s k i ∘ (A.chart i).symm) v) := by
      funext v; simp [Finset.sum_apply]
    rw [this]
    exact DifferentiableOn.sum fun k _ => ((hs k).1 i).const_mul _
  · intro i j y hy hi hj
    simp only
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(hs k).2 i j y hy hi hj]
    ring
  · refine ⟨1 + ∑ k : Fin N, ‖x ^ (k : ℕ)‖ ^ 2, by positivity, fun y => ?_⟩
    simp only [WeightedAtlas.nsq, WeightedAtlas.sqn]
    rw [← Finset.sum_mul, ← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have h1 : ‖∑ k : Fin N, x ^ (k : ℕ) * s k (A.pick y) y‖ ≤ ∑ k : Fin N, ‖x ^ (k : ℕ)‖ * ‖s k (A.pick y) y‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun k _ => norm_mul _ _
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k : Fin N => ‖x ^ (k : ℕ)‖)
      (fun k => ‖s k (A.pick y) y‖)
    have h3 : 0 ≤ ∑ k : Fin N, ‖s k (A.pick y) y‖ ^ 2 := by positivity
    calc ‖∑ k : Fin N, x ^ (k : ℕ) * s k (A.pick y) y‖ ^ 2
        ≤ (∑ k : Fin N, ‖x ^ (k : ℕ)‖ * ‖s k (A.pick y) y‖) ^ 2 := by gcongr
      _ ≤ (∑ k : Fin N, ‖x ^ (k : ℕ)‖ ^ 2) * ∑ k : Fin N, ‖s k (A.pick y) y‖ ^ 2 := h2
      _ ≤ (1 + ∑ k : Fin N, ‖x ^ (k : ℕ)‖ ^ 2) * ∑ k : Fin N, ‖s k (A.pick y) y‖ ^ 2 := by
        gcongr; linarith
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.topologicalKrullDim_eq_of_openImmersion_integral_scheme : ∀ (F : Type) [Field F] (X V : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (ℓ : V ⟶ X) [LocallyOfFiniteType p] [IsOpenImmersion ℓ] [Nonempty V], topologicalKrullDim V = topologicalKrullDim X := by
  first | exact @GlobalTheory.OpenImmDim.topologicalKrullDim_eq_of_isOpenImmersion | exact GlobalTheory.OpenImmDim.topologicalKrullDim_eq_of_isOpenImmersion | (intros; apply GlobalTheory.OpenImmDim.topologicalKrullDim_eq_of_isOpenImmersion <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.comp_eq_of_sqZero_agree_pairs : ∀ (C C₀ : Type) [CommRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (K G : Over (Sp C)) (g g' : K ⟶ G), (∀ (T₀ : Over (Sp C₀)) (y : Over.mk (T₀.hom ≫ spMap π) ⟶ K), y ≫ g = y ≫ g') → ∀ (T : Over (Sp C)) (w w' : T ⟶ K), (∀ (T₀ : Over (Sp C₀)) (j : Over.mk (T₀.hom ≫ spMap π) ⟶ T), j ≫ w = j ≫ w') → w' ≫ g = w' ≫ g' → w ≫ g = w ≫ g' := by
  first | (exact @GlobalTheory.comp_eq_of_sqZero_agree) | (exact GlobalTheory.comp_eq_of_sqZero_agree) | (intros; apply GlobalTheory.comp_eq_of_sqZero_agree  <;> assumption)
end
