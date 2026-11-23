module

public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle433
public import Mathlib.RingTheory.Unramified.Locus
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle435
public import Mathlib.RingTheory.WittVector.Basic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle008
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Trace.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMemLocalizationIffForallPrime
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import GroundTheory.GlobalFields.Bundle001
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle436
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
public import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.Complete
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
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
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.WittVector.Teichmuller
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle005

@[expose] public section

section

open scoped TensorProduct Polynomial

namespace GlobalTheory

theorem exists_integral_primitive_clearing : ∀ (K : Type) [Field K] [NumberField K], ∃ θ : K, IsIntegral ℤ θ ∧ 0 < (minpoly ℤ θ).natDegree ∧ ((minpoly ℤ θ).map (Int.castRingHom ℚ)).Separable ∧ ∀ s : K, ∃ N : ℕ, 0 < N ∧ (N : K) * s ∈ Algebra.adjoin ℤ ({θ} : Set K) := by
  intro K _ _
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ K
  have halg : IsAlgebraic ℤ α := (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic α)
  obtain ⟨y, hy0, hy⟩ := halg.exists_integral_multiple
  set θ : K := (y : K) * α with hθdef
  have hθ : IsIntegral ℤ θ := by rw [hθdef, ← zsmul_eq_mul]; exact hy
  refine ⟨θ, hθ, minpoly.natDegree_pos hθ, ?_, ?_⟩
  · rw [← algebraMap_int_eq, ← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hθ]
    exact Algebra.IsSeparable.isSeparable ℚ θ
  · intro s
    set O := Algebra.adjoin ℤ ({θ} : Set K)
    have hθO : θ ∈ O := Algebra.subset_adjoin rfl
    have hs : s ∈ Algebra.adjoin ℚ ({α} : Set K) := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic α), hα]
      trivial
    induction hs using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, ?_⟩
      rw [hx]
      rcases Int.natAbs_eq y with h | h
      · have : ((y.natAbs : ℕ) : K) = (y : K) := (Int.cast_natCast (R := K) _).symm.trans (congrArg (Int.cast (R := K)) h.symm)
        rw [this]; exact hθO
      · have h' : (y.natAbs : ℤ) = -y := by omega
        have : ((y.natAbs : ℕ) : K) = -(y : K) := (Int.cast_natCast (R := K) _).symm.trans ((congrArg (Int.cast (R := K)) h').trans (Int.cast_neg y))
        rw [this, neg_mul]; exact O.neg_mem hθO
    | algebraMap q =>
      refine ⟨q.den, q.den_pos, ?_⟩
      have : ((q.den : ℕ) : K) * algebraMap ℚ K q = algebraMap ℤ K q.num := by
        rw [algebraMap_int_eq, eq_intCast, ← map_natCast (algebraMap ℚ K), ← map_mul,
          ← map_intCast (algebraMap ℚ K)]
        congr 1
        rw [mul_comm]; exact Rat.mul_den_eq_num q
      rw [this]; exact O.algebraMap_mem _
    | add a b _ _ ha hb =>
      obtain ⟨M, hM, hMa⟩ := ha
      obtain ⟨M', hM', hMb⟩ := hb
      refine ⟨M * M', Nat.mul_pos hM hM', ?_⟩
      have : ((M * M' : ℕ) : K) * (a + b) = (M' : ℤ) • ((M : K) * a) + (M : ℤ) • ((M' : K) * b) := by
        simp only [zsmul_eq_mul]; push_cast; ring
      rw [this]
      exact O.add_mem (O.zsmul_mem hMa _) (O.zsmul_mem hMb _)
    | mul a b _ _ ha hb =>
      obtain ⟨M, hM, hMa⟩ := ha
      obtain ⟨M', hM', hMb⟩ := hb
      refine ⟨M * M', Nat.mul_pos hM hM', ?_⟩
      have : ((M * M' : ℕ) : K) * (a * b) = ((M : K) * a) * ((M' : K) * b) := by
        push_cast; ring
      rw [this]
      exact O.mul_mem hMa hMb

theorem nonempty_adjoin_ringHom_zmod_of_dvd_eval : ∀ (K : Type) [Field K] [NumberField K] (θ : K), IsIntegral ℤ θ → ∀ (m : ℕ) (x : ℤ), (m : ℤ) ∣ (minpoly ℤ θ).eval x → Nonempty (Algebra.adjoin ℤ ({θ} : Set K) →+* ZMod m) := by
  intro K _ _ θ hθ m x hx
  have h : Polynomial.eval₂ (Int.castRingHom (ZMod m)) (x : ZMod m) (minpoly ℤ θ) = 0 := by
    rw [Polynomial.eval₂_at_intCast]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hx
  exact ⟨(AdjoinRoot.lift (Int.castRingHom (ZMod m)) (x : ZMod m) h).comp (minpoly.equivAdjoin hθ).symm.toRingEquiv.toRingHom⟩

theorem nonempty_closure_ringHom_of_mul_mem : ∀ (K : Type) [Field K] [CharZero K] (O : Subring K) (R : Type) [CommRing R] (ψ : O →+* R) (N : ℕ), 0 < N → IsUnit (N : R) → ∀ (S : Finset K), (∀ s ∈ S, (N : K) * s ∈ O) → Nonempty (Subring.closure (S : Set K) →+* R) := by
  intro K _ _ O R _ ψ N hN hu S hS
  set B := Localization.Away (N : O)
  have hNK : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  have hunits : ∀ m : Submonoid.powers (N : O), IsUnit (O.subtype m) := by
    rintro ⟨m, k, rfl⟩
    simp only [map_pow, map_natCast]
    exact (isUnit_iff_ne_zero.mpr hNK).pow k
  let φ : B →+* K := IsLocalization.lift (M := Submonoid.powers (N : O)) hunits
  have hφa : ∀ a : O, φ (algebraMap O B a) = (a : K) := fun a => IsLocalization.lift_eq hunits a
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro b hb
    obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (N : O)) b
    have h1 := congrArg φ (IsLocalization.mk'_spec B a m)
    rw [map_mul, hb, zero_mul, hφa] at h1
    have ha : a = 0 := Subtype.ext h1.symm
    subst ha; exact IsLocalization.mk'_zero _
  have hle : Subring.closure (S : Set K) ≤ φ.range := by
    rw [Subring.closure_le]
    intro s hs
    refine ⟨IsLocalization.mk' B (⟨(N : K) * s, hS s hs⟩ : O) (⟨(N : O), 1, pow_one _⟩ : Submonoid.powers (N : O)), ?_⟩
    have h1 := congrArg φ (IsLocalization.mk'_spec B (⟨(N : K) * s, hS s hs⟩ : O) (⟨(N : O), 1, pow_one _⟩ : Submonoid.powers (N : O)))
    rw [map_mul, hφa, hφa] at h1
    simp only [map_natCast] at h1
    exact mul_right_cancel₀ hNK (h1.trans (mul_comm _ _))
  have hψN : IsUnit (ψ (N : O)) := by rw [map_natCast]; exact hu
  let χ : B →+* R := IsLocalization.Away.lift (N : O) hψN
  let e : B ≃+* φ.range := RingEquiv.ofBijective φ.rangeRestrict ⟨fun x y h => hinj (congrArg Subtype.val h), φ.rangeRestrict_surjective⟩
  exact ⟨χ.comp (e.symm.toRingHom.comp (Subring.inclusion hle))⟩

theorem exists_prime_sq_ringHom_of_closure : ∀ (K : Type) [Field K] [NumberField K] (S : Finset K) (n : ℕ), ∃ p : ℕ, p.Prime ∧ n < p ∧ Nonempty (Subring.closure (S : Set K) →+* ZMod (p ^ 2)) := by
  intro K _ _ S n
  obtain ⟨θ, hθ, hdeg, hsep, hden⟩ := exists_integral_primitive_clearing K
  choose Nf hNf0 hNf using hden
  set N : ℕ := ∏ s ∈ S, Nf s with hN
  have hN0 : 0 < N := Finset.prod_pos (fun s _ => hNf0 s)
  have hNS : ∀ s ∈ S, (N : K) * s ∈ (Algebra.adjoin ℤ ({θ} : Set K)).toSubring := by
    intro s hs
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem Nf hs
    have : (N : K) * s = (c : ℤ) • ((Nf s : K) * s) := by
      rw [hN, hc]; push_cast; rw [zsmul_eq_mul]; push_cast; ring
    rw [this]
    exact Subalgebra.zsmul_mem _ (hNf s) _
  obtain ⟨p, hp, hlt, x, hx⟩ := GlobalTheory.T.exists_large_prime_sq_dvd_eval_of_separable (minpoly ℤ θ) hdeg hsep (max n N)
  refine ⟨p, hp, lt_of_le_of_lt (le_max_left _ _) hlt, ?_⟩
  obtain ⟨ψ⟩ := nonempty_adjoin_ringHom_zmod_of_dvd_eval K θ hθ (p ^ 2) x (by exact_mod_cast hx)
  have hu : IsUnit (N : ZMod (p ^ 2)) := by
    rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.symm
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    exact Nat.not_dvd_of_pos_of_lt hN0 (lt_of_le_of_lt (le_max_right _ _) hlt)
  exact nonempty_closure_ringHom_of_mul_mem K (Algebra.adjoin ℤ ({θ} : Set K)).toSubring (ZMod (p ^ 2)) ψ N hN0 hu S hNS

end GlobalTheory
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.natPrime_not_mem_prime_cube_of_isUnramifiedAt : ∀ (p : ℕ) (K H : Type) [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H] (x : K) (P : Ideal (𝓞 H)) [P.IsPrime], p.Prime → Module.finrank ℚ K = 2 → x ^ 2 = -(p : K) → P ≠ ⊥ → Algebra.IsUnramifiedAt (𝓞 K) P → (p : 𝓞 H) ∉ P ^ 3 := by
  first | exact @GlobalTheory.natPrime_not_mem_cube_of_isUnramifiedAt | exact GlobalTheory.natPrime_not_mem_cube_of_isUnramifiedAt | (intros; apply GlobalTheory.natPrime_not_mem_cube_of_isUnramifiedAt <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.finite_of_maximalIdeal_le_radical_complete_nakayama : ∀ (B R : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (ψ : B →+* R), IsAdicComplete (maximalIdeal B) B → IsLocalHom ψ → maximalIdeal R ≤ ((maximalIdeal B).map ψ).radical → ((residue R).comp ψ).Finite → ψ.Finite := by
  first | exact @GlobalTheory.CompleteNakayamaLocal.finite_of_maximalIdeal_le_radical | exact GlobalTheory.CompleteNakayamaLocal.finite_of_maximalIdeal_le_radical | (intros; apply GlobalTheory.CompleteNakayamaLocal.finite_of_maximalIdeal_le_radical <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem wittModule_free_finite_of_reduction : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (M V : Type) [AddCommGroup M] [Module (WittVector p k) M] [AddCommGroup V] [Module k V] [Module.Finite k V] (r : M →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] V), IsHausdorff (Ideal.span {(p : WittVector p k)}) M → (∀ m : M, (p : WittVector p k) • m = 0 → m = 0) → Function.Surjective r → (∀ m, r m = 0 → ∃ n, m = p • n) → Module.Free (WittVector p k) M ∧ Module.Finite (WittVector p k) M := by
  intro p _ k _ _ _ M V _ _ _ _ _ r hH htf hr hker
  classical
  let I : Ideal (WittVector p k) := Ideal.span {(p : WittVector p k)}
  have hpow : ∀ (j : ℕ) (m : M), ((p : WittVector p k) ^ j) • m = 0 → m = 0 := by
    intro j
    induction j with
    | zero => intro m h; simpa using h
    | succ j ih =>
      intro m h
      rw [pow_succ, mul_smul] at h
      exact htf m (ih _ h)
  haveI : Module.IsTorsionFree (WittVector p k) M :=
    Module.IsTorsionFree.of_smul_eq_zero fun a m h => by
      by_cases ha : a = 0
      · exact Or.inl ha
      right
      obtain ⟨j, u, rfl⟩ := WittVector.exists_eq_pow_p_mul' a ha
      rw [mul_smul] at h
      have h1 := hpow j _ h
      rw [← Units.smul_def] at h1
      exact (smul_eq_zero_iff_eq u).mp h1
  haveI : IsHausdorff I M := hH
  let b := Module.finBasis k V
  choose m hm using fun i => hr (b i)
  let F : (Fin (Module.finrank k V) → WittVector p k) →ₗ[WittVector p k] M :=
    Fintype.linearCombination (WittVector p k) m
  haveI : IsPrecomplete I (Fin (Module.finrank k V) → WittVector p k) :=
    GlobalTheory.isPrecomplete_pi I _
  have hs : Function.Surjective F := by
    apply surjective_of_mkQ_comp_surjective (I := I)
    intro q
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
    refine ⟨fun i => WittVector.teichmuller p (b.repr (r x) i), ?_⟩
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    have h0 : r (F (fun i => WittVector.teichmuller p (b.repr (r x) i)) - x) = 0 := by

      rw [map_sub, Fintype.linearCombination_apply, map_sum]
      simp only [map_smulₛₗ, hm, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
      rw [sub_eq_zero]
      exact b.sum_repr (r x)
    obtain ⟨y, hy⟩ := hker _ h0
    rw [hy]
    have : ((p : WittVector p k)) • y ∈ (I • ⊤ : Submodule (WittVector p k) M) :=
      Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
    simpa [Nat.cast_smul_eq_nsmul] using this
  haveI : Module.Finite (WittVector p k) M := Module.Finite.of_surjective F hs
  exact ⟨Module.free_of_finite_type_torsion_free', inferInstance⟩

end GlobalTheory
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.trace_mem_localization_iff_forall_prime_alt : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (p : Ideal A), p.IsPrime → p.height = 1 → ∀ t : A, Irreducible t → p = Ideal.span {t} → (∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → Q.height = 1) → (∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → ∃ (s : B) (e : ℕ), 1 ≤ e ∧ s ∈ Q ∧ (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) ∧ (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ (r : K) * algebraMap F K t = a * s ^ e)) → ∀ z : K, (∀ b : B, ∃ r c : A, r ∉ p ∧ (r : F) * Algebra.trace F K (z * b) = c) ↔ ∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → ∀ (s : B) (e : ℕ), 1 ≤ e → s ∈ Q → (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) → (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ (r : K) * algebraMap F K t = a * s ^ e) → ∃ c r : B, r ∉ Q ∧ (r : K) * s ^ (e - 1) * z = c := by
  first | (exact @GlobalTheory.CodimDual.trace_mem_localization_iff_forall_prime) | (exact GlobalTheory.CodimDual.trace_mem_localization_iff_forall_prime) | (intros; apply GlobalTheory.CodimDual.trace_mem_localization_iff_forall_prime  <;> assumption)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.exists_not_mem_smul_D_eq_sum : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] (B : Subalgebra k K) [Algebra.FiniteType k B] (Q : Ideal B), Q.IsPrime → ∀ s : B, s ∈ Q → s ≠ 0 → (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) → ∀ (m : ℕ) (y : Fin m → B), IsTranscendenceBasis k (fun j => Ideal.Quotient.mk Q (y j)) → ∀ v : B, ∃ r : B, r ∉ Q ∧ ∃ c : Fin (m + 1) → B, algebraMap K L (r : K) • D k L (algebraMap K L (v : K)) = ∑ l, algebraMap K L (c l : K) • (Fin.cons (D k L (algebraMap K L (s : K))) (fun j => D k L (algebraMap K L (y j : K))) : Fin (m + 1) → Ω[L⁄k]) l := by
  first | (exact @GlobalTheory.span_D_lift_clear_denominators) | (exact GlobalTheory.span_D_lift_clear_denominators) | (intros; apply GlobalTheory.span_D_lift_clear_denominators  <;> assumption)
end

section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

namespace GlobalTheory

theorem bialgHom_factor_through_split :
    ∀ (O : Type) [CommRing O] (A B D : Type) [CommRing A] [CommRing B] [CommRing D] [Bialgebra O A] [Bialgebra O B] [Bialgebra O D] (j : B →ₐc[O] A) (ρ : A →ₗ[O] B) (f : D →ₐc[O] A), (∀ b, ρ (j b) = b) → (∀ d, f d ∈ Set.range j) → ∃ g : D →ₐc[O] B, ∀ d, j (g d) = f d := by
  intro O _ A B D _ _ _ _ _ _ j ρ f hρ hf
  have hjinj : Function.Injective j := fun x y h => by
    have := congrArg ρ h; rwa [hρ, hρ] at this
  have hjg : ∀ d, j (ρ (f d)) = f d := fun d => by
    obtain ⟨b, hb⟩ := hf d; rw [← hb, hρ]
  have hmapinj : Function.Injective (TensorProduct.map (j : B →ₗ[O] A) (j : B →ₗ[O] A)) := by
    have hid : (TensorProduct.map ρ ρ).comp (TensorProduct.map (j : B →ₗ[O] A) (j : B →ₗ[O] A)) = LinearMap.id := by
      apply TensorProduct.ext'
      intro x y
      simp [hρ]
    intro x y h
    have := congrArg (TensorProduct.map ρ ρ) h
    simpa [← LinearMap.comp_apply, hid] using this
  let gl : D →ₗ[O] B := ρ ∘ₗ (f : D →ₗ[O] A)
  have hgl : ∀ d, j (gl d) = f d := hjg
  have hcomp : (j : B →ₗ[O] A) ∘ₗ gl = (f : D →ₗ[O] A) := LinearMap.ext hgl
  refine ⟨{ gl with
    counit_comp := ?_
    map_comp_comul := ?_
    map_one' := ?_
    map_mul' := ?_ }, hgl⟩
  · ext d
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [← CoalgHomClass.counit_comp_apply j, hgl, CoalgHomClass.counit_comp_apply]
  · ext d
    apply hmapinj
    show TensorProduct.map (j : B →ₗ[O] A) (j : B →ₗ[O] A) (TensorProduct.map gl gl (comul d)) =
      TensorProduct.map (j : B →ₗ[O] A) (j : B →ₗ[O] A) (comul (gl d))
    rw [CoalgHomClass.map_comp_comul_apply j, hgl, ← LinearMap.comp_apply, ← TensorProduct.map_comp, hcomp,
      CoalgHomClass.map_comp_comul_apply f]
  · apply hjinj
    show j (gl 1) = j 1
    rw [hgl, map_one, map_one]
  · intro x y
    apply hjinj
    show j (gl (x * y)) = j (gl x * gl y)
    rw [hgl, map_mul, map_mul, hgl, hgl]

end GlobalTheory
end

section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Polynomial

namespace GlobalTheory.AdelicQuadSol

theorem exists_sq_eq_of_approx {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (r b : v.adicCompletionIntegers K) (hb : b ^ 2 - r ∈ maximalIdeal (v.adicCompletionIntegers K))
    (hu : IsUnit (2 * b)) : ∃ s : v.adicCompletionIntegers K, s ^ 2 = r := by
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  have hm : (X ^ 2 - C r : (v.adicCompletionIntegers K)[X]).Monic := monic_X_pow_sub_C r two_ne_zero
  have hd : eval b (derivative (X ^ 2 - C r : (v.adicCompletionIntegers K)[X])) = 2 * b := by
    simp [one_add_one_eq_two]
  obtain ⟨s, hs, -⟩ := HenselianRing.is_henselian (I := maximalIdeal (v.adicCompletionIntegers K))
    (X ^ 2 - C r) hm b (by simpa using hb) (by rw [hd]; exact hu.map _)
  refine ⟨s, ?_⟩
  have h0 : s ^ 2 - r = 0 := by simpa using hs
  linear_combination h0

theorem local_integral : ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (δ a : K), Valued.v (algebraMap K (v.adicCompletion K) 2) = 1 → Valued.v (algebraMap K (v.adicCompletion K) δ) = 1 → Valued.v (algebraMap K (v.adicCompletion K) a) = 1 → ∃ x y : v.adicCompletion K, x ∈ v.adicCompletionIntegers K ∧ y ∈ v.adicCompletionIntegers K ∧ x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2 = algebraMap K (v.adicCompletion K) a := by
  intro K _ _ v δ a h2 hδ ha
  set O := v.adicCompletionIntegers K
  let d : O := ⟨algebraMap K (v.adicCompletion K) δ, by rw [mem_adicCompletionIntegers, hδ]⟩
  let α : O := ⟨algebraMap K (v.adicCompletion K) a, by rw [mem_adicCompletionIntegers, ha]⟩
  have hdu : IsUnit d := adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hδ
  have hαu : IsUnit α := adicCompletionIntegers.isUnit_iff_valued_eq_one.2 ha
  have h2u : IsUnit (2 : O) := by
    apply adicCompletionIntegers.isUnit_iff_valued_eq_one.2
    have e2 : ((2 : O) : v.adicCompletion K) = algebraMap K (v.adicCompletion K) 2 := by
      rw [map_ofNat]; rfl
    rw [e2]; exact h2
  letI := Fintype.ofFinite (ResidueField O)
  have h2k : (2 : ResidueField O) ≠ 0 := by
    have := (h2u.map (residue O)).ne_zero
    rwa [map_ofNat] at this
  have hchar : ringChar (ResidueField O) ≠ 2 := by
    intro h
    apply h2k
    have := ringChar.Nat.cast_ringChar (R := ResidueField O)
    rw [h] at this
    exact_mod_cast this
  have hodd := FiniteField.odd_card_of_char_ne_two hchar
  have hdk : residue O d ≠ 0 := (hdu.map (residue O)).ne_zero
  have hαk : residue O α ≠ 0 := (hαu.map (residue O)).ne_zero
  obtain ⟨s, t, hst⟩ := FiniteField.exists_root_sum_quadratic
    (f := (X ^ 2 : (ResidueField O)[X])) (g := C (-residue O d) * X ^ 2 + C (-residue O α))
    (by simp) (by compute_degree!) hodd
  obtain ⟨x0, rfl⟩ := residue_surjective s
  obtain ⟨y0, rfl⟩ := residue_surjective t
  have he : x0 ^ 2 - d * y0 ^ 2 - α ∈ maximalIdeal O := by
    rw [← residue_eq_zero_iff]
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at hst
    rw [map_sub, map_sub, map_mul, map_pow, map_pow]
    linear_combination hst
  by_cases hx : residue O x0 = 0
  · have hy : residue O y0 ≠ 0 := by
      intro hy
      apply hαk
      have := (residue_eq_zero_iff _).2 he
      rw [map_sub, map_sub, map_mul, map_pow, map_pow, hx, hy] at this
      linear_combination -this
    obtain ⟨e, he'⟩ := hdu
    set di : O := ((e⁻¹ : Oˣ) : O)
    have hdi : di * d = 1 := by rw [← he']; exact e.inv_mul
    obtain ⟨y, hy2⟩ := exists_sq_eq_of_approx v (di * (x0 ^ 2 - α)) y0
      (by
        have : y0 ^ 2 - di * (x0 ^ 2 - α) = -di * (x0 ^ 2 - d * y0 ^ 2 - α) := by
          linear_combination (-(y0 ^ 2)) * hdi
        rw [this]; exact Ideal.mul_mem_left _ _ he)
      (h2u.mul (by
        rw [← IsLocalRing.residue_ne_zero_iff_isUnit]; exact hy))
    refine ⟨(x0 : v.adicCompletion K), (y : v.adicCompletion K), x0.2, y.2, ?_⟩
    have hO : x0 ^ 2 - d * y ^ 2 = α := by
      rw [hy2]; linear_combination (-(x0 ^ 2 - α)) * hdi
    have := congrArg (fun z : O => (z : v.adicCompletion K)) hO
    simpa [d, α] using this
  · obtain ⟨x, hx2⟩ := exists_sq_eq_of_approx v (α + d * y0 ^ 2) x0
      (by
        have : x0 ^ 2 - (α + d * y0 ^ 2) = x0 ^ 2 - d * y0 ^ 2 - α := by ring
        rw [this]; exact he)
      (h2u.mul (by rw [← IsLocalRing.residue_ne_zero_iff_isUnit]; exact hx))
    refine ⟨(x : v.adicCompletion K), (y0 : v.adicCompletion K), x.2, y0.2, ?_⟩
    have hO : x ^ 2 - d * y0 ^ 2 = α := by rw [hx2]; ring
    have := congrArg (fun z : O => (z : v.adicCompletion K)) hO
    simpa [d, α] using this

theorem eventually_valued_eq_one {K : Type} [Field K] [NumberField K] {c : K} (hc : c ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      Valued.v (algebraMap K (v.adicCompletion K) c) = 1 := by
  filter_upwards [(algebraMap K (FiniteAdeleRing (𝓞 K) K) c).2,
    (algebraMap K (FiniteAdeleRing (𝓞 K) K) c⁻¹).2] with v h1 h2
  have h1' : Valued.v (algebraMap K (v.adicCompletion K) c) ≤ 1 := (mem_adicCompletionIntegers (𝓞 K) K v).1 h1
  have h2' : Valued.v (algebraMap K (v.adicCompletion K) c⁻¹) ≤ 1 := (mem_adicCompletionIntegers (𝓞 K) K v).1 h2
  rw [map_inv₀, map_inv₀] at h2'
  have h0 : Valued.v (algebraMap K (v.adicCompletion K) c) ≠ 0 := by
    rw [Ne, map_eq_zero, map_eq_zero]; exact hc
  exact le_antisymm h1' ((inv_le_one₀ (zero_lt_iff.2 h0)).1 h2')

theorem exists_finiteAdele_sq_sub_mul_sq : ∀ (K : Type) [Field K] [NumberField K] (δ a : K), δ ≠ 0 → a ≠ 0 → (∀ v : HeightOneSpectrum (𝓞 K), ∃ x y : v.adicCompletion K, x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2 = algebraMap K (v.adicCompletion K) a) → ∃ x y : FiniteAdeleRing (𝓞 K) K, x ^ 2 - algebraMap K (FiniteAdeleRing (𝓞 K) K) δ * y ^ 2 = algebraMap K (FiniteAdeleRing (𝓞 K) K) a := by
  intro K _ _ δ a hδ ha hloc
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      Valued.v (algebraMap K (v.adicCompletion K) 2) = 1 ∧
      Valued.v (algebraMap K (v.adicCompletion K) δ) = 1 ∧
      Valued.v (algebraMap K (v.adicCompletion K) a) = 1 :=
    (eventually_valued_eq_one h2).and ((eventually_valued_eq_one hδ).and (eventually_valued_eq_one ha))
  classical
  let sol : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K × v.adicCompletion K := fun v =>
    if h : Valued.v (algebraMap K (v.adicCompletion K) 2) = 1 ∧
      Valued.v (algebraMap K (v.adicCompletion K) δ) = 1 ∧
      Valued.v (algebraMap K (v.adicCompletion K) a) = 1 then
      ((local_integral K v δ a h.1 h.2.1 h.2.2).choose, (local_integral K v δ a h.1 h.2.1 h.2.2).choose_spec.choose)
    else ((hloc v).choose, (hloc v).choose_spec.choose)
  have hsol : ∀ v, (sol v).1 ^ 2 - algebraMap K (v.adicCompletion K) δ * (sol v).2 ^ 2 =
      algebraMap K (v.adicCompletion K) a := by
    intro v
    simp only [sol]
    split_ifs with h
    · exact (local_integral K v δ a h.1 h.2.1 h.2.2).choose_spec.choose_spec.2.2
    · exact (hloc v).choose_spec.choose_spec
  have hint : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      (sol v).1 ∈ v.adicCompletionIntegers K ∧ (sol v).2 ∈ v.adicCompletionIntegers K := by
    filter_upwards [hev] with v h
    simp only [sol, dif_pos h]
    exact ⟨(local_integral K v δ a h.1 h.2.1 h.2.2).choose_spec.choose_spec.1,
      (local_integral K v δ a h.1 h.2.1 h.2.2).choose_spec.choose_spec.2.1⟩
  refine ⟨⟨fun v => (sol v).1, hint.mono fun _ h => h.1⟩, ⟨fun v => (sol v).2, hint.mono fun _ h => h.2⟩, ?_⟩
  refine FiniteAdeleRing.ext K fun v => ?_
  change (sol v).1 ^ 2 - algebraMap K (v.adicCompletion K) δ * (sol v).2 ^ 2 = algebraMap K (v.adicCompletion K) a
  exact hsol v

end GlobalTheory.AdelicQuadSol
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.finiteLength_coker_of_etale_punctured_spectrum : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] (A B : Type) [CommRing A] [Algebra R A] [Module.Finite R A] [CommRing B] [Algebra R B] [Module.Finite R B], (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) B)) → ∀ ψ : A →ₐ[R] B, Function.Injective ψ → (∃ s : R, s ≠ 0 ∧ ∀ b : B, s • b ∈ ψ.range) → ∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, x • b ∈ ψ.range := by
  first | (exact @GlobalTheory.EtaleCoker.main) | (exact GlobalTheory.EtaleCoker.main) | (intros; apply GlobalTheory.EtaleCoker.main  <;> assumption)
end
