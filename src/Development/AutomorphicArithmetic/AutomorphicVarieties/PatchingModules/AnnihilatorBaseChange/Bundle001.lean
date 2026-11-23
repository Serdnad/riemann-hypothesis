module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ThetaCoefficientMapEq
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle024
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchedSupportCompletions
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle009
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
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg

@[expose] public section

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.pmMove :
    ∀ (BB MM B B' : Type) [CommRing BB] [IsNoetherianRing BB] [AddCommGroup MM] [Module BB MM] [Module.Finite BB MM] [CommRing B] [Algebra BB B] [CommRing B'] [IsLocalRing B'] [Algebra BB B'] (p' : Ideal BB) (Z : Ideal B), IsCplAt BB p' B' → Z.IsPrime → Module.annihilator B (B ⊗[BB] MM) ≤ Z → Z.comap (algebraMap BB B) ≤ p' → ∃ Z' : Ideal B', Z'.IsPrime ∧ Module.annihilator B' (B' ⊗[BB] MM) ≤ Z' ∧ Z'.comap (algebraMap BB B') = Z.comap (algebraMap BB B) := by
  intro BB MM B B' _ _ _ _ _ _ _ _ _ _ p' Z hB' hZ hann hle
  haveI := hZ
  obtain ⟨Q, hQ, hQc⟩ := (IsCplAt.exists_prime_over BB p' B' hB').1 _ (Ideal.IsPrime.comap _) hle
  refine ⟨Q, hQ, ?_, hQc⟩
  let zP : PrimeSpectrum B := ⟨Z, hZ⟩
  let qP : PrimeSpectrum B' := ⟨Q, hQ⟩
  have hz : zP ∈ Module.support B (B ⊗[BB] MM) := Module.mem_support_iff_of_finite.mpr hann
  have hz' := (mem_support_baseChange BB B MM zP).mp hz
  have heq : PrimeSpectrum.comap (algebraMap BB B') qP = PrimeSpectrum.comap (algebraMap BB B) zP :=
    PrimeSpectrum.ext hQc
  have hq : qP ∈ Module.support B' (B' ⊗[BB] MM) := by
    rw [mem_support_baseChange, heq]
    exact hz'
  exact Module.mem_support_iff_of_finite.mp hq
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem laDim_co (O : Type) [CommRing O] [IsLocalRing O] (K : Type) [Field K] [Algebra O K]
    (h : Function.Surjective (algebraMap O K)) : IsCO O K := by
  refine { complete := ?_, isLocalHom := IsLocalHom.of_surjective _ h, res_surj := ?_ }
  · rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  · intro x
    obtain ⟨a, rfl⟩ := h x
    exact ⟨a, by simp⟩

private theorem laDim_surj (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] (K : Type) [Field K] [Algebra O K] (σ : Type) [Finite σ] (s : σ)
    (g : MvPowerSeries σ O →ₐ[O] PowerSeries K) (h : Function.Surjective (algebraMap O K))
    (hg : g (MvPowerSeries.X s) = PowerSeries.X) : Function.Surjective g := by
  haveI : IsCO O K := laDim_co O K h
  haveI : IsCO O (MvPowerSeries σ O) := co_mvps O O σ
  haveI : IsCO O (PowerSeries K) := co_mvps O K Unit
  refine co_surj O _ _ g (le_trans ?_ le_sup_left)
  rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_le, Set.singleton_subset_iff, ← hg]
  refine Ideal.mem_map_of_mem _ fun hu => ?_
  have := MvPowerSeries.isUnit_constantCoeff _ hu
  simp at this

private theorem laDim_arith (x : WithBot ℕ∞) (n : ℕ) (h : x + 1 = ((n + 1 : ℕ) : WithBot ℕ∞)) :
    x = (n : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h (by rw [WithBot.bot_add]; exact (WithBot.natCast_ne_bot _).symm)
  | coe y =>
    have h' : y + 1 = ((n : ℕ∞) + 1) := by exact_mod_cast h
    have : y = (n : ℕ∞) := WithTop.add_right_cancel ENat.one_ne_top h'
    rw [this]; rfl

private theorem laDim_gen (R : Type) [CommRing R] [IsRegularLocalRing R] (S : Type) [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] (p : Ideal R) (e : (R ⧸ p) ≃+* S) (n : ℕ)
    (hdim : ringKrullDim R = ((n + 1 : ℕ) : WithBot ℕ∞)) :
    ∃ (La : Type) (_ : CommRing La) (_ : IsLocalRing La) (_ : Algebra R La),
      IsCplAt R p La ∧ IsRegularLocalRing La ∧ ringKrullDim La = (n : WithBot ℕ∞) := by
  haveI : IsDomain (R ⧸ p) := e.toMulEquiv.isDomain _
  haveI hp : p.IsPrime := (Ideal.Quotient.isDomain_iff_prime p).1 inferInstance
  haveI : IsRegularLocalRing (R ⧸ p) := IsRegularLocalRing.of_ringEquiv e.symm
  have hq : ringKrullDim (R ⧸ p) = 1 := by
    rw [ringKrullDim_eq_of_ringEquiv e, IsDiscreteValuationRing.ringKrullDim_eq_one]
  obtain ⟨h1, h2⟩ := regular_localization_of_regular_quotient R p
  have hc := isCplAt_cplAt R p
  obtain ⟨h3, h4⟩ := IsCplAt.regular _ _ _ hc h1
  refine ⟨CplAt R p, inferInstance, inferInstance, inferInstance, hc, h3, ?_⟩
  rw [h4]
  apply laDim_arith
  rw [hq] at h2
  rw [h2, hdim]

theorem UpperTheory.V.Pa.Core.laDim :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (K : Type) [Field K] [Finite K] [Algebra O K] (D : ℕ) (g : abelian₂ O Unit D →ₐ[O] PowerSeries K), Function.Surjective (algebraMap O K) → g (MvPowerSeries.X (.inl ())) = PowerSeries.X → ∃ (La : Type) (_ : CommRing La) (_ : IsLocalRing La) (_ : Algebra (abelian₂ O Unit D) La), IsCplAt (abelian₂ O Unit D) (RingHom.ker g) La ∧ IsRegularLocalRing La ∧ ringKrullDim La = ((1 + D : ℕ) : WithBot ℕ∞) := by
  intro O _ _ _ _ K _ _ _ D g h hg
  have hs : Function.Surjective g := laDim_surj O K _ _ g h hg
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨hreg, hdim, -⟩ := mvPowerSeries_cotInd O ϖ hϖ (Unit ⊕ Fin D)
  haveI : IsRegularLocalRing (abelian₂ O Unit D) := hreg
  refine laDim_gen (abelian₂ O Unit D) (PowerSeries K) (RingHom.ker g)
    (Ideal.quotientKerAlgEquivOfSurjective hs).toRingEquiv (1 + D) ?_
  rw [hdim, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.ulimQuot :
    ∀ (R : Type) [CommRing R] (F : Filter ℕ) (I : ℕ → Ideal R) (M M' : ℕ → Type) [∀ N, AddCommGroup (M N)] [∀ N, Module R (M N)] [∀ N, AddCommGroup (M' N)] [∀ N, Module R (M' N)] (ν : ℕ → ℕ) (φ : ∀ N, (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))) →ₗ[R] (M' N ⧸ (I (ν N) • ⊤ : Submodule R (M' N)))), Antitone I → Tendsto ν F atTop → ∃ Φ : ULim F I M →ₗ[R] ULim F I M', ∀ (p : ∀ N, M N) (p' : ∀ N, M' N), (∀ᶠ N in F, Submodule.Quotient.mk (p' N) = φ N (Submodule.Quotient.mk (p N))) → Φ (ULim.mk F I M p) = ULim.mk F I M' p' := by
  intro R _ F I M M' _ _ _ _ ν φ hI hν
  have hev : ∀ j, ∀ᶠ N in F, I (ν N) ≤ I j := fun j =>
    (tendsto_atTop.1 hν j).mono fun N hN => hI hN
  have he : ∀ {X : Type} [AddCommGroup X] [Module R X] (K J : Ideal R),
      (J • ⊤ : Submodule R (X ⧸ (K • ⊤ : Submodule R X))) =
        (J • ⊤ : Submodule R X).map (K • ⊤ : Submodule R X).mkQ := by
    intro X _ _ K J
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
  have hlift : ∀ {X : Type} [AddCommGroup X] [Module R X] (K J : Ideal R), K ≤ J → ∀ x : X,
      (Submodule.Quotient.mk x : X ⧸ (K • ⊤ : Submodule R X)) ∈
        (J • ⊤ : Submodule R (X ⧸ (K • ⊤ : Submodule R X))) → x ∈ (J • ⊤ : Submodule R X) := by
    intro X _ _ K J hKJ x hx
    rw [he] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hd : x - y ∈ (K • ⊤ : Submodule R X) := by
      rw [← Submodule.Quotient.eq]
      exact hyx.symm
    have := Submodule.add_mem _ (Submodule.smul_mono_left hKJ hd) hy
    rwa [sub_add_cancel] at this
  have hmk : ∀ {X : Type} [AddCommGroup X] [Module R X] (K J : Ideal R) (x : X),
      x ∈ (J • ⊤ : Submodule R X) →
        (Submodule.Quotient.mk x : X ⧸ (K • ⊤ : Submodule R X)) ∈
          (J • ⊤ : Submodule R (X ⧸ (K • ⊤ : Submodule R X))) := by
    intro X _ _ K J x hx
    rw [he]
    exact ⟨x, hx, rfl⟩
  have hφ : ∀ N j (z : M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))),
      z ∈ (I j • ⊤ : Submodule R _) → φ N z ∈ (I j • ⊤ : Submodule R _) := by
    intro N j z hz
    have hle : (I j • ⊤ : Submodule R _).map (φ N) ≤ I j • ⊤ := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact hle ⟨z, hz, rfl⟩
  let π : (∀ N, M' N) →ₗ[R] ∀ N, (M' N ⧸ (I (ν N) • ⊤ : Submodule R (M' N))) :=
    LinearMap.pi fun N => (Submodule.mkQ _).comp (LinearMap.proj N)
  have hπ : Function.Surjective π := fun q =>
    ⟨fun N => (Submodule.mkQ_surjective _ (q N)).choose,
      funext fun N => (Submodule.mkQ_surjective _ (q N)).choose_spec⟩
  have hker : LinearMap.ker π ≤ LinearMap.ker (ULim.mk F I M') := by
    intro p hp
    rw [LinearMap.mem_ker] at hp ⊢
    rw [ULim.mk_eq_zero]
    intro j
    refine (hev j).mono fun N hN => ?_
    have hpN : p N ∈ (I (ν N) • ⊤ : Submodule R (M' N)) := by
      rw [← Submodule.Quotient.mk_eq_zero]
      exact congrFun hp N
    exact Submodule.smul_mono_left hN hpN
  let φ' : (∀ N, M N) →ₗ[R] ∀ N, (M' N ⧸ (I (ν N) • ⊤ : Submodule R (M' N))) :=
    LinearMap.pi fun N => (φ N).comp ((Submodule.mkQ _).comp (LinearMap.proj N))
  let Φ0 : (∀ N, M N) →ₗ[R] ULim F I M' :=
    ((LinearMap.ker π).liftQ (ULim.mk F I M') hker).comp
      ((π.quotKerEquivOfSurjective hπ).symm.toLinearMap.comp φ')
  have hΦ0 : ∀ p p', π p' = φ' p → Φ0 p = ULim.mk F I M' p' := by
    intro p p' h
    simp only [Φ0, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← h]
    have hs : (π.quotKerEquivOfSurjective hπ).symm (π p') = Submodule.Quotient.mk p' := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    rw [hs, Submodule.liftQ_apply]
  have hnull : uNull F I M ≤ LinearMap.ker Φ0 := by
    intro p hp
    have hp : ∀ j, ∀ᶠ N in F, p N ∈ (I j • ⊤ : Submodule R (M N)) := hp
    rw [LinearMap.mem_ker]
    obtain ⟨p', hp'⟩ := hπ (φ' p)
    rw [hΦ0 p p' hp', ULim.mk_eq_zero]
    intro j
    refine ((hp j).and (hev j)).mono fun N ⟨h1, h2⟩ => ?_
    apply hlift (I (ν N)) (I j) h2
    have hN : π p' N = φ N (Submodule.Quotient.mk (p N)) := congrFun hp' N
    change π p' N ∈ _
    rw [hN]
    exact hφ N j _ (hmk _ _ _ h1)
  refine ⟨(uNull F I M).liftQ Φ0 hnull, fun p p' h => ?_⟩
  change (uNull F I M).liftQ Φ0 hnull (Submodule.Quotient.mk p) = _
  rw [Submodule.liftQ_apply]
  obtain ⟨q, hq⟩ := hπ (φ' p)
  rw [hΦ0 p q hq, ← sub_eq_zero, ← map_sub, ULim.mk_eq_zero]
  intro j
  refine (h.and (hev j)).mono fun N ⟨h1, h2⟩ => ?_
  apply Submodule.smul_mono_left h2
  rw [← Submodule.Quotient.mk_eq_zero, Pi.sub_apply, Submodule.Quotient.mk_sub, h1]
  have hN : π q N = φ N (Submodule.Quotient.mk (p N)) := congrFun hq N
  exact sub_eq_zero.2 hN
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.kjMap :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [Fintype σ] (s : MvPowerSeries σ Λ →+* R) (k j : ℕ), (kjIdeal Λ σ k j).map s = Ideal.span (Set.range (fun a => s (MvPowerSeries.X a))) ^ k ⊔ ((maximalIdeal Λ).map (s.comp MvPowerSeries.C)) ^ j := by
  intro Λ R σ _ _ _ _ s k j
  rw [kjIdeal, Ideal.map_sup, Ideal.map_pow, Ideal.map_span, ← Set.range_comp, Ideal.map_map, Ideal.map_pow]
  rfl
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem comap_comap_quot {R B : Type} [CommRing R] [CommRing B] [Algebra R B] (ii : Ideal R)
    (Q : Ideal (B ⧸ ii.map (algebraMap R B))) :
    (Q.comap (algebraMap (R ⧸ ii) (B ⧸ ii.map (algebraMap R B)))).comap (Ideal.Quotient.mk ii) =
      (Q.comap (Ideal.Quotient.mk (ii.map (algebraMap R B)))).comap (algebraMap R B) := by
  ext x
  rfl

private theorem dim_quot {B : Type} [CommRing B] (I S : Ideal B) (h : I ≤ S.radical) (d : WithBot ℕ∞)
    (hd : ∀ P ∈ S.minimalPrimes, d ≤ ringKrullDim (B ⧸ P)) (P : Ideal (B ⧸ I))
    (hP : P ∈ (S.map (Ideal.Quotient.mk I)).minimalPrimes) : d ≤ ringKrullDim ((B ⧸ I) ⧸ P) := by
  rw [Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker] at hP
  obtain ⟨P', hP', rfl⟩ := hP
  have hIP : I ≤ P' := le_sup_right.trans hP'.1.2
  have hmin : P' ∈ S.minimalPrimes := by
    refine ⟨⟨hP'.1.1, le_sup_left.trans hP'.1.2⟩, ?_⟩
    intro Q hQ hQP
    haveI := hQ.1
    exact hP'.2 ⟨hQ.1, sup_le hQ.2 (h.trans ((Ideal.IsPrime.radical_le_iff hQ.1).mpr hQ.2))⟩ hQP
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup I P'), sup_eq_right.mpr hIP]
  exact hd P' hmin

theorem UpperTheory.V.Pa.Core.outOfNil :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [IsNoetherianRing R] (s : MvPowerSeries σ Λ →+* R) (ii ann : Ideal R) (ι : Type) (q : ι → Ideal R) (d : ℕ) (B : ι → Type) [∀ i, CommRing (B i)] [∀ i, IsLocalRing (B i)] [∀ i, Algebra R (B i)] (S : ∀ i, Ideal (B i)), (∀ i, ii ≤ q i) → (∀ i, IsCplAt R (q i) (B i)) → (∀ i, ii ≤ (S i).radical.comap (algebraMap R (B i))) → (∀ i, ∀ P ∈ (S i).minimalPrimes, (d : WithBot ℕ∞) ≤ ringKrullDim (B i ⧸ P)) → (∀ i (Q : Ideal (B i)), Q.IsPrime → ii.map (algebraMap R (B i)) ≤ Q → (∀ a, algebraMap R (B i) (s (MvPowerSeries.X a)) ∈ Q) → (S i ≤ Q ↔ ann ≤ Q.comap (algebraMap R (B i)))) → (∀ i i' (Z Q : Ideal (B i)), Z.IsPrime → Q.IsPrime → S i ≤ Z → Z ≤ Q → (∀ a, algebraMap R (B i) (s (MvPowerSeries.X a)) ∈ Q) → Q.comap (algebraMap R (B i)) ≤ q i' → ∃ Z' : Ideal (B i'), Z'.IsPrime ∧ S i' ≤ Z' ∧ Z'.comap (algebraMap R (B i')) = Z.comap (algebraMap R (B i))) → Nonempty (PatchedSupportCompletions s ii ann q d) := by
  intro Λ R σ _ _ _ _ s ii ann ι q d B _ _ _ S hq hcpl hrad hdim hfib hmove
  let J : ∀ i, Ideal (B i) := fun i => ii.map (algebraMap R (B i))
  have hJmax : ∀ i, J i ≤ maximalIdeal (B i) := by
    intro i
    rw [Ideal.map_le_iff_le_comap, (hcpl i).comap_eq]
    exact hq i
  have hJne : ∀ i, J i ≠ ⊤ := fun i h => (IsLocalRing.maximalIdeal.isMaximal (B i)).ne_top (top_le_iff.mp (h ▸ hJmax i))
  haveI : ∀ i, Nontrivial (B i ⧸ J i) := fun i => Ideal.Quotient.nontrivial_iff.mpr (hJne i)
  haveI : ∀ i, IsLocalRing (B i ⧸ J i) := fun i => .of_surjective' _ Ideal.Quotient.mk_surjective
  have hker : ∀ i, J i ≤ RingHom.ker (Ideal.Quotient.mk (J i)) := fun i => by rw [Ideal.mk_ker]
  have hcomap : ∀ i (Z : Ideal (B i ⧸ J i)),
      (Z.comap (algebraMap (R ⧸ ii) (B i ⧸ J i))).comap (Ideal.Quotient.mk ii) =
        (Z.comap (Ideal.Quotient.mk (J i))).comap (algebraMap R (B i)) :=
    fun i Z => comap_comap_quot ii Z
  have hJle : ∀ i (Z : Ideal (B i ⧸ J i)), J i ≤ Z.comap (Ideal.Quotient.mk (J i)) := by
    intro i Z x hx
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact Z.zero_mem
  have hgen : ∀ i (Q : Ideal (B i ⧸ J i)),
      ((∀ a, algebraMap (R ⧸ ii) (B i ⧸ J i) (Ideal.Quotient.mk ii (s (MvPowerSeries.X a))) ∈ Q) ↔
        ∀ a, algebraMap R (B i) (s (MvPowerSeries.X a)) ∈ Q.comap (Ideal.Quotient.mk (J i))) := by
    intro i Q
    rfl
  refine ⟨⟨fun i => B i ⧸ J i, fun i => ?_, fun i => (S i).map (Ideal.Quotient.mk (J i)), fun i => ?_,
    fun i Q hQ hgQ => ?_, fun i i' Z Q hZ hQ hSZ hZQ hgQ hQq => ?_⟩⟩
  · exact IsCplAt.quotient R (q i) (B i) (R ⧸ ii) ((q i).map (Ideal.Quotient.mk ii)) (B i ⧸ J i) (hcpl i)
      Ideal.Quotient.mk_surjective
      (by
        show Ideal.comap (Ideal.Quotient.mk ii) _ = _
        rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
          Ideal.mk_ker]
        exact sup_eq_left.mpr (hq i))
      Ideal.Quotient.mk_surjective
      (by
        show RingHom.ker (Ideal.Quotient.mk (J i)) = Ideal.map _ (RingHom.ker (Ideal.Quotient.mk ii))
        rw [Ideal.mk_ker, Ideal.mk_ker])
  · intro P hP
    exact dim_quot (J i) (S i) (Ideal.map_le_iff_le_comap.mpr (hrad i)) d (hdim i) P hP
  · haveI := hQ
    rw [Ideal.map_le_iff_le_comap, hcomap]
    exact hfib i _ (Ideal.comap_isPrime _ Q) (hJle i Q) ((hgen i Q).mp hgQ)
  · haveI := hZ
    haveI := hQ
    rw [hcomap] at hQq
    obtain ⟨Z'', hZ''p, hSZ'', hZ''⟩ := hmove i i' (Z.comap (Ideal.Quotient.mk (J i)))
      (Q.comap (Ideal.Quotient.mk (J i))) (Ideal.comap_isPrime _ Z) (Ideal.comap_isPrime _ Q)
      (Ideal.map_le_iff_le_comap.mp hSZ) (Ideal.comap_mono hZQ) ((hgen i Q).mp hgQ) hQq
    have hiiZ : ii ≤ Z''.comap (algebraMap R (B i')) := by
      rw [hZ'', ← Ideal.map_le_iff_le_comap]
      exact hJle i Z
    have hJZ : J i' ≤ Z'' := Ideal.map_le_iff_le_comap.mpr hiiZ
    have hkZ : RingHom.ker (Ideal.Quotient.mk (J i')) ≤ Z'' := by rw [Ideal.mk_ker]; exact hJZ
    refine ⟨Z''.map (Ideal.Quotient.mk (J i')), Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hkZ,
      Ideal.map_mono hSZ'', ?_⟩
    apply Ideal.comap_injective_of_surjective _ (Ideal.Quotient.mk_surjective (I := ii))
    rw [hcomap, hcomap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hkZ, hZ'']
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.chainAbs :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [IsNoetherianRing R] (s : MvPowerSeries σ Λ →+* R) (ii ann : Ideal R) (h d : ℕ) (q : Fin (h + 1) → Ideal R) (o : PatchedSupportCompletions s ii ann q d) (St : Ideal (R ⧸ ii) → Prop) (Th : ∀ i, Ideal (o.B i) → Prop), (∀ i, (q i).IsPrime ∧ ii ≤ q i) → (∀ p p', p ≤ p' → St p' → St p) → (∀ i (Z Q : Ideal (o.B i)), Z.IsPrime → Q.IsPrime → St (Z.comap (algebraMap (R ⧸ ii) (o.B i))) → (d : WithBot ℕ∞) ≤ ringKrullDim (o.B i ⧸ Z) → St (Q.comap (algebraMap (R ⧸ ii) (o.B i))) ∨ Th i Q → Z ≤ Q) → ∀ E : Fin h → Ideal (R ⧸ ii), (∀ i, (E i).IsPrime ∧ (∀ a, Ideal.Quotient.mk ii (s (MvPowerSeries.X a)) ∈ E i) ∧ (E i).comap (Ideal.Quotient.mk ii) ≤ q i.castSucc ∧ (E i).comap (Ideal.Quotient.mk ii) ≤ q i.succ ∧ ∀ Q : Ideal (o.B i.castSucc), Q.IsPrime → Q.comap (algebraMap (R ⧸ ii) _) = E i → Th _ Q) → (∃ p : Ideal (R ⧸ ii), p.IsPrime ∧ (∀ a, Ideal.Quotient.mk ii (s (MvPowerSeries.X a)) ∈ p) ∧ p.comap (Ideal.Quotient.mk ii) ≤ q 0 ∧ St p ∧ ann ≤ p.comap (Ideal.Quotient.mk ii)) → ∀ p : Ideal (R ⧸ ii), p.IsPrime → (∀ a, Ideal.Quotient.mk ii (s (MvPowerSeries.X a)) ∈ p) → p.comap (Ideal.Quotient.mk ii) ≤ q (Fin.last h) → (St p ∨ ∀ Q : Ideal (o.B (Fin.last h)), Q.IsPrime → Q.comap (algebraMap (R ⧸ ii) _) = p → Th _ Q) → ann ≤ p.comap (Ideal.Quotient.mk ii) := by
  intro Λ R σ _ _ _ _ s ii ann h d q o St Th hq hSt hkey E hE h0 p hp hpX hpq hpS
  have hOver : ∀ (j : Fin (h + 1)) (P : Ideal (R ⧸ ii)), P.IsPrime →
      P.comap (Ideal.Quotient.mk ii) ≤ q j →
      ∃ Q : Ideal (o.B j), Q.IsPrime ∧ Q.comap (algebraMap (R ⧸ ii) (o.B j)) = P := by
    intro j P hP hle
    apply (IsCplAt.exists_prime_over (R ⧸ ii) _ (o.B j) (o.cpl j)).1 P hP
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.mem_map_of_mem _ (hle hx)
  have hInv : ∀ j : Fin (h + 1), ∃ Z : Ideal (o.B j), Z.IsPrime ∧ o.S j ≤ Z ∧
      St (Z.comap (algebraMap (R ⧸ ii) (o.B j))) := by
    intro j
    induction j using Fin.induction with
    | zero =>
      obtain ⟨p0, hp0, hp0X, hp0q, hp0St, hp0ann⟩ := h0
      obtain ⟨Q, hQ, hQc⟩ := hOver 0 p0 hp0 hp0q
      refine ⟨Q, hQ, ?_, by rw [hQc]; exact hp0St⟩
      refine (o.fib 0 Q hQ ?_).mpr ?_
      · intro a
        have hx := hp0X a
        rw [← hQc] at hx
        exact hx
      · rw [hQc]
        exact hp0ann
    | succ i ih =>
      obtain ⟨Z, hZ, hSZ, hStZ⟩ := ih
      obtain ⟨hEp, hEX, hEc, hEs, hETh⟩ := hE i
      obtain ⟨Q, hQ, hQc⟩ := hOver i.castSucc (E i) hEp hEc
      have hThQ := hETh Q hQ hQc
      obtain ⟨Z0, hZ0, hZ0le⟩ := Ideal.exists_minimalPrimes_le hSZ
      have hStZ0 := hSt _ _ (Ideal.comap_mono hZ0le) hStZ
      have hZ0Q := hkey i.castSucc Z0 Q hZ0.1.1 hQ hStZ0 (o.dim _ Z0 hZ0) (Or.inr hThQ)
      have hQX : ∀ a, algebraMap (R ⧸ ii) (o.B i.castSucc)
          (Ideal.Quotient.mk ii (s (MvPowerSeries.X a))) ∈ Q := by
        intro a
        have hx := hEX a
        rw [← hQc] at hx
        exact hx
      obtain ⟨Z', hZ', hSZ', hZ'c⟩ := o.move i.castSucc i.succ Z0 Q hZ0.1.1 hQ hZ0.1.2 hZ0Q hQX
        (by rw [hQc]; exact hEs)
      exact ⟨Z', hZ', hSZ', by rw [hZ'c]; exact hStZ0⟩
  obtain ⟨Z, hZ, hSZ, hStZ⟩ := hInv (Fin.last h)
  obtain ⟨Q, hQ, hQc⟩ := hOver (Fin.last h) p hp hpq
  have hQX : ∀ a, algebraMap (R ⧸ ii) (o.B (Fin.last h))
      (Ideal.Quotient.mk ii (s (MvPowerSeries.X a))) ∈ Q := by
    intro a
    have hx := hpX a
    rw [← hQc] at hx
    exact hx
  obtain ⟨Z0, hZ0, hZ0le⟩ := Ideal.exists_minimalPrimes_le hSZ
  have hStZ0 := hSt _ _ (Ideal.comap_mono hZ0le) hStZ
  have hQc' : St (Q.comap (algebraMap (R ⧸ ii) (o.B (Fin.last h)))) ∨ Th (Fin.last h) Q := by
    rcases hpS with h1 | h1
    · left
      rw [hQc]
      exact h1
    · right
      exact h1 Q hQ hQc
  have hZ0Q := hkey (Fin.last h) Z0 Q hZ0.1.1 hQ hStZ0 (o.dim _ Z0 hZ0) hQc'
  have hann := (o.fib _ Q hQ hQX).mp (hZ0.1.2.trans hZ0Q)
  rw [hQc] at hann
  exact hann
end
