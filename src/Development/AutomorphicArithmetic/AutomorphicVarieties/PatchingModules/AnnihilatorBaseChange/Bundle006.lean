module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchedSupportCompletions
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.Bundle001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle002
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
public import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection

@[expose] public section

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.quotientRegularAt_of_quotient_free_over_powerSeries :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [Fintype σ] (s : MvPowerSeries σ Λ →+* R) (M : Type) [AddCommGroup M] [Module R M] (a j r : ℕ) (e : (M ⧸ ((kjIdeal Λ σ (a + 1) j).map s • ⊤ : Submodule R M)) ≃+ (Fin r → MvPowerSeries σ Λ ⧸ kjIdeal Λ σ (a + 1) j)), (∀ z m, e (s z • m) = z • e m) → QRegAt M (fun a => s (MvPowerSeries.X a)) (((maximalIdeal Λ).map (s.comp MvPowerSeries.C)) ^ j) a := by
  intro Λ R σ _ _ _ _ s M _ _ a j r e he c hc α
  classical
  rw [← kjMap Λ R σ s (a + 1) j] at hc
  have hsurj := Ideal.Quotient.mk_surjective (I := kjIdeal Λ σ (a + 1) j)
  choose t ht using fun β i => hsurj (e (Submodule.Quotient.mk (c β)) i)
  have hmono : ∀ β : σ →₀ ℕ, GlobalTheory.monoVal (fun a => s (MvPowerSeries.X a)) β =
      s (GlobalTheory.monoVal MvPowerSeries.X β) := fun β => by
    simp only [GlobalTheory.monoVal, Finsupp.prod, map_prod, map_pow]
  have h0 := congrArg e ((Submodule.Quotient.mk_eq_zero _).2 hc)

  rw [map_zero, ← Submodule.mkQ_apply, map_sum, map_sum] at h0
  simp only [map_smul, hmono, he, Submodule.mkQ_apply] at h0
  have hL : ∀ i, t α i ∈ kjIdeal Λ σ 1 j := by
    intro i
    have h1 := congrFun h0 i
    rw [Finset.sum_apply] at h1
    simp only [Pi.smul_apply, ← ht, Pi.zero_apply] at h1
    have h2 : (∑ β : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal (MvPowerSeries.X : σ → MvPowerSeries σ Λ) β.1 * t β i) ∈ kjIdeal Λ σ (a + 1) j := by

      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum, ← h1]
      rfl
    have h3 := qRegAt_mvPowerSeries Λ σ (maximalIdeal Λ ^ j) a (fun β => t β i)
      (by simpa [kjIdeal, Ideal.map_pow] using h2) α
    simpa [kjIdeal, Ideal.map_pow] using h3
  have hs := Submodule.Quotient.mk_surjective ((kjIdeal Λ σ (a + 1) j).map s • ⊤ : Submodule R M)
  choose m hm using fun i : Fin r => hs (e.symm (Pi.single i 1))
  have h4 : c α - ∑ i, s (t α i) • m i ∈ ((kjIdeal Λ σ (a + 1) j).map s • ⊤ : Submodule R M) := by
    rw [← Submodule.Quotient.eq]
    apply e.injective

    rw [← Submodule.mkQ_apply _ (∑ i, _), map_sum, map_sum]
    simp only [map_smul, he, Submodule.mkQ_apply, hm, AddEquiv.apply_symm_apply]
    funext k
    rw [Finset.sum_apply, Finset.sum_eq_single k]
    · rw [← ht, Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, mul_one]
      rfl
    · intro b _ hb
      simp [hb.symm]
    · simp
  have hle : kjIdeal Λ σ (a + 1) j ≤ kjIdeal Λ σ 1 j := by
    unfold kjIdeal
    exact sup_le_sup_right (Ideal.pow_le_pow_right (by omega)) _
  have h5 : c α ∈ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R M) := by
    rw [← sub_add_cancel (c α) (∑ i, s (t α i) • m i)]
    refine add_mem (Submodule.smul_mono_left (Ideal.map_mono hle) h4) (Submodule.sum_mem _ fun i _ => ?_)
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ (hL i)) Submodule.mem_top
  rw [kjMap, pow_one] at h5
  exact h5
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem const_bij {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] (U : Ultrafilter ℕ)
    (m : Ideal R) (I : ℕ → Ideal R) (hc : IsAdicComplete m X)
    (hf : ∀ j : ℕ, Finite (X ⧸ (m ^ j • ⊤ : Submodule R X)))
    (hI : ∀ j, (I j • ⊤ : Submodule R X) = m ^ j • ⊤) :
    Function.Bijective
      (ULim.mk (U : Filter ℕ) I (fun _ => X) ∘ₗ LinearMap.pi fun _ : ℕ => (LinearMap.id : X →ₗ[R] X)) := by
  have hb := ULim.const_bijective R ℕ U m X hc hf
  have key : ∀ p q : ℕ → X, ULim.mk (U : Filter ℕ) I (fun _ => X) p = ULim.mk (U : Filter ℕ) I (fun _ => X) q ↔
      ULim.mk (U : Filter ℕ) (fun j => m ^ j) (fun _ => X) p =
        ULim.mk (U : Filter ℕ) (fun j => m ^ j) (fun _ => X) q := by
    intro p q
    rw [← sub_eq_zero, ← map_sub, ULim.mk_eq_zero, ← sub_eq_zero (a := ULim.mk _ _ _ p), ← map_sub,
      ULim.mk_eq_zero]
    simp only [hI]
  refine ⟨fun a b hab => hb.1 ((key (fun _ => a) (fun _ => b)).1 hab), fun x => ?_⟩
  obtain ⟨p, rfl⟩ := ULim.mk_surjective _ _ _ x
  obtain ⟨z, hz⟩ := hb.2 (ULim.mk _ _ _ p)
  exact ⟨z, (key (fun _ => z) p).2 hz⟩

private theorem comp_smul {R : Type} [CommRing R] (F : Filter ℕ) (I : ℕ → Ideal R) (M M' : ℕ → Type)
    [∀ N, AddCommGroup (M N)] [∀ N, Module R (M N)] [∀ N, AddCommGroup (M' N)] [∀ N, Module R (M' N)]
    (ν : ℕ → ℕ) (hν : Tendsto ν F atTop) (hI : Antitone I) (f : R)
    (φ : ∀ N, (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))) →ₗ[R] (M' N ⧸ (I (ν N) • ⊤ : Submodule R (M' N))))
    (ψ : ∀ N, (M' N ⧸ (I (ν N) • ⊤ : Submodule R (M' N))) →ₗ[R] (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))))
    (h : ∀ᶠ N in F, ∀ z, ψ N (φ N z) = f • z)
    (Φ : ULim F I M →ₗ[R] ULim F I M') (Ψ : ULim F I M' →ₗ[R] ULim F I M)
    (hΦ : ∀ (p : ∀ N, M N) (p' : ∀ N, M' N), (∀ᶠ N in F, Submodule.Quotient.mk (p' N) =
      φ N (Submodule.Quotient.mk (p N))) → Φ (ULim.mk F I M p) = ULim.mk F I M' p')
    (hΨ : ∀ (p : ∀ N, M' N) (p' : ∀ N, M N), (∀ᶠ N in F, Submodule.Quotient.mk (p' N) =
      ψ N (Submodule.Quotient.mk (p N))) → Ψ (ULim.mk F I M' p) = ULim.mk F I M p') (z : ULim F I M) :
    Ψ (Φ z) = f • z := by
  obtain ⟨p, rfl⟩ := ULim.mk_surjective _ _ _ z
  choose q hq using fun N => Submodule.Quotient.mk_surjective _ (φ N (Submodule.Quotient.mk (p N)))
  rw [hΦ p q (Eventually.of_forall hq), ← map_smul]
  refine hΨ q (f • p) (h.mono fun N hN => ?_)
  rw [hq, hN]
  rfl

theorem UpperTheory.V.Pa.Core.exists_ultraLimit_pair_of_eventual_quotient_maps :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [Fintype σ] (s : MvPowerSeries σ Λ →+* R) [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (U : Ultrafilter ℕ) (f : R) (M : ℕ → Type) [∀ N, AddCommGroup (M N)] [∀ N, Module R (M N)] (X : Type) [AddCommGroup X] [Module R X] [Module Λ X] [Module.Finite Λ X], (U : Filter ℕ) ≤ atTop → (∀ (a : Λ) (x : X), a • x = s (MvPowerSeries.C a) • x) → (∀ a (x : X), s (MvPowerSeries.X a) • x = 0) → (∀ j, ∀ᶠ N in (U : Filter ℕ), ∃ (φ : (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X))), (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z) → ∃ (Φ : X →ₗ[R] ULim (U : Filter ℕ) (fun j => Ideal.span (Set.range (fun a => s (MvPowerSeries.X a))) ⊔ ((maximalIdeal Λ).map (s.comp MvPowerSeries.C)) ^ j) M) (Ψ : ULim (U : Filter ℕ) (fun j => Ideal.span (Set.range (fun a => s (MvPowerSeries.X a))) ⊔ ((maximalIdeal Λ).map (s.comp MvPowerSeries.C)) ^ j) M →ₗ[R] X), (∀ z, Φ (Ψ z) = f • z) ∧ ∀ z, Ψ (Φ z) = f • z := by
  intro Λ R σ _ _ _ _ s _ _ _ U f M _ _ X _ _ _ _ hU hs hy h
  classical
  letI : Algebra Λ R := (s.comp MvPowerSeries.C).toAlgebra
  haveI : IsScalarTower Λ R X := IsScalarTower.of_algebraMap_smul fun a x => (hs a x).symm
  set m : Ideal R := (maximalIdeal Λ).map (s.comp MvPowerSeries.C) with hm
  set I : ℕ → Ideal R := fun j => Ideal.span (Set.range (fun a => s (MvPowerSeries.X a))) ⊔ m ^ j with hIdef
  have hkj : ∀ j, (kjIdeal Λ σ 1 j).map s = I j := fun j => by rw [kjMap, pow_one]
  have h' : ∀ j, ∀ᶠ N in (U : Filter ℕ), ∃ (φ : (X ⧸ (I j • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ (I j • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ (I j • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ (I j • ⊤ : Submodule R X))), (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z := by
    intro j
    rw [← hkj j]
    exact h j
  obtain ⟨ν, hν, hP⟩ := exists_diag _ hU _ h'
  have hanti : Antitone I := fun a b hab => sup_le_sup_left (Ideal.pow_le_pow_right hab) _
  have hex : ∀ N, ∃ (φ : (X ⧸ (I (ν N) • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ (I (ν N) • ⊤ : Submodule R X))), (∃ (φ : (X ⧸ (I (ν N) • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ (I (ν N) • ⊤ : Submodule R X))), (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z) → (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z := by
    intro N
    by_cases hN : ∃ (φ : (X ⧸ (I (ν N) • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ (I (ν N) • ⊤ : Submodule R X))), (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z
    · obtain ⟨φ, ψ, hh⟩ := hN
      exact ⟨φ, ψ, fun _ => hh⟩
    · exact ⟨0, 0, fun hh => absurd hh hN⟩
  choose φ ψ hφψ using hex
  have hgood := hP.mono fun N hN => hφψ N (hN _ le_rfl)
  obtain ⟨Φ, hΦ⟩ := ulimQuot R U I (fun _ => X) M ν φ hanti hν
  obtain ⟨Ψ, hΨ⟩ := ulimQuot R U I M (fun _ => X) ν ψ hanti hν
  have h1 := comp_smul U I (fun _ => X) M ν hν hanti f φ ψ (hgood.mono fun _ hN => hN.2) Φ Ψ hΦ hΨ
  have h2 := comp_smul U I M (fun _ => X) ν hν hanti f ψ φ (hgood.mono fun _ hN => hN.1) Ψ Φ hΨ hΦ
  have hc : IsAdicComplete m X :=
    (IsAdicComplete.map_algebraMap_iff (S := R) (maximalIdeal Λ) X).2 (AnnihilatorQuotientFinite.finCompl Λ X _)
  have hf : ∀ j : ℕ, Finite (X ⧸ (m ^ j • ⊤ : Submodule R X)) := by
    intro j
    haveI : Finite (Λ ⧸ maximalIdeal Λ) := inferInstanceAs (Finite (ResidueField Λ))
    haveI : Finite (Λ ⧸ maximalIdeal Λ ^ j) := Ideal.finite_quotient_pow (IsNoetherian.noetherian _) j
    haveI : Finite (X ⧸ (maximalIdeal Λ ^ j • ⊤ : Submodule Λ X)) :=
      Submodule.finite_quotient_smul _ Module.Finite.fg_top
    have hle : (maximalIdeal Λ ^ j • ⊤ : Submodule Λ X) ≤ (m ^ j • ⊤ : Submodule R X).restrictScalars Λ := by
      refine Submodule.smul_le.2 fun a ha x _ => ?_
      rw [Submodule.restrictScalars_mem, hs]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      rw [hm, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem (s.comp MvPowerSeries.C) ha
    haveI : Finite (X ⧸ (m ^ j • ⊤ : Submodule R X).restrictScalars Λ) :=
      Finite.of_surjective _ (Submodule.factor_surjective hle)
    exact Finite.of_equiv _ (Submodule.Quotient.restrictScalarsEquiv Λ _).toEquiv
  have hI : ∀ j, (I j • ⊤ : Submodule R X) = m ^ j • ⊤ := by
    intro j
    have h0 : (Ideal.span (Set.range (fun a => s (MvPowerSeries.X a))) • ⊤ : Submodule R X) = ⊥ := by
      rw [← Submodule.le_annihilator_iff, Ideal.span_le]
      rintro _ ⟨a, rfl⟩
      exact Submodule.mem_annihilator.2 fun x _ => hy a x
    show ((_ ⊔ _ : Ideal R) • ⊤ : Submodule R X) = _
    rw [Submodule.sup_smul, h0, bot_sup_eq]
  let e := LinearEquiv.ofBijective _ (const_bij U m I hc hf hI)
  refine ⟨Φ ∘ₗ e.toLinearMap, e.symm.toLinearMap ∘ₗ Ψ, fun z => ?_, fun z => ?_⟩
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact h2 z
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [h1, map_smul, LinearEquiv.symm_apply_apply]
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem exists_pow_maximalIdeal_smul_finite_eq_zero (R Q : Type) [CommRing R] [IsLocalRing R] [AddCommGroup Q] [Module R Q] [Finite Q] :
    ∃ c : ℕ, ∀ a ∈ maximalIdeal R ^ c, ∀ z : Q, a • z = 0 :=
  _root_.UpperTheory.Reformulated.B.FiniteModuleMaximalIdealAnnihilation.exists_pow_maximalIdeal_smul_finite_eq_zero R Q

private theorem finite_quotient_of_power_maximal_ideal_le (Λ R X : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [IsNoetherianRing Λ]
    [Finite (ResidueField Λ)] [AddCommGroup X] [Module R X] [Module Λ X] [Module.Finite Λ X] (t : Λ →+* R)
    (ht : ∀ (a : Λ) (x : X), a • x = t a • x) (j : ℕ) (K : Ideal R) (hK : (maximalIdeal Λ).map t ^ j ≤ K) :
    Finite (X ⧸ (K • ⊤ : Submodule R X)) := by
  haveI h0 : Finite (Λ ⧸ maximalIdeal Λ) := ‹Finite (ResidueField Λ)›
  haveI h1 : Finite (Λ ⧸ maximalIdeal Λ ^ j) := Ideal.finite_quotient_pow (IsNoetherian.noetherian _) j
  haveI h2 : Finite (X ⧸ (maximalIdeal Λ ^ j • ⊤ : Submodule Λ X)) :=
    Submodule.finite_quotient_smul _ (Module.Finite.fg_top)
  have hle : ∀ x ∈ (maximalIdeal Λ ^ j • ⊤ : Submodule Λ X), x ∈ (K • ⊤ : Submodule R X) := by
    intro x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha y _
      rw [ht]
      refine Submodule.smul_mem_smul (hK ?_) Submodule.mem_top
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ ha
    · intro a b ha hb
      exact Submodule.add_mem _ ha hb
  let g : (X ⧸ (maximalIdeal Λ ^ j • ⊤ : Submodule Λ X)) → (X ⧸ (K • ⊤ : Submodule R X)) := fun q =>
    Quotient.liftOn' q (fun x => Submodule.Quotient.mk x)
      (fun a b h => (Submodule.Quotient.eq _).2 (hle _ ((Submodule.quotientRel_def _).1 h)))
  refine Finite.of_surjective g fun z => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact ⟨Submodule.Quotient.mk x, rfl⟩

theorem UpperTheory.V.Pa.Core.finite_quotient_of_ultrafilter_limit_module :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [Fintype σ] (s : MvPowerSeries σ Λ →+* R) [IsNoetherianRing Λ] [Finite (ResidueField Λ)] [IsLocalRing R] (U : Ultrafilter ℕ) (f : R) (M : ℕ → Type) [∀ N, AddCommGroup (M N)] [∀ N, Module R (M N)] (X : Type) [AddCommGroup X] [Module R X] [Module Λ X] [Module.Finite Λ X], (∀ (a : Λ) (x : X), a • x = s (MvPowerSeries.C a) • x) → (∀ a (x : X), s (MvPowerSeries.X a) • x = 0) → (∀ j, ∀ᶠ N in (U : Filter ℕ), ∃ (φ : (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X))), (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z) → ∀ k j : ℕ, ∃ c : ℕ, ∀ᶠ N in (U : Filter ℕ), ∀ a ∈ maximalIdeal R ^ c, ∀ x : M N, (f ^ k * a) • x ∈ ((Ideal.span (Set.range (fun a => s (MvPowerSeries.X a))) ^ k ⊔ ((maximalIdeal Λ).map (s.comp MvPowerSeries.C)) ^ j) • ⊤ : Submodule R (M N)) := by
  intro Λ R σ _ _ _ _ s _ _ _ U f M _ _ X _ _ _ _ hC _ h k j
  have hK := kjMap Λ R σ s 1 j
  haveI : Finite (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X)) :=
    finite_quotient_of_power_maximal_ideal_le Λ R X (s.comp MvPowerSeries.C) hC j _ (hK ▸ le_sup_right)
  obtain ⟨c, hc⟩ := exists_pow_maximalIdeal_smul_finite_eq_zero R (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X))
  refine ⟨c * k, (h j).mono ?_⟩
  rintro N ⟨φ, ψ, hφψ, -⟩ a ha x
  have h1 : ((Ideal.span {f} * maximalIdeal R ^ c) • ⊤ : Submodule R (M N)) ≤ (kjIdeal Λ σ 1 j).map s • ⊤ := by
    refine Submodule.smul_le.2 ?_
    intro r hr y _
    obtain ⟨b, hb, rfl⟩ := Ideal.mem_span_singleton_mul.1 hr
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul, mul_comm, mul_smul, ← hφψ, ← map_smul,
      hc b hb, map_zero]
  rw [hK, pow_one, sup_comm] at h1
  have h2 := (smul_pow_le_of_step R (maximalIdeal R ^ c) _ _ f).2 (M N) h1 k
  rw [sup_comm]
  refine h2 (Submodule.smul_mem_smul (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_) Submodule.mem_top)
  rwa [← pow_mul]
end
