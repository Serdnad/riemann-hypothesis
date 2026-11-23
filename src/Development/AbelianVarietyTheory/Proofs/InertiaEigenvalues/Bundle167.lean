module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeCountProdOfIdempotentSeparable
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle142
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle098
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle023
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle141
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle070
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle077
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle086
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle117
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle104
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle143
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle144
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle103
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle100

@[expose] public section

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial

theorem _root_.GlobalTheory.T.finite_integralClosure_of_separable_involution_algebra : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → Module.Finite K.O (integralClosure K.O B.A) := by
  first | exact @GlobalTheory.UnitLemma.IntegralFinite.finite_integralClosure | exact GlobalTheory.UnitLemma.IntegralFinite.finite_integralClosure | (intros; apply GlobalTheory.UnitLemma.IntegralFinite.finite_integralClosure <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.latticeCount_and_gramDetSign_norm_class : ∀ (K : UQ) (B : InvAlg K) (x : B.A) (u : B.Aˣ), B.N (x * (u * B.σ (u : B.A))) = B.N x ∧ K.eta (B.gramDet (x * (u * B.σ (u : B.A)))) = K.eta (B.gramDet x) := by
  first | exact @GlobalTheory.UnitLemma.NormClass.N_norm_class | exact GlobalTheory.UnitLemma.NormClass.N_norm_class | (intros; apply GlobalTheory.UnitLemma.NormClass.N_norm_class <;> assumption)
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem _root_.GlobalTheory.T.card_residueField_adjoin_unitary_prod : ∀ (K : UQ), K.Odd → ∀ B₁ B₂ : InvAlg K, B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → ∀ hl : IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)), ∃ d : ℕ, Odd d ∧ Nat.card (@IsLocalRing.ResidueField (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) _ hl) = K.q ^ (2 * d) := by
  first | exact @GlobalTheory.UnitLemma.ResDeg.card_residueField_prod | exact GlobalTheory.UnitLemma.ResDeg.card_residueField_prod | (intros; apply GlobalTheory.UnitLemma.ResDeg.card_residueField_prod <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.latticeCount_prod_of_idempotent_separable : ∀ (K : UQ) (B₁ B₂ : InvAlg K), ((1, 0) : B₁.A × B₂.A) ∈ Algebra.adjoin K.O ({(B₁.g, B₂.g)} : Set (B₁.A × B₂.A)) → (B₁.P * B₂.P).Separable → ∀ (x₁ : B₁.A) (x₂ : B₂.A), IsUnit x₁ → IsUnit x₂ → B₁.σ x₁ = x₁ → B₂.σ x₂ = x₂ → (B₁.prod B₂).N (x₁, x₂) = B₁.N x₁ * B₂.N x₂ := by
  first | exact @GlobalTheory.UnitLemma.ProdCount.N_prod | exact GlobalTheory.UnitLemma.ProdCount.N_prod | (intros; apply GlobalTheory.UnitLemma.ProdCount.N_prod <;> assumption)
end

section

noncomputable section

open Polynomial

namespace GlobalTheory.UnitLemma.PrincipalLatDVR

theorem isReduced_of_charpoly_separable {E A : Type} [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] (g : A) (hP : (LinearMap.mulLeft E g).charpoly.Separable) :
    IsReduced A := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨f, rfl⟩ := exists_aeval_eq_of_charpoly_separable g hP a
  obtain ⟨m, hm⟩ := ha
  have hf : aeval (LinearMap.mulLeft E g) (f ^ m) = 0 := by
    have h2 : aeval g (f ^ m) = 0 := by rw [map_pow, hm]
    have := aeval_algHom_apply (Algebra.lmul E A) g (f ^ m)
    rw [h2, map_zero] at this
    exact this
  have h1 := GlobalTheory.CharpolyDvd.charpoly_dvd_pow_finrank _ _ hf
  rw [← pow_mul] at h1
  obtain ⟨q, hq⟩ := hP.squarefree.isRadical _ _ h1
  have hc : aeval g (LinearMap.mulLeft E g).charpoly = 0 := by
    have h := LinearMap.aeval_self_charpoly (LinearMap.mulLeft E g)
    have h' : Algebra.lmul E A (aeval g (LinearMap.mulLeft E g).charpoly) = 0 := by
      rw [← aeval_algHom_apply]; exact h
    simpa using congrArg (fun F : Module.End E A => F 1) h'
  rw [hq, map_mul, hc, zero_mul]

theorem isPrincipalIdealRing_integralClosure_field {O E L : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [Field L]
    [Algebra E L] [Algebra O L] [IsScalarTower O E L] [FiniteDimensional E L] :
    IsPrincipalIdealRing (integralClosure O L) := by
  haveI : IsDedekindDomain (integralClosure O L) :=
    GlobalTheory.isDedekindDomain_integralClosure_of_dimensionLEOne E
  have hinj : Function.Injective (algebraMap O L) := by
    rw [IsScalarTower.algebraMap_eq O E L]
    exact (algebraMap E L).injective.comp (IsFractionRing.injective O E)
  haveI : Module.IsTorsionFree O (integralClosure O L) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr fun x y h => hinj (congrArg Subtype.val h)
  apply IsPrincipalIdealRing.of_finite_primes
  have hfin := IsDedekindDomain.primesOver_finite (IsLocalRing.maximalIdeal O) (integralClosure O L)
  refine (hfin.insert ⊥).subset ?_
  intro P hP
  by_cases h : P = ⊥
  · exact Or.inl h
  · right
    haveI : P.IsPrime := hP
    have hne : P.comap (algebraMap O (integralClosure O L)) ≠ ⊥ := fun h0 => h (Ideal.eq_bot_of_comap_eq_bot h0)
    have hmax : (P.comap (algebraMap O (integralClosure O L))).IsMaximal :=
      Ring.DimensionLEOne.maximalOfPrime hne inferInstance
    refine ⟨hP, ⟨?_⟩⟩
    exact (IsLocalRing.eq_maximalIdeal hmax).symm

theorem isPrincipalIdealRing_integralClosure {O E A : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A]
    [Algebra E A] [Algebra O A] [IsScalarTower O E A] [Module.Finite E A] [IsReduced A] :
    IsPrincipalIdealRing (integralClosure O A) := by
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite E A
  let ψ : A ≃ₐ[O] (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) :=
    (IsArtinianRing.equivPi A).restrictScalars O
  haveI hpir : ∀ I : MaximalSpectrum A, IsPrincipalIdealRing (integralClosure O (A ⧸ I.asIdeal)) := by
    intro I
    haveI := I.isMaximal
    letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : FiniteDimensional E (A ⧸ I.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ E I.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    exact isPrincipalIdealRing_integralClosure_field (E := E)
  let G : (∀ I : MaximalSpectrum A, integralClosure O (A ⧸ I.asIdeal)) →ₐ[O]
      (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) :=
    Pi.algHom O _ fun I => (integralClosure O (A ⧸ I.asIdeal)).val.comp (Pi.evalAlgHom O _ I)
  let F := (ψ.symm.toAlgHom.comp G).codRestrict (integralClosure O A) fun l =>
    (PrincipalLat.isIntegral_pi' (G l) fun I => (l I).2).map ψ.symm
  refine IsPrincipalIdealRing.of_surjective F ?_
  intro x
  refine ⟨fun I => ⟨ψ x I, x.2.map ((Pi.evalAlgHom O _ I).comp ψ.toAlgHom)⟩, ?_⟩
  apply Subtype.ext
  change ψ.symm (G _) = (x : A)
  have : G (fun I => ⟨ψ x I, x.2.map ((Pi.evalAlgHom O _ I).comp ψ.toAlgHom)⟩) = ψ x := rfl
  rw [this, AlgEquiv.symm_apply_apply]

theorem eq_mulLat_integralClosure_of_separable : ∀ (O E A : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A]
    [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A),
    (LinearMap.mulLeft E g).charpoly.Separable → ∀ N : Submodule O A, IsLat O E N →
    (∀ x ∈ integralClosure O A, ∀ y ∈ N, x * y ∈ N) →
    ∃ t : Aˣ, N = mulLat O (t : A) (Subalgebra.toSubmodule (integralClosure O A)) := by
  intro O E A _ _ _ _ _ _ _ _ _ _ _ g hsep N hN hst
  haveI := isReduced_of_charpoly_separable g hsep
  haveI := isPrincipalIdealRing_integralClosure (O := O) (E := E) (A := A)
  exact PrincipalLat.eq_mulLat_of_isPrincipalIdealRing N hN hst

end GlobalTheory.UnitLemma.PrincipalLatDVR
end
end

section

noncomputable section

namespace GlobalTheory.StableLatCount

open GlobalTheory.UnitLemma Polynomial

theorem card_stable_lattices : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂), resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly ≠ 0 → ∀ (M₁ : Submodule O A₁) (M₂ : Submodule O A₂), IsLat O E M₁ → IsLat O E M₂ → (∀ y ∈ M₁, g₁ * y ∈ M₁) → (∀ y ∈ M₂, g₂ * y ∈ M₂) → (Nat.card {M : Submodule O (A₁ × A₂) // (∀ y ∈ M, (g₁, g₂) * y ∈ M) ∧ M.comap (LinearMap.inl O A₁ A₂) = M₁ ∧ M.map (LinearMap.snd O A₁ A₂) = M₂} : ℚ) = (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^ val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) := by
  intro O _ _ _ _ E _ _ _ A₁ A₂ _ _ _ _ _ _ _ _ _ _ g₁ g₂ hres M₁ M₂ hM₁ hM₂ hs₁ hs₂
  have hdet : LinearMap.det (adE E g₁ g₂) = resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly :=
    GlobalTheory.T.det_commutator_map_eq_charpoly_resultant E A₁ A₂ (LinearMap.mulLeft E g₁) (LinearMap.mulLeft E g₂)
  have hdet0 : LinearMap.det (adE E g₁ g₂) ≠ 0 := hdet ▸ hres
  have hunit : IsUnit (adE E g₁ g₂) := (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet0)
  have hbij : Function.Bijective ((adE E g₁ g₂).restrictScalars O) := by
    have := (Module.End.isUnit_iff _).1 hunit
    simpa only [LinearMap.coe_restrictScalars] using this
  have hN : ∀ x ∈ homLat E M₁ M₂, (adE E g₁ g₂) x ∈ homLat E M₁ M₂ := by
    intro ψ hψ x hx
    rw [adE_apply]
    exact M₁.sub_mem (hs₁ _ (hψ x hx)) (hψ _ (hs₂ x hx))
  have hL := GlobalTheory.T.lattice_hom_submodule_fg_and_span_eq_top O E A₁ A₂ M₁ M₂ hM₁ hM₂
  have h2 := GlobalTheory.card_kernel_quot_of_bijective O _ (homLat E M₁ M₂) ((adE E g₁ g₂).restrictScalars O) hbij hN
  simp only [LinearMap.coe_restrictScalars] at h2
  rw [GlobalTheory.StableGraph.card_stable_eq_card_hom O A₁ A₂ g₁ g₂ M₁ M₂ hs₂, GlobalTheory.StableLatCount.card_commMaps_eq_card_homQuot O E A₁ A₂ g₁ g₂ M₁ M₂ hM₂ hs₁ hs₂, h2,
    GlobalTheory.LatIndexDet.card_quot_eq_pow_val O E _ (homLat E M₁ M₂) hL.1 hL.2 (adE E g₁ g₂) hdet0 hN, hdet]

end GlobalTheory.StableLatCount
end
end

section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.haar_measure_L_unit_smul_absK_sq : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μ : Measure A.L), μ.IsAddHaarMeasure → ∀ (c : A.Kˣ) (S : Set A.L), μ {y : A.L | ∃ z ∈ S, y = algebraMap A.K A.L (c : A.K) * z} = ENNReal.ofReal (A.absK (c : A.K) ^ 2) * μ S := by
  first | exact @GlobalTheory.JR.ScaleHaarL.main | exact GlobalTheory.JR.ScaleHaarL.main | (intros; apply GlobalTheory.JR.ScaleHaarL.main <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.TruncInt

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem absK_ne_zero (A : Et F E) {t : A.K} (h : IsUnit t) : A.absK t ≠ 0 := by
  unfold Et.absK
  rw [dif_pos h]
  exact NNReal.coe_ne_zero.2 (IsUnit.map (distribHaarChar A.K) (Group.isUnit h.unit)).ne_zero

theorem absK_nonneg (A : Et F E) (t : A.K) : 0 ≤ A.absK t := by
  unfold Et.absK
  split_ifs <;> simp

theorem isLocallyConstant_indicator {X : Type} [TopologicalSpace X] {W : Set X} (hW : IsClopen W) (c : ℂ) :
    IsLocallyConstant (W.indicator fun _ => c) := fun s => by
  have h := Set.indicator_const_preimage W s c
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h <;> rw [h]
  exacts [isOpen_univ, hW.isOpen, hW.isClosed.isOpen_compl, isOpen_empty]

end GlobalTheory.JR.TruncInt


open GlobalTheory.JR.TruncInt in
theorem GlobalTheory.JR.truncated_integral_eq_vol_mul_orbL : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), ((∀ s : A.K, A.NL (algebraMap A.K A.L s) = s ^ 2) ∧ (∀ y y' : A.L, A.NL (y * y') = A.NL y * A.NL y') ∧ (∀ t : unitary A.L, A.NL (t : A.L) = 1) ∧ (∀ y : A.L, IsUnit (A.NL y) → IsUnit y) ∧ (∀ y : A.L, IsUnit y → IsUnit (A.NL y))) → ((∀ s t : A.K, A.absK (s * t) = A.absK s * A.absK t) ∧ (∀ s s' : A.K, s ∈ A.OK → s' ∈ A.OK → s * s' = 1 → A.absK s = 1) ∧ (∀ (μ : Measure A.K), μ.IsAddHaarMeasure → ∀ (x : A.Kˣ) (a : A.K) (S : Set A.K), MeasurableSet S → μ {a' : A.K | (x : A.K) * a' - a ∈ S} = ENNReal.ofReal (A.absK (x : A.K))⁻¹ * μ S)) → ∀ (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (m : A.Meas ψ) (x : A.Kˣ) (y₀ : A.L), IsUnit y₀ → ∀ (D : AddSubgroup A.K), IsOpen (D : Set A.K) → IsCompact (D : Set A.K) → ∀ φ : A.L → ℂ, IsTest φ → (∀ b ∈ D, ∃ s s' : A.K, s ∈ A.OK ∧ s' ∈ A.OK ∧ s * s' = 1 ∧ s ^ 2 = 1 + Ring.inverse ((x : A.K) * A.NL y₀) * b ∧ ∀ y : A.L, φ (y * algebraMap A.K A.L s) = φ y) → ∫ y, φ y * Set.indicator (D : Set A.K) (fun _ => (1 : ℂ)) ((x : A.K) * A.NL y - (x : A.K) * A.NL y₀) ∂(m.μL x) = ((m.μK D).toReal : ℂ) * A.orbL m.ν φ y₀ := by
  intro F E _ _ _ _ _ A hN hK ψ hψ m x y₀ hy₀ D hDo hDc φ hφ hsq
  classical
  obtain ⟨hNs, hNmul, hNt, hNu1, hNu2⟩ := hN
  obtain ⟨habs, habs1, hvol⟩ := hK
  set a : A.K := (x : A.K) * A.NL y₀ with ha_def
  have ha : IsUnit a := x.isUnit.mul (hNu2 y₀ hy₀)
  have hx : IsUnit (x : A.K) := x.isUnit
  have hkey : ∀ b : A.K, ∀ s : A.K, s ^ 2 = 1 + Ring.inverse a * b → a * s ^ 2 = a + b := by
    intro b s hs
    rw [hs, mul_add, mul_one, ← mul_assoc, Ring.mul_inverse_cancel a ha, one_mul]
  have hsec : ∀ a' : A.K, ∀ s : A.K, s ^ 2 = 1 + Ring.inverse a * ((x : A.K) * a' - a) →
      A.NL (y₀ * algebraMap A.K A.L s) = a' := by
    intro a' s hs
    have h1 := hkey _ s hs
    rw [hNmul, hNs]
    apply hx.mul_left_cancel
    calc (x : A.K) * (A.NL y₀ * s ^ 2) = a * s ^ 2 := by rw [ha_def]; ring
      _ = _ := by rw [h1]; ring
  have habsT : ∀ a' : A.K, (x : A.K) * a' - a ∈ (D : Set A.K) →
      A.absK a' = A.absK a / A.absK x ∧ IsUnit a' := by
    intro a' hD
    obtain ⟨s, s', hs, hs', hss, hsq2, -⟩ := hsq _ hD
    have h1 := hkey _ s hsq2
    have h2 : (x : A.K) * a' = a * s ^ 2 := by rw [h1]; ring
    have hsu : IsUnit s := ⟨⟨s, s', hss, by rw [mul_comm]; exact hss⟩, rfl⟩
    have hu : IsUnit a' := by
      have : IsUnit ((x : A.K) * a') := by rw [h2]; exact ha.mul (hsu.pow 2)
      exact isUnit_of_mul_isUnit_right this
    refine ⟨?_, hu⟩
    have h3 := congrArg A.absK h2
    rw [habs (x : A.K) a', habs a (s ^ 2), pow_two, habs s s, habs1 s s' hs hs' hss, mul_one, mul_one] at h3
    rw [eq_div_iff (TruncInt.absK_ne_zero A hx), ← h3]; ring
  set f : A.L → A.K := fun y => (x : A.K) * A.NL y - a with hf
  have hfc : Continuous f := (continuous_const.mul (EtMeas.continuous_NL A)).sub continuous_const
  have hSu : ∀ y, f y ∈ (D : Set A.K) → IsUnit y := fun y hy => hNu1 y (habsT _ hy).2
  set h : A.L → ℂ := fun y => φ y * Set.indicator (D : Set A.K) (fun _ => (1 : ℂ)) (f y) with hh
  show ∫ y, h y ∂(m.μL x) = _
  have hDcl : IsClosed (D : Set A.K) := AddSubgroup.isClosed_of_isOpen D hDo
  have hTest : IsTest h := by
    refine ⟨hφ.1.mul ((TruncInt.isLocallyConstant_indicator ⟨hDcl, hDo⟩ (1 : ℂ)).comp_continuous hfc), ?_⟩
    exact hφ.2.mul_right
  have hsupp : tsupport h ⊆ {y | IsUnit y} := by
    refine (closure_minimal ?_ (hDcl.preimage hfc)).trans ?_
    · intro y hy
      by_contra hn
      exact hy (by simp only [h, Set.indicator_of_notMem (show f y ∉ (D : Set A.K) from hn), mul_zero])
    · intro y hy
      exact hSu y hy
  have hμ := (GlobalTheory.JR.exists_meas_and_scale F E A ψ hψ).2 m x
  rw [hμ, integral_smul_measure, ENNReal.toReal_ofReal (TruncInt.absK_nonneg A _)]
  have hxa : A.absK a / A.absK x ≠ 0 :=
    div_ne_zero (TruncInt.absK_ne_zero A ha) (TruncInt.absK_ne_zero A hx)
  have hxaC : ((A.absK a / A.absK x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hxa
  have hpt : ∀ y, h y = ((A.absK a / A.absK x : ℝ) : ℂ) * (h y * ((A.absK (A.NL y) : ℂ))⁻¹) := by
    intro y
    by_cases hy : f y ∈ (D : Set A.K)
    · rw [(habsT _ hy).1, mul_comm (h y), mul_inv_cancel_left₀ hxaC]
    · simp only [h, Set.indicator_of_notMem hy, mul_zero, zero_mul]
  have hI1 : ∫ y, h y ∂(m.μL 1) = ∫ y, ((A.absK a / A.absK x : ℝ) : ℂ) * (h y * ((A.absK (A.NL y) : ℂ))⁻¹) ∂(m.μL 1) :=
    integral_congr_ae (ae_of_all _ hpt)
  rw [hI1, integral_const_mul]
  let σ : A.K → A.L := fun a' =>
    if hb : (x : A.K) * a' - a ∈ (D : Set A.K) then y₀ * algebraMap A.K A.L (Classical.choose (hsq _ hb))
    else if he : ∃ y : A.L, A.NL y = a' then Classical.choose he else 0
  have hσD : ∀ a' (hb : (x : A.K) * a' - a ∈ (D : Set A.K)), ∃ s : A.K, σ a' = y₀ * algebraMap A.K A.L s ∧
      s ^ 2 = 1 + Ring.inverse a * ((x : A.K) * a' - a) ∧ ∀ y : A.L, φ (y * algebraMap A.K A.L s) = φ y := by
    intro a' hb
    obtain ⟨s', -, -, -, h4, h5⟩ := Classical.choose_spec (hsq _ hb)
    exact ⟨Classical.choose (hsq _ hb), by simp only [σ, dif_pos hb], h4, h5⟩
  have hσN : ∀ a', ((x : A.K) * a' - a ∈ (D : Set A.K) ∨ ∃ y : A.L, A.NL y = a') → A.NL (σ a') = a' := by
    intro a' hor
    by_cases hb : (x : A.K) * a' - a ∈ (D : Set A.K)
    · obtain ⟨s, hσs, hs2, -⟩ := hσD a' hb
      rw [hσs]; exact hsec a' s hs2
    · have he := hor.resolve_left hb
      simp only [σ, dif_neg hb, dif_pos he]
      exact Classical.choose_spec he
  have hσ : ∀ y : A.L, IsUnit y → A.NL (σ (A.NL y)) = A.NL y := fun y _ => hσN _ (Or.inr ⟨y, rfl⟩)
  rw [m.nat.2 σ hσ h hTest hsupp]
  set T : Set A.K := {a' | (x : A.K) * a' - a ∈ (D : Set A.K)} with hT
  have hTm : MeasurableSet T :=
    (hDo.preimage ((continuous_const.mul continuous_id).sub continuous_const)).measurableSet
  have hTN : T ⊆ {a' : A.K | ∃ y : A.L, IsUnit y ∧ A.NL y = a'} := by
    intro a' hb
    refine ⟨σ a', ?_, hσN a' (Or.inl hb)⟩
    exact hNu1 _ (by rw [hσN a' (Or.inl hb)]; exact (habsT a' hb).2)
  have hNL0 : A.NL 0 = 0 := by simpa using hNs 0
  have hpt2 : ∀ a', A.orbL m.ν h (σ a') * ((A.absK a' : ℂ))⁻¹ =
      T.indicator (fun a' => A.orbL m.ν φ y₀ * ((A.absK a' : ℂ))⁻¹) a' := by
    intro a'
    by_cases hb : a' ∈ T
    · obtain ⟨s, hσs, -, hφs⟩ := hσD a' hb
      have hNσ : A.NL (σ a') = a' := hσN a' (Or.inl hb)
      rw [Set.indicator_of_mem hb]
      congr 1
      unfold Et.orbL
      congr 1
      funext t
      have hft : f (t.1 * σ a') ∈ (D : Set A.K) := by
        show (x : A.K) * A.NL (t.1 * σ a') - a ∈ (D : Set A.K)
        rw [hNmul, hNt, hNσ, one_mul]; exact hb
      show φ (t.1 * σ a') * Set.indicator _ _ (f (t.1 * σ a')) = φ (t.1 * y₀)
      rw [Set.indicator_of_mem hft, mul_one, hσs, ← mul_assoc, hφs]
    · rw [Set.indicator_of_notMem hb]
      have hz : ∀ t : unitary A.L, h (t.1 * σ a') = 0 := by
        intro t
        have hft : f (t.1 * σ a') ∉ (D : Set A.K) := by
          by_cases he : ∃ y : A.L, A.NL y = a'
          · show (x : A.K) * A.NL (t.1 * σ a') - a ∉ (D : Set A.K)
            rw [hNmul, hNt, hσN a' (Or.inr he), one_mul]; exact hb
          · have h0 : σ a' = 0 := by simp only [σ, dif_neg (show ¬ ((x : A.K) * a' - a ∈ (D : Set A.K)) from hb), dif_neg he]
            show (x : A.K) * A.NL (t.1 * σ a') - a ∉ (D : Set A.K)
            rw [h0, mul_zero, hNL0, mul_zero, zero_sub]
            intro hD
            obtain ⟨s, s', -, -, hss, hs2, -⟩ := hsq _ hD
            have h1 := hkey _ s hs2
            rw [add_neg_cancel] at h1
            have hsu : IsUnit s := ⟨⟨s, s', hss, by rw [mul_comm]; exact hss⟩, rfl⟩
            have hu : IsUnit (a * s ^ 2) := ha.mul (hsu.pow 2)
            rw [h1, isUnit_zero_iff] at hu
            haveI := subsingleton_of_zero_eq_one hu
            exact he ⟨0, Subsingleton.elim _ _⟩
        simp only [h, Set.indicator_of_notMem hft, mul_zero]
      simp only [Et.orbL, hz, integral_zero, zero_mul]
  have hI2 : ∫ a' in {a' : A.K | ∃ y : A.L, IsUnit y ∧ A.NL y = a'}, A.orbL m.ν h (σ a') * ((A.absK a' : ℂ))⁻¹ ∂m.μK =
      ∫ a' in {a' : A.K | ∃ y : A.L, IsUnit y ∧ A.NL y = a'},
        T.indicator (fun a' => A.orbL m.ν φ y₀ * ((A.absK a' : ℂ))⁻¹) a' ∂m.μK :=
    integral_congr_ae (ae_of_all _ hpt2)
  rw [hI2, setIntegral_indicator hTm, Set.inter_eq_right.2 hTN]
  have hI3 : ∫ a' in T, A.orbL m.ν φ y₀ * ((A.absK a' : ℂ))⁻¹ ∂m.μK =
      ∫ a' in T, A.orbL m.ν φ y₀ * (((A.absK a / A.absK x : ℝ) : ℂ))⁻¹ ∂m.μK :=
    setIntegral_congr_fun hTm (fun a' hb => by simp only [(habsT a' hb).1])
  rw [hI3, setIntegral_const, Measure.real, hT, hvol m.μK m.sdK.1 x a _ hDo.measurableSet, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.2 (TruncInt.absK_nonneg A _))]
  have hx0 : A.absK x ≠ 0 := TruncInt.absK_ne_zero A hx
  have ha0 : A.absK a ≠ 0 := TruncInt.absK_ne_zero A ha
  simp only [Complex.real_smul]
  have hx0C : ((A.absK x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx0
  have ha0C : ((A.absK a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha0
  push_cast
  field_simp
end
end

section

open GlobalTheory.JR MeasureTheory

theorem _root_.GlobalTheory.T.absK_mul_of_etale_splitting : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (t : A.K), A.absK t = A₁.absK (eK t).1 * A₂.absK (eK t).2 := by
  first | exact @GlobalTheory.JR.EtProdAbs.absK_prod | exact GlobalTheory.JR.EtProdAbs.absK_prod | (intros; apply GlobalTheory.JR.EtProdAbs.absK_prod <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_selfDual_measures_and_absK_scale : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → Nonempty (A.Meas ψ) ∧ ∀ (m : A.Meas ψ) (x : A.Kˣ), m.μL x = ENNReal.ofReal (A.absK x) • m.μL 1 := by
  first | exact @GlobalTheory.JR.exists_meas_and_scale | exact GlobalTheory.JR.exists_meas_and_scale | (intros; apply GlobalTheory.JR.exists_meas_and_scale <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.fullLattice_sandwich_between_integral_elements : ∀ (K : UQ) (B : InvAlg K), B.LieReg → ∀ a : K.O, K.Small a → ∀ L : Submodule K.O B.A, IsLat K.O K.E L → ∃ m : ℕ, ∀ n : ℕ, m ≤ n → (∀ y : B.A, IsIntegral K.O y → algebraMap K.O B.A a ^ n * y ∈ L) ∧ ∀ y ∈ L, IsIntegral K.O (algebraMap K.O B.A a ^ n * y) := by
  first | exact @GlobalTheory.UnitLemma.lattice_sandwich | exact GlobalTheory.UnitLemma.lattice_sandwich | (intros; apply GlobalTheory.UnitLemma.lattice_sandwich <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.isReduced_of_lieReg' : ∀ (K : UQ) (B : InvAlg K), B.LieReg → IsReduced B.A := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.isReduced_of_lieReg | exact GlobalTheory.UnitLemma.InvAlg.isReduced_of_lieReg | (intros; apply GlobalTheory.UnitLemma.InvAlg.isReduced_of_lieReg <;> assumption)
end
