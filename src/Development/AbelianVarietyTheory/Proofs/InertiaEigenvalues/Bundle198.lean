module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle124
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle183
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle097
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle185
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle186
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianBlockInvariantsIffIsometry
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SgnLatProdEqEtaResultantMul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnimodularHeightSqLintegralLtTop
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConnPhiExtensionGeneratorEqZeta
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle187
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle103

@[expose] public section

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

noncomputable section

namespace GlobalTheory.UnitLemma.FibSum

theorem fib_card (K : UQ) (B₁ B₂ : InvAlg K) (hg₁ : B₁.σ B₁.g = B₁.g) (hg₂ : B₂.σ B₂.g = B₂.g)
    (hres : resultant B₁.P B₂.P ≠ 0)
    (M₁ : Submodule K.O B₁.A) (M₂ : Submodule K.O B₂.A) (h₁ : M₁ ∈ B₁.Lin) (h₂ : M₂ ∈ B₂.Lin) :
    (Nat.card {M : Submodule K.O (B₁.A × B₂.A) // M ∈ (B₁.prod B₂).Lin ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} : ℚ) =
      (K.q : ℚ) ^ val K.O (resultant B₁.P B₂.P) := by
  have hI := GlobalTheory.T.card_stable_lattices_alt K.O K.E B₁.A B₂.A B₁.g B₂.g hres M₁ M₂ h₁.1 h₂.1 h₁.2.1 h₂.2.1
  have hH := GlobalTheory.T.card_sigma_stable_prod_lattice_ext_sq K B₁ B₂ hg₁ hg₂ M₁ M₂ h₁ h₂
  have e : {M : Submodule K.O (B₁.A × B₂.A) // M ∈ (B₁.prod B₂).Lin ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} ≃
      {M : Submodule K.O (B₁.A × B₂.A) // ((∀ y ∈ M, (B₁.g, B₂.g) * y ∈ M) ∧
        ∀ y ∈ M, (B₁.σ y.1, B₂.σ y.2) ∈ M) ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} :=
    { toFun := fun M => ⟨M.1, ⟨M.2.1.2.1, M.2.1.2.2⟩, M.2.2⟩
      invFun := fun M => ⟨M.1, ⟨GlobalTheory.T.isFullLattice_prod_of_comap_inl_map_snd K B₁ B₂ M.1 (by rw [M.2.2.1]; exact h₁.1)
          (by rw [M.2.2.2]; exact h₂.1), M.2.1.1, M.2.1.2⟩, M.2.2⟩
      left_inv := fun M => rfl
      right_inv := fun M => rfl }
  rw [Nat.card_congr e]
  have hq2 : (Nat.card (IsLocalRing.ResidueField K.O) : ℚ) = (K.q : ℚ) ^ 2 := by
    rw [K.card_res]; push_cast; ring
  rw [hq2] at hI
  have hqpos : (0 : ℚ) < K.q := by
    have : 0 < Nat.card (IsLocalRing.ResidueField K.O) := Nat.card_pos
    rw [K.card_res] at this
    exact_mod_cast pos_of_ne_zero (fun h => by simp [h] at this)
  have hsq : ((Nat.card {M : Submodule K.O (B₁.A × B₂.A) // ((∀ y ∈ M, (B₁.g, B₂.g) * y ∈ M) ∧
        ∀ y ∈ M, (B₁.σ y.1, B₂.σ y.2) ∈ M) ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} : ℚ)) ^ 2 =
      ((K.q : ℚ) ^ val K.O (resultant B₁.P B₂.P)) ^ 2 := by
    have hpw : ((K.q : ℚ) ^ 2) ^ val K.O (resultant B₁.P B₂.P) = ((K.q : ℚ) ^ val K.O (resultant B₁.P B₂.P)) ^ 2 := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    have hP₁ : (LinearMap.mulLeft K.E B₁.g).charpoly = B₁.P := rfl
    have hP₂ : (LinearMap.mulLeft K.E B₂.g).charpoly = B₂.P := rfl
    rw [hP₁, hP₂, hpw] at hI
    rw [← hI]
    exact_mod_cast hH
  exact (pow_left_inj₀ (by positivity) (zpow_pos hqpos _).le two_ne_zero).1 hsq

theorem fibsum : ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.σ B₁.g = B₁.g → B₂.σ B₂.g = B₂.g → (B₁.P * B₂.P).Separable → ∀ (φ₁ : Submodule K.O B₁.A → ℚ) (φ₂ : Submodule K.O B₂.A → ℚ), {M ∈ B₁.Lin | φ₁ M ≠ 0}.Finite → {M ∈ B₂.Lin | φ₂ M ≠ 0}.Finite → {M ∈ (B₁.prod B₂).Lin | φ₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ (M.map (LinearMap.snd K.O B₁.A B₂.A)) ≠ 0}.Finite ∧ ∑ᶠ M ∈ (B₁.prod B₂).Lin, φ₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ (M.map (LinearMap.snd K.O B₁.A B₂.A)) = (K.q : ℚ) ^ val K.O (resultant B₁.P B₂.P) * ((∑ᶠ M ∈ B₁.Lin, φ₁ M) * ∑ᶠ M ∈ B₂.Lin, φ₂ M) := by
  intro K B₁ B₂ hg₁ hg₂ hsep φ₁ φ₂ hf₁ hf₂
  have hres : resultant B₁.P B₂.P ≠ 0 := resultant_ne_zero _ _ hsep.isCoprime
  set v := val K.O (resultant B₁.P B₂.P) with hv
  set π : Submodule K.O (B₁.prod B₂).A → Submodule K.O B₁.A × Submodule K.O B₂.A := fun M =>
    (M.comap (LinearMap.inl K.O B₁.A B₂.A), M.map (LinearMap.snd K.O B₁.A B₂.A)) with hπ
  suffices key : ∀ F : Submodule K.O (B₁.prod B₂).A → ℚ, (∀ M, F M =
      φ₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ (M.map (LinearMap.snd K.O B₁.A B₂.A))) →
      {M | M ∈ (B₁.prod B₂).Lin ∧ F M ≠ 0}.Finite ∧ ∑ᶠ M ∈ (B₁.prod B₂).Lin, F M =
        (K.q : ℚ) ^ v * ((∑ᶠ M ∈ B₁.Lin, φ₁ M) * ∑ᶠ M ∈ B₂.Lin, φ₂ M) from key _ (fun _ => rfl)
  intro F hF
  set s₁ := hf₁.toFinset
  set s₂ := hf₂.toFinset
  have hs₁ : ∀ M, M ∈ s₁ ↔ M ∈ B₁.Lin ∧ φ₁ M ≠ 0 := fun M => by simp [s₁]
  have hs₂ : ∀ M, M ∈ s₂ ↔ M ∈ B₂.Lin ∧ φ₂ M ≠ 0 := fun M => by simp [s₂]
  have hfibfin : ∀ p ∈ s₁ ×ˢ s₂, {M | M ∈ (B₁.prod B₂).Lin ∧ π M = p}.Finite := by
    intro p hp
    rw [Finset.mem_product, hs₁, hs₂] at hp
    have hc := fib_card K B₁ B₂ hg₁ hg₂ hres p.1 p.2 hp.1.1 hp.2.1
    have hqpos : (0 : ℚ) < K.q := by
      have : 0 < Nat.card (IsLocalRing.ResidueField K.O) := Nat.card_pos
      rw [K.card_res] at this
      exact_mod_cast pos_of_ne_zero (fun h => by simp [h] at this)
    have hne : Nat.card {M : Submodule K.O (B₁.A × B₂.A) // M ∈ (B₁.prod B₂).Lin ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = p.1 ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = p.2} ≠ 0 := by
      intro h0
      rw [h0] at hc
      exact (zpow_pos hqpos v).ne' (by simpa using hc.symm)
    have := Nat.finite_of_card_ne_zero hne
    refine (Set.finite_coe_iff.1 ?_)
    have e : {M | M ∈ (B₁.prod B₂).Lin ∧ π M = p} = {M | M ∈ (B₁.prod B₂).Lin ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = p.1 ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = p.2} := by
      ext M; simp only [Set.mem_setOf_eq, hπ, Prod.ext_iff]
    rw [e]; exact this
  set W := {M | M ∈ (B₁.prod B₂).Lin ∧ π M ∈ s₁ ×ˢ s₂} with hW
  have hWfin : W.Finite := by
    refine (Set.Finite.biUnion (t := fun p => {M | M ∈ (B₁.prod B₂).Lin ∧ π M = p})
      (s₁ ×ˢ s₂).finite_toSet hfibfin).subset ?_
    intro M hM
    exact Set.mem_biUnion (x := π M) hM.2 (show M ∈ {M' | M' ∈ (B₁.prod B₂).Lin ∧ π M' = π M} from ⟨hM.1, rfl⟩)
  have hsupp : ∀ M ∈ (B₁.prod B₂).Lin, F M ≠ 0 → M ∈ W := by
    intro M hM hFM
    have hl := GlobalTheory.T.lieLattice_prod_comap_inl_and_map_snd K B₁ B₂ M hM
    rw [hF M] at hFM
    refine ⟨hM, Finset.mem_product.2 ⟨(hs₁ _).2 ⟨hl.1, left_ne_zero_of_mul hFM⟩,
      (hs₂ _).2 ⟨hl.2, right_ne_zero_of_mul hFM⟩⟩⟩
  refine ⟨hWfin.subset fun M hM => hsupp M hM.1 hM.2, ?_⟩
  have hL : ∑ᶠ M ∈ (B₁.prod B₂).Lin, F M = ∑ M ∈ hWfin.toFinset, F M := by
    have hset : (B₁.prod B₂).Lin ∩ Function.support F = W ∩ Function.support F := by
      ext M
      simp only [Set.mem_inter_iff, Function.mem_support]
      exact ⟨fun h => ⟨hsupp M h.1 h.2, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rw [← finsum_mem_eq_finite_toFinset_sum _ hWfin, ← finsum_mem_inter_support,
      ← finsum_mem_inter_support (s := W), hset]
  have h1 : ∑ᶠ M ∈ B₁.Lin, φ₁ M = ∑ M ∈ s₁, φ₁ M := by
    have hset : B₁.Lin ∩ Function.support φ₁ = {M | M ∈ B₁.Lin ∧ φ₁ M ≠ 0} ∩ Function.support φ₁ := by
      ext M
      simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨⟨h.1, h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rw [← finsum_mem_eq_finite_toFinset_sum _ hf₁, ← finsum_mem_inter_support,
      ← finsum_mem_inter_support (s := {M | M ∈ B₁.Lin ∧ φ₁ M ≠ 0}), hset]
  have h2 : ∑ᶠ M ∈ B₂.Lin, φ₂ M = ∑ M ∈ s₂, φ₂ M := by
    have hset : B₂.Lin ∩ Function.support φ₂ = {M | M ∈ B₂.Lin ∧ φ₂ M ≠ 0} ∩ Function.support φ₂ := by
      ext M
      simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨⟨h.1, h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rw [← finsum_mem_eq_finite_toFinset_sum _ hf₂, ← finsum_mem_inter_support,
      ← finsum_mem_inter_support (s := {M | M ∈ B₂.Lin ∧ φ₂ M ≠ 0}), hset]
  rw [hL, h1, h2, ← Finset.sum_fiberwise_of_maps_to (s := hWfin.toFinset) (t := s₁ ×ˢ s₂) (g := π)
    (fun M hM => ((Set.Finite.mem_toFinset hWfin).1 hM).2), Finset.sum_mul_sum, ← Finset.sum_product', Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hin : ∀ M ∈ hWfin.toFinset.filter (fun M => π M = p), F M = φ₁ p.1 * φ₂ p.2 := by
    intro M hM
    have hM' := (Finset.mem_filter.1 hM).2
    rw [hF, ← hM']
  rw [Finset.sum_congr rfl hin, Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hp' := hp
  rw [Finset.mem_product, hs₁, hs₂] at hp'
  rw [← fib_card K B₁ B₂ hg₁ hg₂ hres p.1 p.2 hp'.1.1 hp'.2.1]
  congr 1
  rw [← Set.ncard_coe_finset, ← Nat.card_coe_set_eq]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro M
  simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, hW, hπ, Prod.ext_iff]
  constructor
  · rintro ⟨⟨h, _⟩, h'⟩; exact ⟨h, h'⟩
  · rintro ⟨h, h'⟩
    refine ⟨⟨h, ?_⟩, h'⟩
    rw [Finset.mem_product]; rw [h'.1, h'.2]; exact Finset.mem_product.1 hp

end GlobalTheory.UnitLemma.FibSum
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.whittakerFunctional_weyl_vanish_of_weylUnipotent_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ, A.InI Ψ → (∀ z, Ψ (wS A.K * nS z) = 0) → ∀ (a : A.K) (c : F), A.abelian₂ μK ψ a (fun h => Ψ (h * wS A.K)) c = 0 := by
  first | exact @GlobalTheory.JR.lam_flip_eq_zero | exact GlobalTheory.JR.lam_flip_eq_zero | (intros; apply GlobalTheory.JR.lam_flip_eq_zero <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.absK_multiplicative_unitOne_haarScaling : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), ((∀ s t : A.K, A.absK (s * t) = A.absK s * A.absK t) ∧ (∀ s s' : A.K, s ∈ A.OK → s' ∈ A.OK → s * s' = 1 → A.absK s = 1) ∧ (∀ (μ : Measure A.K), μ.IsAddHaarMeasure → ∀ (x : A.Kˣ) (a : A.K) (S : Set A.K), MeasurableSet S → μ {a' : A.K | (x : A.K) * a' - a ∈ S} = ENNReal.ofReal (A.absK (x : A.K))⁻¹ * μ S)) := by
  first | exact @GlobalTheory.JR.Et.absK_facts | exact GlobalTheory.JR.Et.absK_facts | (intros; apply GlobalTheory.JR.Et.absK_facts <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.eventually_dual_scaled_OK_subset_nhds : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ V ∈ 𝓝 (0 : A.K), ∀ᶠ c in 𝓝[≠] (0 : F), {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} ⊆ V := by
  first | exact @GlobalTheory.dual_cinvOK_small | exact GlobalTheory.dual_cinvOK_small | (intros; apply GlobalTheory.dual_cinvOK_small <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.partialFourier_etaleKProd_locallyConstantCompactSupport : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ φ' : A.K × A.K → ℂ, IsTest φ' → IsTest (fun p : A.K × A.K => A.tilde μK ψ φ' p.1 p.2) := by
  first | exact @GlobalTheory.JR.TildeTest.main | exact GlobalTheory.JR.TildeTest.main | (intros; apply GlobalTheory.JR.TildeTest.main <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.fourierTransformKProd_locallyConstantCompactSupport : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ φ' : A.K × A.K → ℂ, IsTest φ' → IsTest (A.fourK μK ψ φ') := by
  first | exact @GlobalTheory.FourKTest.fourK_isTest | exact GlobalTheory.FourKTest.fourK_isTest | (intros; apply GlobalTheory.FourKTest.fourK_isTest <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.jHyp_unipotent_torus_equivariance : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (ψ : AddChar F ℂ) (φ' : A.K × A.K → ℂ) (z : A.K) (s : A.Kˣ) (g : SpecialLinearGroup (Fin 2) A.K), A.jHyp μK ψ φ' (nS z * mS s * g) = A.etaK s * (A.absK s : ℂ) * A.jHyp μK ψ φ' g := by
  first | exact @GlobalTheory.JHypEquiv.jHyp_nm | exact GlobalTheory.JHypEquiv.jHyp_nm | (intros; apply GlobalTheory.JHypEquiv.jHyp_nm <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.setIntegral_integral_psiK_swap : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (μ : Measure A.L), μ.IsAddHaarMeasure → ∀ φ : A.L → ℂ, IsTest φ → ∀ (x a : A.K) (c : F), c ≠ 0 → ∫ z in {z : A.K | c • z ∈ A.OK}, (∫ y, φ y * A.psiK ψ (z * x * A.NL y) ∂μ) * A.psiK ψ (-(a * z)) ∂μK = ∫ y, φ y * ∫ z in {z : A.K | c • z ∈ A.OK}, A.psiK ψ (z * (x * A.NL y - a)) ∂μK ∂μ := by
  first | exact @GlobalTheory.JR.Et.whittaker_swap | exact GlobalTheory.JR.Et.whittaker_swap | (intros; apply GlobalTheory.JR.Et.whittaker_swap <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.hermitianBlock_invariants_iff_isometry : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (lam : F), A.IsGen τ p → (∀ (a : A.K) (X : Hn r F E), IsUnit a → HasInv X (A.invK τ p lam a) → ∀ (x : A.K) (y : A.L), IsUnit y → a = x * A.NL y → ∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom x j ∧ (∀ z, j (algebraMap A.K A.L τ * z) = X.1.1 *ᵥ j z) ∧ j y = X.2.1) ∧ ∀ (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∃ Ax : selfAdjoint (Matrix (Fin r) (Fin r) E), (∀ z, j (algebraMap A.K A.L τ * z) = Ax.1 *ᵥ j z) ∧ ∀ y, HasInv ((Ax, j y, lam) : Hn r F E) (A.invK τ p lam (x * A.NL y)) := by
  first | exact @GlobalTheory.EtIsom.herm_iff_isom | exact GlobalTheory.EtIsom.herm_iff_isom | (intros; apply GlobalTheory.EtIsom.herm_iff_isom <;> assumption)
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

theorem _root_.GlobalTheory.T.sgnLat_prod_eq_eta_resultant_mul : ∀ (K : UQ) (B₁ B₂ : InvAlg K), (B₁.P * B₂.P).Separable → ∀ M ∈ (B₁.prod B₂).Lin, (B₁.prod B₂).sgnLat M = K.eta (resultant B₁.P B₂.P) * B₁.sgnLat (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * B₂.sgnLat (M.map (LinearMap.snd K.O B₁.A B₂.A)) := by
  first | exact @GlobalTheory.UnitLemma.SgnProd.sgnLat_prod | exact GlobalTheory.UnitLemma.SgnProd.sgnLat_prod | (intros; apply GlobalTheory.UnitLemma.SgnProd.sgnLat_prod <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.unimodularHeight_sq_lintegral_lt_top : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μ : Measure A.K), μ.IsAddHaarMeasure → ∫⁻ z, (⨅ (s : A.Kˣ) (_ : (s : A.K) ∈ A.OK ∧ (s : A.K) * z ∈ A.OK ∧ ∃ α ∈ A.OK, ∃ β ∈ A.OK, α * s + β * (s * z) = 1), ENNReal.ofReal (A.absK s)) ^ 2 ∂μ < ⊤ := by
  first | exact @GlobalTheory.JR.HeightSquareIntegrable.height_sq_lintegral_lt_top | exact GlobalTheory.JR.HeightSquareIntegrable.height_sq_lintegral_lt_top | (intros; apply GlobalTheory.JR.HeightSquareIntegrable.height_sq_lintegral_lt_top <;> assumption)
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.breuilKisin_section_trivialises_invertPrime_tensor : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι), (∀ k : ℝ, k < 1 / ((e : ℝ) * (l - 1)) → R O K l k ≤ invL l (S O K e)) ∧ ∀ w : Vec K a ι, P.xiExt w ∈ P.MMl ↔ w ∈ P.Mext (invL l (S O K e)) := by
  exact @GlobalTheory.BK.xi_trivialises_invL_S
end
