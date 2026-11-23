module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalUnitarySplitDenominator
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle025
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle056
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle020
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle057
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle052
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle060
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle054
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle047
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle045
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle033
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle004
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1

@[expose] public section

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem cf_congr_of_vanI_eq {ι : Type} [Fintype ι] [DecidableEq ι] {Γ Δ : Set (Matrix ι ι ℂ)}
    (h : vanI Γ = vanI Δ) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R) :
    CF Γ R R₀ ↔ CF Δ R R₀ := by

  have key : ∀ (S : Type) [CommRing S] [Algebra ℚ S], pts Γ S = pts Δ S := by
    intro S _ _
    simp only [pts, h]
  simp only [CF, key]

theorem cf_of_isQGroup : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), IsQGroup Γ → AdelicPair R R₀ → CF Γ R R₀ := by
  intro ι _ _

  suffices H : ∀ n : ℕ, ∀ (Γ : Set (Matrix ι ι ℂ)), Module.finrank ℂ (Submodule.span ℂ Γ) = n →
      ∀ (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), IsQGroup Γ → AdelicPair R R₀ → CF Γ R R₀ by
    intro Γ R _ _ R₀ hQ hA
    exact H _ Γ rfl R R₀ hQ hA
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Γ hn R _ _ R₀ hQ hA
    by_cases hS : SS Γ
    · exact GlobalTheory.T.classFiniteness_completelyReducible ι Γ R R₀ hQ hS hA
    · obtain ⟨e, he, hup, a, ha, ha0, hblk⟩ := GlobalTheory.T.exists_rat_idempotent_blockDiagPart_kills_span ι Γ hQ.toIsPre hS

      have hPre : IsPre (blk e '' Γ) := GlobalTheory.T.isAutStableSLMatrixGroup_image_blockDiagPart ι Γ e hQ.toIsPre he hup
      obtain ⟨hQ', hvan, hspan⟩ := GlobalTheory.T.ratZariskiClosure_of_autStable_SL_group ι (blk e '' Γ) hPre
      have hlt := GlobalTheory.T.finrank_span_blockDiagPart_image_lt ι Γ e a ha ha0 hblk
      have hcl : CF (pts (blk e '' Γ) ℂ) R R₀ :=
        ih _ (by rw [← hn, hspan]; exact hlt) _ rfl R R₀ hQ' hA
      have hblkCF : CF (blk e '' Γ) R R₀ := (cf_congr_of_vanI_eq hvan R R₀).mp hcl
      exact GlobalTheory.T.hasFiniteAdelicDoubleCosets_of_blockDiagPart_image ι Γ e R R₀ hQ he hup hA hblkCF

end GlobalTheory.ClassFin
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_rational_unitary_split_denominator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → Module.finrank F E = 2 → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (g : GL (Fin n) (RA F E)) (N : ℕ), IsUnA c G g.1 → 0 < N → ∃ γ : GL (Fin n) E, IsUnE c G γ.1 ∧ CongAtA F L N N (fm F γ.1 * g.1) ∧ ∃ s : 𝓞 E, SplitOff c N s ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • ((fm F γ.1 * g.1) *ᵥ z) ∈ hat F (L : Set (Fin n → E)) ∧ ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • (((g⁻¹).1 * fm F (γ⁻¹).1) *ᵥ z) ∈ hat F (L : Set (Fin n → E)) := by
  first | exact @GlobalTheory.UnRep.LatForm.exists_rep_split_denominator | exact GlobalTheory.UnRep.LatForm.exists_rep_split_denominator | (intros; apply GlobalTheory.UnRep.LatForm.exists_rep_split_denominator <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem index_eq_relIndex_mul_index_sup_normThm {G : Type} [CommGroup G] (U W : Subgroup G) :
    W.index = W.relIndex U * (U ⊔ W).index := by
  rw [← Subgroup.relIndex_mul_index (le_sup_right : W ≤ U ⊔ W), Subgroup.relIndex_sup_right]

theorem inf_le_of_index_count_normThm {G : Type} [CommGroup G] (p : ℕ) (hp : 0 < p)
    (U W D N : Subgroup G) (s k t : ℕ)
    (hWD : W ≤ D) (hND : N ≤ D) (hk : k + 1 = 2 * s) (hW0 : W.index ≠ 0)
    (hW : W.index ≤ p ^ (2 * s)) (hWU : W.relIndex U = p ^ k) (hD : p ^ t ≤ D.index)
    (hN0 : N.relIndex U ≠ 0) (hN : p * N.relIndex U ≤ p ^ t) : D ⊓ U ≤ N := by
  have e1 := index_eq_relIndex_mul_index_sup_normThm U W
  have e2 := index_eq_relIndex_mul_index_sup_normThm U D
  have h4 : p ^ (2 * s) = p ^ k * p := by
    rw [← pow_succ, hk]
  have hUW0 : (U ⊔ W).index ≠ 0 := by
    intro h; rw [h, mul_zero] at e1; exact hW0 e1
  have hUW : (U ⊔ W).index ≤ p := by
    rw [e1, hWU, h4] at hW
    exact Nat.le_of_mul_le_mul_left hW (by positivity)
  have hUD : (U ⊔ D).index ≤ p :=
    le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hUW0)
      (Subgroup.index_dvd_of_le (sup_le_sup_left hWD U))) hUW
  have h3 : N.relIndex U ≤ D.relIndex U := by
    have : p * N.relIndex U ≤ p * D.relIndex U := by
      calc p * N.relIndex U ≤ D.relIndex U * (U ⊔ D).index := by
            rw [← e2]; exact hN.trans hD
        _ ≤ D.relIndex U * p := Nat.mul_le_mul_left _ hUD
        _ = p * D.relIndex U := mul_comm _ _
    exact Nat.le_of_mul_le_mul_left this hp
  have e3 : N.relIndex (D ⊓ U) * D.relIndex U = N.relIndex U := by
    have := Subgroup.relIndex_inf_mul_relIndex N D U
    rwa [inf_eq_left.mpr hND] at this
  have hD0 : D.relIndex U ≠ 0 := by
    intro h; rw [h, mul_zero] at e3; exact hN0 e3.symm
  have hm0 : N.relIndex (D ⊓ U) ≠ 0 := by
    intro h; rw [h, zero_mul] at e3; exact hN0 e3.symm
  have hm : N.relIndex (D ⊓ U) ≤ 1 := by
    rw [← e3] at h3
    have : N.relIndex (D ⊓ U) * D.relIndex U ≤ 1 * D.relIndex U := by rwa [one_mul]
    exact Nat.le_of_mul_le_mul_right this (Nat.pos_of_ne_zero hD0)
  exact Subgroup.relIndex_eq_one.mp (by omega)

theorem pows_le_finPow_normThm (p : ℕ) (F : Type) [Field F] [NumberField F] (U : Subgroup Fˣ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : pows p U ≤ finPow p F S := by
  rintro _ ⟨y, -, rfl⟩
  have h : ∀ {L : Type} [Field L] (φ : F →+* L), powMonoidHom p y ∈ powSub p φ := by
    intro L _ φ
    exact ⟨φ y, by simp⟩
  exact Subgroup.mem_iInf.mpr fun _ => Subgroup.mem_iInf.mpr fun _ => h _

theorem mem_pows_sUnits_normThm (p : ℕ) (hp : 0 < p) (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (y : Fˣ) (hy : y ∈ sUnits F S)
    (h : ∃ r : F, r ^ p = (y : F)) : y ∈ pows p (sUnits F S) := by
  obtain ⟨r, hr⟩ := h
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact y.ne_zero (by rw [← hr, zero_pow hp.ne'])
  refine ⟨Units.mk0 r hr0, ?_, ?_⟩
  · intro v hv
    have h1 := hy v hv
    have h2 : v.valuation F r ^ p = 1 := by
      rw [← map_pow, hr]; exact h1
    exact (pow_eq_one_iff_of_nonneg zero_le' hp.ne').mp h2
  · ext
    simp [hr]

theorem sUnit_mem_kNorm_of_mem_finNorm : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (ζ : F) (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → δ ∈ sUnits F S → (∀ r : F, r ^ p ≠ (δ : F)) → ∀ x ∈ sUnits F S, x ∈ finNorm p F δ S → x ∈ kNorm p (RingHom.id F) (δ : F) := by
  intro p F _ _ _ ζ δ S hp hζ hS hδ hns x hx hxl
  classical
  have hp0 := hp.pos
  obtain ⟨T, hST, hcard, hsq, hA⟩ := GlobalTheory.T.exists_places_with_pth_roots_and_separating_units p F ζ δ S hp hζ hS hδ hns
  have hsurj := GlobalTheory.T.sUnits_union_sup_powers_eq_top_at_places p F S T hp hS hST hA
  have hinj := GlobalTheory.T.pow_of_sUnit_localPower_at_places p F ζ S T hp hζ hS hsurj
  have hmono : sUnits F S ≤ sUnits F (S ∪ T) := fun y hy v hv =>
    hy v (fun h => hv (by simp only [Finset.coe_union, Set.mem_union]; exact Or.inl h))
  have hS' : AdmP p F (S ∪ T) :=
    (exists_admissiblePlaces_superset_and_mono p F hp0).2 S (S ∪ T) Finset.subset_union_left hS
  obtain ⟨hN0, hN⟩ := GlobalTheory.T.first_inequality_sUnits_prime_degree p F ζ δ (S ∪ T) hp hζ hS' (hmono hδ) hns
  have ht : tNon p F δ (S ∪ T) = tNon p F δ S := by
    unfold tNon
    congr 1
    ext v
    simp only [Finset.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h | h, h'⟩
      · exact ⟨h, h'⟩
      · obtain ⟨r, hr⟩ := hsq v h
        exact absurd hr (h' r)
    · rintro ⟨h, h'⟩
      exact ⟨Or.inl h, h'⟩
  rw [ht] at hN
  obtain ⟨-, hD⟩ := GlobalTheory.T.pow_countPlacesNotLocalPower_le_index p F ζ δ S hp hζ
  obtain ⟨hW0, hW⟩ := GlobalTheory.T.unitsLocalPowersAtPlaces_index_le p F S hp0
  have hU := (pTor_pIdx_sUnits p F ζ (S ∪ T) hp hζ).2
  unfold pIdx at hU
  have hinf : finPow p F S ⊓ sUnits F (S ∪ T) = pows p (sUnits F (S ∪ T)) ⊓ sUnits F (S ∪ T) := by
    apply le_antisymm
    · rintro y ⟨h1, h2⟩
      exact ⟨mem_pows_sUnits_normThm p hp0 F _ y h2 (hinj y h2 h1), h2⟩
    · exact inf_le_inf_right _ (pows_le_finPow_normThm p F _ S)
  have hWU : (finPow p F S).relIndex (sUnits F (S ∪ T)) =
      p ^ ((S ∪ T).card + Fintype.card (InfinitePlace F)) := by
    rw [← Subgroup.inf_relIndex_right, hinf, Subgroup.inf_relIndex_right, hU]
  obtain ⟨k1, k2⟩ := GlobalTheory.T.unitsMappingToPowers_le_unitsLocalKummerNorms p hp0
  have hWD : finPow p F S ≤ finNorm p F δ S := iInf₂_mono fun _ _ => k1 _ _ _ _
  have hND : kNorm p (RingHom.id F) (δ : F) ≤ finNorm p F δ S :=
    le_iInf₂ fun _ _ => k2 _ _ _ _
  refine inf_le_of_index_count_normThm p hp0 (sUnits F (S ∪ T)) (finPow p F S) (finNorm p F δ S)
    _ _ _ _ hWD hND ?_ hW0 hW hWU hD hN0 hN ⟨hxl, hmono hx⟩
  rw [Finset.card_union_of_disjoint hST]
  omega

end GlobalTheory.CNorm
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.scaled_matrix_mem_rational_lattice : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Submodule.IsFullLattice D.host.E ΛS → Submodule.IsFullLattice D.host.E ΛT → ∀ M : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ N • M ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) := by
  intro D S T ΛS ΛT hS hT M
  first
  | exact GlobalTheory.LatVacFull.latRat_full D S T ΛS ΛT hS hT M
  | exact GlobalTheory.LatVacFull.latRat_full D S T ΛS ΛT hS.toIsLattice hT.toIsLattice M
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_dual_family_selfDual_hermitianSpace : ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)), IsSelfDualC S Λ → ∃ (n : ℕ) (s s' : Fin n → Fin S.rank → D.host.E), (∀ i, s i ∈ Λ ∧ s' i ∈ Λ) ∧ ∀ a j, ∑ i, s i a * ∑ k, star (s' i k) * S.gram k j = if a = j then 1 else 0 := by
  first | exact @GlobalTheory.LatVacDual.dualFamily | exact GlobalTheory.LatVacDual.dualFamily | (intros; apply GlobalTheory.LatVacDual.dualFamily <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompletedLatticeFinite

section General

variable {E : Type} [Field E] [NumberField E]

theorem exists_denom {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    ∃ d : E, d ≠ 0 ∧ ∀ x ∈ L, ∀ i, IsIntegral ℤ (d * x i) := by
  classical
  obtain ⟨s, rfl⟩ := hL
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    ((s ×ˢ (Finset.univ : Finset (Fin n))).image fun p => p.1 p.2)
  refine ⟨(y : E), by exact_mod_cast hy0, fun x hx i => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    have := hy (x i) (Finset.mem_image.2 ⟨(x, i), by simpa using hx, rfl⟩)
    simpa [zsmul_eq_mul] using this
  | zero => simpa using isIntegral_zero
  | add x z _ _ hx hz => rw [Pi.add_apply, mul_add]; exact hx.add hz
  | smul c x _ hx =>
    have : (y : E) * (c • x) i = (c : E) * ((y : E) * x i) := by
      change (y : E) * ((c : E) * x i) = _
      ring
    rw [this]
    exact c.isIntegral_coe.mul hx

theorem finite_of_denom (d : E) (hd : d ≠ 0) (R : ℝ) :
    {x : E | IsIntegral ℤ (d * x) ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ R}.Finite := by
  have h := NumberField.Embeddings.finite_of_norm_le E ℂ ((∑ φ : E →+* ℂ, ‖φ d‖) * R)
  refine (h.preimage (f := fun x => d * x) (mul_right_injective₀ hd).injOn).subset ?_
  rintro x ⟨hx, hb⟩
  refine ⟨hx, fun φ => ?_⟩
  rw [map_mul, norm_mul]
  exact mul_le_mul (Finset.single_le_sum (f := fun φ : E →+* ℂ => ‖φ d‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ φ)) (hb φ) (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)

theorem mem_spanSingleton_inv (d : E) (hd : d ≠ 0) (x : E) :
    x ∈ FractionalIdeal.spanSingleton (𝓞 E)⁰ d⁻¹ ↔ IsIntegral ℤ (d * x) := by
  rw [FractionalIdeal.mem_spanSingleton]
  constructor
  · rintro ⟨z, rfl⟩
    have : d * (z • d⁻¹) = (z : E) := by
      change d * ((z : E) * d⁻¹) = _
      field_simp
    rw [this]
    exact z.isIntegral_coe
  · intro h
    refine ⟨⟨d * x, h⟩, ?_⟩
    change d * x * d⁻¹ = x
    field_simp

end General

theorem isIntegral_star (D : D7) {x : D.host.E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (star x) :=
  hx.map (starRingEnd D.host.E).toIntAlgHom

theorem norm_emb_le (D : D7) {x : D.host.E} {R : ℝ} (h : ∀ τ, ‖tauE D τ x‖ ≤ R) (φ : D.host.E →+* ℂ) :
    ‖φ x‖ ≤ R := by
  obtain ⟨τ, hτ⟩ := (GlobalTheory.CMTypePlaces.mk_tauE_bijective D).2 (InfinitePlace.mk φ)
  have := h τ
  rw [← InfinitePlace.apply] at this ⊢
  rw [← hτ]
  exact this

theorem finite_rational_points : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ R : ℝ, {g : Matrix (Fin T.rank) (Fin S.rank) D.host.E | (∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), ((ratW T S g : WO S T) - l).map (finPart D) = 0) ∧ ∀ τ i j, ‖tauE D τ (g i j)‖ ≤ R}.Finite := by
  classical
  intro D S T ΛS ΛT hS hT R
  obtain ⟨dS, hdS, hS'⟩ := exists_denom ΛS hS.1.fg
  obtain ⟨dT, hdT, hT'⟩ := exists_denom ΛT hT.1.fg
  obtain ⟨dA, hdA, hA'⟩ := D.host.AA.2
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    ((Finset.univ : Finset (Fin S.rank × Fin S.rank)).image fun p => S.gram p.1 p.2)
  have hdA0 : (dA : D.host.E) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hdA
    exact_mod_cast this
  have hd : (dA : D.host.E) * dT * (star dS * (y : D.host.E)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hdA0 hdT) (mul_ne_zero (star_ne_zero.2 hdS) (by exact_mod_cast hy0))
  set d : D.host.E := (dA : D.host.E) * dT * (star dS * (y : D.host.E)) with hdd
  have hgen : ∀ a ∈ D.host.AA, ∀ s ∈ ΛS, ∀ t ∈ ΛT, ∀ i j,
      IsIntegral ℤ (d * (a * t i * ∑ k, star (s k) * S.gram k j)) := by
    intro a ha s hs t ht i j
    have e : d * (a * t i * ∑ k, star (s k) * S.gram k j) =
        ((dA : D.host.E) * a) * (dT * t i) * ∑ k, star (dS * s k) * ((y : D.host.E) * S.gram k j) := by
      simp only [hdd, Finset.mul_sum, star_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e]
    refine IsIntegral.mul (IsIntegral.mul ?_ (hT' t ht i)) (IsIntegral.sum _ fun k _ =>
      (isIntegral_star D (hS' s hs k)).mul ?_)
    · obtain ⟨b, hb⟩ := hA' a ha
      have : (dA : D.host.E) * a = (b : D.host.E) := hb.symm
      rw [this]
      exact b.isIntegral_coe
    · have := hy (S.gram k j) (Finset.mem_image.2 ⟨(k, j), Finset.mem_univ _, rfl⟩)
      simpa [zsmul_eq_mul] using this
  have hlat : ∀ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
      ∀ i j, finPart D (l i j) ∈ GlobalTheory.AdLat.hat1 D.host.F
        ((FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ d⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Set D.host.E) := by
    intro l hl i j
    induction hl using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
      exact AddSubgroup.subset_closure ⟨α, hα, _, (mem_spanSingleton_inv d hd _).2 (hgen a ha s hs t ht i j), rfl⟩
    | zero => rw [Matrix.zero_apply, RingHom.map_zero]; exact zero_mem _
    | add x z _ _ hx hz => rw [Matrix.add_apply, RingHom.map_add (f := _)]; exact add_mem hx hz
    | neg x _ hx => rw [Matrix.neg_apply, RingHom.map_neg]; exact neg_mem hx
  refine (Set.Finite.pi' fun _ : Fin T.rank => Set.Finite.pi' fun _ : Fin S.rank =>
    finite_of_denom d hd R).subset ?_
  rintro g ⟨⟨l, hl, hgl⟩, hb⟩ i j
  refine ⟨?_, norm_emb_le D fun τ => hb τ i j⟩
  have h1 : finPart D (incA D (g i j) - l i j) = 0 := congrFun (congrFun hgl i) j
  rw [RingHom.map_sub, sub_eq_zero] at h1
  have h2 := hlat l hl i j
  rw [← h1] at h2
  exact (mem_spanSingleton_inv d hd _).1 (((GlobalTheory.AdLat.adelicCompletion_fractionalIdeal_properties D.host.F D.host.E).2.1 _ (g i j)).1 h2)

end GlobalTheory.CompletedLatticeFinite
end
