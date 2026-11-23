module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle043
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle008
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PIdxUnitsFiniteExtensionAdicCompletion
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle042
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

@[expose] public section

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.isCompletelyReducible_kronecker_of_span_eq_top : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Type) [Group G] (ρ : G →* Matrix ι ι ℂ) (ρ' : G →* Matrix κ κ ℂ), Submodule.span ℂ (Set.range ρ) = ⊤ → Submodule.span ℂ (Set.range ρ') = ⊤ → SS (Set.range fun g => ρ g ⊗ₖ ρ' g) := by
  first | exact @GlobalTheory.ClassFin.ss_kronecker_of_span_top | exact GlobalTheory.ClassFin.ss_kronecker_of_span_top | (intros; apply GlobalTheory.ClassFin.ss_kronecker_of_span_top <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.mem_span_ratPolysVanishing_of_autStable : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ f : MvPolynomial (ι × ι) ℂ, (∀ g ∈ Γ, evC f g = 0) → f ∈ Submodule.span ℂ ((MvPolynomial.map (algebraMap ℚ ℂ)) '' vanI Γ) := by
  first | exact @GlobalTheory.ClassFin.mem_span_vanI_of_vanish | exact GlobalTheory.ClassFin.mem_span_vanI_of_vanish | (intros; apply GlobalTheory.ClassFin.mem_span_vanI_of_vanish <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.mem_span_rational_kroneckerInvariants : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ (n : ℕ) (l : (Fin n → ι) → ℂ), (∀ g ∈ Γ, l ᵥ* tpow n g = l) → l ∈ Submodule.span ℂ {μ : (Fin n → ι) → ℂ | (∀ g ∈ Γ, μ ᵥ* tpow n g = μ) ∧ ∀ a, ∃ q : ℚ, μ a = q} := by
  first | exact @GlobalTheory.ClassFin.RationalInvariants.mem_span_rational | exact GlobalTheory.ClassFin.RationalInvariants.mem_span_rational | (intros; apply GlobalTheory.ClassFin.RationalInvariants.mem_span_rational <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.exists_rat_projector_of_autStable_matrices : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (E : Submodule ℂ (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ x ∈ E, x.map σ ∈ E) → ∃ c : ι × ι → ι × ι → ℚ, (∀ X : Matrix ι ι ℂ, linExt c X ∈ E) ∧ ∀ x ∈ E, linExt c x = x := by
  first | exact @GlobalTheory.ClassFin.RatProj.exists_rat_projector | exact GlobalTheory.ClassFin.RatProj.exists_rat_projector | (intros; apply GlobalTheory.ClassFin.RatProj.exists_rat_projector <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.finite_integral_classes_closedOrbit : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → ℚ), IsClosed (orb d (fun k => ((t k : ℚ) : ℂ))) → ∀ D : ℕ, 0 < D → ∃ Z : Finset (TIdx ι d → ℚ), ∀ h : Matrix ι ι ℚ, h.det = 1 → (∀ k, ∃ z : ℤ, (D : ℚ) * act d t h k = z) → ∃ γ : Matrix ι ι ℤ, γ.det = 1 ∧ act d t (h * γ.map (Int.cast : ℤ → ℚ)) ∈ Z := by
  first | exact @GlobalTheory.ClassFin.finite_integral_classes_closed_orbit | exact GlobalTheory.ClassFin.finite_integral_classes_closed_orbit | (intros; apply GlobalTheory.ClassFin.finite_integral_classes_closed_orbit <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unitary_eq_quasiReflection_mul_transvections : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHerm (c : E →+* E) G → (∃ z : Fin n → E, z ≠ 0 ∧ hf (c : E →+* E) G z z = 0) → ∀ γ, IsU (c : E →+* E) G γ → (∀ x, hf (c : E →+* E) G x x ≠ 0 → ∃ m ∈ TvGen (c : E →+* E) G, γ = tv (c : E →+* E) G x ((γ.det - 1) / hf (c : E →+* E) G x x) * m) ∧ (γ.det = 1 → γ ∈ TvGen (c : E →+* E) G) := by
  first | exact @GlobalTheory.UTrans.isU_eq_tv_mul_tvGen | exact GlobalTheory.UTrans.isU_eq_tv_mul_tvGen | (intros; apply GlobalTheory.UTrans.isU_eq_tv_mul_tvGen <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.index_unitsLocalSquaresFiniteRealPlaces_le : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), (locSq F S).index ≠ 0 ∧ (locSq F S).index ≤ 4 ^ (S.card + Fintype.card (InfinitePlace F)) := by
  first | exact @GlobalTheory.QNorm.index_locSq_le | exact GlobalTheory.QNorm.index_locSq_le | (intros; apply GlobalTheory.QNorm.index_locSq_le <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem sUnits_union_sup_finPow_eq_top :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [DecidableEq (HeightOneSpectrum (𝓞 F))] (S T : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → AdmP p F S → Disjoint S T → (∀ v ∈ T, ∃ u ∈ sUnits F S, u ∉ powSub p (algebraMap F (v.adicCompletion F)) ∧ ∀ v' ∈ T, v' ≠ v → u ∈ powSub p (algebraMap F (v'.adicCompletion F))) → sUnits F (S ∪ T) ⊔ finPow p F T = ⊤ := by
  intro p F _ _ _ S T hp hS hST hA
  have hval : ∀ (v : HeightOneSpectrum (𝓞 F)) (z : F),
      Valued.v (algebraMap F (v.adicCompletion F) z) = v.valuation F z :=
    fun v z => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z
  have hTS : ∀ v ∈ T, v ∉ S := fun v hv h => Finset.disjoint_left.1 hST h hv
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, ha⟩ := exists_unit_valuation_eq_of_adm F S T
    (fun v => if v ∈ T then -WithZero.log (v.valuation F (x : F)) else 0) hS.1
    (fun v hv => by simp [hv])
  have haU : a ∈ sUnits F (S ∪ T) := by
    rw [mem_sUnits]
    intro v hv
    rw [Finset.mem_union, not_or] at hv
    rw [ha v hv.1]
    simp [hv.2]
  have hy : ∀ v ∈ T, v.valuation F ((a * x : Fˣ) : F) = 1 := by
    intro v hv
    have hx0 : v.valuation F (x : F) ≠ 0 := by simp
    rw [Units.val_mul, map_mul, ha v (hTS v hv), if_pos hv, WithZero.exp_neg,
      WithZero.exp_log hx0, inv_mul_cancel₀ hx0]
  have key : ∀ v ∈ T, ∃ w ∈ sUnits F S,
      w⁻¹ * (a * x) ∈ powSub p (algebraMap F (v.adicCompletion F)) ∧
        ∀ v' ∈ T, v' ≠ v → w ∈ powSub p (algebraMap F (v'.adicCompletion F)) := by
    intro v hv
    obtain ⟨u, hu, hnu, hu'⟩ := hA v hv
    obtain ⟨k, r, hr⟩ := GlobalTheory.T.exists_eq_pow_mul_pth_pow_adicCompletion_unit p F v (algebraMap F (v.adicCompletion F) (u : F))
      (algebraMap F (v.adicCompletion F) ((a * x : Fˣ) : F)) hp (hS.2 v (hTS v hv))
      (by rw [hval]; exact (mem_sUnits F S u).1 hu v (hTS v hv))
      (by rw [hval]; exact hy v hv) (fun r h => hnu ⟨r, h⟩)
    refine ⟨u ^ k, pow_mem hu k, ⟨r, ?_⟩, fun v' hv' hne => pow_mem (hu' v' hv' hne) k⟩
    have hu0 : algebraMap F (v.adicCompletion F) (u : F) ≠ 0 := by simp
    rw [Units.val_mul, map_mul, hr, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀,
      map_pow, inv_mul_cancel_left₀ (pow_ne_zero k hu0)]
  choose! w hwS hw1 hw2 using key
  have huU : ∏ v ∈ T, w v ∈ sUnits F (S ∪ T) := by
    refine prod_mem fun t ht => ?_
    rw [mem_sUnits]
    intro v hv
    exact (mem_sUnits F S _).1 (hwS t ht) v fun h => hv (Finset.mem_union_left _ h)
  have hsq : (∏ v ∈ T, w v)⁻¹ * (a * x) ∈ finPow p F T := by
    simp only [finPow, Subgroup.mem_iInf]
    intro v hv
    rw [← Finset.mul_prod_erase T w hv, mul_inv, mul_right_comm]
    refine mul_mem (hw1 v hv) (inv_mem (prod_mem fun t ht => ?_))
    exact hw2 t (Finset.mem_of_mem_erase ht) v hv (Finset.ne_of_mem_erase ht).symm
  have hx : x = ((∏ v ∈ T, w v) * a⁻¹) * ((∏ v ∈ T, w v)⁻¹ * (a * x)) := by
    rw [mul_mul_mul_comm, mul_inv_cancel, one_mul, inv_mul_cancel_left]
  rw [hx]
  exact Subgroup.mul_mem_sup (mul_mem huU (inv_mem haU)) hsq

end GlobalTheory.CNorm
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

open NumberField IsDedekindDomain in
private theorem exists_valuation_natCast_eq_exp_neg_and_dvd {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {p : ℕ} (hp : 0 < p) :
    ∃ e : ℕ, HeightOneSpectrum.valuation F v (p : F) = WithZero.exp (-(e : ℤ)) ∧
      v.asIdeal ^ e ∣ Ideal.span {(p : 𝓞 F)} := by
  have hval : HeightOneSpectrum.valuation F v (p : F) = v.intValuation (p : 𝓞 F) := by
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := F)]
    simp
  have hne : v.intValuation (p : 𝓞 F) ≠ 0 :=
    v.intValuation_ne_zero _ (by exact_mod_cast hp.ne')
  have hle : v.intValuation (p : 𝓞 F) ≤ 1 := v.intValuation_le_one _
  set a := v.intValuation (p : 𝓞 F) with ha
  have hlog : WithZero.log a ≤ 0 := by
    rw [← WithZero.exp_le_exp, WithZero.exp_log hne, WithZero.exp_zero]
    exact hle
  refine ⟨(-WithZero.log a).toNat, ?_, ?_⟩
  · rw [hval, Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log hne]
  · rw [← HeightOneSpectrum.intValuation_le_pow_iff_dvd, Int.toNat_of_nonneg (by omega), neg_neg,
      WithZero.exp_log hne]

open NumberField IsDedekindDomain in
private theorem powSub_eq_comap_pows_units_map {F L : Type} [Field F] [Field L] {p : ℕ} (hp : 0 < p)
    (φ : F →+* L) :
    _root_.GlobalTheory.CNorm.powSub p φ =
      (_root_.GlobalTheory.CNorm.pows p (⊤ : Subgroup Lˣ)).comap (Units.map φ.toMonoidHom) := by
  ext x
  rw [_root_.GlobalTheory.CNorm.mem_powSub, Subgroup.mem_comap]
  unfold _root_.GlobalTheory.CNorm.pows
  simp only [Subgroup.mem_map, Subgroup.mem_top, true_and, powMonoidHom_apply]
  constructor
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne'] at hr
      exact (map_ne_zero φ).2 x.ne_zero hr.symm
    exact ⟨Units.mk0 r hr0, Units.ext (by simpa using hr)⟩
  · rintro ⟨y, hy⟩
    refine ⟨(y : L), ?_⟩
    have := congrArg Units.val hy
    simpa using this

open NumberField IsDedekindDomain in
private theorem powSub_index_ne_zero_and_le_pIdx {F L : Type} [Field F] [Field L] {p : ℕ} (hp : 0 < p)
    (φ : F →+* L) (h : _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup Lˣ) ≠ 0) :
    (_root_.GlobalTheory.CNorm.powSub p φ).index ≠ 0 ∧
      (_root_.GlobalTheory.CNorm.powSub p φ).index ≤ _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup Lˣ) := by
  have hdef : _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup Lˣ) = (_root_.GlobalTheory.CNorm.pows p (⊤ : Subgroup Lˣ)).index := by
    unfold _root_.GlobalTheory.CNorm.pIdx
    exact Subgroup.relIndex_top_right _
  rw [hdef] at h ⊢
  rw [powSub_eq_comap_pows_units_map hp, Subgroup.index_comap]
  have hd := Subgroup.relIndex_dvd_index_of_normal (_root_.GlobalTheory.CNorm.pows p (⊤ : Subgroup Lˣ))
    (Units.map φ.toMonoidHom).range
  exact ⟨ne_zero_of_dvd_ne_zero h hd, Nat.le_of_dvd (Nat.pos_of_ne_zero h) hd⟩

open NumberField IsDedekindDomain in
private theorem pTor_units_le {L : Type} [Field L] {p : ℕ} (hp : 0 < p) :
    _root_.GlobalTheory.CNorm.pTor p (⊤ : Subgroup Lˣ) ≤ p := by
  unfold _root_.GlobalTheory.CNorm.pTor
  classical
  have hinj : Function.Injective (fun x : {x : Lˣ // x ∈ (⊤ : Subgroup Lˣ) ∧ x ^ p = 1} =>
      (⟨(x.1 : L), by
        rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hp, ← Units.val_pow_eq_pow_val, x.2.2,
          Units.val_one]⟩ : (Polynomial.nthRoots p (1 : L)).toFinset)) := by
    intro x y hxy
    exact Subtype.ext (Units.ext (congrArg Subtype.val hxy))
  calc Nat.card {x : Lˣ // x ∈ (⊤ : Subgroup Lˣ) ∧ x ^ p = 1}
      ≤ Nat.card (Polynomial.nthRoots p (1 : L)).toFinset := Nat.card_le_card_of_injective _ hinj
    _ = (Polynomial.nthRoots p (1 : L)).toFinset.card := Nat.card_eq_finsetCard _
    _ ≤ (Polynomial.nthRoots p (1 : L)).card := Multiset.toFinset_card_le _
    _ ≤ p := Polynomial.card_nthRoots p 1

open NumberField IsDedekindDomain in
private theorem prod_absNorm_pow_le_pow_finrank {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) {p : ℕ} (hp : 0 < p) (e : HeightOneSpectrum (𝓞 F) → ℕ)
    (he : ∀ v ∈ S, v.asIdeal ^ e v ∣ Ideal.span {(p : 𝓞 F)}) :
    ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ e v ≤ p ^ Module.finrank ℚ F := by
  have hdvd : ∏ v ∈ S, v.asIdeal ^ e v ∣ Ideal.span {(p : 𝓞 F)} := by
    refine Finset.prod_dvd_of_coprime ?_ he
    intro v _ w _ hvw
    have hne : v.asIdeal ≠ w.asIdeal := fun h => hvw (HeightOneSpectrum.ext h)
    exact (Ideal.isCoprime_iff_sup_eq.mpr
      (Ideal.IsMaximal.coprime_of_ne v.isMaximal w.isMaximal hne)).pow
  have hnorm : Ideal.absNorm (Ideal.span {(p : 𝓞 F)}) = p ^ Module.finrank ℚ F := by
    rw [Ideal.absNorm_span_singleton]
    have : (p : 𝓞 F) = algebraMap ℤ (𝓞 F) (p : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
    simp
  have h := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdvd)
  rw [hnorm, map_prod] at h
  simp only [map_pow] at h
  exact Nat.le_of_dvd (pow_pos hp _) h


open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
theorem _root_.GlobalTheory.CNorm.index_finPow_le : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F]
    [_root_.NumberField.IsTotallyComplex F] (S : Finset (HeightOneSpectrum (𝓞 F))), 0 < p →
    (_root_.GlobalTheory.CNorm.finPow p F S).index ≠ 0 ∧
      (_root_.GlobalTheory.CNorm.finPow p F S).index ≤
        p ^ (2 * (S.card + Fintype.card (InfinitePlace F))) := by
  intro p F _ _ _ S hp
  choose! e he hdiv using fun v : HeightOneSpectrum (𝓞 F) => exists_valuation_natCast_eq_exp_neg_and_dvd v hp
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      (_root_.GlobalTheory.CNorm.powSub p (algebraMap F (v.adicCompletion F))).index ≠ 0 ∧
        (_root_.GlobalTheory.CNorm.powSub p (algebraMap F (v.adicCompletion F))).index ≤
          p * Ideal.absNorm v.asIdeal ^ e v * p := by
    intro v
    obtain ⟨ht, hrel⟩ :=
      _root_.GlobalTheory.CNorm.pIdx_units_finite_extension_adicCompletion p F v (e v) (v.adicCompletion F) hp (he v)
    rw [Module.finrank_self, pow_one] at hrel
    have hN : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact v.ne_bot
    have hne : _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup (v.adicCompletion F)ˣ) ≠ 0 := by
      rw [hrel]
      exact mul_ne_zero (mul_ne_zero hp.ne' (pow_ne_zero _ hN)) ht
    obtain ⟨h1, h2⟩ := powSub_index_ne_zero_and_le_pIdx hp (algebraMap F (v.adicCompletion F)) hne
    refine ⟨h1, h2.trans ?_⟩
    rw [hrel]
    exact Nat.mul_le_mul_left _ (pTor_units_le hp)
  have hinf : _root_.GlobalTheory.CNorm.finPow p F S =
      ⨅ v : S, _root_.GlobalTheory.CNorm.powSub p
        (algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)) := by
    unfold _root_.GlobalTheory.CNorm.finPow
    rw [iInf_subtype']
  rw [hinf]
  refine ⟨Subgroup.index_iInf_ne_zero fun v => (hloc v).1, (Subgroup.index_iInf_le _).trans ?_⟩
  calc ∏ v : S, (_root_.GlobalTheory.CNorm.powSub p
          (algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F))).index
      ≤ ∏ v : S, (p * Ideal.absNorm (v : HeightOneSpectrum (𝓞 F)).asIdeal ^ e v * p) :=
        Finset.prod_le_prod' fun v _ => (hloc v).2
    _ = p ^ (2 * S.card) * ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ e v := by
        rw [Finset.prod_coe_sort S (fun v => p * Ideal.absNorm v.asIdeal ^ e v * p)]
        simp only [Finset.prod_mul_distrib, Finset.prod_const]
        ring
    _ ≤ p ^ (2 * S.card) * p ^ Module.finrank ℚ F :=
        Nat.mul_le_mul_left _ (prod_absNorm_pow_le_pow_finrank S hp e fun v _ => hdiv v)
    _ = p ^ (2 * (S.card + Fintype.card (InfinitePlace F))) := by
        rw [IsTotallyComplex.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
          IsTotallyComplex.nrRealPlaces_eq_zero, ← pow_add]
        ring_nf

end GlobalTheory.CNorm
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.pIdx_units_finite_extension_adicCompletion' : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : ℕ) (L : Type) [Field L] [Algebra (v.adicCompletion F) L] [FiniteDimensional (v.adicCompletion F) L], 0 < p → v.valuation F (p : F) = WithZero.exp (-(e : ℤ)) → pTor p (⊤ : Subgroup Lˣ) ≠ 0 ∧ pIdx p (⊤ : Subgroup Lˣ) = p * (Ideal.absNorm v.asIdeal ^ e) ^ Module.finrank (v.adicCompletion F) L * pTor p (⊤ : Subgroup Lˣ) := by
  first | exact @GlobalTheory.CNorm.pIdx_units_finite_extension_adicCompletion | exact GlobalTheory.CNorm.pIdx_units_finite_extension_adicCompletion | (intros; apply GlobalTheory.CNorm.pIdx_units_finite_extension_adicCompletion <;> assumption)
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

theorem integral_div_covolume_eq_of_haar {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ ν : Measure V)
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] (f : V → ℂ) (s : ℝ) :
    (∫ x, f x ∂μ) / ((ZLattice.covolume L μ * s : ℝ) : ℂ) =
      (∫ x, f x ∂ν) / ((ZLattice.covolume L ν * s : ℝ) : ℂ) := by
  obtain ⟨c, hc⟩ : ∃ c : NNReal, μ = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul μ ν⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    have : μ = 0 := by simpa using hc
    exact (NeZero.ne μ) this
  let b := Module.Free.chooseBasis ℤ L
  have h1 := ZLattice.covolume_eq_measure_fundamentalDomain L μ
    (ZLattice.isAddFundamentalDomain b μ)
  have h2 := ZLattice.covolume_eq_measure_fundamentalDomain L ν
    (ZLattice.isAddFundamentalDomain b ν)
  have h3 : ZLattice.covolume L μ = (c : ℝ) * ZLattice.covolume L ν := by
    rw [h1, h2]
    conv_lhs => rw [hc]
    simp [Measure.real]
  have h4 : ∫ x, f x ∂μ = (c : ℂ) * ∫ x, f x ∂ν := by
    conv_lhs => rw [hc]
    rw [integral_smul_nnreal_measure]
    simp [NNReal.smul_def]
  have hc1 : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc0
  rw [h3, h4]
  push_cast
  rw [mul_assoc, mul_div_mul_left _ _ hc1]

theorem lattice_sum_dilate_haar :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (f : V → ℂ), ContDiff ℝ ∞ f → HasCompactSupport f → ∀ A : ℕ, ∃ C : ℝ, ∀ (x₀ : V) (t : ℝ), 0 < t → t ≤ 1 → ‖∑' l : L, f (t • ((l : V) + x₀)) - (∫ x, f x ∂μ) / ((ZLattice.covolume L μ * t ^ Module.finrank ℝ V : ℝ) : ℂ)‖ ≤ C * t ^ A := by
  intro V _ _ _ _ _ μ _ L _ _ f hf hs A
  let e : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) ≃L[ℝ] V := toEuclidean.symm
  let ν : Measure V := (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ V)))).map e
  have : ν.IsAddHaarMeasure := ContinuousLinearEquiv.isAddHaarMeasure_map e _
  have hmp : MeasurePreserving e volume ν := ⟨e.continuous.measurable, rfl⟩
  obtain ⟨C, hC⟩ := GlobalTheory.T.zlattice_tsum_dilate_sub_integral_le_rapid _ (ZLattice.comap ℝ L e.toLinearMap) (f ∘ e)
    (hf.comp e.contDiff) (hs.comp_homeomorph e.toHomeomorph) A
  refine ⟨C, fun x₀ t ht ht1 => ?_⟩
  have h := hC (e.symm x₀) t ht ht1
  rw [ZLattice.covolume_comap L ν volume hmp, finrank_euclideanSpace_fin] at h
  have hi : ∫ x, (f ∘ e) x = ∫ x, f x ∂ν :=
    (hmp.integral_comp e.toHomeomorph.measurableEmbedding f)
  have hsum : ∑' l : ZLattice.comap ℝ L e.toLinearMap,
      (f ∘ e) (t • ((l : EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) + e.symm x₀)) =
      ∑' l : L, f (t • ((l : V) + x₀)) := by
    let q : ZLattice.comap ℝ L e.toLinearMap ≃ L :=
      e.toEquiv.subtypeEquiv (fun _ => Iff.rfl)
    rw [← q.tsum_eq]
    refine tsum_congr fun l => ?_
    have : ((q l : L) : V) = e l := rfl
    simp [this]
  rw [hi, hsum] at h
  rw [integral_div_covolume_eq_of_haar μ ν L f]
  exact h

end GlobalTheory
end

end

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.unitsLocalPowersAtPlaces_index_le : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (S : Finset (HeightOneSpectrum (𝓞 F))), 0 < p → (finPow p F S).index ≠ 0 ∧ (finPow p F S).index ≤ p ^ (2 * (S.card + Fintype.card (InfinitePlace F))) := by
  first | exact @GlobalTheory.CNorm.index_finPow_le | exact GlobalTheory.CNorm.index_finPow_le | (intros; apply GlobalTheory.CNorm.index_finPow_le <;> assumption)

end
end
