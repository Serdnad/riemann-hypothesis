module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle008
public import Formalism.LocalRingCardinality.Lemmas
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PowEqPowIffModEqOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle013
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle012
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle256
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem

theorem re_pos_of_majAt {K V ι M : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (σ : K →+* ℂ) (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : IsUnit (X (InfinitePlace.mk σ)).det) (e : V →ₛₗ[σ] M) (Q : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ)
    (h : ∀ x, (Formalism.HermitianLatticesTheory.majAt b X (InfinitePlace.mk σ) x x).re = (Q (e x) (e x)).re)
    (φ : M) (hφ : φ ∈ Submodule.span ℂ (Set.range fun a => e (b a))) (h0 : φ ≠ 0) :
    0 < (Q φ φ).re := by
  set v := InfinitePlace.mk σ with hv
  obtain ⟨ρ, hρc, hρρ, hρσ⟩ : ∃ ρ : ℂ →+* ℂ, Continuous ρ ∧ (∀ z, ρ (ρ z) = z) ∧
      ∀ x, ρ (v.embedding x) = σ x := by
    rcases InfinitePlace.embedding_mk_eq σ with h1 | h1
    · exact ⟨RingHom.id ℂ, continuous_id, fun _ => rfl, fun x => by rw [hv, h1]; rfl⟩
    · exact ⟨starRingEnd ℂ, Complex.continuous_conj, fun z => Complex.conj_conj z, fun x => by
        rw [hv, h1, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]⟩
  have hd0 : DenseRange (Pi.map (fun _ : ι => (v.embedding : K → ℂ))) :=
    DenseRange.piMap (fun _ => denseRange_embedding_of_isComplex v (IsTotallyComplex.isComplex v))
  have key : ∀ w : ι → ℂ, (Q (∑ a, ρ (w a) • e (b a)) (∑ a, ρ (w a) • e (b a))).re =
      ∑ i, ‖((X v)⁻¹.mulVec w) i‖ ^ 2 := by
    intro w
    induction w using hd0.induction_on with
    | hp =>
      apply isClosed_eq
      · set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
            RingHom.id_apply]
        have hρ : ∀ i : ι, Continuous (fun y : ι → ℂ => ρ (y i)) :=
          fun i => hρc.comp (continuous_apply i)
        fun_prop
      · have : Continuous fun w : ι → ℂ => (X v)⁻¹.mulVec w :=
          Continuous.matrix_mulVec continuous_const continuous_id
        fun_prop
    | ih y =>
      have h1 := h (b.equivFun.symm y)
      have h2 : e (b.equivFun.symm y) =
          ∑ a, ρ (Pi.map (fun _ : ι => (v.embedding : K → ℂ)) y a) • e (b a) := by

        rw [b.equivFun_symm_apply, map_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [LinearMap.map_smulₛₗ, Pi.map_apply, hρσ]
      have h3 : Formalism.HermitianLatticesTheory.vecAt b v (b.equivFun.symm y) = Pi.map (fun _ : ι => (v.embedding : K → ℂ)) y := by
        funext a
        have : b.repr (b.equivFun.symm y) a = y a := by
          rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
        simp only [Formalism.HermitianLatticesTheory.vecAt, this, Pi.map_apply]
      rw [← h2, ← h1, ← normAt_sq_eq_majAt, Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm,
        Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity), Formalism.HermitianLatticesTheory.fcoord, h3]
  obtain ⟨z, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hφ
  have hk := key fun a => ρ (z a)
  simp only [hρρ] at hk
  rw [hk]
  refine lt_of_le_of_ne (Finset.sum_nonneg fun i _ => by positivity) fun hs => h0 ?_
  have h4 : (X v)⁻¹.mulVec (fun a => ρ (z a)) = 0 := by
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 hs.symm i (Finset.mem_univ i)
    simpa using this
  have h5 : (fun a => ρ (z a)) = 0 := by
    have := congrArg (X v).mulVec h4
    rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hX, Matrix.one_mulVec, Matrix.mulVec_zero] at this
  refine Finset.sum_eq_zero fun a _ => ?_
  have h6 : z a = 0 := by
    rw [← hρρ (z a), show ρ (z a) = 0 from congrFun h5 a, map_zero]
  rw [h6, zero_smul]

theorem ipC_zero_re_pos : ∀ (B : Base) (C : Cols B) (u : B.Word), (∀ φ ψ : (C.mem u).A.Mu0, (C.fm u).ipC 0 ψ φ = star ((C.fm u).ipC 0 φ ψ)) → ∀ φ : (C.mem u).A.Mu0, φ ≠ 0 → 0 < ((C.fm u).ipC 0 φ φ).re := by
  intro B C u _ φ hφ
  let Q : ((C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) →ₗ⋆[ℂ] ((C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) ((C.fm u).ipC 0)
      (fun x y z => by simp [MemberForms.ipC, mul_add, Finset.sum_add_distrib])
      (fun c x y => by simp [MemberForms.ipC, Finset.mul_sum, mul_left_comm])
      (fun x y z => by simp [MemberForms.ipC, mul_add, Finset.sum_add_distrib])
      (fun c x y => by simp [MemberForms.ipC, Finset.mul_sum, mul_left_comm])
  refine re_pos_of_majAt B.embLL ((C.fm u).lat 0).b ((C.fm u).lat 0).X (((C.fm u).lat_good 0).1 _)
    ((C.fm u).emb 0) Q ((C.fm u).emb_norm 0) φ ?_ (fun h => hφ (Subtype.ext h))
  rw [((C.fm u).emb_basis 0).2, (C.fm u).Fi_zero]
  exact φ.2

end GlobalTheory.Mem
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.FieldsEx

variable {E : Type} [Field E] [NumberField E]

theorem exists_finite_units_mod_pow {h : ℕ} (h0 : h ≠ 0) :
    ∃ S : Set (𝓞 E)ˣ, S.Finite ∧ ∀ u : (𝓞 E)ˣ, ∃ s ∈ S, ∃ w : (𝓞 E)ˣ, u = s * w ^ h := by
  have : Group.FG (𝓞 E)ˣ := Group.fg_iff_monoid_fg.2 inferInstance
  have := Subgroup.finiteIndex_range_powMonoidHom_of_fg (𝓞 E)ˣ h0
  have : Finite ((𝓞 E)ˣ ⧸ (powMonoidHom h : (𝓞 E)ˣ →* (𝓞 E)ˣ).range) := Subgroup.finite_quotient_of_finiteIndex
  refine ⟨Set.range (Quotient.out : (𝓞 E)ˣ ⧸ (powMonoidHom h : (𝓞 E)ˣ →* (𝓞 E)ˣ).range → (𝓞 E)ˣ),
    @Set.finite_range _ _ _ this, fun u => ?_⟩
  obtain ⟨⟨_, w, rfl⟩, hw⟩ := QuotientGroup.mk_out_eq_mul (powMonoidHom h : (𝓞 E)ˣ →* (𝓞 E)ˣ).range u
  refine ⟨_, ⟨(u : (𝓞 E)ˣ ⧸ (powMonoidHom h : (𝓞 E)ˣ →* (𝓞 E)ˣ).range), rfl⟩, w⁻¹, ?_⟩
  rw [hw]
  simp

theorem exists_finite_mod_units_pow {h : ℕ} (h0 : h ≠ 0) :
    ∃ S : Set E, S.Finite ∧ ∀ y ∈ powIdealElts E h, ∃ s ∈ S, ∃ (x : E) (u : (𝓞 E)ˣ),
      y = x ^ h * s * ((u : 𝓞 E) : E) := by
  classical
  have key : ∀ y : powIdealElts E h, ∃ 𝔞 : (FractionalIdeal (𝓞 E)⁰ E)ˣ,
      FractionalIdeal.spanSingleton (𝓞 E)⁰ (y : E) = (𝔞 : FractionalIdeal (𝓞 E)⁰ E) ^ h := by
    rintro ⟨y, hy, 𝔞, ha⟩
    refine ⟨Units.mk0 𝔞 ?_, ha⟩
    rintro rfl
    rw [zero_pow h0, FractionalIdeal.spanSingleton_eq_zero_iff] at ha
    exact hy ha
  choose A hA using key
  let c : powIdealElts E h → ClassGroup (𝓞 E) := fun y => ClassGroup.mk E (A y)
  let r : Set.range c → E := fun t => (t.2.choose : E)
  refine ⟨Set.range r, Set.finite_range _, fun y hy => ⟨_, ⟨⟨c ⟨y, hy⟩, _, rfl⟩, rfl⟩, ?_⟩⟩
  have ht : c ⟨y, hy⟩ ∈ Set.range c := ⟨_, rfl⟩
  have h1 : c ht.choose = c ⟨y, hy⟩ := ht.choose_spec
  change ∃ (x : E) (u : (𝓞 E)ˣ), y = x ^ h * (ht.choose : E) * ((u : 𝓞 E) : E)
  generalize ht.choose = s at h1
  have h2 : ClassGroup.mk E (A ⟨y, hy⟩ * (A s)⁻¹) = 1 := by
    rw [map_mul, map_inv, mul_inv_eq_one]
    exact h1.symm
  obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).1 (ClassGroup.mk_eq_one_iff.1 h2)
  have h3 : ((A ⟨y, hy⟩ : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ x * A s := by
    rw [← hx, ← Units.val_mul, inv_mul_cancel_right]
  have h4 : FractionalIdeal.spanSingleton (𝓞 E)⁰ (x ^ h * s) = FractionalIdeal.spanSingleton (𝓞 E)⁰ y := by
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, ← FractionalIdeal.spanSingleton_pow, hA s, ← mul_pow,
      ← h3]
    exact (hA ⟨y, hy⟩).symm
  obtain ⟨u, hu⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.1 h4
  refine ⟨x, u, ?_⟩
  rw [← hu, Units.smul_def, Algebra.smul_def, mul_comm]

theorem exists_finite_mod_pow {h : ℕ} (h0 : h ≠ 0) :
    ∃ S : Set E, S.Finite ∧ ∀ y ∈ powIdealElts E h, ∃ s ∈ S, ∃ x : E, y = x ^ h * s := by
  obtain ⟨S, hS, H⟩ := exists_finite_mod_units_pow (E := E) h0
  obtain ⟨T, hT, H'⟩ := exists_finite_units_mod_pow (E := E) h0
  refine ⟨Set.image2 (fun s (t : (𝓞 E)ˣ) => s * ((t : 𝓞 E) : E)) S T, hS.image2 _ hT, fun y hy => ?_⟩
  obtain ⟨s, hs, x, u, rfl⟩ := H y hy
  obtain ⟨t, ht, w, rfl⟩ := H' u
  refine ⟨_, ⟨s, hs, t, ht, rfl⟩, x * ((w : 𝓞 E) : E), ?_⟩
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, RingOfIntegers.coe_eq_algebraMap]
  ring

theorem finiteDimensional_kummerField (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (h : ℕ) (h0 : h ≠ 0) :
    FiniteDimensional ℚ (kummerField φ h) := by
  obtain ⟨S, hS, H⟩ := exists_finite_mod_pow (E := E) h0
  let R : Set ℂ := ⋃ s ∈ insert 1 S, {z | z ^ h = φ s}
  have hR : R.Finite := (hS.insert 1).biUnion fun s _ =>
    ((Polynomial.nthRoots h (φ s)).finite_toSet).subset fun z hz =>
      (Polynomial.mem_nthRoots (Nat.pos_of_ne_zero h0)).2 hz
  have : Finite R := hR
  have h1 : FiniteDimensional ℚ (IntermediateField.adjoin ℚ R) := by
    refine IntermediateField.finiteDimensional_adjoin fun z hz => ?_
    obtain ⟨s, -, hs⟩ := Set.mem_iUnion₂.1 hz
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero h0) ?_
    rw [show z ^ h = φ s from hs]
    exact (Algebra.IsIntegral.isIntegral s).map φ.toRatAlgHom
  have h2 : FiniteDimensional ℚ (imField φ) :=
    (AlgEquiv.ofInjectiveField φ.toRatAlgHom).toLinearEquiv.finiteDimensional
  have h3 : FiniteDimensional ℚ (imField φ ⊔ IntermediateField.adjoin ℚ R : IntermediateField ℚ ℂ) :=
    IntermediateField.finiteDimensional_sup _ _
  have hE : ∀ x, φ x ∈ imField φ ⊔ IntermediateField.adjoin ℚ R := fun x =>
    (le_sup_left : imField φ ≤ _) ⟨x, rfl⟩
  have hz : ∀ s ∈ insert 1 S, ∀ z : ℂ, z ^ h = φ s → z ∈ imField φ ⊔ IntermediateField.adjoin ℚ R :=
    fun s hs z hz => (le_sup_right : IntermediateField.adjoin ℚ R ≤ _)
      (IntermediateField.subset_adjoin ℚ R (Set.mem_iUnion₂.2 ⟨s, hs, hz⟩))
  have hle : kummerField φ h ≤ imField φ ⊔ IntermediateField.adjoin ℚ R := by
    refine (kummerField_le_iff φ).2 ⟨hE, hz 1 (Set.mem_insert _ _) _ ?_, fun y hy z hzy => ?_⟩
    · rw [map_one]
      exact (Complex.isPrimitiveRoot_exp h h0).pow_eq_one
    · obtain ⟨s, hs, x, rfl⟩ := H y hy
      have hx : φ x ≠ 0 := by
        rw [map_ne_zero]
        rintro rfl
        exact hy.1 (by rw [zero_pow h0, zero_mul])
      have h4 := hz s (Set.mem_insert_of_mem _ hs) (z / φ x) (by
        rw [div_pow, hzy, map_mul, map_pow, mul_div_cancel_left₀ _ (pow_ne_zero _ hx)])
      simpa [hx] using mul_mem h4 (hE x)
  exact Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion_injective hle)

end GlobalTheory.Mem.FieldsEx

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.Fld

theorem prod_orderOf_le_card_of_indep {G ι : Type} [CommGroup G] [Fintype G] [Fintype ι] (x : ι → G)
    (hx : ∀ a : ι → ℤ, ∏ i, x i ^ a i = 1 → ∀ i, x i ^ a i = 1) : ∏ i, orderOf (x i) ≤ Fintype.card G := by
  classical
  have hinj : Function.Injective (fun a : (∀ i, Fin (orderOf (x i))) => ∏ i, x i ^ (a i : ℕ)) := by
    intro a a' h
    have h1 := hx (fun i => ((a i : ℕ) : ℤ) - ((a' i : ℕ) : ℤ)) (by
      simp only [zpow_sub, zpow_natCast, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
      exact mul_inv_eq_one.2 h)
    funext i
    have h2 := h1 i
    rw [zpow_sub, zpow_natCast, zpow_natCast, mul_inv_eq_one] at h2
    exact Fin.ext (pow_injOn_Iio_orderOf (a i).2 (a' i).2 h2)
  simpa using Fintype.card_le_of_injective _ hinj

theorem card_filter_le_log_classNumber {E : Type} [Field E] [NumberField E] (b : GlobalTheory.IndefiniteRowSideFullHecke.RootValueClassBasis.ClassBasis E) :
    (Finset.univ.filter fun i => b.h i ≠ 1).card ≤ Nat.log 2 (classNumber E) := by
  refine Nat.le_log_of_pow_le (by norm_num) ?_
  have h1 : ∏ i, b.h i ≤ classNumber E := prod_orderOf_le_card_of_indep _ b.indep
  refine le_trans ?_ h1
  rw [← Finset.prod_filter_ne_one]
  refine Finset.pow_card_le_prod _ _ _ fun i hi => ?_
  have h2 := (Finset.mem_filter.1 hi).2
  have h3 := b.h_pos i
  omega

theorem exists_kPsiField_generators (R : Ranks) (H : Host R) (b : GlobalTheory.IndefiniteRowSideFullHecke.RootValueClassBasis.ClassBasis H.E) (p q : ℕ) :
    ∃ S : Finset ℂ, S.card ≤ Nat.log 2 (classNumber H.E) ∧
      (∀ y ∈ S, ∃ n : ℕ, 0 < n ∧ n ∣ classNumber H.E ∧ y ^ n ∈ imField H.φ₀) ∧
      kPsiField H b p q = imField H.φ₀ ⊔ cycField (classNumber H.E) ⊔ IntermediateField.adjoin ℚ (S : Set ℂ) := by
  classical
  choose ψ hψ using fun i : Fin b.k =>
    IsAlgClosed.exists_pow_nat_eq (H.φ₀ (typeNorm H p q (b.γ i : H.E))) (b.h_pos i)
  refine ⟨(Finset.univ.filter fun i => b.h i ≠ 1).image ψ,
    Finset.card_image_le.trans (card_filter_le_log_classNumber b), fun y hy => ?_, ?_⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨b.h i, b.h_pos i, orderOf_dvd_card, _, (hψ i).symm⟩
  · rw [kPsiField_eq H b p q ψ hψ]
    refine le_antisymm (sup_le le_sup_left ?_) (sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) _)
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      by_cases h : b.h i = 1
      · have h1 : ψ i ∈ imField H.φ₀ := ⟨_, by have := hψ i; rw [h, pow_one] at this; exact this.symm⟩
        exact (le_sup_left.trans le_sup_left : imField H.φ₀ ≤ _) h1
      · exact (le_sup_right : IntermediateField.adjoin ℚ _ ≤ _) (IntermediateField.subset_adjoin ℚ _
          (Finset.mem_coe.2 (Finset.mem_image_of_mem ψ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩))))
    · intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
      exact ⟨i, rfl⟩

end GlobalTheory.Mem.Fld
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.ClassDvd

theorem classGroup_exists_integral_ideal_coprime {R : Type} [CommRing R] [IsDedekindDomain R] {m : Ideal R} (hm : m ≠ ⊥)
    (c : ClassGroup R) : ∃ I : (Ideal R)⁰, IsCoprime (I : Ideal R) m ∧ ClassGroup.mk0 I = c := by
  by_cases ht : m = ⊤
  · obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective c
    exact ⟨I, by rw [ht, ← Ideal.one_eq_top]; exact isCoprime_one_right, hI⟩
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective c⁻¹
  have hJ0 : (J : Ideal R) ≠ 0 := nonZeroDivisors.coe_ne_zero J
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq (I := (J : Ideal R) * m) (J := J) Ideal.mul_le_left
    (mul_ne_zero hJ0 hm)
  obtain ⟨M, hM⟩ : (J : Ideal R) ∣ Ideal.span {a} := Ideal.dvd_iff_le.2 (ha ▸ le_sup_right)
  have h1 : m ⊔ M = ⊤ := by
    apply mul_left_cancel₀ hJ0
    rw [Ideal.mul_sup, ← hM, ha, Ideal.mul_top]
  have hM0 : M ≠ 0 := by
    rintro rfl
    exact ht (by simpa using h1)
  refine ⟨⟨M, mem_nonZeroDivisors_of_ne_zero hM0⟩, ?_, ?_⟩
  · rw [Ideal.isCoprime_iff_sup_eq, sup_comm]; exact h1
  · have ha0 : a ≠ 0 := by
      rintro rfl
      exact mul_ne_zero hJ0 hM0 (by simpa using hM.symm)
    rw [← inv_inv c, ← hJ, ClassGroup.mk0_eq_mk0_inv_iff]
    exact ⟨a, ha0, by rw [hM, mul_comm]⟩

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] {𝔮 : Ideal (𝓞 K)}

theorem exists_symbol [IsGalois K L] (hR : IsRay L 𝔮) (I : Ideal (𝓞 K)) :
    I ≠ ⊥ → IsCoprime I 𝔮 → ∃ σ : L ≃ₐ[K] L, ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = (χ σ : ℂˣ) := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact fun h => absurd rfl h
  | h₂ I hI =>
    intro _ _
    obtain rfl : I = 1 := by rw [Ideal.one_eq_top]; exact Ideal.isUnit_iff.1 hI
    exact ⟨1, fun χ => by rw [GlobalTheory.NT.Model.heckeIdeal_top]; simp⟩
  | h₃ I p hI0 hp ih =>
    intro _ hc
    obtain ⟨σ, hσ⟩ := ih hI0 hc.of_mul_left_right
    let v : HeightOneSpectrum (𝓞 K) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    have hv : ¬ v.asIdeal ∣ 𝔮 := fun h => hp.not_isUnit (hc.of_mul_left_left.isUnit_of_dvd h)
    obtain ⟨τ, hτ⟩ := GlobalTheory.NT.exists_isFrob L v
    refine ⟨τ * σ, fun χ => ?_⟩
    have h1 := GlobalTheory.NT.Model.heckeIdeal_prime L χ v
    rw [heckeVal_of_unramIn L χ (hR.1 v hv) hτ] at h1
    rw [GlobalTheory.NT.Model.heckeIdeal_mul L χ hp.ne_zero hI0, hσ]
    change heckeIdeal L χ v.asIdeal * _ = _
    rw [h1]; simp

theorem classNumber_dvd_finrank : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (𝔮 : Ideal (𝓞 K)), 𝔮 ≠ ⊥ → IsRayField K L 𝔮 → classNumber K ∣ Module.finrank K L := by
  intro K L _ _ _ _ _ 𝔮 h𝔮 h
  have := h.1
  have hR : IsRay L 𝔮 := h.2
  let S : Submonoid ((L ≃ₐ[K] L) × ClassGroup (𝓞 K)) :=
    { carrier := {x | ∃ I : (Ideal (𝓞 K))⁰, IsCoprime (I : Ideal (𝓞 K)) 𝔮 ∧ ClassGroup.mk0 I = x.2 ∧
        ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = (χ x.1 : ℂˣ)}
      one_mem' := ⟨1, isCoprime_one_left, map_one _, fun χ => by
        rw [OneMemClass.coe_one, GlobalTheory.NT.Model.heckeIdeal_top]; simp⟩
      mul_mem' := by
        rintro x y ⟨I, hI, hIc, hx⟩ ⟨J, hJ, hJc, hy⟩
        refine ⟨I * J, hI.mul_left hJ, by rw [map_mul, hIc, hJc]; rfl, fun χ => ?_⟩
        rw [Submonoid.coe_mul, GlobalTheory.NT.Model.heckeIdeal_mul L χ (nonZeroDivisors.coe_ne_zero I)
          (nonZeroDivisors.coe_ne_zero J), hx, hy]; simp }
  let H : Subgroup ((L ≃ₐ[K] L) × ClassGroup (𝓞 K)) :=
    { S with
      inv_mem' := by
        intro x hx
        have : x⁻¹ = x ^ (orderOf x - 1) := by
          rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
        rw [this]
        exact S.pow_mem hx _ }
  have h1 : Function.Bijective ((MonoidHom.fst _ _).comp H.subtype) := by
    refine ⟨(injective_iff_map_eq_one _).2 ?_, fun σ => ?_⟩
    · rintro ⟨⟨σ, c⟩, I, hI, hIc, hx⟩ hσ
      obtain rfl : σ = 1 := hσ
      obtain ⟨α, β, hp, he⟩ := (hR.2.2 I (nonZeroDivisors.coe_ne_zero I) hI).1 fun χ => by simpa using hx χ
      have hc : ClassGroup.mk0 I = ClassGroup.mk0 1 :=
        ClassGroup.mk0_eq_mk0_iff.2 ⟨β, α, hp.2.1, hp.1, by simpa [mul_comm] using he⟩
      rw [map_one] at hc
      obtain rfl : c = 1 := hIc.symm.trans hc
      rfl
    · obtain ⟨I, hI0, hI, hx⟩ := RayDegree.exists_ideal hR σ
      let J : (Ideal (𝓞 K))⁰ := ⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩
      exact ⟨⟨(σ, ClassGroup.mk0 J), J, hI, rfl, hx⟩, rfl⟩
  have h2 : Function.Surjective ((MonoidHom.snd _ _).comp H.subtype) := fun c => by
    obtain ⟨I, hI, hc⟩ := classGroup_exists_integral_ideal_coprime h𝔮 c
    obtain ⟨σ, hσ⟩ := exists_symbol hR I (nonZeroDivisors.coe_ne_zero I) hI
    exact ⟨⟨(σ, c), I, hI, hc, hσ⟩, rfl⟩
  rw [← IsGalois.card_aut_eq_finrank, ← Nat.card_eq_of_bijective _ h1, classNumber, ← Nat.card_eq_fintype_card]
  exact Subgroup.card_dvd_of_surjective h2

end GlobalTheory.Mem.ClassDvd

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.Mem.Fld.RaySize

theorem isEmpty_realEmb (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] : IsEmpty (E →+* ℝ) := by
  refine ⟨fun ψ => ?_⟩
  have h : InfinitePlace.IsReal (InfinitePlace.mk (Complex.ofRealHom.comp ψ)) :=
    ⟨_, ComplexEmbedding.isReal_iff.2 (by ext x; simp [ComplexEmbedding.conjugate]), rfl⟩
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)) h

theorem degOver_le_and_sz : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (φ : E →+* ℂ) (N : ℕ) (M : IntermediateField ℚ ℂ) (h : IsRayFieldIn φ (natIdeal E N) M), N ≠ 0 → degOver φ M h.emb_mem ≤ classNumber E * N ^ Module.finrank ℚ E ∧ Sz M (Real.log (Module.finrank ℚ E) + Real.log (degOver φ M h.emb_mem)) (Real.log |((discr E : ℤ) : ℝ)| / Module.finrank ℚ E + Real.log N + Real.log (degOver φ M h.emb_mem)) := by
  intro E _ _ _ φ N M h hN
  haveI : NumberField M := h.numberField
  letI := algOf φ M h.emb_mem
  have hR : IsRayField E M (natIdeal E N) := h.isRayField
  haveI : IsAbelianGalois E M := hR.1
  have hdeg : degOver φ M h.emb_mem = Module.finrank E M := rfl
  have hfin := finrank_mul_degOver φ M h.emb_mem
  rw [hdeg] at hfin ⊢
  refine ⟨?_, ?_⟩
  · have h1 := GlobalTheory.FieldSize.RayDegree.finrank_le E M (natIdeal E N) (natIdeal_ne_bot hN) hR.2
    haveI := isEmpty_realEmb E
    rwa [Fintype.card_eq_zero, pow_zero, mul_one, Ideal.absNorm_span_natCast, RingOfIntegers.rank] at h1
  · refine ⟨inferInstance, ?_, ?_⟩
    · rw [← hfin]
      have : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
      have : (0 : ℝ) < Module.finrank E M := by exact_mod_cast Module.finrank_pos
      rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    · have hun : ∀ 𝔭 : HeightOneSpectrum (𝓞 E), (N : 𝓞 E) ∉ 𝔭.asIdeal → GlobalTheory.NT.UnramIn M 𝔭 :=
        fun 𝔭 h𝔭 => hR.2.1 𝔭 (fun hd => h𝔭 (Ideal.dvd_span_singleton.1 hd))
      have hmem := GlobalTheory.DifferentBound.natCast_mul_finrank_mem_differentIdeal E M N (Nat.pos_of_ne_zero hN) hun
      have h2 := GlobalTheory.log_rootDiscr_le_of_natCast_mem_differentIdeal E M (N * Module.finrank E M)
        (Nat.mul_pos (Nat.pos_of_ne_zero hN) Module.finrank_pos) hmem
      have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
      have hd : (0 : ℝ) < Module.finrank E M := by exact_mod_cast Module.finrank_pos
      rw [Nat.cast_mul, Real.log_mul hN'.ne' hd.ne', ← add_assoc] at h2
      exact h2

end GlobalTheory.Mem.Fld.RaySize
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr


open Classical in
theorem splitsC_of_modEq_one : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (p : ℕ), p.Prime →
    p ≡ 1 [MOD H.QS * H.q * H.d] → SplitsC H.E p := by
  intro R H p hp h
  have hd16 : H.d % 16 = 7 := H.hyp.2.2.2.1
  have hpos : 0 < H.QS * H.q * H.d := Nat.pos_of_ne_zero H.condN_ne_zero
  have hlt : 1 < H.QS * H.q * H.d :=
    lt_of_lt_of_le (by omega : 1 < H.d) (Nat.le_of_dvd hpos (dvd_mul_left _ _))
  refine (GlobalTheory.HostSplit.split_of_one_mod R H p hp ?_).1
  rw [h]
  exact Nat.mod_eq_of_lt hlt

end GlobalTheory.Mem.Chr
end
