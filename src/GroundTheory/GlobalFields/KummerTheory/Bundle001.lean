module

public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import GroundTheory.LocalFields.UnitsBasic
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import GroundTheory.GlobalFields.KummerTheory.LocalIndex
public import GroundTheory.GlobalFields.Bundle001
public import GroundTheory.GlobalFields.SemilocalAlgebras.Bundle001
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.TotallySplit
public import GroundTheory.GlobalFields.SemilocalAlgebras.Galois
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.GlobalFields.SemilocalAlgebras.Bundle002

@[expose] public section

section

namespace GroundTheory.Global

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
  GroundTheory.LocalField

section FinitePlace

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem coe_mem_adicCompletionIntegers (x : 𝒪[v.adicCompletion K]) :
    (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K :=
  (mem_valuationInteger_iff v (x : v.adicCompletion K)).1 x.2

theorem coe_mem_valuationInteger (x : v.adicCompletionIntegers K) :
    (x : v.adicCompletion K) ∈ 𝒪[v.adicCompletion K] :=
  (mem_valuationInteger_iff v (x : v.adicCompletion K)).2 x.2

def integerEquivAdicCompletionIntegers :
    𝒪[v.adicCompletion K] ≃+* v.adicCompletionIntegers K where
  toFun x := ⟨x, coe_mem_adicCompletionIntegers v x⟩
  invFun x := ⟨x, coe_mem_valuationInteger v x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem coe_integerEquivAdicCompletionIntegers (x : 𝒪[v.adicCompletion K]) :
    ((integerEquivAdicCompletionIntegers v x : v.adicCompletionIntegers K) :
      v.adicCompletion K) = x :=
  rfl

theorem natCard_residueField_adicCompletion :
    Nat.card 𝓀[v.adicCompletion K] = Ideal.absNorm v.asIdeal := by
  rw [← natCard_residueField_adicCompletionIntegers v]
  exact Nat.card_congr
    (IsLocalRing.ResidueField.mapEquiv (integerEquivAdicCompletionIntegers v)).toEquiv

theorem norm_eq_absNorm_zpow_neg_ord {x : v.adicCompletion K} (hx : x ≠ 0) :
    ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-ord x) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[v.adicCompletion K]
  set p := unitsEquivIntProd hϖ (Units.mk0 x hx)
  have hxp : x = ((ϖ : v.adicCompletion K)) ^ (Multiplicative.toAdd p.1) *
      ((p.2 : 𝒪[v.adicCompletion K]) : v.adicCompletion K) := by
    rw [← coe_unitsOfIntProd hϖ, ← unitsEquivIntProd_symm_apply hϖ, MulEquiv.symm_apply_apply]
    rfl
  have hord : Multiplicative.toAdd p.1 = ord x := by
    rw [unitsEquivIntProd_fst hϖ]
    rfl
  have hϖ' : Irreducible (integerEquivAdicCompletionIntegers v ϖ) :=
    hϖ.map (integerEquivAdicCompletionIntegers v)
  have hnϖ : ‖(ϖ : v.adicCompletion K)‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
    have h := normalizedAbv_of_irreducible v hϖ'
    rw [normalizedAbv_apply, coe_integerEquivAdicCompletionIntegers] at h
    exact h
  have hu : ‖((p.2 : 𝒪[v.adicCompletion K]) : v.adicCompletion K)‖ = 1 := by
    have hunit : IsUnit (integerEquivAdicCompletionIntegers v p.2) :=
      p.2.isUnit.map (integerEquivAdicCompletionIntegers v)
    have h1 := (adicCompletionIntegers.isUnit_iff_valued_eq_one).1 hunit
    have h0 : ((p.2 : 𝒪[v.adicCompletion K]) : v.adicCompletion K) ≠ 0 := by
      exact_mod_cast p.2.ne_zero
    rw [← normalizedAbv_apply, normalizedAbv_eq_zpow v h0]
    rw [coe_integerEquivAdicCompletionIntegers] at h1
    rw [h1]
    simp
  conv_lhs => rw [hxp]
  rw [norm_mul, norm_zpow, hnϖ, hu, mul_one, hord, inv_zpow']

variable {v}

theorem natCast_ne_zero_adicCompletion {n : ℕ} (hn : n ≠ 0) :
    (n : v.adicCompletion K) ≠ 0 := by
  rw [← map_natCast (algebraMap K (v.adicCompletion K)), ne_eq,
    map_eq_zero_iff _ (algebraMap K (v.adicCompletion K)).injective]
  exact_mod_cast hn

variable (v)

theorem index_range_powMonoidHom_adicCompletion {n : ℕ} (hn : n ≠ 0) :
    ((powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range.index : ℝ) =
      n * Nat.card (rootsOfUnity n (v.adicCompletion K)) / ‖(n : v.adicCompletion K)‖ := by
  have hn' := natCast_ne_zero_adicCompletion (v := v) hn
  rw [index_range_powMonoidHom hn', natCard_residueField_adicCompletion,
    norm_eq_absNorm_zpow_neg_ord v hn', zpow_neg, div_inv_eq_mul]

theorem index_range_powMonoidHom_adicCompletion_of_hasEnoughRootsOfUnity {n : ℕ} [NeZero n]
    [HasEnoughRootsOfUnity (v.adicCompletion K) n] :
    ((powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range.index : ℝ) =
      n ^ 2 / ‖(n : v.adicCompletion K)‖ := by
  rw [index_range_powMonoidHom_adicCompletion v (NeZero.ne n),
    HasEnoughRootsOfUnity.natCard_rootsOfUnity, sq]

theorem isOpen_range_powMonoidHom_adicCompletion {n : ℕ} (hn : n ≠ 0) :
    IsOpen ((powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range :
      Set (v.adicCompletion K)ˣ) :=
  isOpen_range_powMonoidHom (natCast_ne_zero_adicCompletion hn)

end FinitePlace

section Archimedean

theorem exists_pos_real_pow_eq {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    ∃ y : ℝ, 0 < y ∧ y ^ n = x :=
  ⟨x ^ (n⁻¹ : ℝ), Real.rpow_pos_of_pos hx _, Real.rpow_inv_natCast_pow hx.le hn⟩

theorem mem_range_powMonoidHom_real_iff_of_even {n : ℕ} (hn : n ≠ 0) (he : Even n) (x : ℝˣ) :
    x ∈ (powMonoidHom n : ℝˣ →* ℝˣ).range ↔ 0 < (x : ℝ) := by
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    rw [powMonoidHom_apply, Units.val_pow_eq_pow_val]
    exact he.pow_pos y.ne_zero
  · intro hx
    obtain ⟨y, hy, hyx⟩ := exists_pos_real_pow_eq hx hn
    refine ⟨Units.mk0 y hy.ne', ?_⟩
    ext
    rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, hyx]

theorem range_powMonoidHom_real_of_odd {n : ℕ} (ho : Odd n) :
    (powMonoidHom n : ℝˣ →* ℝˣ).range = ⊤ := by
  have hn : n ≠ 0 := by rintro rfl; simp at ho
  refine eq_top_iff.2 fun x _ ↦ ?_
  rw [MonoidHom.mem_range]
  rcases lt_or_gt_of_ne x.ne_zero with hx | hx
  · obtain ⟨y, hy, hyx⟩ := exists_pos_real_pow_eq (neg_pos.2 hx) hn
    refine ⟨Units.mk0 (-y) (neg_ne_zero.2 hy.ne'), ?_⟩
    ext
    rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, ho.neg_pow, hyx, neg_neg]
  · obtain ⟨y, hy, hyx⟩ := exists_pos_real_pow_eq hx hn
    refine ⟨Units.mk0 y hy.ne', ?_⟩
    ext
    rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, hyx]

theorem index_range_powMonoidHom_real_of_even {n : ℕ} (hn : n ≠ 0) (he : Even n) :
    (powMonoidHom n : ℝˣ →* ℝˣ).range.index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨-1, fun b ↦ ?_⟩
  rw [mem_range_powMonoidHom_real_iff_of_even hn he, mem_range_powMonoidHom_real_iff_of_even hn he,
    Units.val_mul, Units.val_neg, Units.val_one, mul_neg_one]
  rcases lt_or_gt_of_ne b.ne_zero with hb | hb
  · exact Or.inl ⟨neg_pos.2 hb, hb.not_gt⟩
  · exact Or.inr ⟨hb, by linarith⟩

theorem index_range_powMonoidHom_real_of_odd {n : ℕ} (ho : Odd n) :
    (powMonoidHom n : ℝˣ →* ℝˣ).range.index = 1 := by
  rw [range_powMonoidHom_real_of_odd ho, Subgroup.index_top]

theorem index_range_powMonoidHom_real {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : ℝˣ →* ℝˣ).range.index = if Even n then 2 else 1 := by
  split_ifs with he
  · exact index_range_powMonoidHom_real_of_even hn he
  · exact index_range_powMonoidHom_real_of_odd (Nat.not_even_iff_odd.1 he)

theorem range_powMonoidHom_complex {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : ℂˣ →* ℂˣ).range = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ ?_
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (x : ℂ) (Nat.pos_of_ne_zero hn)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hz
    exact x.ne_zero hz.symm
  refine ⟨Units.mk0 z hz0, ?_⟩
  ext
  rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, hz]

theorem index_range_powMonoidHom_complex {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : ℂˣ →* ℂˣ).range.index = 1 := by
  rw [range_powMonoidHom_complex hn, Subgroup.index_top]

end Archimedean

end GroundTheory.Global
end

section

noncomputable section

namespace GroundTheory.Global

open IsDedekindDomain NumberField Module
open scoped TensorProduct

section Algebra

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

theorem mem_range_algebraMap_of_surjective_pi {ι : Type*} [Fintype ι]
    (f : (ι → F) →ₐ[F] E) (hf : Function.Surjective f) (e : E) :
    e ∈ Set.range (algebraMap F E) := by
  obtain ⟨y, rfl⟩ := hf e
  have h0 : ∏ i, (y - algebraMap F (ι → F) (y i)) = 0 := by
    funext j
    rw [Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)
  have h1 : ∏ i, (f y - algebraMap F E (y i)) = 0 := by
    simpa [map_prod, map_sub, AlgHom.commutes] using congrArg f h0
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp h1
  exact ⟨y i, (sub_eq_zero.mp hi).symm⟩

theorem finrank_eq_one_of_surjective_pi {ι : Type*} [Fintype ι]
    (f : (ι → F) →ₐ[F] E) (hf : Function.Surjective f) : finrank F E = 1 := by
  rw [← Subalgebra.bot_eq_top_iff_finrank_eq_one]
  exact eq_top_iff.2 fun e _ ↦ Algebra.mem_bot.2 (mem_range_algebraMap_of_surjective_pi f hf e)

def algEquivOfFinrankEqOne (h : finrank F E = 1) : F ≃ₐ[F] E :=
  AlgEquiv.ofBijective (Algebra.ofId F E) (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h)

theorem isFiniteSplit_pi_iff {ι : Type*} [Finite ι] {E : ι → Type*} [∀ i, Field (E i)]
    [∀ i, Algebra F (E i)] :
    Algebra.IsFiniteSplit F (∀ i, E i) ↔ ∀ i, finrank F (E i) = 1 := by
  constructor
  · intro h i
    obtain ⟨n, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun F (∀ i, E i)
    refine finrank_eq_one_of_surjective_pi ((Pi.evalAlgHom F E i).comp e.symm.toAlgHom) ?_
    exact (Function.surjective_eval i).comp e.symm.surjective
  · intro h
    exact .of_algEquiv (AlgEquiv.piCongrRight fun i ↦ algEquivOfFinrankEqOne (h i))

end Algebra

section Finite

open SemiLocal

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]

def SplitsCompletely (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal →
    w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ w.asIdeal.inertiaDeg (𝓞 K) = 1

variable {L} (v : HeightOneSpectrum (𝓞 K))

theorem splitsCompletely_iff_forall_finrank :
    SplitsCompletely L v ↔
      ∀ w : PlacesOver (L := L) v, finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1 := by
  constructor
  · intro h w
    obtain ⟨h1, h2⟩ := h w.1 w.2
    rw [finrank_eq_ramificationIdx_mul_inertiaDeg L v w.1, h1, h2]
  · intro h w hw
    have := h ⟨w, hw⟩
    rw [finrank_eq_ramificationIdx_mul_inertiaDeg L v w] at this
    exact mul_eq_one.mp this

open scoped Valued in
theorem splitsCompletely_iff_isFiniteSplit :
    SplitsCompletely L v ↔
      Algebra.IsFiniteSplit (v.adicCompletion K) (v.adicCompletion K ⊗[K] L) := by
  rw [splitsCompletely_iff_forall_finrank, ← isFiniteSplit_pi_iff]
  let C := (w : PlacesOver (L := L) v) → w.1.adicCompletion L
  let f : v.adicCompletion K ⊗[K] L →ₐ[v.adicCompletion K] C :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) (IsScalarTower.toAlgHom K L _)
      (fun _ _ ↦ Commute.all _ _)
  have hf : Function.Surjective f := by
    have hclosed : IsClosed (LinearMap.range f.toLinearMap : Set C) :=
      Submodule.isClosed_of_finiteDimensional _
    have hdense : DenseRange (algebraMap L C) :=
      denseRange_algebraMap_pi (fun w : PlacesOver (L := L) v ↦ w.1) Subtype.val_injective
    have hdense' : Dense (Set.range f) := hdense.mono (by
      rintro _ ⟨x, rfl⟩
      exact ⟨1 ⊗ₜ x, by simp [f]⟩)
    rw [LinearMap.coe_range] at hclosed
    change IsClosed (Set.range f) at hclosed
    rw [← Set.range_eq_univ, ← hclosed.closure_eq, hdense'.closure_eq]
  have hdim : finrank (v.adicCompletion K) (v.adicCompletion K ⊗[K] L) =
      finrank (v.adicCompletion K) C := by
    dsimp [C]
    rw [Module.finrank_baseChange, Module.finrank_pi_fintype]
    calc
      finrank K L =
          ∑ w : PlacesOver (L := L) v,
            w.1.asIdeal.ramificationIdx (𝓞 K) * w.1.asIdeal.inertiaDeg (𝓞 K) := by
        have := v.isPrime
        rw [IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L,
          ← Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 L)]
        exact (Fintype.sum_equiv (placesOverEquiv (L := L) v) _ _ (fun _ ↦ rfl)).symm
      _ = _ := Finset.sum_congr rfl fun w _ ↦
        (finrank_eq_ramificationIdx_mul_inertiaDeg L v w.1).symm
  have hi : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f.toLinearMap) hdim).2 hf
  have e := AlgEquiv.ofBijective f ⟨hi, hf⟩
  exact ⟨fun h ↦ .of_algEquiv e.symm, fun h ↦ .of_algEquiv e⟩

variable (L) in
theorem nonempty_placesOver : Nonempty (PlacesOver (L := L) v) := by
  have := v.isPrime
  exact (placesOverEquiv (L := L) v).nonempty

theorem finrank_eq_of_isGalois [IsGalois K L] (w w' : PlacesOver (L := L) v) :
    finrank (v.adicCompletion K) (w.1.adicCompletion L) =
      finrank (v.adicCompletion K) (w'.1.adicCompletion L) := by
  obtain ⟨σ, hσ⟩ :=
    Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal w.1.asIdeal w'.1.asIdeal (L ≃ₐ[K] L)
  have hw : w'.1 = σ • w.1 := HeightOneSpectrum.ext hσ.symm
  exact (galEquiv v σ w.1 w'.1 hw).toLinearEquiv.finrank_eq

theorem splitsCompletely_iff_exists_finrank [IsGalois K L] :
    SplitsCompletely L v ↔
      ∃ w : PlacesOver (L := L) v, finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1 := by
  rw [splitsCompletely_iff_forall_finrank]
  refine ⟨fun h ↦ ?_, fun ⟨w, hw⟩ w' ↦ (finrank_eq_of_isGalois v w w').symm.trans hw⟩
  obtain ⟨w⟩ := nonempty_placesOver L v
  exact ⟨w, h w⟩

end Finite

end GroundTheory.Global
end
end
