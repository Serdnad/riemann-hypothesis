module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle006
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.SemistableReduction.Bundle005
public import ReciprocityTheory.SemistableReduction.RestBlockSubstIsMultiHomogeneous
public import ReciprocityTheory.SemistableReduction.Bundle014
import ReciprocityTheory.SemistableReduction.Bundle008
public import ReciprocityTheory.SemistableReduction.Bundle027
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussHeights.GaussGenericHeight.GaussGenericStatements.GaussGenericTheorem.HtGaussGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussHeights.GaussUniqueness.GaussUniquenessStatements.GaussUniquenessTheorem.HtGaussUniq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.UniformizerOfResidueIndep

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.T0

namespace ValPl

open IsDedekindDomain WithZero IsLocalRing

variable {O F L : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L]
  [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]

variable (F) in
theorem resDeg_addv (v : HeightOneSpectrum (integralClosure O L)) :
    letI := resAlg (F := F) (addv L v);
    Module.finrank (ResidueField ((vRing (addv L v)).comap (algebraMap F L)))
      (ResidueField (vRing (addv L v))) = v.asIdeal.inertiaDeg O := by
  classical
  set w := addv L v with hw_def
  letI : Algebra (ResidueField ((vRing w).comap (algebraMap F L))) (ResidueField (vRing w)) :=
    resAlg (F := F) w
  have hunit : ∀ x : vRing w, IsUnit x ↔ w (x : L) = 0 := by
    intro x
    constructor
    · rintro ⟨u, rfl⟩
      have hm : ((u : vRing w) : L) * ((↑u⁻¹ : vRing w) : L) = 1 :=
        congrArg Subtype.val u.mul_inv
      have h1 : w ((u : vRing w) : L) + w ((↑u⁻¹ : vRing w) : L) = 0 := by
        rw [← AddValuation.map_mul, hm, AddValuation.map_one]
      exact wt_add_eq_zero (u : vRing w).2 (↑u⁻¹ : vRing w).2 h1
    · intro h0
      have hx0 : (x : L) ≠ 0 := fun h => by
        rw [h, AddValuation.map_zero] at h0; exact WithTop.top_ne_zero h0
      have hinv : (x : L)⁻¹ ∈ vRing w := by
        show 0 ≤ w (x : L)⁻¹
        have h2 : w (x : L) + w (x : L)⁻¹ = 0 := by
          rw [← AddValuation.map_mul, mul_inv_cancel₀ hx0, AddValuation.map_one]
        rw [h0, zero_add] at h2
        rw [h2]
      exact ⟨⟨x, ⟨_, hinv⟩, Subtype.ext (by simp [mul_inv_cancel₀ hx0]),
        Subtype.ext (by simp [inv_mul_cancel₀ hx0])⟩, rfl⟩
  have hmaxV : ∀ x : vRing w, x ∈ maximalIdeal (vRing w) ↔ 0 < w (x : L) := by
    intro x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit]
    exact ⟨fun h => lt_of_le_of_ne x.2 (Ne.symm h), fun h => h.ne'⟩

  let φB : integralClosure O L →+* vRing w :=
    (algebraMap (integralClosure O L) L).codRestrict (vRing w) (fun b => addv_nonneg v b)
  let ψB : integralClosure O L →+* ResidueField (vRing w) := (residue (vRing w)).comp φB
  have hψB : ∀ b, ψB b = residue (vRing w) (φB b) := fun _ => rfl
  have hkerB : RingHom.ker ψB = v.asIdeal := by
    ext b
    rw [RingHom.mem_ker, hψB, IsLocalRing.residue_eq_zero_iff, hmaxV]
    exact addv_pos_iff v b
  haveI := v.isMaximal
  have hsurjB : Function.Surjective ψB := by
    intro z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    have hxv : v.valuation L (x : L) ≤ 1 := by
      by_cases hx0 : (x : L) = 0
      · rw [hx0, map_zero]; exact zero_le
      have h := x.2
      change 0 ≤ addv L v (x : L) at h
      rw [addv_apply v hx0] at h
      have h' : 0 ≤ -log (v.valuation L (x : L)) := by exact_mod_cast h
      have hne : v.valuation L (x : L) ≠ 0 := by simpa using hx0
      rw [← exp_log hne, ← exp_zero, exp_le_exp]
      omega
    obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v (x : L) hxv
    obtain ⟨d', i, hi, hdi⟩ := Ideal.IsMaximal.exists_inv v.isMaximal d.2
    refine ⟨n * d', ?_⟩
    have hd1 : ψB d * ψB d' = 1 := by
      have : d' * d - 1 ∈ RingHom.ker ψB := by
        rw [hkerB]
        have : d' * d - 1 = -i := by linear_combination hdi
        rw [this]; exact v.asIdeal.neg_mem hi
      rw [RingHom.mem_ker, map_sub, map_mul, map_one, sub_eq_zero] at this
      rw [mul_comm]; exact this
    have hxd : x * φB d = φB n := Subtype.ext (by
      change (x : L) * algebraMap (integralClosure O L) L d = algebraMap (integralClosure O L) L n
      exact hnd)
    have hres := congrArg (residue (vRing w)) hxd
    rw [map_mul] at hres
    rw [map_mul, hψB n, ← hres, mul_assoc, ← hψB, hd1, mul_one]
  let jB : (integralClosure O L ⧸ v.asIdeal) ≃+* ResidueField (vRing w) :=
    (Ideal.quotEquivOfEq hkerB.symm).trans (RingHom.quotientKerEquivOfSurjective hsurjB)

  have hOw : ∀ a : O, algebraMap O F a ∈ (vRing w).comap (algebraMap F L) := fun a => by
    rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact ((addv_mem_placesOver v).2 a).1
  let φO : O →+* (vRing w).comap (algebraMap F L) := (algebraMap O F).codRestrict _ hOw
  let ψO : O →+* ResidueField ((vRing w).comap (algebraMap F L)) := (residue _).comp φO
  have hψO : ∀ a, ψO a = residue _ (φO a) := fun _ => rfl
  have hmaxV0 : ∀ x : (vRing w).comap (algebraMap F L),
      x ∈ maximalIdeal ((vRing w).comap (algebraMap F L)) ↔ 0 < w (algebraMap F L x) := by
    intro x
    have h := hmaxV (comapIncl (vRing w) (algebraMap F L) x)
    have e : ((comapIncl (vRing w) (algebraMap F L) x : vRing w) : L) = algebraMap F L x := rfl
    rw [e] at h
    rw [← h, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff]
    exact ⟨fun hx hu => hx (isUnit_of_map_unit _ _ hu), fun hx hu => hx (hu.map _)⟩
  have hkerO : RingHom.ker ψO = maximalIdeal O := by
    ext a
    rw [RingHom.mem_ker, hψO, IsLocalRing.residue_eq_zero_iff, hmaxV0]
    change 0 < w (algebraMap F L (algebraMap O F a)) ↔ _
    rw [← IsScalarTower.algebraMap_apply]
    exact ((addv_mem_placesOver v).2 a).2
  have hsurjO : Function.Surjective ψO := by
    intro z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    by_cases hx0 : (x : F) = 0
    · refine ⟨0, ?_⟩
      rw [map_zero]
      have : x = 0 := Subtype.ext hx0
      rw [this, map_zero]
    rcases ValuationRing.isInteger_or_isInteger O (x : F) with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨a, by rw [hψO]; congr 1; exact Subtype.ext ha⟩
    · by_cases hau : IsUnit a
      · obtain ⟨u, rfl⟩ := hau
        refine ⟨↑u⁻¹, ?_⟩
        rw [hψO]; congr 1
        apply Subtype.ext
        change algebraMap O F ↑u⁻¹ = (x : F)
        have h1 : algebraMap O F (u : O) * algebraMap O F ↑u⁻¹ = 1 := by
          rw [← map_mul, Units.mul_inv, map_one]
        have h2 : algebraMap O F (u : O) = (x : F)⁻¹ := ha
        rw [h2] at h1
        field_simp at h1
        linear_combination h1
      · exfalso
        have ham : a ∈ maximalIdeal O := hau
        have hpos := (((addv_mem_placesOver v).2 a).2).2 ham
        rw [IsScalarTower.algebraMap_apply O F L, ha, map_inv₀] at hpos
        have hxnn : 0 ≤ w (algebraMap F L (x : F)) := x.2
        have hxL : algebraMap F L (x : F) ≠ 0 := by
          rw [Ne, map_eq_zero_iff _ (algebraMap F L).injective]; exact hx0
        have hs : w (algebraMap F L (x : F)) + w (algebraMap F L (x : F))⁻¹ = 0 := by
          rw [← AddValuation.map_mul, mul_inv_cancel₀ hxL, AddValuation.map_one]
        have := wt_add_eq_zero hxnn hpos.le hs
        rw [this, zero_add] at hs
        rw [hs] at hpos
        exact lt_irrefl _ hpos
  let jO : (O ⧸ maximalIdeal O) ≃+* ResidueField ((vRing w).comap (algebraMap F L)) :=
    (Ideal.quotEquivOfEq hkerO.symm).trans (RingHom.quotientKerEquivOfSurjective hsurjO)
  have hmax : (v.asIdeal.comap (algebraMap O (integralClosure O L))).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := O) v.asIdeal
  haveI : v.asIdeal.LiesOver (maximalIdeal O) := ⟨(IsLocalRing.eq_maximalIdeal hmax).symm⟩
  have hc : (algebraMap (ResidueField ((vRing w).comap (algebraMap F L)))
      (ResidueField (vRing w))).comp jO.toRingHom =
      jB.toRingHom.comp (algebraMap (O ⧸ maximalIdeal O) (integralClosure O L ⧸ v.asIdeal)) := by
    apply Ideal.Quotient.ringHom_ext
    ext a
    simp only [RingHom.comp_apply, Ideal.Quotient.algebraMap_mk_of_liesOver]
    change ResidueField.map (comapIncl (vRing w) (algebraMap F L)) (jO _) = jB _
    simp only [jO, jB, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk, hψO, hψB, ResidueField.map_residue]
    congr 1
    apply Subtype.ext
    change algebraMap F L (algebraMap O F a) = algebraMap (integralClosure O L) L (algebraMap O _ a)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal O) v.asIdeal]
  exact (Algebra.finrank_eq_of_equiv_equiv jO jB hc).symm

end ValPl

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem ae_evT_ne_zero (sg : K →+* ℂ) (q : KTp K d.D d.N) (hq : q ≠ 0) (m : Fin (d.D + 1) → ℕ)
    (hm : m 0 = 0) (hqm : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m q) :
    ∀ᵐ z ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)), d.evT sg 0 (d.tOf z) q ≠ 0 := by
  classical
  have hnpos : 0 < d.N + 1 := Nat.succ_pos _
  have hqm' : ∀ s ∈ q.support, ∀ b, ∑ j, s (b, j) = m b := hqm

  let ψ : Fin d.D × Fin (d.N + 1) → TVar d.D d.N := fun p => (p.1.succ, p.2)
  have hψ : Function.Injective ψ := by
    intro p p' h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    exact Prod.ext (Fin.succ_injective _ h1) h2
  have hvars : (q.vars : Set (TVar d.D d.N)) ⊆ Set.range ψ := by
    intro v hv
    rcases v with ⟨i, j⟩
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
    · exfalso
      obtain ⟨s, hs, hsv⟩ := (MvPolynomial.mem_vars_iff_mem_support _).1 (Finset.mem_coe.1 hv)
      have h0 := hqm' s hs 0
      rw [hm] at h0
      have hz : s ((0 : Fin (d.D + 1)), j) = 0 :=
        (Finset.sum_eq_zero_iff.1 h0) j (Finset.mem_univ j)
      exact (Finsupp.mem_support_iff.1 hsv) hz
    · exact ⟨(k, j), rfl⟩
  obtain ⟨q', hq'⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range q ψ hψ hvars
  obtain ⟨g, hgdef⟩ : ∃ g : MvPolynomial (Fin d.D × Fin (d.N + 1)) ℂ,
      g = MvPolynomial.map sg q' := ⟨_, rfl⟩

  have hev : ∀ z, d.evT sg 0 (d.tOf z) q = MvPolynomial.eval (ReciprocityTheory.MultiplicativeHeights.blockPoint z) g := by
    intro z
    rw [hgdef, MvPolynomial.eval_map, ← hq']
    unfold ReciprocityTheory.ChartRestriction.G.T0.Data.evT
    rw [MvPolynomial.eval₂_rename]
    congr 1

  have hg : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun b : Fin d.D => m b.succ) g := by
    unfold ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous
    intro s hs b
    have hs' : AddMonoidAlgebra.coeff q' s ≠ 0 := by
      rw [hgdef, MvPolynomial.mem_support_iff, MvPolynomial.coeff_map] at hs
      intro h0
      rw [h0, map_zero] at hs
      exact hs rfl
    have hmem : Finsupp.mapDomain ψ s ∈ q.support := by
      rw [MvPolynomial.mem_support_iff, ← hq', MvPolynomial.coeff_rename_mapDomain ψ hψ]
      exact hs'
    exact (Finset.sum_congr rfl fun j _ => (Finsupp.mapDomain_apply_of_injective hψ s (b, j)).symm).trans
      (hqm' _ hmem b.succ)

  have hg0 : g ≠ 0 := by
    rw [hgdef]
    intro h
    apply hq
    rw [← hq']
    have h' : q' = 0 := MvPolynomial.map_injective (f := sg) sg.injective (by rw [h, map_zero])
    rw [h', map_zero]

  obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.1 hg0
  obtain ⟨z, hz1, hzle⟩ := ReciprocityTheory.MultiplicativeHeights.exists_torus_coeff_le g s
  have hz0 : MvPolynomial.eval z g ≠ 0 := by
    intro h
    rw [h, norm_zero] at hzle
    exact hs (norm_le_zero_iff.1 hzle)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (Real.sqrt ((d.N + 1 : ℕ) : ℝ))⁻¹ := ⟨_, rfl⟩
  have hrpos : 0 < r := by
    rw [hr]
    exact inv_pos.2 (Real.sqrt_pos.2 (Nat.cast_pos.2 hnpos))
  have hvec : ∀ b : Fin d.D, (WithLp.toLp 2 (fun j : Fin (d.N + 1) => (r : ℂ) * z (b, j)) :
      EuclideanSpace ℂ (Fin (d.N + 1))) ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1 := by
    intro b
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq]
    have hterm : ∀ j : Fin (d.N + 1), ‖(WithLp.toLp 2 (fun j : Fin (d.N + 1) => (r : ℂ) * z (b, j)) :
        EuclideanSpace ℂ (Fin (d.N + 1))) j‖ ^ 2 = r ^ 2 := by
      intro j
      show ‖(r : ℂ) * z (b, j)‖ ^ 2 = r ^ 2
      rw [norm_mul, hz1, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hr, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _),
      mul_inv_cancel₀ (Nat.cast_pos.2 hnpos).ne', Real.sqrt_one]
  let u : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) := fun b => ⟨_, hvec b⟩
  have hu : MvPolynomial.eval (ReciprocityTheory.MultiplicativeHeights.blockPoint u) g ≠ 0 := by
    have hbp : ReciprocityTheory.MultiplicativeHeights.blockPoint u = fun p => (r : ℂ) * z p := by
      funext p
      rfl
    rw [hbp, ReciprocityTheory.MultiplicativeHeights.eval_mul_of_isMultiHomogeneous hg]
    exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.2 hrpos.ne')) hz0

  have key := ReciprocityTheory.MultiplicativeHeights.null_of_logBound hnpos ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable
    (ReciprocityTheory.MultiplicativeHeights.blockSphere_logMean_bound ReciprocityTheory.MultiplicativeHeights.Closed.sj ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable
      hnpos d.D) _ g u hg hu
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ key
  intro w hw
  simp only [Set.mem_setOf_eq, not_not] at hw ⊢
  rw [← hev w]
  exact hw

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed

section

variable {K : Type} [Field K] [NumberField K] {κ : Type} [Fintype κ]

theorem map_ne_zero_of_ne_zero {f : MvPolynomial κ K} (hf : f ≠ 0) (σ : K →+* ℂ) :
    MvPolynomial.map σ f ≠ 0 := fun h => hf ((MvPolynomial.map_injective σ σ.injective) (by rw [h, map_zero]))

end

theorem logHeight_le_torusHeight {K : Type} [Field K] [NumberField K] {B n : ℕ} (hn : 0 < n) (a : Fin B → ℕ)
    (f : MvPolynomial (Fin B × Fin n) K) (hf : f ≠ 0) (ha : IsMultiHomogeneous a f) :
    h0 f ≤ hTX5 f := by
  unfold h0 hTX5
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  refine add_le_add le_rfl (Finset.sum_le_sum fun σ _ => ?_)
  exact sphereLeTorus B n a _ hn (map_ne_zero_of_ne_zero hf σ) (isMultiHomogeneous_map_ring a f ha σ)

theorem continuous_torusPoint' {κ : Type} : Continuous (fun θ : κ → ℝ => torusPoint θ) := by
  unfold torusPoint
  exact continuous_pi fun i => Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply i)))

theorem measurable_log_eval_torus {κ : Type} [Fintype κ] (f : MvPolynomial κ ℂ) :
    Measurable (fun θ : κ → ℝ => Real.log ‖MvPolynomial.eval (torusPoint θ) f‖) := (Real.measurable_log.comp (continuous_norm.comp ((MvPolynomial.continuous_eval f).comp continuous_torusPoint')).measurable)

theorem torusProb_map_comp {κ κ' : Type} [Fintype κ] [Fintype κ'] (e : κ → κ')
    (he : Function.Injective e) :
    Measure.map (fun θ : κ' → ℝ => θ ∘ e) (torusProb κ') = torusProb κ := by
  classical
  have hmeas : Measurable (fun θ : κ' → ℝ => θ ∘ e) :=
    Measurable.of_eval (fun a => measurable_pi_apply (e a))
  unfold torusProb
  symm
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun θ : κ' → ℝ => θ ∘ e) ⁻¹' Set.univ.pi s =
      Set.univ.pi (Function.extend e s (fun _ => Set.univ)) := by
    ext θ
    simp only [Set.mem_preimage, Set.mem_univ_pi, Function.comp_apply]
    constructor
    · intro h y
      by_cases hy : ∃ a, e a = y
      · obtain ⟨a, rfl⟩ := hy
        rw [he.extend_apply]
        exact h a
      · rw [Function.extend_apply' _ _ _ hy]
        trivial
    · intro h a
      have h1 := h (e a)
      rwa [he.extend_apply] at h1
  rw [hpre, Measure.pi_pi]
  set ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hν : ν Set.univ = 1 := by simp [ν]
  calc ∏ y, ν (Function.extend e s (fun _ => Set.univ) y)
      = ∏ y ∈ Finset.univ.image e, ν (Function.extend e s (fun _ => Set.univ) y) := by
        refine (Finset.prod_subset (Finset.subset_univ _) (fun y _ hy => ?_)).symm
        have hy' : ¬ ∃ a, e a = y := by simpa using hy
        rw [Function.extend_apply' _ _ _ hy', hν]
    _ = ∏ a, ν (s a) := by
        rw [Finset.prod_image (fun a _ b _ h => he h)]
        refine Finset.prod_congr rfl (fun a _ => ?_)
        rw [he.extend_apply]

theorem torusMean_rename {κ κ' : Type} [Fintype κ] [Fintype κ'] (e : κ → κ')
    (he : Function.Injective e) (f : MvPolynomial κ ℂ) :
    torusMean (MvPolynomial.rename e f) = torusMean f := by
  unfold torusMean
  simp_rw [MvPolynomial.eval_rename]
  rw [← torusProb_map_comp e he, MeasureTheory.integral_map]
  · rfl
  · exact (Measurable.of_eval fun i => measurable_pi_apply (e i)).aemeasurable
  · exact (measurable_log_eval_torus f).aestronglyMeasurable

theorem gaussAbs_rename_of_injective {K : Type} [Field K] [NumberField K] {κ κ' : Type} (e : κ → κ')
    (he : Function.Injective e) (w : FinitePlace K) (f : MvPolynomial κ K) :
    gaussAbs w (MvPolynomial.rename e f) = gaussAbs w f := by
  classical
  unfold gaussAbs
  rw [MvPolynomial.support_rename_of_injective he, Finset.sup_image]
  congr 1
  refine Finset.sup_congr rfl fun s _ => ?_
  simp only [Function.comp_apply, MvPolynomial.coeff_rename_mapDomain e he]

theorem hTX5_rename {K : Type} [Field K] [NumberField K] {κ κ' : Type} [Fintype κ] [Fintype κ']
    (e : κ → κ') (he : Function.Injective e) (f : MvPolynomial κ K) :
    hTX5 (MvPolynomial.rename e f) = hTX5 f := by
  unfold hTX5
  congr 2
  · exact finsum_congr fun w => by rw [gaussAbs_rename_of_injective e he w f]
  · refine Finset.sum_congr rfl fun σ _ => ?_
    rw [MvPolynomial.map_rename, torusMean_rename e he]

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem AdmissibleValuationPrimeUnique (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    ∀ v : AddValuation (Ω c) (WithTop ℤ), d.admitted c v → IsTrivOn K v →
      {p | p ∈ d.HtOne ∧ ∃ w ∈ d.GoodP c p, d.Wres c w = v}.Subsingleton :=
  HtGaussUniq 𝒜 d hd h c

theorem GeneratorMultiHomogeneous (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    ∀ p ∈ d.HtOne, (∃ w, w ∈ d.GoodP c p) →
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun b : Fin (d.D + 1) => if b = 0 then 0 else d.dg (d.gen p))
        (d.gen p) :=
  HtGaussGen 𝒜 d (Data.PlaceTrivialOrPositive (𝒜 := 𝒜) d) (Data.AdmissibleValuationPrimeUnique (𝒜 := 𝒜) d) hd h c

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
