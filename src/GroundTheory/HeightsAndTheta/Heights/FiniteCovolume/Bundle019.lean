module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle011
import GroundTheory.AutomorphicForms.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Examples
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
import Mathlib.Data.Finset.Functor
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

theorem exists_finset_of_finite_image {α β : Type*} (s : Set α) (f : α → β) (hf : (f '' s).Finite)
    (P : α → α → Prop) (hP : ∀ x ∈ s, ∀ y ∈ s, f x = f y → P y x) :
    ∃ S : Finset α, (S : Set α) ⊆ s ∧ ∀ x ∈ s, ∃ y ∈ S, P y x := by
  classical
  rcases isEmpty_or_nonempty α with hα | hα
  · exact ⟨∅, by simp, fun x _ => isEmptyElim x⟩
  choose! g hg1 hg2 using fun b (hb : b ∈ f '' s) => hb
  refine ⟨hf.toFinset.image g, ?_, fun x hx => ?_⟩
  · intro y hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
    exact hg1 b (hf.mem_toFinset.1 hb)
  · have hb : f x ∈ f '' s := ⟨x, hx, rfl⟩
    exact ⟨g (f x), Finset.mem_image_of_mem _ (hf.mem_toFinset.2 hb),
      hP x hx _ (hg1 _ hb) (hg2 _ hb).symm⟩

section Vectors

variable {E : Type*} [Field E] [NumberField E] {W : Type*} [AddCommGroup W] [Module E W]

omit [NumberField E] in
theorem mem_ringMultiples {x y : W} : y ∈ ringMultiples E x ↔ ∃ a : 𝓞 E, (a : E) • x = y := by
  simp [ringMultiples]

theorem exists_unit_of_ringMultiples_eq {x b : W} (hb : b ≠ 0)
    (hxb : ringMultiples E x = ringMultiples E b) : ∃ ε : (𝓞 E)ˣ, x = ((ε : 𝓞 E) : E) • b := by
  have hx : x ∈ ringMultiples E b := hxb ▸ mem_ringMultiples.2 ⟨1, by simp⟩
  have hbx : b ∈ ringMultiples E x := hxb ▸ mem_ringMultiples.2 ⟨1, by simp⟩
  obtain ⟨a, ha⟩ := mem_ringMultiples.1 hx
  obtain ⟨c, hc⟩ := mem_ringMultiples.1 hbx
  have h1 : ((c : E) * (a : E)) • b = (1 : E) • b := by rw [mul_smul, ha, hc, one_smul]
  have hca : c * a = 1 := RingOfIntegers.ext (by simpa using smul_left_injective E hb h1)
  exact ⟨⟨a, c, by rw [mul_comm]; exact hca, hca⟩, ha.symm⟩

end Vectors

section Spaces

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W]

omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem unitary_smul_smul {h : HermitianForm F E W} (γ : h.unitaryGroup) (c : E) (w : W) :
    γ • (c • w) = c • (γ • w) := by
  simp only [Subgroup.smul_def, LinearEquiv.smul_def, map_smul]

theorem line_vectorOrbits (h : HermitianForm F E W) (h₂ : IsotropicScaling.Statement h)
    (h₃ : BoundedIndexSubgroupsFinite.Statement W) (h₅ : LineIndexNeZero.Statement E W)
    {D : ℕ} {La : AddSubgroup W} {VV : Set W} (hLa : IsDIntegral h D La) (hsub : VV ⊆ La)
    (hiso : ∀ x ∈ VV, x ≠ 0 ∧ h.toSesq x x = 0) {C : ℕ} (hC : ∀ x ∈ VV, lineIndex E La x ≤ C)
    {v₀ : W} (hv₀ : v₀ ∈ VV) :
    ∃ S : Finset W, (S : Set W) ⊆ VV ∧ ∀ x ∈ VV, x ∈ Submodule.span E {v₀} →
      ∃ y ∈ S, ∃ γ ∈ latticeStab h La, γ • y = x := by
  classical
  obtain ⟨N, hN, hγ⟩ := h₂ La v₀ hLa.isLattice hLa.integral (hsub hv₀) (hiso v₀ hv₀).1
    (hiso v₀ hv₀).2
  have hUfin : Finite ((𝓞 E)ˣ ⧸ congruenceUnits E N) := by
    have : (congruenceUnits E N).FiniteIndex := ⟨CongruenceUnitsFiniteIndex.proof E N hN⟩
    exact Subgroup.finite_quotient_of_finiteIndex
  let L : Set W := {x ∈ VV | x ∈ Submodule.span E {v₀}}
  have hspan : ∀ x ∈ L, Submodule.span E {x} = Submodule.span E {v₀} := by
    rintro x ⟨hx, hxs⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hxs
    have hc : c ≠ 0 := by
      rintro rfl
      exact (hiso _ hx).1 (zero_smul E v₀)
    exact Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc) v₀
  have hT : ∀ x ∈ L, ringMultiples E x ∈ {H : AddSubgroup W |
      H ≤ La ⊓ (Submodule.span E {v₀}).toAddSubgroup ∧
      H.relIndex (La ⊓ (Submodule.span E {v₀}).toAddSubgroup) ≠ 0 ∧
      H.relIndex (La ⊓ (Submodule.span E {v₀}).toAddSubgroup) ≤ C} := by
    intro x hxL
    have h1 := h₅ La x hLa.isLattice (hsub hxL.1) (hiso x hxL.1).1
    have h2 := hC x hxL.1
    unfold lineIndex at h1 h2
    rw [hspan x hxL] at h1 h2
    refine ⟨fun y hy => ?_, h1, h2⟩
    obtain ⟨a, rfl⟩ := mem_ringMultiples.1 hy
    exact ⟨hLa.isLattice.smul_mem a x (hsub hxL.1), Submodule.smul_mem _ _ hxL.2⟩
  have hTfin := h₃ (La ⊓ (Submodule.span E {v₀}).toAddSubgroup) La hLa.isLattice.fg inf_le_left C
  choose! b hbL hb using fun H (hH : H ∈ (fun x => ringMultiples E x) '' L) => hH
  have hunit : ∀ x ∈ L, ∃ ε : (𝓞 E)ˣ, x = ((ε : 𝓞 E) : E) • b (ringMultiples E x) := by
    intro x hx
    have hH : ringMultiples E x ∈ (fun x => ringMultiples E x) '' L := ⟨x, hx, rfl⟩
    exact exists_unit_of_ringMultiples_eq (hiso _ (hbL _ hH).1).1 (hb _ hH).symm
  choose! ε hε using hunit
  let f : W → AddSubgroup W × ((𝓞 E)ˣ ⧸ congruenceUnits E N) :=
    fun x => (ringMultiples E x, QuotientGroup.mk (ε x))
  have hfin : (f '' L).Finite :=
    (hTfin.prod Set.finite_univ).subset (by rintro _ ⟨x, hx, rfl⟩; exact ⟨hT x hx, trivial⟩)
  have hP : ∀ x ∈ L, ∀ y ∈ L, f x = f y → ∃ γ ∈ latticeStab h La, γ • y = x := by
    intro x hx y hy hxy
    simp only [f, Prod.mk.injEq] at hxy
    obtain ⟨hR, hQ⟩ := hxy
    rw [QuotientGroup.eq] at hQ
    have hδ : (ε y)⁻¹ * ε x ∈ congruenceUnits E N := by
      have := inv_mem hQ
      rwa [mul_inv_rev, inv_inv] at this
    obtain ⟨γ, hγS, hγv⟩ := hγ _ hδ
    refine ⟨γ, hγS, ?_⟩
    have hx' := hε x hx
    have hy' := hε y hy
    rw [hR] at hx'
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hy.2
    have key : (((ε y)⁻¹ * ε x : (𝓞 E)ˣ) : 𝓞 E) * ((ε y : 𝓞 E)) = (ε x : 𝓞 E) := by
      rw [← Units.val_mul, mul_comm, mul_inv_cancel_left]
    have keyE : ((((ε y)⁻¹ * ε x : (𝓞 E)ˣ) : 𝓞 E) : E) * ((ε y : 𝓞 E) : E) = ((ε x : 𝓞 E) : E) := by
      rw [← key]
      rfl
    rw [← hc, unitary_smul_smul, hγv, smul_smul, mul_comm, ← smul_smul, hc,
      congrArg (fun t => ((((ε y)⁻¹ * ε x : (𝓞 E)ˣ) : 𝓞 E) : E) • t) hy', smul_smul, keyE, ← hx']
  obtain ⟨S, hS, hcov⟩ := exists_finset_of_finite_image L f hfin
    (fun y x => ∃ γ ∈ latticeStab h La, γ • y = x) hP
  exact ⟨S, hS.trans fun x hx => hx.1, fun x hx hxs => hcov x ⟨hx, hxs⟩⟩

theorem VectorOrbitsFinite.proof (h : HermitianForm F E W) [FiniteDimensional E W]
    (h₁ : LinePairOrbitsFinite.Statement h) (h₂ : IsotropicScaling.Statement h)
    (h₃ : BoundedIndexSubgroupsFinite.Statement W) (h₅ : LineIndexNeZero.Statement E W) :
    VectorOrbitsFinite.Statement h := by
  classical
  intro D La VV hLa hsub hiso hst ⟨C, hC⟩
  obtain ⟨Sp, hSp, hcov⟩ := h₁ D
  have hline : ∀ x ∈ VV, ∃ p ∈ Sp, ∃ g : h.unitaryGroup, g • p.1 = La ∧
      p.2.map ((g : W ≃ₗ[E] W) : W →ₗ[E] W) = Submodule.span E {x} := by
    intro x hx
    refine hcov La _ hLa ⟨finrank_span_singleton (hiso x hx).1, fun a ha c hc => ?_⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hc
    rw [h.toSesq.map_smulₛₗ a x, LinearMap.smul_apply, map_smul, (hiso x hx).2, smul_zero,
      smul_zero]
  choose! pf hpf gf hgf using hline
  have hfin : (pf '' VV).Finite := hSp.subset (by rintro _ ⟨x, hx, rfl⟩; exact hpf x hx)
  choose! rr hrr1 hrr2 using fun p (hp : p ∈ pf '' VV) => hp
  have hlines : ∀ p ∈ pf '' VV, ∃ S : Finset W, (S : Set W) ⊆ VV ∧ ∀ x ∈ VV,
      x ∈ Submodule.span E {rr p} → ∃ y ∈ S, ∃ γ ∈ latticeStab h La, γ • y = x :=
    fun p hp => line_vectorOrbits h h₂ h₃ h₅ hLa hsub hiso hC (hrr1 p hp)
  choose! Sl hSl1 hSl2 using hlines
  refine ⟨hfin.toFinset.biUnion Sl, ?_, fun x hx => ?_⟩
  · intro y hy
    obtain ⟨p, hp, hyp⟩ := Finset.mem_biUnion.1 hy
    exact hSl1 p (hfin.mem_toFinset.1 hp) hyp
  have hp : pf x ∈ pf '' VV := ⟨x, hx, rfl⟩
  set r := rr (pf x) with hr
  have hr1 : r ∈ VV := hrr1 _ hp
  have hr2 : pf r = pf x := hrr2 _ hp
  set γ₀ := gf r * (gf x)⁻¹ with hγ₀def
  have hγ₀ : γ₀ ∈ latticeStab h La := by
    refine MulAction.mem_stabilizer_iff.2 ?_
    rw [hγ₀def, mul_smul, inv_smul_eq_iff.2 (hgf x hx).1.symm, ← hr2]
    exact (hgf r hr1).1
  have hxm : x ∈ (pf x).2.map ((gf x : W ≃ₗ[E] W) : W →ₗ[E] W) := by
    rw [(hgf x hx).2]
    exact Submodule.mem_span_singleton_self x
  obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.1 hxm
  have hzx' : gf x • z = x := hzx
  have hγ₀x : γ₀ • x ∈ Submodule.span E {r} := by
    rw [hγ₀def, mul_smul, inv_smul_eq_iff.2 hzx'.symm, ← (hgf r hr1).2, hr2]
    exact Submodule.mem_map_of_mem hz
  obtain ⟨y, hy, γ, hγ, hγy⟩ := hSl2 _ hp _ (hst γ₀ hγ₀ x hx) hγ₀x
  refine ⟨y, Finset.mem_biUnion.2 ⟨pf x, hfin.mem_toFinset.2 hp, hy⟩, γ₀⁻¹ * γ,
    mul_mem (inv_mem hγ₀) hγ, ?_⟩
  rw [mul_smul, hγy, inv_smul_smul]

end Spaces

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_len_invApply {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (y : InfinitePlace E → ι → ℂ) : Continuous fun g : archUnitary h v => M.len (invApply g y) := by
  have hw : ∀ w, Continuous fun g : archUnitary h v => invApply g y w := fun w =>
    (Units.continuous_val.comp ((continuous_apply w).comp
      (continuous_subtype_val.comp continuous_inv))).matrix_mulVec continuous_const
  refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun w _ => Complex.continuous_re.comp ?_)
  exact (hw w).star.dotProduct (continuous_const.matrix_mulVec (hw w))

theorem ArithmeticCovolumeFinite.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : ScalingLaw.Statement h v) (h₂ : MahlerCompactness.Statement h v)
    (h₃ : ShortVectorIsotropic.Statement h v) (h₄ : ShortestVectorIndex.Statement h v)
    (h₅ : IntegralFamilyBound.Statement E) (h₆ : MajorantExists.Statement h v)
    (h₈ : ArchLatticeDiscrete.Statement h v) (h₉ : LatticePointsBelowFinite.Statement h v) :
    ArithmeticCovolumeFinite.Statement h v := by
  classical
  intro μ _ D La hLa
  obtain ⟨M⟩ := h₆

  obtain ⟨r, a, ha, har⟩ := h₅
  have hdeg : finrank ℚ E = 2 * finrank ℚ F := by
    rw [← Module.finrank_mul_finrank ℚ F E, Algebra.IsQuadraticExtension.finrank_eq_two F E,
      mul_comm]
  have ha' : ∃ b : Fin (2 * finrank ℚ F) → 𝓞 E, LinearIndependent ℚ (fun i => (b i : E)) ∧
      ∀ i (σ : E →+* ℂ), ‖σ (b i)‖ ≤ r :=
    ⟨a ∘ Fin.cast hdeg.symm, ha.comp _ (Fin.cast_injective _), fun i σ => har _ σ⟩
  set C₀ : ℕ := ⌊(r * Real.sqrt (2 * finrank ℚ F)) ^ (2 * finrank ℚ F)⌋₊ with hC₀

  set VV : Set W := {x | x ∈ La ∧ x ≠ 0 ∧ h.toSesq x x = 0 ∧ lineIndex E La x ≤ C₀} with hVV
  have hstable : ∀ γ ∈ latticeStab h La, ∀ x ∈ VV, γ • x ∈ VV := by
    intro γ hγ x hx
    have hγ' : γ • La = La := MulAction.mem_stabilizer_iff.1 hγ
    refine ⟨?_, fun h0 => hx.2.1 ((smul_eq_zero_iff_eq γ).1 h0), ?_, ?_⟩
    · have h1 : γ • x ∈ γ • La := AddSubgroup.smul_mem_pointwise_smul _ _ _ hx.1
      rwa [hγ'] at h1
    · rw [← hx.2.2.1]
      exact HermitianForm.mem_unitaryGroup.1 γ.2 x x
    · rw [GaussianPlane.lineIndex_smul hγ']
      exact hx.2.2.2
  obtain ⟨FD, hFD, hm⟩ := h₁ M μ D La VV hLa (fun x hx => hx.1) (fun x hx => ⟨hx.2.1, hx.2.2.1⟩)
    hstable ⟨C₀, fun x hx => hx.2.2.2⟩
  refine ⟨FD, hFD, ?_⟩

  set B : Set (archUnitary h v) :=
    ⋃ x : W, ⋃ (_ : x ∈ La ∧ x ≠ 0), {g | M.len (invApply g (vecAt v x)) < 1} with hB
  have hBmeas : MeasurableSet B :=
    (isOpen_iUnion fun x => isOpen_iUnion fun _ =>
      isOpen_lt (continuous_len_invApply M _) continuous_const).measurableSet
  have hBle : μ (FD ∩ B) ≤ massBelow M μ FD VV 1 := by
    rw [Set.inter_comm, ← Measure.restrict_apply hBmeas, ← lintegral_indicator_one hBmeas]
    refine lintegral_mono fun g => ?_
    by_cases hg : g ∈ B
    · rw [Set.indicator_of_mem hg, Pi.one_apply]
      obtain ⟨x₁, hx₁⟩ := Set.mem_iUnion.1 hg
      obtain ⟨⟨hx₁La, hx₁0⟩, hx₁lt⟩ := Set.mem_iUnion.1 hx₁
      set S : Set W := {x | x ∈ La ∧ M.len (invApply g (vecAt v x)) < 1} ∩ {x | x ≠ 0}
      have hSfin : S.Finite := (h₉ M La g 1 hLa.isLattice).inter_of_left _
      obtain ⟨x, hxS, hxmin⟩ := Set.exists_min_image S (fun x => M.len (invApply g (vecAt v x)))
        hSfin ⟨x₁, ⟨hx₁La, hx₁lt⟩, hx₁0⟩
      obtain ⟨⟨hxLa, hxlt⟩, hx0⟩ := hxS
      have hshort : ∀ y ∈ La, y ≠ 0 →
          M.len (invApply g (vecAt v x)) ≤ M.len (invApply g (vecAt v y)) := by
        intro y hy hy0
        by_cases hylt : M.len (invApply g (vecAt v y)) < 1
        · exact hxmin y ⟨⟨hy, hylt⟩, hy0⟩
        · exact hxlt.le.trans (not_lt.1 hylt)
      have hxVV : x ∈ VV := by
        refine ⟨hxLa, hx0, h₃ M D La g x hLa hxLa hxlt, ?_⟩
        exact Nat.le_floor (h₄ M r ha' D La g x hLa hxLa hx0 hshort)
      have hne : ({y ∈ VV | M.len (invApply g (vecAt v y)) < 1}).Nonempty := ⟨x, hxVV, hxlt⟩
      unfold countBelow
      rw [← ENat.toENNReal_one, ENat.toENNReal_le]
      exact Set.one_le_encard_iff_nonempty.2 hne
    · rw [Set.indicator_of_notMem hg]
      exact bot_le

  obtain ⟨S, hS, K, hK, hMah⟩ := h₂ M D 1 one_pos
  have : DiscreteTopology (archLatticeGroup h v La) := h₈ La hLa.isLattice
  have : Countable (archLatticeGroup h v La) :=
    TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  let c : AddSubgroup W → h.unitaryGroup := fun L =>
    if hL : ∃ γ : h.unitaryGroup, γ • La = L then hL.choose else 1
  set K' : Set (archUnitary h v) :=
    ⋃ L ∈ S, (fun k => (archEmbed h v (c L))⁻¹ * k) '' K with hK'
  have hK'c : IsCompact K' :=
    hS.isCompact_biUnion fun L _ => hK.image (continuous_const.mul continuous_id)
  have hcover : FD ∩ Bᶜ ⊆ ⋃ δ : archLatticeGroup h v La, δ • K' ∩ FD := by
    rintro g ⟨hgFD, hgB⟩
    have hlam : ∀ x ∈ La, x ≠ 0 → (1 : ℝ) ≤ M.len (invApply g (vecAt v x)) := by
      intro x hx hx0
      by_contra hlt
      exact hgB (Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨⟨hx, hx0⟩, not_le.1 hlt⟩⟩)
    obtain ⟨γ, hγS, hγK⟩ := hMah La g hLa hlam
    have hL : ∃ γ' : h.unitaryGroup, γ' • La = γ • La := ⟨γ, rfl⟩
    have hcL : c (γ • La) • La = γ • La := by
      simp only [c, dif_pos hL]
      exact hL.choose_spec
    have hstab : γ⁻¹ * c (γ • La) ∈ latticeStab h La := by
      change (γ⁻¹ * c (γ • La)) • La = La
      rw [mul_smul, hcL, inv_smul_smul]
    refine Set.mem_iUnion.2 ⟨⟨archEmbed h v (γ⁻¹ * c (γ • La)), Subgroup.mem_map_of_mem _ hstab⟩,
      ?_, hgFD⟩
    refine Set.mem_smul_set.2 ⟨(archEmbed h v (c (γ • La)))⁻¹ * (archEmbed h v γ * g),
      Set.mem_biUnion hγS ⟨_, hγK, rfl⟩, ?_⟩
    rw [Subgroup.smul_def, smul_eq_mul]
    simp only [map_mul, map_inv]
    group
  have hAlt : μ (FD ∩ Bᶜ) < ⊤ := by
    calc μ (FD ∩ Bᶜ) ≤ μ (⋃ δ : archLatticeGroup h v La, δ • K' ∩ FD) := measure_mono hcover
      _ ≤ ∑' δ : archLatticeGroup h v La, μ (δ • K' ∩ FD) := measure_iUnion_le _
      _ = μ K' := (hFD.measure_eq_tsum K').symm
      _ < ⊤ := hK'c.measure_lt_top
  calc μ FD = μ ((FD ∩ B) ∪ (FD ∩ Bᶜ)) := by rw [Set.inter_union_compl]
    _ ≤ μ (FD ∩ B) + μ (FD ∩ Bᶜ) := measure_union_le _ _
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hBle.trans_lt (hm 1 one_pos).1, hAlt⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory
open scoped ENNReal Pointwise

variable (G : Type*) [Group G]

theorem UnfoldOrbit.bijective_mul_out_inv {Γ Γ₀ : Subgroup G} (hle : Γ₀ ≤ Γ) :
    Function.Bijective (fun p : (Γ ⧸ Γ₀.subgroupOf Γ) × Γ₀ =>
      (⟨(p.2 : G) * ((Quotient.out p.1 : Γ) : G)⁻¹,
        Γ.mul_mem (hle p.2.2) (Γ.inv_mem (Quotient.out p.1).2)⟩ : Γ)) := by
  constructor
  · rintro ⟨q, h⟩ ⟨q', h'⟩ heq
    simp only [Subtype.mk.injEq] at heq
    have hmem : (Quotient.out q' : Γ)⁻¹ * Quotient.out q ∈ Γ₀.subgroupOf Γ := by
      rw [Subgroup.mem_subgroupOf]
      have key : (((Quotient.out q' : Γ)⁻¹ * Quotient.out q : Γ) : G) = (h' : G)⁻¹ * h := by
        rw [show (h' : G)⁻¹ * h = (h' : G)⁻¹ * ((h : G) * ((Quotient.out q : Γ) : G)⁻¹) *
          ((Quotient.out q : Γ) : G) by group, heq]
        push_cast
        group
      rw [key]
      exact Γ₀.mul_mem (Γ₀.inv_mem h'.2) h.2
    have hq : q' = q := by
      rw [← QuotientGroup.out_eq' q', ← QuotientGroup.out_eq' q]
      exact QuotientGroup.eq.2 hmem
    subst hq
    have hh : h = h' := Subtype.ext (mul_right_cancel heq)
    rw [hh]
  · intro γ
    have hmem := QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk γ⁻¹ :
      Γ ⧸ Γ₀.subgroupOf Γ)).symm
    rw [Subgroup.mem_subgroupOf] at hmem
    refine ⟨⟨QuotientGroup.mk γ⁻¹, ⟨_, hmem⟩⟩, ?_⟩
    apply Subtype.ext
    simp

theorem UnfoldOrbit.proof [MeasurableSpace G] [MeasurableMul G] : UnfoldOrbit.Statement G := by
  intro μ _ Γ Γ₀ _ hle FD FD₀ hFD hFD₀ φ hφ hinv
  have : Countable Γ₀ := (Subgroup.inclusion_injective hle).countable
  have : Countable (Γ ⧸ Γ₀.subgroupOf Γ) := QuotientGroup.mk_surjective.countable
  rw [lintegral_tsum (f := fun (q : Γ ⧸ Γ₀.subgroupOf Γ) g => φ (((Quotient.out q : Γ) : G)⁻¹ * g))
      fun q => (hφ.comp (measurable_const_mul _)).aemeasurable,
    hFD.setLIntegral_eq_tsum φ FD₀,
    ← (Equiv.ofBijective _ (UnfoldOrbit.bijective_mul_out_inv G hle)).tsum_eq,
    ENNReal.tsum_prod']
  refine tsum_congr fun q => ?_
  have h1 : ∫⁻ g in FD, φ (((Quotient.out q : Γ) : G)⁻¹ * g) ∂μ =
      ∫⁻ x in ((Quotient.out q : Γ) : G)⁻¹ • FD, φ x ∂μ := by
    rw [← Set.image_smul]
    exact (measurePreserving_mul_left μ _).setLIntegral_comp_emb (measurableEmbedding_mulLeft _) φ FD
  rw [h1, hFD₀.setLIntegral_eq_tsum' φ]
  refine tsum_congr fun h => ?_
  have hset : h • ((Quotient.out q : Γ) : G)⁻¹ • FD ∩ FD₀ =
      FD₀ ∩ (Equiv.ofBijective _ (UnfoldOrbit.bijective_mul_out_inv G hle) (q, h)) • FD := by
    rw [Set.inter_comm]
    congr 1
    show (h : G) • ((Quotient.out q : Γ) : G)⁻¹ • FD = ((h : G) * ((Quotient.out q : Γ) : G)⁻¹) • FD
    rw [smul_smul]
  rw [hset]
  exact lintegral_congr fun x => hinv _ (h⁻¹).2 x

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module

theorem IntegralFamilyBound.proof (E : Type*) [Field E] [NumberField E] :
    IntegralFamilyBound.Statement E := by
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) = finrank ℚ E := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
  let e : Fin (finrank ℚ E) ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 E) :=
    (Fintype.equivFinOfCardEq hcard).symm
  let a : Fin (finrank ℚ E) → 𝓞 E := fun i => RingOfIntegers.basis E (e i)
  refine ⟨∑ i, ∑ σ : E →+* ℂ, ‖σ (a i)‖, a, ?_, ?_⟩
  · have := (integralBasis E).linearIndependent.comp e e.injective
    convert this using 1
    funext i
    simp [a, integralBasis_apply]
  · intro i σ
    calc ‖σ (a i)‖ ≤ ∑ σ' : E →+* ℂ, ‖σ' (a i)‖ :=
          Finset.single_le_sum (f := fun σ' : E →+* ℂ => ‖σ' (a i)‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_univ σ)
      _ ≤ ∑ j, ∑ σ' : E →+* ℂ, ‖σ' (a j)‖ :=
          Finset.single_le_sum (f := fun j => ∑ σ' : E →+* ℂ, ‖σ' (a j)‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
