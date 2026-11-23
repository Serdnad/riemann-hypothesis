module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle001
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.IndexNSmul
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle165
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle163
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Mathlib.MeasureTheory.Group.MeasurableEquiv
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Function.JacobianOneDim

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.ReImLattice

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem covolume_prod (μ : Measure E) [μ.IsAddHaarMeasure] (L L' : Submodule ℤ E)
    [DiscreteTopology L] [DiscreteTopology L'] [IsZLattice ℝ L] [IsZLattice ℝ L'] :
    ZLattice.covolume (L.prod L') (μ.prod μ) = ZLattice.covolume L μ * ZLattice.covolume L' μ := by
  have hD : IsAddFundamentalDomain (L.prod L') (latticeDomain L ×ˢ latticeDomain L')
      (μ.prod μ) := by
    refine IsAddFundamentalDomain.mk' ((measurableSet_latticeDomain L).prod
      (measurableSet_latticeDomain L')).nullMeasurableSet fun x => ?_
    obtain ⟨a, ha, hu⟩ := existsUnique_add_mem_latticeDomain L x.1
    obtain ⟨a', ha', hu'⟩ := existsUnique_add_mem_latticeDomain L' x.2
    refine ⟨⟨(a, a'), a.2, a'.2⟩, ⟨?_, ?_⟩, ?_⟩
    · simpa [Submodule.vadd_def, add_comm] using ha
    · simpa [Submodule.vadd_def, add_comm] using ha'
    · rintro ⟨b, hb⟩ hb'
      have h1 := hu ⟨b.1, hb.1⟩ (by simpa [Submodule.vadd_def, add_comm] using hb'.1)
      have h2 := hu' ⟨b.2, hb.2⟩ (by simpa [Submodule.vadd_def, add_comm] using hb'.2)
      apply Subtype.ext
      simp [← h1, ← h2]
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ hD, measureReal_prod_prod,
    ZLattice.covolume_eq_measure_fundamentalDomain _ _ (isAddFundamentalDomain_latticeDomain L μ),
    ZLattice.covolume_eq_measure_fundamentalDomain _ _ (isAddFundamentalDomain_latticeDomain L' μ)]

theorem reflection_stable (μ : Measure E) [μ.IsAddHaarMeasure] (M : Submodule ℤ (E × E))
    [DiscreteTopology M] [IsZLattice ℝ M] (hM : ∀ p ∈ M, (p.1, -p.2) ∈ M) (A B : Submodule ℤ E)
    (hA : ∀ y, y ∈ A ↔ (y, (0 : E)) ∈ M) (hB : ∀ y, y ∈ B ↔ ((0 : E), y) ∈ M) :
    (∃ _ : DiscreteTopology A, IsZLattice ℝ A) ∧ (∃ _ : DiscreteTopology B, IsZLattice ℝ B) ∧
      ZLattice.covolume A μ * ZLattice.covolume B μ ≤
        2 ^ Module.finrank ℝ E * ZLattice.covolume M (μ.prod μ) := by
  have h2A : ∀ p ∈ M, p.1 + p.1 ∈ A := fun p hp => by
    rw [hA]
    have := M.add_mem hp (hM p hp)
    convert this using 1
    ext <;> simp
  have h2B : ∀ p ∈ M, p.2 + p.2 ∈ B := fun p hp => by
    rw [hB]
    have := M.sub_mem hp (hM p hp)
    convert this using 1
    ext <;> simp
  haveI dA : DiscreteTopology A :=
    DiscreteTopology.of_continuous_injective
      (f := fun x : A => (⟨(x.1, 0), (hA _).1 x.2⟩ : M))
      ((continuous_subtype_val.prodMk continuous_const).subtype_mk _)
      (fun x y h => Subtype.ext (congrArg (fun z : M => z.1.1) h))
  haveI dB : DiscreteTopology B :=
    DiscreteTopology.of_continuous_injective
      (f := fun x : B => (⟨(0, x.1), (hB _).1 x.2⟩ : M))
      ((continuous_const.prodMk continuous_subtype_val).subtype_mk _)
      (fun x y h => Subtype.ext (congrArg (fun z : M => z.1.2) h))
  have key : ∀ (C : Submodule ℤ E) (f : E × E →ₗ[ℝ] E), Function.Surjective f →
      (∀ p ∈ M, f p + f p ∈ C) → Submodule.span ℝ (C : Set E) = ⊤ := by
    intro C f hf hC
    rw [eq_top_iff, ← LinearMap.range_eq_top.2 hf, LinearMap.range_eq_map,
      ← IsZLattice.span_top (K := ℝ) (L := M), Submodule.map_span, Submodule.span_le]
    rintro _ ⟨p, hp, rfl⟩
    have h := (Submodule.span ℝ (C : Set E)).smul_mem (2⁻¹ : ℝ) (Submodule.subset_span (hC p hp))
    rwa [← two_smul ℝ, inv_smul_smul₀ two_ne_zero] at h
  haveI lA : IsZLattice ℝ A := ⟨key A (LinearMap.fst ℝ E E) LinearMap.fst_surjective h2A⟩
  haveI lB : IsZLattice ℝ B := ⟨key B (LinearMap.snd ℝ E E) LinearMap.snd_surjective h2B⟩
  refine ⟨⟨dA, lA⟩, ⟨dB, lB⟩, ?_⟩
  have hle : A.prod B ≤ M := fun p hp => by
    have := M.add_mem ((hA _).1 hp.1) ((hB _).1 hp.2)
    simpa using this
  rw [← covolume_prod μ A B, covolume_eq_relIndex_mul_of_haar (μ.prod μ) _ M hle]
  refine mul_le_mul_of_nonneg_right ?_ (ZLattice.covolume_pos M (μ.prod μ)).le
  let f : M.toAddSubgroup →+ A :=
    { toFun := fun p => ⟨p.1.1 + p.1.1, h2A _ p.2⟩
      map_zero' := by ext; simp
      map_add' := fun p q => by ext; simp; abel }
  have hK : (nsmulAddMonoidHom (α := A) 2).range.index = 2 ^ Module.finrank ℝ E := by
    rw [AddSubgroup.index_range_nsmul, ZLattice.rank ℝ A]
  have hc : (A.prod B).toAddSubgroup.addSubgroupOf M.toAddSubgroup =
      (nsmulAddMonoidHom (α := A) 2).range.comap f := by
    ext p
    simp only [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, Submodule.mem_prod,
      AddSubgroup.mem_comap, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
    constructor
    · rintro ⟨h1, -⟩
      exact ⟨⟨_, h1⟩, Subtype.ext (by simp [f, two_nsmul])⟩
    · rintro ⟨y, hy⟩
      have h1 : y.1 + y.1 = p.1.1 + p.1.1 := by
        have := congrArg Subtype.val hy
        simpa [f, two_nsmul] using this
      have h2 : y.1 = p.1.1 := by
        rw [← two_smul ℝ, ← two_smul ℝ] at h1
        exact smul_right_injective E two_ne_zero h1
      have h3 : p.1.1 ∈ A := h2 ▸ y.2
      refine ⟨h3, (hB _).2 ?_⟩
      have := M.sub_mem p.2 ((hA _).1 h3)
      convert this using 1
      ext <;> simp
  have hidx : (A.prod B).toAddSubgroup.relIndex M.toAddSubgroup ≤ 2 ^ Module.finrank ℝ E := by
    rw [AddSubgroup.relIndex, hc, AddSubgroup.index_comap, ← hK, ← AddSubgroup.relIndex_top_right]
    refine AddSubgroup.relIndex_le_of_le_right le_top ?_
    rw [AddSubgroup.relIndex_top_right, hK]
    positivity
  exact_mod_cast hidx

end General

noncomputable def reImEquiv (ι κ : Type) [Fintype ι] [Fintype κ] :
    ((ι → κ → ℝ) × (ι → κ → ℝ)) ≃L[ℝ] (ι → κ → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p v i => ⟨p.1 v i, p.2 v i⟩
      invFun := fun z => (fun v i => (z v i).re, fun v i => (z v i).im)
      map_add' := fun p q => by ext v i; apply Complex.ext <;> simp
      map_smul' := fun c p => by ext v i; apply Complex.ext <;> simp
      left_inv := fun p => rfl
      right_inv := fun z => rfl }

theorem reImEquiv_apply {ι κ : Type} [Fintype ι] [Fintype κ] (p : (ι → κ → ℝ) × (ι → κ → ℝ))
    (v : ι) (i : κ) : reImEquiv ι κ p v i = ⟨p.1 v i, p.2 v i⟩ := rfl

theorem measurePreserving_reImEquiv (ι κ : Type) [Fintype ι] [Fintype κ] :
    MeasurePreserving (reImEquiv ι κ) (Measure.prod volume volume) volume := by
  have h1 := (volume_measurePreserving_arrowProdEquivProdArrow (κ → ℝ) (κ → ℝ) ι).symm
  have h2 := (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ κ).symm
  have h3 := Complex.volume_preserving_equiv_real_prod.symm
  have h4 := volume_preserving_pi (ι := κ) (fun _ => h3)
  have h5 := volume_preserving_pi (ι := ι) (fun _ => h4.comp h2)
  exact h5.comp h1

theorem real_imag_covolume_le : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (L : Submodule ℤ (ι → κ → ℂ)) [DiscreteTopology L] [IsZLattice ℝ L], (∀ z ∈ L, (fun v i => starRingEnd ℂ (z v i)) ∈ L) → ∀ A B : Submodule ℤ (ι → κ → ℝ), (∀ y, y ∈ A ↔ (fun v i => (y v i : ℂ)) ∈ L) → (∀ y, y ∈ B ↔ (fun v i => Complex.I * (y v i : ℂ)) ∈ L) → (∃ _ : DiscreteTopology A, IsZLattice ℝ A) ∧ (∃ _ : DiscreteTopology B, IsZLattice ℝ B) ∧ ZLattice.covolume A volume * ZLattice.covolume B volume ≤ 2 ^ (Fintype.card ι * Fintype.card κ) * ZLattice.covolume L volume := by
  intro ι κ _ _ L _ _ hL A B hA hB
  have hmem : ∀ p, p ∈ ZLattice.comap ℝ L (reImEquiv ι κ).toLinearMap ↔ reImEquiv ι κ p ∈ L :=
    fun p => Iff.rfl
  have h := reflection_stable volume (ZLattice.comap ℝ L (reImEquiv ι κ).toLinearMap)
    (fun p hp => by
      rw [hmem] at hp ⊢
      convert hL _ hp using 1
      ext v i; apply Complex.ext <;> simp [reImEquiv_apply]) A B
    (fun y => by
      rw [hA, hmem]
      congr! 1)
    (fun y => by
      rw [hB, hmem]
      congr! 1
      ext v i; apply Complex.ext <;> simp [reImEquiv_apply])
  haveI : (volume : Measure (κ → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (ι → κ → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (κ → ℝ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (ι → κ → ℝ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : ((volume : Measure (ι → κ → ℝ)).prod (volume : Measure (ι → κ → ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  rw [ZLattice.covolume_comap L volume _ (measurePreserving_reImEquiv ι κ)] at h
  have hr : Module.finrank ℝ (ι → κ → ℝ) = Fintype.card ι * Fintype.card κ := by
    rw [Module.finrank_pi_fintype]; simp
  rwa [hr] at h

end GlobalTheory.ReImLattice
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov

theorem exists_unitary_of_skew_layer (R K : Type) [CommRing R] [Field K] [StarRing K]
    [Algebra R K] (n m : ℕ) (J : Matrix (Fin n) (Fin n) K)
    (A : ℕ → Submodule R (Matrix (Fin n) (Fin n) K)) (w : R)
    (hJ : Jᴴ = J) (hdet : J.det ≠ 0)
    (hw : algebraMap R K w + star (algebraMap R K w) = 1)
    (hA : ∀ c, A (c + 1) ≤ A c) (hm : A m = ⊥)
    (hmul : ∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1))
    (_hadj : ∀ c, ∀ X ∈ A c, J⁻¹ * Xᴴ * J ∈ A c)
    (c : ℕ) (X : Matrix (Fin n) (Fin n) K) (hX : X ∈ A c) (hskew : J⁻¹ * Xᴴ * J = -X) :
    ∃ Y ∈ A (c + 1), (1 + X + Y)ᴴ * J * (1 + X + Y) = J := by
  classical
  have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hdet
  have cL : ∀ B : Matrix (Fin n) (Fin n) K, J * (J⁻¹ * B) = B :=
    fun B => Matrix.mul_nonsing_inv_cancel_left J B hu
  have cL' : ∀ B : Matrix (Fin n) (Fin n) K, J⁻¹ * (J * B) = B :=
    fun B => Matrix.nonsing_inv_mul_cancel_left J B hu
  have cR : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hu
  have cR' : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hu
  have hJi : (J⁻¹)ᴴ = J⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hJ]
  have hanti : Antitone A := antitone_nat_of_succ_le hA
  have to0 : ∀ {d : ℕ} {M : Matrix (Fin n) (Fin n) K}, M ∈ A d → M ∈ A 0 :=
    fun h => hanti (Nat.zero_le _) h
  have smem : ∀ (r : R) {d : ℕ} {M : Matrix (Fin n) (Fin n) K}, M ∈ A d →
      algebraMap R K r • M ∈ A d := by
    intro r d M h
    rw [algebraMap_smul]
    exact (A d).smul_mem r h
  set β : K := algebraMap R K w with hβ
  have hst : star β = 1 - β := by rw [← hw]; ring

  have key : ∀ k : ℕ, ∃ Y ∈ A (c + 1),
      J⁻¹ * (1 + X + Y)ᴴ * J * (1 + X + Y) - 1 ∈ A (c + 1 + k) := by
    intro k
    induction k with
    | zero =>
      refine ⟨0, (A (c + 1)).zero_mem, ?_⟩
      have hX' : Xᴴ = -(J * (X * J⁻¹)) := by
        calc Xᴴ = J * ((J⁻¹ * Xᴴ * J) * J⁻¹) := by
              simp only [mul_assoc, cR, mul_one, cL]
          _ = -(J * (X * J⁻¹)) := by rw [hskew]; simp only [neg_mul, mul_neg]
      have h0 : J⁻¹ * (1 + X + 0)ᴴ * J * (1 + X + 0) - 1 = -(X * X) := by
        simp only [add_zero, Matrix.conjTranspose_add, Matrix.conjTranspose_one, hX']
        simp only [mul_add, add_mul, mul_one, one_mul, mul_neg, neg_mul, mul_assoc, cL', cR']
        abel
      rw [h0, Nat.add_zero]
      exact (A (c + 1)).neg_mem (hmul c X hX X (to0 hX)).1
    | succ k ih =>
      obtain ⟨Y, hY, hE⟩ := ih
      set g := 1 + X + Y with hg
      set E := J⁻¹ * gᴴ * J * g - 1 with hEdef
      have hEE : E * E ∈ A (c + 1 + (k + 1)) := (hmul (c + 1 + k) E hE E (to0 hE)).1
      have hEEE : E * (E * E) ∈ A (c + 1 + (k + 1)) :=
        (hmul (c + 1 + k) E hE (E * E) (to0 hEE)).1
      refine ⟨Y - β • (g * E), ?_, ?_⟩
      · have hEc : E ∈ A (c + 1) := hanti (by omega) hE
        have hgE : g * E ∈ A (c + 1) := by
          rw [hg, add_mul, add_mul, one_mul]
          exact add_mem (add_mem hEc (hmul c X hX E (to0 hE)).1)
            (hanti (by omega) (hmul (c + 1) Y hY E (to0 hE)).1)
        exact sub_mem hY (smem w hgE)
      · have hgeq : 1 + X + (Y - β • (g * E)) = g - β • (g * E) := by rw [hg]; abel
        rw [hgeq]

        have hEH : J⁻¹ * Eᴴ * J = E := by
          rw [hEdef]
          simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose, hJi, hJ, sub_mul, mul_sub, mul_one, mul_assoc, cR']
        have h1 : J⁻¹ * (Eᴴ * (gᴴ * J)) = E * (J⁻¹ * (gᴴ * J)) := by
          calc J⁻¹ * (Eᴴ * (gᴴ * J)) = (J⁻¹ * Eᴴ * J) * (J⁻¹ * (gᴴ * J)) := by
                simp only [mul_assoc, cL]
            _ = E * (J⁻¹ * (gᴴ * J)) := by rw [hEH]
        have hP' : J⁻¹ * (g - β • (g * E))ᴴ * J
            = J⁻¹ * (gᴴ * J) - star β • (E * (J⁻¹ * (gᴴ * J))) := by
          simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
            mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc, h1]
        have hPg0 : J⁻¹ * (gᴴ * (J * g)) = 1 + E := by
          rw [hEdef]; simp only [mul_assoc]; abel
        have hPg : ∀ M, J⁻¹ * (gᴴ * (J * (g * M))) = M + E * M := by
          intro M
          rw [hEdef]; simp only [sub_mul, one_mul, mul_assoc]; abel
        have hid : J⁻¹ * (g - β • (g * E))ᴴ * J * (g - β • (g * E)) - 1
            = (β - β * β - 1) • (E * E) + (β - β * β) • (E * (E * E)) := by
          rw [hP']
          simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_assoc, hPg, hPg0,
            mul_add, mul_one, smul_add, hst]
          module
        have s1 : β - β * β - 1 = algebraMap R K (w - w * w - 1) := by simp [hβ]
        have s2 : β - β * β = algebraMap R K (w - w * w) := by simp [hβ]
        rw [hid, s1, s2]
        exact add_mem (smem _ hEE) (smem _ hEEE)
  obtain ⟨Y, hY, hEm⟩ := key m
  refine ⟨Y, hY, ?_⟩
  have hz : J⁻¹ * (1 + X + Y)ᴴ * J * (1 + X + Y) - 1 ∈ A m := hanti (by omega) hEm
  rw [hm, Submodule.mem_bot, sub_eq_zero] at hz
  calc (1 + X + Y)ᴴ * J * (1 + X + Y)
      = J * (J⁻¹ * (1 + X + Y)ᴴ * J * (1 + X + Y)) := by simp only [mul_assoc, cL]
    _ = J := by rw [hz, mul_one]

end GlobalTheory.RadCov
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem iwasawa_shift_lintegral {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    (M : Set G) (μM μK : Measure G) [SFinite μK] (δ φ ψ : G → ENNReal)
    (hδ : Measurable δ) (hφ : Measurable φ) (hψ : Measurable ψ) (hM : μM Mᶜ = 0) (l : G)
    (h1 : μM.map (fun g => g * l) = μM) (h2 : μK.map (fun g => l * g) = μK)
    (h3 : ∀ m ∈ M, δ (m * l) = δ m) (u : G) :
    ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ k ∂μK ∂μM
      = ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂μM := by
  have hae : ∀ᵐ m ∂μM, m ∈ M := by rw [ae_iff]; exact hM

  have hK : ∀ m, ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK
      = ∫⁻ k, φ (u * (m * l⁻¹) * k) * ψ k ∂μK := by
    intro m
    conv_rhs => rw [← h2, show (fun g : G => l * g) = ⇑(MeasurableEquiv.mulLeft l) from rfl,
      lintegral_map_equiv]
    simp [mul_assoc]
  simp_rw [hK]

  conv_rhs => rw [← h1, show (fun g : G => g * l) = ⇑(MeasurableEquiv.mulRight l) from rfl,
    lintegral_map_equiv]
  apply lintegral_congr_ae
  filter_upwards [hae] with m hm
  simp [mul_assoc, h3 m hm]

theorem iwasawa_unfold_lintegral : ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (M L : Set G) (μN μM μK νL : Measure G) [SFinite μN] [SFinite μM] [SFinite μK] [SFinite νL] (δ φ ψ : G → ENNReal), Measurable δ → Measurable φ → Measurable ψ → μM Mᶜ = 0 → νL Lᶜ = 0 → (∀ l ∈ L, μM.map (fun g => g * l) = μM) → (∀ l ∈ L, μK.map (fun g => l * g) = μK) → (∀ l ∈ L, ∀ m ∈ M, δ (m * l) = δ m) → νL Set.univ * ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ k ∂μK ∂μM ∂μN = ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ∫⁻ l, ψ (l * k) ∂νL ∂μK ∂μM ∂μN := by
  intro G _ _ _ M L μN μM μK νL _ _ _ _ δ φ ψ hδ hφ hψ hM hL h1 h2 h3
  have hLae : ∀ᵐ l ∂νL, l ∈ L := by rw [ae_iff]; exact hL

  have hH : Measurable fun p : G × G × G =>
      δ p.2.1 * ∫⁻ k, φ (p.1 * p.2.1 * k) * ψ (p.2.2 * k) ∂μK := by
    refine Measurable.mul (hδ.comp measurable_snd.fst) ?_
    exact Measurable.lintegral_prod_right'
      (f := fun q : (G × G × G) × G => φ (q.1.1 * q.1.2.1 * q.2) * ψ (q.1.2.2 * q.2)) (by fun_prop)
  have hX : Measurable fun p : G × G =>
      ∫⁻ m, δ m * ∫⁻ k, φ (p.1 * m * k) * ψ (p.2 * k) ∂μK ∂μM :=
    Measurable.lintegral_prod_right' (f := fun q : (G × G) × G =>
        δ q.2 * ∫⁻ k, φ (q.1.1 * q.2 * k) * ψ (q.1.2 * k) ∂μK)
      (hH.comp (f := fun q : (G × G) × G => (q.1.1, q.2, q.1.2)) (by fun_prop))

  have step1 : ∀ u m, δ m * ∫⁻ k, φ (u * m * k) * ∫⁻ l, ψ (l * k) ∂νL ∂μK
      = ∫⁻ l, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂νL := by
    intro u m
    have hg : Measurable fun l => ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK :=
      Measurable.lintegral_prod_right' (f := fun q : G × G => φ (u * m * q.2) * ψ (q.1 * q.2))
        (by fun_prop)
    calc δ m * ∫⁻ k, φ (u * m * k) * ∫⁻ l, ψ (l * k) ∂νL ∂μK
        = δ m * ∫⁻ k, ∫⁻ l, φ (u * m * k) * ψ (l * k) ∂νL ∂μK := by
          congr 1
          exact lintegral_congr fun k => (lintegral_const_mul _ (hψ.comp (measurable_mul_const k))).symm
      _ = δ m * ∫⁻ l, ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂νL := by
          congr 1
          exact lintegral_lintegral_swap (by
            exact (show Measurable fun q : G × G => φ (u * m * q.1) * ψ (q.2 * q.1) by fun_prop).aemeasurable)
      _ = ∫⁻ l, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂νL := (lintegral_const_mul _ hg).symm
  have step2 : ∀ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ∫⁻ l, ψ (l * k) ∂νL ∂μK ∂μM
      = ∫⁻ l, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂μM ∂νL := by
    intro u
    calc _ = ∫⁻ m, ∫⁻ l, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂νL ∂μM :=
          lintegral_congr fun m => step1 u m
      _ = _ := lintegral_lintegral_swap (by
          exact (hH.comp (f := fun q : G × G => (u, q.1, q.2)) (by fun_prop)).aemeasurable)

  have key : ∀ᵐ l ∂νL, ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂μM ∂μN
      = ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ k ∂μK ∂μM ∂μN := by
    filter_upwards [hLae] with l hl
    exact lintegral_congr fun u =>
      (iwasawa_shift_lintegral M μM μK δ φ ψ hδ hφ hψ hM l (h1 l hl) (h2 l hl) (h3 l hl) u).symm
  calc νL Set.univ * ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ k ∂μK ∂μM ∂μN
      = ∫⁻ _l, (∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ k ∂μK ∂μM ∂μN) ∂νL := by
        rw [lintegral_const]; exact mul_comm _ _
    _ = ∫⁻ l, ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂μM ∂μN ∂νL :=
        lintegral_congr_ae (key.mono fun _ hl => hl.symm)
    _ = ∫⁻ u, ∫⁻ l, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂μM ∂νL ∂μN :=
        (lintegral_lintegral_swap (by exact hX.aemeasurable)).symm
    _ = _ := lintegral_congr fun u => (step2 u).symm

end GlobalTheory.IwConst
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

namespace GlobalTheory

theorem lintegral_Ioi_comp_const_div_mul_div :
    ∀ (κ : ℝ), 0 < κ → ∀ w : ℝ → ENNReal, Measurable w →
      ∫⁻ t in Set.Ioi (0 : ℝ), w (κ / t) * ENNReal.ofReal t / ENNReal.ofReal t =
        ENNReal.ofReal κ * ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal (t ^ 2) := by
  intro κ hκ w _hw
  have hκ0 : κ ≠ 0 := ne_of_gt hκ
  have himg : (fun u : ℝ => κ / u) '' Set.Ioi (0 : ℝ) = Set.Ioi (0 : ℝ) := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact div_pos hκ hu
    · intro ht
      have ht0 : t ≠ 0 := ne_of_gt (Set.mem_Ioi.mp ht)
      refine ⟨κ / t, div_pos hκ ht, ?_⟩
      show κ / (κ / t) = t
      field_simp
  have hderiv : ∀ u ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt (fun u : ℝ => κ / u) (-(κ / u ^ 2)) (Set.Ioi (0 : ℝ)) u := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hu)
    have h := ((hasDerivAt_inv hu0).const_mul κ).hasDerivWithinAt (s := Set.Ioi (0 : ℝ))
    have hfun : (fun u : ℝ => κ / u) = fun y => κ * y⁻¹ := by
      funext y
      rw [div_eq_mul_inv]
    rw [hfun]
    exact h.congr_deriv (by ring)
  have hinj : Set.InjOn (fun u : ℝ => κ / u) (Set.Ioi (0 : ℝ)) := by
    intro a ha b hb hab
    have ha0 : a ≠ 0 := ne_of_gt (Set.mem_Ioi.mp ha)
    have hb0 : b ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hb)
    have hab' : κ / a = κ / b := hab
    field_simp at hab'
    exact hab'.symm
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj,
    himg, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ((ae_restrict_iff' measurableSet_Ioi).2
    (Filter.Eventually.of_forall fun u hu => ?_))
  have hu : 0 < u := Set.mem_Ioi.mp hu
  have hu0 : u ≠ 0 := ne_of_gt hu
  have hκu : 0 < κ / u := div_pos hκ hu
  have hsq : 0 < u ^ 2 := by positivity
  have hinv : κ / (κ / u) = u := by field_simp
  have habs : |(-(κ / u ^ 2))| = κ / u ^ 2 := by
    rw [abs_neg, abs_of_pos (div_pos hκ hsq)]
  have hne : ENNReal.ofReal (κ / u) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hκu
  simp only [hinv, habs]
  rw [ENNReal.mul_div_cancel_right hne ENNReal.ofReal_ne_top, ENNReal.ofReal_div_of_pos hsq]
  simp only [div_eq_mul_inv]
  ring

end GlobalTheory
end
