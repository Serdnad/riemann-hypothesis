module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveDegree
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveAlgebraic
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle039
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle011

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

namespace PointVertRAux

theorem degC_eq_finrank {T : Type} [Fintype T] {K' : Type} [Field K'] [NumberField K']
    {y : (Σ _ : Unit, T) → K'} (hP : IsArithVar (mCoordIdeal y) 1) :
    degC (mCoordIdeal y) = Module.finrank ℚ (blockFnField y) := by
  rw [IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.full Unit (fun _ => T) K' y hP, Nat.card_eq_fintype_card,
    AlgHom.card]

end PointVertRAux

theorem PointVertR.proof (hI : VertRIndex.Statement) (hN : SectionIndexNorm.Statement) :
    PointVertR.Statement := by
  intro T _ K' _ _ y s hP hs hsP
  rw [hI T K' y s hP hs hsP, PointVertRAux.degC_eq_finrank hP,
    ← (letI : Module.Free (blockFnField y) K' := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (blockFnField y) K'), Nat.cast_mul, mul_assoc,
    hN T K' y s hP hs hsP]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 NumberField

noncomputable section

namespace PointDegreeComplexPositive

theorem card_algHom_pos {K' : Type} [Field K'] [NumberField K'] (E : IntermediateField ℚ K') :
    0 < Nat.card (E →ₐ[ℚ] ℂ) := by
  have : FiniteDimensional ℚ E := inferInstance
  have : Algebra.IsAlgebraic ℚ E := Algebra.IsAlgebraic.of_finite ℚ E
  have : Nonempty (E →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  exact Nat.card_pos

end PointDegreeComplexPositive

theorem PointDegCPos.proof : PointDegCPos.Statement := by
  intro T _ K' _ _ y hP
  rw [IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.full Unit (fun _ => T) K' y hP]
  exact PointDegreeComplexPositive.card_algHom_pos _

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace PointArithIntersection

open IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree

variable {T : Type} [Fintype T]

theorem logNorm_smul {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (fun _ : Unit => T)} {s : MRing (fun _ : Unit => T)}
    {P : Ideal (MRing (fun _ : Unit => T))} (hs : IsSectionOn P A s) (c : ℂ) (hc : c ≠ 0)
    (z : (Σ _ : Unit, T) → ℂ) : logNorm A s (fun p => c * z p) = logNorm A s z := by
  obtain ⟨a, ha, hhom, -⟩ := hs
  have hz : (fun p : Σ _ : Unit, T => c * z p) = scaleBlock () c z := by
    funext p
    simp [scaleBlock]
  have hh : A.h (fun p => c * z p) = ‖c‖ ^ A.a () * A.h z := by
    simpa using A.smul (fun _ => c) z (fun _ => hc)
  unfold logNorm
  rw [hh, hz, eval_scaleBlock () c z s a hhom, ha (), zpow_natCast, norm_mul, norm_pow]
  rw [mul_div_mul_left _ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hc))]

variable {K' : Type} [Field K'] [NumberField K']

theorem eq_of_ptOf_eq_smul {y : (Σ _ : Unit, T) → K'} {c : Unit → T} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {φ ψ : blockFnField y →ₐ[ℚ] ℂ} (t : ℂ) (h : ptOf y c φ = fun p => t * ptOf y c ψ p) : φ = ψ := by
  have ht : t = 1 := by
    have := congrFun h ⟨(), c ()⟩
    simp only [ptOf_chart hc, mul_one] at this
    exact this.symm
  subst ht
  refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (blockFnField_eq y c hc) ?_
  rintro _ ⟨p, rfl⟩
  have := congrFun h p
  simp only [one_mul] at this
  exact this

theorem sum_reps_eq {y : (Σ _ : Unit, T) → K'} (hP : IsArithVar (mCoordIdeal y) 1) {c : Unit → T}
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (R : Finset ((Σ _ : Unit, T) → ℂ))
    (hR : ∀ t ∈ R, t ∈ mcPts (mCoordIdeal y))
    (hU : ∀ z ∈ mcPts (mCoordIdeal y), ∃! t, t ∈ R ∧ SameOrbit z t)
    (F : ((Σ _ : Unit, T) → ℂ) → ℝ) (hF : ∀ t : ℂ, t ≠ 0 → ∀ z, F (fun p => t * z p) = F z)
    [Fintype (blockFnField y →ₐ[ℚ] ℂ)] :
    ∑ t ∈ R, F t = ∑ φ : blockFnField y →ₐ[ℚ] ℂ, F (ptOf y c φ) := by
  have hex : ∀ t ∈ R, ∃ φ : blockFnField y →ₐ[ℚ] ℂ,
      ptOf y c φ = (fun p => (t ⟨p.1, c p.1⟩)⁻¹ * t p) ∧ ∀ k, t ⟨k, c k⟩ ≠ 0 :=
    fun t ht => exists_ptOf hP hc (hR t ht)
  refine Finset.sum_bij (fun t ht => (hex t ht).choose) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro t ht t' ht' he
    have h1 := (hex t ht).choose_spec
    have h2 := (hex t' ht').choose_spec
    rw [he] at h1
    obtain ⟨u, -, hu⟩ := hU t (hR t ht)
    have e1 : t = u := hu t ⟨ht, ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩⟩
    have e2 : t' = u := by
      refine hu t' ⟨ht', fun k => t ⟨k, c k⟩ * (t' ⟨k, c k⟩)⁻¹,
        fun k => mul_ne_zero (h1.2 k) (inv_ne_zero (h2.2 k)), funext fun p => ?_⟩
      have := congrFun (h1.1.symm.trans h2.1) p
      have h0 := h1.2 p.1
      have h0' := h2.2 p.1
      simp only at this ⊢
      rw [show t p = t ⟨p.1, c p.1⟩ * ((t ⟨p.1, c p.1⟩)⁻¹ * t p) by field_simp, this]
      ring
    rw [e1, e2]
  · intro φ _
    obtain ⟨u, ⟨hu, ⟨d, hd, hdu⟩⟩, -⟩ := hU _ (ptOf_mem hc φ)
    refine ⟨u, hu, eq_of_ptOf_eq_smul hc ((u ⟨(), c ()⟩)⁻¹ * (d ())⁻¹) ?_⟩
    rw [(hex u hu).choose_spec.1, hdu]
    funext p
    have h0 := hd ()
    ring_nf
    field_simp
  · intro t ht
    rw [(hex t ht).choose_spec.1]
    exact (hF _ (inv_ne_zero ((hex t ht).choose_spec.2 ())) t).symm

theorem sum_ringHom_restrict (κ : IntermediateField ℚ K') (H : (κ →ₐ[ℚ] ℂ) → ℝ)
    [Fintype (κ →ₐ[ℚ] ℂ)] :
    ∑ σ : K' →+* ℂ, H ((σ.toRatAlgHom).comp (IsScalarTower.toAlgHom ℚ κ K')) =
      (Module.finrank κ K' : ℝ) * ∑ f, H f := by
  classical
  rw [Fintype.sum_equiv (RingHom.equivRatAlgHom K' ℂ)
    (fun σ : K' →+* ℂ => H ((σ.toRatAlgHom).comp (IsScalarTower.toAlgHom ℚ κ K')))
    (fun σ : K' →ₐ[ℚ] ℂ => H (σ.comp (IsScalarTower.toAlgHom ℚ κ K'))) (fun _ => rfl)]
  let res : (K' →ₐ[ℚ] ℂ) → (κ →ₐ[ℚ] ℂ) := fun σ => σ.comp (IsScalarTower.toAlgHom ℚ κ K')
  rw [← Fintype.sum_fiberwise res, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hconst : ∀ i : {σ // res σ = f}, H (res i) = H f := fun i => by rw [i.2]
  rw [Finset.sum_congr rfl fun i _ => hconst i, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  congr 1
  have e : {σ // res σ = f} ≃ @AlgHom κ K' ℂ _ _ _ _ f.toRingHom.toAlgebra :=
    ((algHomEquivSigma (A := ℚ) (B := κ) (C := K') (D := ℂ)).subtypeEquiv
      (p := fun σ => res σ = f) (q := fun x => x.1 = f) fun σ => Iff.rfl).trans (Equiv.sigmaSubtype f)
  let _ := f.toRingHom.toAlgebra
  rw [Fintype.card_eq_nat_card, Nat.card_congr e,
    AlgHom.natCard_of_splits κ K' ℂ fun _ => IsAlgClosed.splits _]

end PointArithIntersection


open PointArithIntersection IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree in
theorem PointArInt.proof : PointArInt.Statement := by
  intro T _ K' _ _ y A s hP hs
  classical
  obtain ⟨c0, hc0⟩ := hP.2.1.2.2 ()
  let c : Unit → T := fun _ => c0
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h => hc0 (X_mem_of_eq_zero h)
  obtain ⟨R, hR, hU, hsum⟩ := Inter.regularityPointsSum_holds.proof Unit (fun _ => T) (mCoordIdeal y) hP
  have harInt : arInt (mCoordIdeal y) s A (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (fun _ : Unit => T)) =
      ∑ t ∈ R, logNorm A s t := by
    unfold arInt
    have e0 : (fun (j : Fin 0) (z : (Σ _ : Unit, T) → ℂ) =>
        Real.log (((Fin.elim0 j : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (fun _ : Unit => T))).h z)) =
        (Fin.elim0 : Fin 0 → ((Σ _ : Unit, T) → ℂ) → ℝ) := funext fun j => j.elim0
    rw [e0]
    apply hsum
    rintro z z' - ⟨d, hd, rfl⟩
    exact logNorm_smul hs (d ()) (hd ()) z'
  set κ := blockFnField y
  have hσ : ∀ σ : K' →+* ℂ, logNorm A s (fun p => σ (y p)) =
      logNorm A s (ptOf y c ((σ.toRatAlgHom).comp (IsScalarTower.toAlgHom ℚ κ K'))) := by
    intro σ
    have hy0 : σ (y ⟨(), c0⟩) ≠ 0 := (map_ne_zero σ).mpr (hc ())
    have e : (fun p => σ (y p)) = fun p => σ (y ⟨(), c0⟩) *
        ptOf y c ((σ.toRatAlgHom).comp (IsScalarTower.toAlgHom ℚ κ K')) p := by
      funext p
      have : ptOf y c ((σ.toRatAlgHom).comp (IsScalarTower.toAlgHom ℚ κ K')) p =
          σ (y p / y ⟨(), c0⟩) := rfl
      rw [this, map_div₀]
      field_simp
    rw [e, logNorm_smul hs _ hy0]
  rw [harInt, sum_reps_eq hP hc R hR hU (logNorm A s) (fun t ht z => logNorm_smul hs t ht z),
    Finset.sum_congr rfl (fun σ _ => hσ σ),
    sum_ringHom_restrict κ (fun φ => logNorm A s (ptOf y c φ)), degC_eq hP,
    AlgHom.natCard_of_splits ℚ κ ℂ fun _ => IsAlgClosed.splits _, ← Module.finrank_mul_finrank ℚ κ K']
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

namespace StackedExceptionalBaseBound

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i} {T : Type} [Fintype T]

theorem centre_mem {b : Module.Basis T ℤ (dualLattice F)} {b' : Module.Basis T ℤ (dualLattice F')} {a : T → ℤ}
    (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) {k : Type} [Field k] {α : T → k}
    {M : T → Fin i → k} (hres : IsExcResidueData b b' α M) (t : T) :
    C (a t) * graphFirst t ∈ linPrime α M := by
  obtain ⟨ρ, ρ', σ, -, -, -, hker, -, -, hα, -⟩ := hres
  have hmem : ((a t • b' t : dualLattice F') : Fin i → K) ∈ dualLattice F := by
    rw [Submodule.coe_smul_of_tower, ← hab t]
    exact (b t).2
  have h0 : ((a t : ℤ) : k) * α t = 0 := by
    rw [hα t, ← zsmul_eq_mul, ← map_zsmul]
    exact (hker _).mpr hmem
  have h1 : linPointMap α M (C (a t)) = C ((a t : k)) := by simp [linPointMap]
  rw [linPrime, RingHom.mem_ker, map_mul, h1, LinPrimeExample.linPointMap_first, ← mul_assoc, ← C_mul, h0, C_0,
    zero_mul]

end StackedExceptionalBaseBound


open StackedExceptionalBaseBound in
theorem DualStackedExcBaseLe.proof (hBihom : DualStackedGraphBihomog.Statement)
    (hLead : DualStackedExcLeadForm.Statement) : DualStackedExcBaseLe.Statement := by
  intro K _ _ i F F' T _ _ b b' a hi hlt hcov hab k _ α M hres
  refine sup_le ?_ ?_
  · intro f hf
    obtain ⟨s, g, rfl, hg⟩ := hBihom K i F F' T b b' a hab f hf

    rw [linPrime, RingHom.mem_ker, map_sum]
    exact Finset.sum_eq_zero fun p hp =>
      hLead K i F F' T b b' a hi hlt hcov hab k α M hres p.1 p.2 (g p) (hg p hp).1 (hg p hp).2
  · rw [Ideal.span_le, Set.range_subset_iff]
    exact centre_mem hab hres

end

end GroundTheory.Heights₂.Heights
end
