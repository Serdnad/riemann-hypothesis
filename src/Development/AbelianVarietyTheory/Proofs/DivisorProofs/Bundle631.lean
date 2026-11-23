module

public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
import Mathlib.Algebra.Module.StablyFree.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle587
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle588
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Mul
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle003
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
namespace GlobalTheory.L2Cutoff

theorem cutoff_smooth_dbar : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M], ∀ (X : EtaleStein n M) (ψ : M → ℝ) (G : M → ℂ) (Ω : Set M) (δ b : ℝ) (θ : ℝ → ℝ), SmoothR n X.z ψ → ContDiff ℝ ∞ θ → (∀ t, b ≤ t → θ t = 0) → IsOpen Ω → (∀ e : OpenPartialHomeomorph M (V n), IsChart n X.z e → DifferentiableOn ℂ (G ∘ e.symm) (e.target ∩ e.symm ⁻¹' Ω)) → (∀ x, δ * ψ x ≤ b → x ∈ Ω) → Smooth n X.z (fun x => (θ (δ * ψ x) : ℂ) * G x) ∧ ∀ (x : M) (ξ : Fin n → ℂ), dbarDot n X.z (fun y => (θ (δ * ψ y) : ℂ) * G y) x ξ = ((deriv θ (δ * ψ x) * δ : ℝ) : ℂ) * G x * dbarDot n X.z (fun y => (ψ y : ℂ)) x ξ := by
  intro n M _ _ _ _ _ X ψ G Ω δ b θ hψ hθ hθ0 hΩ hG hsub
  have hψe : ∀ e : OpenPartialHomeomorph M (V n), IsChart n X.z e →
      ContDiffOn ℝ ∞ (fun v => ψ (e.symm v)) e.target := by
    intro e he
    have h1 := (Complex.reCLM.contDiff (n := ∞)).comp_contDiffOn (hψ e he)
    refine h1.congr fun v _ => ?_
    simp
  have hθd : ∀ t, DifferentiableAt ℝ θ t := fun t => (hθ.differentiable (by simp)) t
  have hθzero : ∀ t, b < t → θ =ᶠ[𝓝 t] fun _ => 0 := by
    intro t ht
    filter_upwards [lt_mem_nhds ht] with s hs
    exact hθ0 s hs.le
  have hloc : ∀ e : OpenPartialHomeomorph M (V n), IsChart n X.z e → ∀ v ∈ e.target,
      (e.symm v ∈ Ω → DifferentiableAt ℂ (G ∘ e.symm) v) ∧
      (e.symm v ∉ Ω → ((fun x => (θ (δ * ψ x) : ℂ) * G x) ∘ e.symm) =ᶠ[𝓝 v] fun _ => 0) := by
    intro e he v hv
    constructor
    · intro hvΩ
      exact (hG e he).differentiableAt
        ((e.isOpen_inter_preimage_symm hΩ).mem_nhds ⟨hv, hvΩ⟩)
    · intro hvΩ
      have hb : b < δ * ψ (e.symm v) := by
        by_contra h
        exact hvΩ (hsub _ (not_lt.1 h))
      have hc : ContinuousAt (fun w => δ * ψ (e.symm w)) v :=
        continuousAt_const.mul ((hψe e he).continuousOn.continuousAt (e.open_target.mem_nhds hv))
      filter_upwards [hc.eventually (lt_mem_nhds hb)] with w hw
      simp [hθ0 _ hw.le]
  refine ⟨?_, ?_⟩
  · intro e he v hv
    apply ContDiffAt.contDiffWithinAt
    by_cases hvΩ : e.symm v ∈ Ω
    · have hU := (e.isOpen_inter_preimage_symm hΩ).mem_nhds ⟨hv, hvΩ⟩
      have hGc : ContDiffAt ℝ ∞ (G ∘ e.symm) v :=
        ((contDiffOn_of_differentiableOn n _ _ (e.isOpen_inter_preimage_symm hΩ) (hG e he)).contDiffAt
          hU).restrict_scalars ℝ
      have hk : ContDiffAt ℝ ∞ (fun w => ((θ (δ * ψ (e.symm w)) : ℝ) : ℂ)) v :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp v
          (hθ.contDiffAt.comp v (contDiffAt_const.mul
            ((hψe e he).contDiffAt (e.open_target.mem_nhds hv))))
      exact hk.mul hGc
    · exact contDiffAt_const.congr_of_eventuallyEq ((hloc e he v hv).2 hvΩ)
  · intro x ξ
    obtain ⟨e, he, hx⟩ := exists_chart n X.z X.isLocalHomeomorph x
    have hzx : X.z x = e x := he hx
    have hv : X.z x ∈ e.target := by rw [hzx]; exact e.map_source hx
    have hsx : e.symm (X.z x) = x := by rw [hzx]; exact e.left_inv hx
    unfold dbarDot
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [db_eq_wdb n X.z e he j _ x hx, db_eq_wdb n X.z e he j _ x hx]
    by_cases hxΩ : x ∈ Ω
    · have hGd := (hloc e he _ hv).1 (by rw [hsx]; exact hxΩ)
      have hψd : DifferentiableAt ℝ (fun w => ψ (e.symm w)) (X.z x) :=
        ((hψe e he).contDiffAt (e.open_target.mem_nhds hv)).differentiableAt (by simp)
      have hkd : DifferentiableAt ℝ (fun t => θ (δ * t)) (ψ (e.symm (X.z x))) :=
        (hθd _).comp _ ((differentiableAt_id).const_mul δ)
      have hderiv : deriv (fun t => θ (δ * t)) (ψ (e.symm (X.z x))) =
          deriv θ (δ * ψ (e.symm (X.z x))) * δ := by
        have h1 : HasDerivAt (fun t : ℝ => δ * t) δ (ψ (e.symm (X.z x))) := by
          simpa using (hasDerivAt_id (ψ (e.symm (X.z x)))).const_mul δ
        exact ((hθd _).hasDerivAt.comp _ h1).deriv
      have h1 : ((fun y => (θ (δ * ψ y) : ℂ) * G y) ∘ e.symm) =
          fun w => (((fun t => θ (δ * t)) (ψ (e.symm w)) : ℝ) : ℂ) * (G ∘ e.symm) w := rfl
      have hkd' : DifferentiableAt ℝ (fun w => (((fun t => θ (δ * t)) (ψ (e.symm w)) : ℝ) : ℂ))
          (X.z x) := differentiableAt_ofReal (DifferentiableAt.comp (f := fun w => ψ (e.symm w)) (X.z x) hkd hψd)
      rw [h1, wdb_mul hkd' (hGd.restrictScalars ℝ), wdb_of_differentiableAt hGd,
        wdb_ofReal_comp (k := fun t => θ (δ * t)) (v := fun w => ψ (e.symm w)) hkd hψd, hderiv]
      have h2 : ((fun y => (ψ y : ℂ)) ∘ e.symm) = fun w => ((ψ (e.symm w) : ℝ) : ℂ) := rfl
      rw [h2]
      simp only [Function.comp_apply, hsx]
      push_cast
      ring
    · have hb : b < δ * ψ x := by
        by_contra h
        exact hxΩ (hsub _ (not_lt.1 h))
      rw [wdb_congr n j _ _ _ ((hloc e he _ hv).2 (by rw [hsx]; exact hxΩ)),
        ((hθzero _ hb).deriv_eq)]
      simp [wdb]

end GlobalTheory.L2Cutoff
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_finite_ext_twoTorsion_point_abelianVariety : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] (ga : K →+* Ω) (A : PolAV (Sp K)) (G : Over (Sp Ω)) [GrpObj G] (α : G.left ⟶ A.A.left), IsGrpPullback G A.A (spMap ga) α → ∀ x : 𝟙_ (Over (Sp Ω)) ⟶ G, x * x = 1 → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (l : K' →+* Ω) (y : Over.mk (spMap io) ⟶ A.A), io.Finite ∧ l.comp io = ga ∧ y * y = 1 ∧ spMap l ≫ y.left = x.left ≫ α := by
  first | exact @GlobalTheory.TwoTorsionDescent.exists_finite_ext_of_sq_eq_one | exact GlobalTheory.TwoTorsionDescent.exists_finite_ext_of_sq_eq_one | (intros; apply GlobalTheory.TwoTorsionDescent.exists_finite_ext_of_sq_eq_one <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.SemiAbAct

theorem exists_torus_quotient_act : ∀ (O : Type) [CommRing O] (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (act : OAct O G), IsSemiAbelian G → ∀ (T : TorusExtension G), letI := T.addCommGroup; letI := T.grpB; ∃ (actB : OAct O T.B) (actT : OAct O (splitTorus (Sp k) T.X)), (∀ a, T.q ≫ actB.act a = act.act a ≫ T.q) ∧ (∀ a, actT.act a ≫ T.i = T.i ≫ act.act a) := by
  intro O _ k _ _ G _ act _ T
  letI := T.addCommGroup
  letI := T.grpB
  have := T.free
  have := T.finite
  have := T.i_hom
  have := T.q_hom
  have := T.q_flat
  have := T.q_surjective
  have := T.q_quasiCompact
  have := T.isAbelian.proper
  have hmono : Mono T.i := T.isKernel.flip.mono_snd_of_mono
  have hepi : Epi T.q := GlobalTheory.SemiRigid.epi_of_fpqc T.q
  have hA : ∀ a, IsMonHom (act.act a) := act.hom

  have hT : ∀ a, T.i ≫ act.act a ≫ T.q = toUnit _ ≫ η := by
    intro a
    rw [GlobalTheory.SemiRigid.torus_const T.X T.B (T.i ≫ act.act a ≫ T.q)]
    simp [IsMonHom.one_hom_assoc, IsMonHom.one_hom]
  let fT : ∀ a, splitTorus (Sp k) T.X ⟶ splitTorus (Sp k) T.X := fun a ↦
    T.isKernel.lift (T.i ≫ act.act a) (toUnit _) (by rw [Category.assoc, hT])
  have hfT : ∀ a, fT a ≫ T.i = T.i ≫ act.act a := fun a ↦ T.isKernel.lift_fst _ _ _

  have hB : ∀ a, ∃ g, T.q ≫ g = act.act a ≫ T.q := fun a ↦
    GlobalTheory.SemiRigid.exists_desc T.q (act.act a ≫ T.q) fun Z x y h ↦ by
      obtain ⟨τ, hτ⟩ := GlobalTheory.SemiRigid.exists_eq_mul T.isKernel h
      rw [hτ, MonObj.mul_comp_assoc, MonObj.mul_comp, Category.assoc, Category.assoc, hT,
        comp_toUnit_assoc, ← Hom.one_def, _root_.one_mul, Category.assoc]
  choose fB hfB using hB
  have hmulT : ∀ a, IsMonHom (fT a) := fun a ↦ by
    refine ⟨?_, ?_⟩
    · rw [← cancel_mono T.i, Category.assoc, hfT, IsMonHom.one_hom_assoc, IsMonHom.one_hom,
        IsMonHom.one_hom]
    · rw [← cancel_mono T.i, Category.assoc, hfT, IsMonHom.mul_hom_assoc, IsMonHom.mul_hom,
        Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc,
        tensorHom_comp_tensorHom_assoc, hfT]
  have hmulB : ∀ a, IsMonHom (fB a) := fun a ↦ by
    refine ⟨?_, ?_⟩
    · have h := IsMonHom.one_hom (f := T.q)
      rw [← h, Category.assoc, hfB, IsMonHom.one_hom_assoc, h]
    · have hqq : Epi (T.q ⊗ₘ T.q) := by
        have : Epi (T.q ▷ G) := GlobalTheory.SemiRigid.epi_of_fpqc _
        have : Epi (T.q ▷ T.B) := GlobalTheory.SemiRigid.epi_of_fpqc _
        have : Epi (lift (snd T.B G) (fst T.B G)) :=
          epi_of_epi_fac (h := 𝟙 _) (f := lift (snd G T.B) (fst G T.B)) (by apply CartesianMonoidalCategory.hom_ext <;> simp)
        have : Epi (lift (snd T.B T.B) (fst T.B T.B)) :=
          epi_of_epi_fac (h := 𝟙 _) (f := lift (snd T.B T.B) (fst T.B T.B)) (by apply CartesianMonoidalCategory.hom_ext <;> simp)
        have hs : T.B ◁ T.q =
            lift (snd T.B G) (fst T.B G) ≫ (T.q ▷ T.B) ≫ lift (snd T.B T.B) (fst T.B T.B) := by
          apply CartesianMonoidalCategory.hom_ext <;> simp
        rw [MonoidalCategory.tensorHom_def, hs]
        infer_instance
      rw [← cancel_epi (T.q ⊗ₘ T.q), ← IsMonHom.mul_hom_assoc, hfB, IsMonHom.mul_hom_assoc,
        IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc, hfB]
  refine ⟨⟨fB, hmulB, ?_, ?_, ?_⟩, ⟨fT, hmulT, ?_, ?_, ?_⟩, hfB, hfT⟩
  · rw [← cancel_epi T.q, hfB, act.one, Category.comp_id, Category.id_comp]
  · intro a b
    rw [← cancel_epi T.q, hfB, act.mul, Category.assoc, ← hfB, reassoc_of% hfB]
  · intro a b
    rw [← cancel_epi T.q, hfB, MonObj.comp_mul, hfB, hfB, act.add, MonObj.mul_comp]
  · rw [← cancel_mono T.i, hfT, act.one, Category.comp_id, Category.id_comp]
  · intro a b
    rw [← cancel_mono T.i, hfT, act.mul, Category.assoc, hfT, reassoc_of% hfT]
  · intro a b
    rw [← cancel_mono T.i, hfT, MonObj.mul_comp, hfT, hfT, act.add, MonObj.comp_mul]

end GlobalTheory.SemiAbAct
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory.LocalTangent

open IsLocalRing

variable {k S : Type} [Field k] [CommRing S] [IsLocalRing S] [Algebra k S]

theorem algebraMap_mem_maximalIdeal_iff (c : k) :
    algebraMap k S c ∈ maximalIdeal S ↔ c = 0 := by
  constructor
  · intro h
    by_contra hc
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h
    exact h ((isUnit_iff_ne_zero.mpr hc).map (algebraMap k S))
  · rintro rfl
    simp

theorem residue_eq {π : S → k} (hπ : ∀ s, s - algebraMap k S (π s) ∈ maximalIdeal S)
    (s : S) (c : k) (h : s - algebraMap k S c ∈ maximalIdeal S) : π s = c := by
  have hm : algebraMap k S (π s - c) ∈ maximalIdeal S := by
    have := sub_mem h (hπ s)
    rw [map_sub]; convert this using 1; ring
  rw [algebraMap_mem_maximalIdeal_iff] at hm
  exact sub_eq_zero.mp hm

def tangentHom (π : S → k) (hπ : ∀ s, s - algebraMap k S (π s) ∈ maximalIdeal S)
    (f : S →ₗ[k] k) (hf1 : f 1 = 0) (hf2 : ∀ y ∈ maximalIdeal S ^ 2, f y = 0) :
    S →ₐ[k] DualNumber k where
  toFun s := TrivSqZeroExt.inl (π s) + TrivSqZeroExt.inr (f s)
  map_one' := by
    have : π 1 = 1 := residue_eq hπ 1 1 (by simp)
    ext <;> simp [this, hf1]
  map_mul' s t := by
    have hm : π (s * t) = π s * π t := residue_eq hπ _ _ (by
      rw [map_mul]
      convert add_mem (Ideal.mul_mem_right t _ (hπ s)) (Ideal.mul_mem_left _ (algebraMap k S (π s)) (hπ t))
        using 1
      ring)
    have hfa : ∀ c, f (algebraMap k S c) = 0 := by
      intro c; rw [Algebra.algebraMap_eq_smul_one, map_smul, hf1, smul_zero]
    have e : s * t = algebraMap k S (π s * π t) + π s • (t - algebraMap k S (π t)) +
        π t • (s - algebraMap k S (π s)) +
        (s - algebraMap k S (π s)) * (t - algebraMap k S (π t)) := by
      simp only [Algebra.smul_def, map_mul]; ring
    have hf : f (s * t) = π s * f t + π t * f s := by
      have huv := hf2 _ (by rw [pow_two]; exact Ideal.mul_mem_mul (hπ s) (hπ t))
      rw [e, map_add (f := _), map_add (f := _), map_add (f := _), map_smul, map_smul, huv, map_sub, map_sub, hfa, hfa, hfa]
      simp
    ext <;> simp [hm, hf] <;> ring
  map_zero' := by
    have : π 0 = 0 := residue_eq hπ 0 0 (by simp)
    ext <;> simp [this]
  map_add' s t := by
    have : π (s + t) = π s + π t := residue_eq hπ _ _ (by
      rw [map_add (f := _)]; convert add_mem (hπ s) (hπ t) using 1; ring)
    ext <;> simp [this]
  commutes' c := by
    have : π (algebraMap k S c) = c := residue_eq hπ _ _ (by simp)
    have h0 : f (algebraMap k S c) = 0 := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, hf1, smul_zero]
    ext <;> simp [this, h0, TrivSqZeroExt.algebraMap_eq_inl]

theorem tangentHom_snd (π : S → k) (hπ : ∀ s, s - algebraMap k S (π s) ∈ maximalIdeal S)
    (f : S →ₗ[k] k) (hf1 : f 1 = 0) (hf2 : ∀ y ∈ maximalIdeal S ^ 2, f y = 0) (s : S) :
    (tangentHom π hπ f hf1 hf2 s).snd = f s := by
  simp [tangentHom]

theorem epsScaleR_snd (c : k) (x : DualNumber k) : (epsScaleR c x).snd = c * x.snd := by
  simp [epsScaleR]

end GlobalTheory.LocalTangent

namespace GlobalTheory.LocalTangent

open IsLocalRing

variable {k S : Type} [Field k] [CommRing S] [IsLocalRing S] [Algebra k S]

theorem exists_form {a b : S} (ha : a ∈ maximalIdeal S) (hb : b ∈ maximalIdeal S)
    (h : ∀ c : k, a - c • b ∉ maximalIdeal S ^ 2) :
    ∃ f : S →ₗ[k] k, f 1 = 0 ∧ (∀ y ∈ maximalIdeal S ^ 2, f y = 0) ∧ f b = 0 ∧ f a = 1 := by
  let P : Submodule k S := Submodule.span k {1, b} ⊔ (maximalIdeal S ^ 2).restrictScalars k
  have haP : a ∉ P := by
    intro hP
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hP
    obtain ⟨l, r, rfl⟩ := Submodule.mem_span_pair.mp hy
    have hz2 : z ∈ maximalIdeal S ^ 2 := hz
    have hz' : z ∈ maximalIdeal S := Ideal.pow_le_self two_ne_zero hz2
    have hl : l = 0 := by
      rw [← algebraMap_mem_maximalIdeal_iff (S := S)]
      have e : algebraMap k S l = a - r • b - z := by
        rw [← hyz, Algebra.algebraMap_eq_smul_one]; abel
      rw [e]
      exact sub_mem (sub_mem ha (Submodule.smul_of_tower_mem _ r hb)) hz'
    apply h r
    have e : a - r • b = z := by rw [← hyz, hl]; simp
    rw [e]; exact hz2
  obtain ⟨g, hga, hgP⟩ := Submodule.exists_dual_map_eq_bot_of_notMem haP (by infer_instance)
  have hg0 : ∀ y ∈ P, g y = 0 := fun y hy => by
    have : g y ∈ P.map g := Submodule.mem_map_of_mem hy
    rw [hgP] at this; exact (Submodule.mem_bot k).mp this
  refine ⟨(g a)⁻¹ • g, ?_, ?_, ?_, ?_⟩
  · simp [hg0 1 (Submodule.mem_sup_left (Submodule.subset_span (by simp)))]
  · intro y hy
    simp [hg0 y (Submodule.mem_sup_right hy)]
  · simp [hg0 b (Submodule.mem_sup_left (Submodule.subset_span (by simp)))]
  · simp [hga]

theorem pair_dependent
    (h1 : ∀ a : S, ∃ c : k, a - algebraMap k S c ∈ maximalIdeal S)
    (h3 : ∀ ψ₁ ψ₂ : S →ₐ[k] DualNumber k, ∃ c : k,
      (ψ₁ : S →+* DualNumber k) = (epsScaleR c).comp (ψ₂ : S →+* DualNumber k) ∨
      (ψ₂ : S →+* DualNumber k) = (epsScaleR c).comp (ψ₁ : S →+* DualNumber k))
    {a b : S} (ha : a ∈ maximalIdeal S) (hb : b ∈ maximalIdeal S) :
    ∃ c : k, a - c • b ∈ maximalIdeal S ^ 2 ∨ b - c • a ∈ maximalIdeal S ^ 2 := by
  by_contra hne
  push_neg at hne
  choose π hπ using h1
  obtain ⟨f₁, h11, h12, h13, h14⟩ := exists_form ha hb (fun c => (hne c).1)
  obtain ⟨f₂, h21, h22, h23, h24⟩ := exists_form hb ha (fun c => (hne c).2)
  obtain ⟨c, hc | hc⟩ := h3 (tangentHom π hπ f₁ h11 h12) (tangentHom π hπ f₂ h21 h22)
  · have := congrArg (fun φ : S →+* DualNumber k => (φ a).snd) hc
    simp only [RingHom.coe_coe, RingHom.comp_apply, epsScaleR_snd, tangentHom_snd] at this
    rw [h14, h23, mul_zero] at this
    exact one_ne_zero this
  · have := congrArg (fun φ : S →+* DualNumber k => (φ b).snd) hc
    simp only [RingHom.coe_coe, RingHom.comp_apply, epsScaleR_snd, tangentHom_snd] at this
    rw [h24, h13, mul_zero] at this
    exact one_ne_zero this

theorem maximalIdeal_isPrincipal : ∀ (k : Type) [Field k] (S : Type) [CommRing S] [IsLocalRing S] [Algebra k S],
    (∀ a : S, ∃ c : k, a - algebraMap k S c ∈ IsLocalRing.maximalIdeal S) →
    IsNilpotent (IsLocalRing.maximalIdeal S) →
    (∀ ψ₁ ψ₂ : S →ₐ[k] DualNumber k, ∃ c : k,
      (ψ₁ : S →+* DualNumber k) = (epsScaleR c).comp (ψ₂ : S →+* DualNumber k) ∨
      (ψ₂ : S →+* DualNumber k) = (epsScaleR c).comp (ψ₁ : S →+* DualNumber k)) →
    (IsLocalRing.maximalIdeal S).IsPrincipal := by
  intro k _ S _ _ _ h1 hnil h3
  set m := maximalIdeal S with hm
  have hx : ∃ x ∈ m, m ≤ Ideal.span {x} ⊔ m ^ 2 := by
    by_cases hle : m ≤ m ^ 2
    · exact ⟨0, zero_mem _, le_sup_of_le_right hle⟩
    · obtain ⟨x, hxm, hx2⟩ := Set.not_subset.mp hle
      refine ⟨x, hxm, fun a ha => ?_⟩
      have key : ∃ c : k, a - c • x ∈ m ^ 2 := by
        obtain ⟨c, hc | hc⟩ := pair_dependent h1 h3 ha hxm
        · exact ⟨c, hc⟩
        · have hc0 : c ≠ 0 := by
            rintro rfl; apply hx2; simpa using hc
          refine ⟨c⁻¹, ?_⟩
          have e : a - c⁻¹ • x = (-c⁻¹) • (x - c • a) := by
            rw [smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hc0, neg_smul, neg_smul, one_smul]; abel
          rw [e]; exact Submodule.smul_of_tower_mem _ _ hc
      obtain ⟨c, hc⟩ := key
      have e : a = c • x + (a - c • x) := by abel
      rw [e]
      refine Submodule.add_mem_sup ?_ hc
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self x)
  obtain ⟨x, hxm, hle⟩ := hx
  set I := Ideal.span {x}
  have hstep : ∀ n : ℕ, m ≤ I ⊔ m ^ (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc m ≤ I ⊔ m ^ 2 := hle
        _ = I ⊔ m * m := by rw [pow_two]
        _ ≤ I ⊔ m * (I ⊔ m ^ (n + 1)) := sup_le_sup_left (Ideal.mul_mono_right ih) _
        _ = I ⊔ (m * I ⊔ m ^ (n + 1 + 1)) := by rw [Ideal.mul_sup, ← pow_succ']
        _ ≤ I ⊔ m ^ (n + 1 + 1) := sup_le (le_sup_left) (sup_le (le_sup_of_le_left Ideal.mul_le_right) le_sup_right)
  obtain ⟨n, hn⟩ := hnil
  have hmI : m ≤ I := by
    have := hstep n
    rwa [pow_succ, hn, zero_mul, Ideal.zero_eq_bot, sup_bot_eq] at this
  have hIm : I ≤ m := (Ideal.span_singleton_le_iff_mem _).mpr hxm
  exact ⟨⟨x, le_antisymm hmI hIm⟩⟩

end GlobalTheory.LocalTangent
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isColimit_spec_quotient_complementary_idempotents : ∀ (R : Type) [CommRing R] (e e' : R), IsIdempotentElem e → e + e' = 1 → Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk (spMap (Ideal.Quotient.mk (Ideal.span {e}))) (spMap (Ideal.Quotient.mk (Ideal.span {e'}))))) := by
  first | exact @GlobalTheory.specQuotIdemCoprod | exact GlobalTheory.specQuotIdemCoprod | (intros; apply GlobalTheory.specQuotIdemCoprod <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isPullback_spMap_quotient_span_baseChange : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀) (f : R) (ρ : R ⧸ Ideal.span {f} →+* R₀ ⧸ Ideal.span {π f}), ρ.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp π → IsPullback (spMap (Ideal.Quotient.mk (Ideal.span {π f}))) (spMap ρ) (spMap π) (spMap (Ideal.Quotient.mk (Ideal.span {f}))) := by
  first | exact @GlobalTheory.QuotBaseChange.isPullback_spMap_quot | exact GlobalTheory.QuotBaseChange.isPullback_spMap_quot | (intros; apply GlobalTheory.QuotBaseChange.isPullback_spMap_quot <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_opens_preimage_eq_of_sqZero_augmentation : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀), (∀ y y', q y = 0 → q y' = 0 → y * y' = 0) → ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀), IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)) → ∀ W : X₁.Opens, ∃ W₀ : X₀.Opens, pr ⁻¹ᵁ W₀ = W := by
  first | exact @GlobalTheory.LiftSys.exists_opens_preimage_eq_of_sqZero_aug | exact GlobalTheory.LiftSys.exists_opens_preimage_eq_of_sqZero_aug | (intros; apply GlobalTheory.LiftSys.exists_opens_preimage_eq_of_sqZero_aug <;> assumption)
end
