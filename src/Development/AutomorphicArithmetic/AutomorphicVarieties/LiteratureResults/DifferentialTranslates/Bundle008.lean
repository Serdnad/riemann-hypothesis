module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct ContDiff

namespace UpperTheory.V.Lit.Dr

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

private theorem sub_smooth {f : X → HV E a} {x : X} (h : ContDiffAt ℝ ∞ (fun y => (f y).1) x) :
    ContDiffAt ℝ ∞ f x := by
  obtain ⟨r, hr⟩ := (HV E a).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  have e : f = fun y => LinearMap.toContinuousLinearMap r (f y).1 :=
    funext fun y => (LinearMap.congr_fun hr (f y)).symm
  rw [e]
  exact (LinearMap.toContinuousLinearMap r).contDiff.contDiffAt.comp x h

private theorem inv_smooth {τ : X → GL (Fin a) (Cinf E)} {x : X}
    (h : ContDiffAt ℝ ∞ (fun y => toL (τ y).val) x) (i j : Fin a) :
    ContDiffAt ℝ ∞ (fun y => (τ y)⁻¹.val i j) x := by
  have hd : ContDiffAt ℝ ∞ (fun y => (τ y).val.det) x := (contDiff_det (E := E) (a := a)).contDiffAt.comp x h
  have hu : IsUnit (τ x).val.det := (Matrix.isUnit_iff_isUnit_det _).1 (τ x).isUnit
  have hi : ContDiffAt ℝ ∞ (fun y => Ring.inverse (τ y).val.det) x := by
    have := contDiffAt_ringInverse ℝ (n := ∞) hu.unit
    rw [hu.unit_spec] at this
    exact this.comp x hd
  have ha : ContDiffAt ℝ ∞ (fun y => (τ y).val.adjugate i j) x := by
    simp only [Matrix.adjugate_apply]
    refine (contDiff_det (E := E) (a := a)).contDiffAt.comp x
      (f := fun y => toL ((τ y).val.updateRow j (Pi.single i 1))) ?_
    refine contDiffAt_pi.2 fun k => ?_
    by_cases hk : k = j
    · subst hk
      have : (fun y => toL ((τ y).val.updateRow k (Pi.single i 1)) k) = fun _ => Pi.single i 1 :=
        funext fun y => Matrix.updateRow_self
      rw [this]; exact contDiffAt_const
    · have : (fun y => toL ((τ y).val.updateRow j (Pi.single i 1)) k) = fun y => toL (τ y).val k :=
        funext fun y => Matrix.updateRow_ne hk
      rw [this]; exact contDiffAt_pi.1 h k
  have e : (fun y => (τ y)⁻¹.val i j) = fun y => Ring.inverse (τ y).val.det * (τ y).val.adjugate i j := by
    funext y
    rw [Matrix.coe_units_inv, Matrix.inv_def]; rfl
  rw [e]
  exact hi.mul ha

private theorem sand_smooth {σ : X → GL (Fin a) (Cinf E)} {x : X}
    (h : ∀ i j, ContDiffAt ℝ ∞ (fun y => (σ y).val i j) x) (v : HV E a) :
    ContDiffAt ℝ ∞ (fun y => sand (σ y) v) x := by
  refine sub_smooth (contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_)
  have e : (fun y => (sand (σ y) v).1 i j) =
      fun y => ∑ l, (∑ k, (σ y).val i k * v.1 k l) * star ((σ y).val j l) := by
    funext y
    change ((σ y).val * Matrix.of v.1 * star (σ y).val) i j = _
    simp [Matrix.mul_apply]
  rw [e]
  refine ContDiffAt.sum fun l _ => (ContDiffAt.sum fun k _ => (h i k).mul contDiffAt_const).mul ?_
  exact (starL' ℝ : Cinf E ≃L[ℝ] Cinf E).contDiff.contDiffAt.comp x (h j l)

theorem corrSmooth : CorrSmooth := by
  intro E _ _ _ a U Ξ q α w hc s p₀ hp₀
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨τ, hτ, hs⟩ := locSec E a p₀ hp₀
  refine ContDiffAt.contDiffWithinAt ?_
  set f : HV E a → HV E a [⋀^Fin q]→L[ℝ] (Fin Ξ.d → ℂ) := fun p =>
    (w (x : GL (Fin a) (Af E) ⧸ U) p).compContinuousLinearMap ((2 : ℝ) • sand (τ p)) with hf
  have hfs : ContDiffAt ℝ ∞ f p₀ := by
    refine altSmooth _ _ _ q f p₀ fun Y => ?_
    have h1 : ContDiffAt ℝ ∞ (fun p => Ξ.mat (τ p) *ᵥ
        ev (α fun i => hv.symm (Y i)) (infGL E a (τ p) * finGL E a x)) p₀ := by
      refine contDiffAt_pi.2 fun i => ?_
      simp only [Matrix.mulVec, dotProduct]
      refine ContDiffAt.sum fun j _ => ContDiffAt.mul ?_ ?_
      · have := (((matSmooth E a Ξ i j).1).contDiffAt
          (isOpen_invSet.mem_nhds (val_mem_invSet (τ p₀)))).comp p₀ hτ
        simpa only [Function.comp_def, extGL_val] using this
      · have := (contDiffAt_chart ((evFacts E a Ξ.d).2.1 (α fun i => hv.symm (Y i)) j) (finGL E a x)
          (val_mem_invSet (τ p₀))).comp p₀ hτ
        simpa only [Function.comp_def, chart_val, infGL_comm] using this
    refine h1.congr_of_eventuallyEq (hs.mono fun p hp => ?_)
    have := hc (τ p) x fun i => hv.symm (Y i)
    simp only [hp, LinearEquiv.apply_symm_apply] at this
    exact this
  refine altSmooth _ _ _ q _ p₀ fun v => ?_
  have h2 := applySmooth _ _ _ q f (fun i p => (2 : ℝ)⁻¹ • sand (τ p)⁻¹ (v i)) p₀ hfs
    fun i => (sand_smooth (σ := fun p => (τ p)⁻¹) (inv_smooth hτ) (v i)).const_smul _
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun p => ?_)
  change w _ p v = w _ p _
  congr 1
  funext i
  have : sand (τ p) (sand (τ p)⁻¹ (v i)) = v i := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  simp [this, smul_smul]

end UpperTheory.V.Lit.Dr
end
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct ContDiff

namespace UpperTheory.V.Lit.Dr

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private def sandL (Z : HV E a) (x : Lie E a) : HV E a :=
  ⟨toL (Matrix.of x * Matrix.of Z.1 * star (Matrix.of x)), IsSelfAdjoint.conjugate Z.2 (Matrix.of x)⟩

private theorem contDiff_sandL (Z : HV E a) : ContDiff ℝ ∞ (sandL Z) := by
  obtain ⟨π, hπ⟩ := (HV E a).subtype.exists_leftInverse_of_injective (HV E a).ker_subtype
  have h1 : ContDiff ℝ ∞ fun x : Lie E a => (sandL Z x).1 := by
    refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
    have e : (fun x : Lie E a => (sandL Z x).1 i j) =
        fun x : Lie E a => ∑ k, (∑ l, x i l * Z.1 l k) * star (x j k) := by
      funext x
      simp only [sandL, Matrix.of_symm_apply, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply]
    rw [e]
    have hs : ContDiff ℝ ∞ fun z : Cinf E => star z := (starL' ℝ (A := Cinf E)).contDiff
    refine ContDiff.sum fun k _ => ContDiff.mul (ContDiff.sum fun l _ => ContDiff.mul ?_ contDiff_const) (hs.comp ?_)
    all_goals fun_prop
  have e : sandL Z = fun x => LinearMap.toContinuousLinearMap π (sandL Z x).1 :=
    funext fun x => (LinearMap.congr_fun hπ _).symm
  rw [e]
  exact (LinearMap.toContinuousLinearMap π).contDiff.comp h1

end UpperTheory.V.Lit.Dr

open UpperTheory.V.Lit.Dr

theorem UpperTheory.V.Lit.Dr.bwdSmooth :
    BwdSmooth := by
  intro E _ _ _ a ho U Ξ q w X j g x hx
  let y := GeneralLinearGroup.map (pInf E) g
  let s : GL (Fin a) (Af E) ⧸ U := QuotientGroup.mk (GeneralLinearGroup.map (pFin E) g)
  let L : Lie E a →L[ℝ] Lie E a := LinearMap.toContinuousLinearMap
    (LinearMap.mulLeft ℝ y.val : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] Matrix (Fin a) (Fin a) (Cinf E))
  have hL : ∀ u : GL (Fin a) (Cinf E), L (toL u.val) = toL (y * u).val := fun _ => rfl
  have hS : ∀ (Z : HV E a) (u : GL (Fin a) (Cinf E)), sandL Z (toL u.val) = sand u Z := fun _ _ => rfl
  obtain ⟨u, hu⟩ := hx
  obtain rfl : x = toL u.val := hu.symm
  have hSL : ∀ Z : HV E a, ContDiffAt ℝ ∞ (fun z => sandL Z (L z)) (toL u.val) := fun Z =>
    ((contDiff_sandL Z).comp L.contDiff).contDiffAt
  have hw : ContDiffAt ℝ ∞ (fun z => w.1 s (sandL (hOne E a) (L z))) (toL u.val) := by
    refine ContDiffAt.comp (g := w.1 s) _ (Geo.contDiffAt_Om w s ?_) (hSL _)
    rw [hL, hS]
    exact sand_mem_cone _ hOne_mem_cone
  have hv' := applySmooth _ _ _ q _ (fun i z => (2 : ℝ) • sandL (hv (X i)) (L z)) _ hw fun i => (hSL _).const_smul _
  have hm : ∀ k, ContDiffAt ℝ ∞ (fun z => extGL (fun t => Ξ.mat t⁻¹ j k) (L z)) (toL u.val) := fun k => by
    refine ContDiffAt.comp (g := extGL fun t => Ξ.mat t⁻¹ j k) _ ?_ L.contDiff.contDiffAt
    rw [hL]
    exact (matSmooth E a Ξ j k).2.contDiffAt (isOpen_invSet.mem_nhds (val_mem_invSet _))
  have hall := ContDiffAt.sum (s := Finset.univ) fun k _ => (hm k).mul (contDiffAt_pi.1 hv' k)
  refine (hall.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [isOpen_invSet.mem_nhds (val_mem_invSet u)] with z hz
  obtain ⟨v, hv⟩ := hz
  obtain rfl : z = toL v.val := hv.symm
  rw [chart_val]
  simp only [map_mul, pInf_infGL, pFin_infGL, mul_one, hL, hS, extGL_val]
  rfl
end
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private def jor (X : Herm E a) : HV E a →L[ℝ] HV E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => ⟨toL (X.1 * Matrix.of v.1 + Matrix.of v.1 * X.1), by
        have hX : star X.1 = X.1 := X.2
        have hv : star (Matrix.of v.1) = Matrix.of v.1 := v.2
        change star (X.1 * Matrix.of v.1 + Matrix.of v.1 * X.1) = X.1 * Matrix.of v.1 + Matrix.of v.1 * X.1
        rw [star_add, star_mul, star_mul, hX, hv, add_comm]⟩
      map_add' := fun p p' => Subtype.ext (by
        change X.1 * (Matrix.of p.1 + Matrix.of p'.1) + (Matrix.of p.1 + Matrix.of p'.1) * X.1 =
          (X.1 * Matrix.of p.1 + Matrix.of p.1 * X.1) + (X.1 * Matrix.of p'.1 + Matrix.of p'.1 * X.1)
        rw [mul_add, add_mul]; abel)
      map_smul' := fun c p => Subtype.ext (by
        change X.1 * (c • Matrix.of p.1) + (c • Matrix.of p.1) * X.1 = c • (X.1 * Matrix.of p.1 + Matrix.of p.1 * X.1)
        rw [mul_smul_comm, smul_mul_assoc, smul_add]) }

private theorem jor_one (X : Herm E a) : jor X (hOne E a) = (2 : ℝ) • hv X := Subtype.ext (by
  change X.1 * 1 + 1 * X.1 = (2 : ℝ) • X.1
  rw [mul_one, one_mul, two_smul])

private theorem jor_comm (X Y : Herm E a) : jor X (hv Y) = jor Y (hv X) := Subtype.ext (by
  change X.1 * Y.1 + Y.1 * X.1 = Y.1 * X.1 + X.1 * Y.1
  rw [add_comm])

private theorem exists_curve (X : Herm E a) : ∃ c : ℝ → GL (Fin a) (Cinf E), c 0 = 1 ∧
    HasDerivAt (fun t => toL (c t).val) (toL X.1) 0 ∧
    ∀ v : HV E a, HasDerivAt (fun t => sand (c t) v) (jor X v) 0 := by
  classical
  have hX : star X.1 = X.1 := X.2
  have hu : ∀ᶠ t : ℝ in nhds 0, IsUnit (1 + t • X.1) := by
    have hc : Continuous fun t : ℝ => (1 + t • X.1).det :=
      (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
    have h : ∀ᶠ t : ℝ in nhds 0, IsUnit (1 + t • X.1).det :=
      hc.continuousAt.eventually (Units.isOpen.mem_nhds (by simp))
    exact h.mono fun t ht => (Matrix.isUnit_iff_isUnit_det _).2 ht
  let c : ℝ → GL (Fin a) (Cinf E) := fun t => if h : IsUnit (1 + t • X.1) then h.unit else 1
  have hc : ∀ᶠ t : ℝ in nhds 0, (c t).val = 1 + t • X.1 :=
    hu.mono fun t ht => by simp only [c, dif_pos ht, IsUnit.unit_spec]
  refine ⟨c, Units.ext (by simpa using hc.self_of_nhds), ?_, fun v => ?_⟩
  · have h := (((hasDerivAt_id (0 : ℝ)).smul_const (toL X.1)).const_add (toL (1 : Matrix (Fin a) (Fin a) (Cinf E))))
    rw [one_smul] at h
    exact h.congr_of_eventuallyEq (hc.mono fun t ht => by
      beta_reduce
      rw [ht]; rfl)
  · let B : HV E a := ⟨toL (X.1 * Matrix.of v.1 * star X.1), IsSelfAdjoint.conjugate v.2 X.1⟩
    have h := (((hasDerivAt_id (0 : ℝ)).smul_const (jor X v)).const_add v).add
      (((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))).smul_const B)
    simp only [id, mul_zero, zero_mul, add_zero, zero_smul, one_smul] at h
    refine h.congr_of_eventuallyEq (hc.mono fun t ht => Subtype.ext ?_)
    change (c t).val * Matrix.of v.1 * star (c t).val =
      Matrix.of v.1 + t • (X.1 * Matrix.of v.1 + Matrix.of v.1 * X.1) + (t * t) • (X.1 * Matrix.of v.1 * star X.1)
    rw [ht, star_add, star_one, star_smul, star_trivial t, hX]
    simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
    abel

theorem corrD : CorrD := by
  intro E _ _ _ a ho U Ξ q α w h g x X
  choose c hc0 hc1 hc2 using fun i => exists_curve (X i)
  have hp : sand g (hOne E a) ∈ (geo ho U Ξ).Y := ⟨g, rfl⟩
  have hinv : ∀ v : HV E a, sand g⁻¹ (sand g v) = v := fun v => by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  let L : Fin (q + 1) → HV E a →L[ℝ] HV E a := fun i => (sand g).comp ((jor (X i)).comp (sand g⁻¹))
  have hL : ∀ i v, L i (sand g v) = sand g (jor (X i) v) := fun i v => by
    simp only [L, ContinuousLinearMap.comp_apply, hinv]
  have hL1 : ∀ i, L i (sand g (hOne E a)) = (2 : ℝ) • sand g (hv (X i)) := fun i => by
    rw [hL, jor_one, map_smul]
  have hL2 : ∀ i j, L j (L i (sand g (hOne E a))) = (2 : ℝ) • sand g (jor (X i) (hv (X j))) := fun i j => by
    rw [hL1, map_smul, hL, jor_comm]
  have hd : ∀ i v, HasDerivAt (fun t => sand (g * c i t) v) (sand g (jor (X i) v)) 0 := fun i v => by
    have h1 := (sand g).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hc2 i v)
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    beta_reduce
    rw [map_mul]; rfl
  have key := altSym (HV E a) (Fin Ξ.d → ℂ) q (w.1 (x : GL (Fin a) (Af E) ⧸ U)) (sand g (hOne E a)) L
    (fun i t => sand (g * c i t) (hOne E a)) (fun i j t => (2 : ℝ) • sand (g * c i t) (hv (X j)))
    (fun i => Ξ.mat g *ᵥ ev (smLie Ξ (toL (X i).1) (α (i.removeNth X))) (infGL E a g * finGL E a x))
    (Geo.differentiableAt_Om w _ hp)
    (fun i j => by rw [hL2, hL2, jor_comm])
    (fun i => ⟨by rw [hc0, mul_one], by rw [hL]; exact hd i _⟩)
    (fun i j => ⟨by rw [hc0, mul_one, hL1], by rw [hL2]; exact (hd i _).const_smul (2 : ℝ)⟩)
    (fun i => by
      refine (evDeriv E a Ξ (α (i.removeNth X)) g x (c i) _ (hc0 i) (hc1 i)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun t => ?_)
      exact h (g * c i t) x (i.removeNth X))
  rw [Geo.dOm_apply _ w _ hp]
  simp only [hL1] at key

  rw [key, dCo_apply, map_sum, Finset.sum_apply, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, Pi.smul_apply, Matrix.mulVec_smul]

end UpperTheory.V.Lit.Dr
end
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

private theorem cont_multi {V F ι : Type} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : (ι → V) →ₘₗ[ℝ] F) : Continuous f := by
  classical
  let b := Module.finBasis ℝ V
  have h : (f : (ι → V) → F) = fun v => ∑ r : ι → Fin (Module.finrank ℝ V),
      (∏ i, b.coord (r i) (v i)) • f fun i => b (r i) := by
    funext v
    have e : v = fun i => ∑ j, b.coord j (v i) • b j := funext fun i => (b.sum_repr (v i)).symm
    conv_lhs => rw [e]

    rw [f.map_sum]
    exact Finset.sum_congr rfl fun r _ => f.map_smul_univ _ _
  rw [h]
  exact continuous_finsetSum _ fun r _ => (continuous_finsetProd _ fun i _ =>
    (b.coord (r i)).continuous_of_finiteDimensional.comp (continuous_apply i)).smul continuous_const

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private def back (g : GL (Fin a) (Cinf E)) : HV E a →ₗ[ℝ] Herm E a :=
  (hv.symm : HV E a ≃ₗ[ℝ] Herm E a).toLinearMap ∘ₗ ((2⁻¹ : ℝ) • (sand g⁻¹).toLinearMap)

private theorem back_apply (g : GL (Fin a) (Cinf E)) (v : HV E a) :
    back g v = hv.symm ((2⁻¹ : ℝ) • sand g⁻¹ v) := rfl

private theorem sand_sand (g h : GL (Fin a) (Cinf E)) (v : HV E a) : sand g (sand h v) = sand (g * h) v := by
  rw [map_mul]; rfl

private theorem back_sand (g : GL (Fin a) (Cinf E)) (X : Herm E a) : back g ((2 : ℝ) • sand g (hv X)) = X := by
  rw [back_apply, map_smul (sand g⁻¹), smul_smul, sand_sand, inv_mul_cancel, map_one, inv_mul_cancel₀ two_ne_zero, one_smul]
  exact hv.symm_apply_apply X

private theorem adHerm_back (g : GL (Fin a) (Cinf E)) (k : Kinf E a) (v : HV E a) :
    adHerm k (back (g * Unitary.toUnits k) v) = back g v := by
  have h : ∀ y : HV E a, adHerm k (hv.symm y) = hv.symm (sand (Unitary.toUnits k) y) := fun _ => rfl
  rw [back_apply, back_apply, h, map_smul, sand_sand, _root_.mul_inv_rev, mul_inv_cancel_left]

private theorem exists_unitary {g h : GL (Fin a) (Cinf E)} (e : sand g (hOne E a) = sand h (hOne E a)) :
    ∃ k : Kinf E a, h = g * Unitary.toUnits k := by
  have h1 : sand (g⁻¹ * h) (hOne E a) = hOne E a := by
    rw [← sand_sand, ← e, sand_sand, inv_mul_cancel, map_one]; rfl
  have h2 : (g⁻¹ * h).val * star (g⁻¹ * h).val = 1 := by
    have h3 := sand_val (g⁻¹ * h) (hOne E a)
    rw [h1, hOne_val, mul_one] at h3
    exact h3.symm
  refine ⟨⟨(g⁻¹ * h).val, Matrix.mem_unitaryGroup_iff.2 h2⟩, ?_⟩
  rw [← inv_mul_eq_iff_eq_mul]
  exact Units.ext rfl

variable [_root_.NumberField.IsTotallyComplex E] (Ξ : AlgRep E a) {q : ℕ}
  (α : Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)))

private def alt (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) : HV E a [⋀^Fin q]→ₗ[ℝ] (Fin Ξ.d → ℂ) :=
  ((Matrix.toLin' (Ξ.mat g) ∘ₗ (LinearMap.proj (infGL E a g * finGL E a x) : (GA E a → Fin Ξ.d → ℂ) →ₗ[ℂ] (Fin Ξ.d → ℂ)) ∘ₗ
    ev).restrictScalars ℝ).compAlternatingMap (α.compLinearMap (back g))

private theorem alt_apply (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) (v : Fin q → HV E a) :
    alt Ξ α g x v = Ξ.mat g *ᵥ ev (α fun i => back g (v i)) (infGL E a g * finGL E a x) := rfl

private def altL (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) : HV E a [⋀^Fin q]→L[ℝ] (Fin Ξ.d → ℂ) :=
  { alt Ξ α g x with cont := cont_multi (alt Ξ α g x).toMultilinearMap }

private theorem altL_apply (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) (v : Fin q → HV E a) :
    altL Ξ α g x v = alt Ξ α g x v := rfl

private theorem alt_cpt (hα : IsCochain (smK Ξ) α) (g : GL (Fin a) (Cinf E)) (k : Kinf E a) (x : GL (Fin a) (Af E))
    (v : Fin q → HV E a) : alt Ξ α (g * Unitary.toUnits k) x v = alt Ξ α g x v := by
  have h := hα k fun i => back (g * Unitary.toUnits k) (v i)
  simp only [adHerm_back] at h
  rw [alt_apply, alt_apply, h, evK, Matrix.mulVec_mulVec, ← map_mul Ξ.mat, map_mul (infGL E a), mul_assoc, mul_assoc,
    infGL_comm]

private theorem alt_fin {U : Subgroup (GL (Fin a) (Af E))} (hU : ∀ X, RightInv U (α X)) (g : GL (Fin a) (Cinf E))
    (x : GL (Fin a) (Af E)) {u : GL (Fin a) (Af E)} (hu : u ∈ U) (v : Fin q → HV E a) :
    alt Ξ α g (x * u) v = alt Ξ α g x v := by
  rw [alt_apply, alt_apply, map_mul (finGL E a), ← mul_assoc, hU _ u hu]

end UpperTheory.V.Lit.Dr

open UpperTheory.V.Lit.Dr

theorem UpperTheory.V.Lit.Dr.corrFwd :
    CorrFwd := by
  classical
  intro E _ _ _ a U Ξ q α hα hU
  refine ⟨fun s p => if h : p ∈ cone E a then altL Ξ α h.choose s.out else 0, fun g x X => ?_,
    fun s p hp => dite_eq_right hp⟩
  have hp : sand g (hOne E a) ∈ cone E a := ⟨g, rfl⟩
  obtain ⟨k, hk⟩ := exists_unitary hp.choose_spec.symm
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U x
  beta_reduce
  rw [dite_eq_left hp, altL_apply, hk, hu, alt_cpt Ξ α hα, alt_fin Ξ α hU _ _ u.2, alt_apply]
  simp only [back_sand]
end
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct ContDiff ComplexOrder

namespace UpperTheory.V.Lit.Dr

theorem coneConvex : ConeConvex := by
  intro E _ _ a
  have hs : IsCone (cone E a) := by
    intro t ht p hp
    rw [conePos] at hp ⊢
    intro w
    have h := (hp w).smul ht
    convert h using 1
    ext i j
    rfl
  have hadd : ∀ p ∈ cone E a, ∀ q ∈ cone E a, p + q ∈ cone E a := by
    intro p hp q hq
    rw [conePos] at hp hq ⊢
    intro w
    have h := (hp w).add (hq w)
    convert h using 1
    ext i j
    rfl
  refine ⟨?_, hs⟩
  rw [convex_iff_forall_pos]
  intro x hx y hy s t hs' ht _
  exact hadd _ (hs s hs' x hx) _ (hs t ht y hy)

end UpperTheory.V.Lit.Dr
end
end
