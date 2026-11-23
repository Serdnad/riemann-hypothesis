module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBoxInvariantSnd
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.Bundle002
public import Mathlib.Analysis.CStarAlgebra.Classes
import GroundTheory.AutomorphicForms.GLnLocal
import GroundTheory.AutomorphicForms.MeasuresModulus
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil.Four.Phi2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}
  [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure]
  (hZ : CR Z) (h : Hyp Z)

include hZ h

def phi0 (f : Sp k n → ℂ) : Sp k n → ℂ :=
  fun p => GlobalTheory.SplitDict.pf ψ (Measure.pi fun _ : Fin (d Z) => ν) (fun q => f (F1 hZ h q)) (Hb hZ h p)

theorem characteristic_function_integral_apply (f : Sp k n → ℂ) (p : Sp k n) :
    phi0 ψ ν hZ h f p = ∫ u, f (p.1 - Pr Z p.1 + E Z u, p.2) * (ψ (u ⬝ᵥ D Z p.1) : ℂ) ∂(Measure.pi fun _ => ν) := by
  have key : ∀ x : Fin (d Z) → k, ((G Z)⁻¹ * G Z) *ᵥ x = x := fun x => by
    rw [← Matrix.mulVec_mulVec]
    exact (Gm hZ h).symm_apply_apply x
  simp [phi0, GlobalTheory.SplitDict.pf, F1, Hb, Gm, key]

theorem test_vector_mem_schwartz_bruhat {c : kˣ} (hc : HasConductor ψ c) {f : Sp k n → ℂ} (hf : f ∈ supportedIn (Set.univ : Set (Sp k n))) :
    phi0 ψ ν hZ h f ∈ supportedIn (Set.univ : Set (Sp k n)) := by
  have hg : (fun q => f (F1 hZ h q)) ∈ SB (TT Z × (Fin (d Z) → k)) :=
    ⟨hf.1.1.comp_continuous (F1 hZ h).continuous, hf.1.2.comp_homeomorph (F1 hZ h)⟩
  have hpf := GlobalTheory.SplitDict.pf_mem_SB (Measure.pi fun _ : Fin (d Z) => ν) hc hg
  refine ⟨⟨?_, ?_⟩, Set.subset_univ _⟩
  · exact hpf.1.comp_continuous (Hb hZ h).continuous
  · exact hpf.2.comp_homeomorph (Hb hZ h)

theorem integrable_slice (hψ : Continuous ψ) {f : Sp k n → ℂ} (hf : f ∈ supportedIn (Set.univ : Set (Sp k n)))
    (p : Sp k n) :
    Integrable (fun u => f (p.1 - Pr Z p.1 + E Z u, p.2) * (ψ (u ⬝ᵥ D Z p.1) : ℂ)) (Measure.pi fun _ => ν) := by
  have key : ∀ x : Fin (d Z) → k, ((G Z)⁻¹ * G Z) *ᵥ x = x := fun x => by
    rw [← Matrix.mulVec_mulVec]
    exact (Gm hZ h).symm_apply_apply x
  have hslice : (fun x => f (p.1 - Pr Z p.1 + E Z x, p.2)) = fun x => (f ∘ F1 hZ h) ((Hb hZ h p).1, x) := by
    funext x
    simp [F1, Hb, Gm, key]
  have hg : HasCompactSupport (f ∘ F1 hZ h) := hf.1.2.comp_homeomorph _
  have hfc : Continuous f := hf.1.1.continuous
  have hcs : HasCompactSupport (fun x => f (p.1 - Pr Z p.1 + E Z x, p.2)) := by
    refine HasCompactSupport.intro (hg.isCompact.image continuous_snd) ?_
    intro x hx
    rw [congrFun hslice x]
    by_contra hne
    exact hx ⟨((Hb hZ h p).1, x), subset_tsupport _ hne, rfl⟩
  refine Continuous.integrable_of_hasCompactSupport ?_ (hcs.mul_right (f' := fun u => (ψ (u ⬝ᵥ D Z p.1) : ℂ)))
  have h1 : Continuous (fun x => f (p.1 - Pr Z p.1 + E Z x, p.2)) := by
    rw [hslice]
    exact (hfc.comp (F1 hZ h).continuous).comp (Continuous.prodMk_right _)
  have h2 : Continuous (fun u : Fin (d Z) → k => (ψ (u ⬝ᵥ D Z p.1) : ℂ)) := by
    fun_prop
  exact h1.mul h2

def phiS (hψ : Continuous ψ) : (supportedIn (Set.univ : Set (Sp k n))) →ₗ[ℂ] (Sp k n → ℂ) where
  toFun f := phi0 ψ ν hZ h f.1
  map_add' f g := by
    funext p
    simp only [Submodule.coe_add, Pi.add_apply, characteristic_function_integral_apply, add_mul]
    exact integral_add (integrable_slice ψ ν hZ h hψ f.2 p) (integrable_slice ψ ν hZ h hψ g.2 p)
  map_smul' c f := by
    funext p
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, characteristic_function_integral_apply, mul_assoc, RingHom.id_apply]
    exact integral_const_mul _ _

end PositivityTheory.RgUd.T.Nil.Four.Phi2
end
end

section

noncomputable section

open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil.Four.Phi2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

def adL {g : GL (Fin n) k} (hg : g ∈ Gz Z) : (Fin (d Z) → k) →ₗ[k] (Fin (d Z) → k) where
  toFun u := (bas Z).equivFun ⟨g.val * E Z u * g⁻¹.val, conj_mem_nilpotent_cone hg (E_mem Z u)⟩
  map_add' u u' := by
    rw [← map_add (f := _)]
    congr 1
    ext1
    simp [E_add, mul_add, add_mul]
  map_smul' c u := by
    rw [← map_smul]
    congr 1
    ext1
    simp [E_smul]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem E_adL {g : GL (Fin n) k} (hg : g ∈ Gz Z) (u : Fin (d Z) → k) :
    E Z (adL hg u) = g.val * E Z u * g⁻¹.val := by
  simp [adL, E]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem trace_conj (g : GL (Fin n) k) (A : Matrix (Fin n) (Fin n) k) : trace (g.val * A * g⁻¹.val) = trace A := by
  rw [trace_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem dot_conj {g : GL (Fin n) k} (hg : g ∈ Gz Z) (u : Fin (d Z) → k) (x : Matrix (Fin n) (Fin n) k) :
    adL hg u ⬝ᵥ D Z (g.val * x * g⁻¹.val) = u ⬝ᵥ D Z x := by
  rw [dot_D, dot_D, E_adL]
  have : g.val * E Z u * g⁻¹.val * (g.val * x * g⁻¹.val) = g.val * (E Z u * x) * g⁻¹.val := by
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  rw [this, trace_conj]

def adM {g : GL (Fin n) k} (hg : g ∈ Gz Z) : Matrix (Fin (d Z)) (Fin (d Z)) k := LinearMap.toMatrix' (adL hg)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem adM_mulVec {g : GL (Fin n) k} (hg : g ∈ Gz Z) (u : Fin (d Z) → k) : adM hg *ᵥ u = adL hg u :=
  LinearMap.toMatrix'_mulVec _ _

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem dot_G (u u' : Fin (d Z) → k) : u ⬝ᵥ (G Z *ᵥ u') = trace (E Z u * E Z u') := by
  rw [← D_E, dot_D]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem gram_adM {g : GL (Fin n) k} (hg : g ∈ Gz Z) : (adM hg)ᵀ * G Z * adM hg = G Z := by
  have key : ∀ u u', u ⬝ᵥ (((adM hg)ᵀ * G Z * adM hg) *ᵥ u') = u ⬝ᵥ (G Z *ᵥ u') := by
    intro u u'
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, adM_mulVec, adM_mulVec, dot_G,
      dot_G, E_adL, E_adL]
    have : g.val * E Z u * g⁻¹.val * (g.val * E Z u' * g⁻¹.val) = g.val * (E Z u * E Z u') * g⁻¹.val := by
      simp only [mul_assoc, Units.inv_mul_cancel_left]
    rw [this, trace_conj]
  ext i j
  have := key (Pi.single i 1) (Pi.single j 1)
  simpa [single_dotProduct, mulVec_single_one] using this

variable (hZ : CR Z) (h : Hyp Z)
include hZ h

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_adM_sq {g : GL (Fin n) k} (hg : g ∈ Gz Z) : (adM hg).det ^ 2 = 1 := by
  have h1 := congrArg Matrix.det (gram_adM hg)
  rw [det_mul, det_mul, det_transpose] at h1
  have h2 : ((adM hg).det ^ 2 - 1) * (G Z).det = 0 := by linear_combination h1
  rcases mul_eq_zero.1 h2 with h3 | h3
  · linear_combination h3
  · exact absurd h3 (G_det hZ h)

def adU {g : GL (Fin n) k} (hg : g ∈ Gz Z) : GL (Fin (d Z)) k :=
  Matrix.nonsingInvUnit (adM hg) (Ne.isUnit fun h0 => by
    have := det_adM_sq hZ h hg
    rw [h0] at this
    norm_num at this)

theorem distribHaarChar_adU {g : GL (Fin n) k} (hg : g ∈ Gz Z) :
    (distribHaarChar k (Matrix.GeneralLinearGroup.det (adU hZ h hg)) : NNReal) = 1 := by
  set u := Matrix.GeneralLinearGroup.det (adU hZ h hg)
  have hu : u ^ 2 = 1 := Units.ext (by
    simp only [Units.val_pow_eq_pow_val, Units.val_one, u, Matrix.GeneralLinearGroup.val_det_apply]
    exact det_adM_sq hZ h hg)
  have h2 : (distribHaarChar k u) ^ 2 = 1 := by rw [← map_pow, hu, map_one]
  exact (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).1 h2

end PositivityTheory.RgUd.T.Nil.Four.Phi2
end
end
