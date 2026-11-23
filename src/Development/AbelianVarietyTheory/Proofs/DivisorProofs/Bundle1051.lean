module

public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle745
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle236
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle209
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle133
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle126
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial MeasureTheory GlobalTheory.FockTensor

noncomputable section

namespace GlobalTheory.CoefProjector

variable {p q : ℕ} {T : GrpData p q}

theorem inner_opE (πU : URep T) {e : T.G → ℂ} (hi : Integrable e T.haar)
    (hc : Continuous e) (z x : πU.H) :
    inner ℂ z (opE T πU.π e x) = ∫ g, e g * inner ℂ z (πU.π g x) ∂T.haar := by
  have h : Integrable (fun g => e g • πU.π g x) T.haar := by
    refine Integrable.mono' (hi.norm.mul_const ‖x‖) (hc.smul (πU.cont x)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => ?_)
    rw [norm_smul, πU.isom]
  unfold opE
  rw [← integral_inner h]
  simp only [inner_smul_right]

theorem continuous_eFun (D : DSRep T) (v : D.HK.V) : Continuous (eFun D v) :=
  continuous_const.mul (continuous_const.inner (D.U.cont _)).star

theorem pi_mul (πU : URep T) (g h : T.G) (x : πU.H) : πU.π (g * h) x = πU.π g (πU.π h x) := by
  rw [map_mul]; rfl

theorem eFun_inv (D : DSRep T) (v : D.HK.V) (g : T.G) : eFun D v g⁻¹ = star (eFun D v g) := by
  simp only [eFun, mcoef]
  rw [← inner_pi_left]
  simp [inner_conj_symm]

theorem fdeg_ne (D : DSRep T) : (D.fdeg : ℂ) ≠ 0 := by exact_mod_cast D.fdeg_pos.ne'

theorem integral_eFun_mul (D : DSRep T) (v : D.HK.V) (w u : D.U.H) :
    ∫ g, eFun D v g * inner ℂ w (D.U.π g u) ∂T.haar = inner ℂ (D.ι v) u * inner ℂ w (D.ι v) := by
  have h := (GlobalTheory.SchurPol.schur_polarised p q T D u w (D.ι v) (D.ι v)).2
  have h2 : ∀ g, eFun D v g * inner ℂ w (D.U.π g u) =
      (D.fdeg : ℂ) * (inner ℂ w (D.U.π g u) * star (inner ℂ (D.ι v) (D.U.π g (D.ι v)))) := by
    intro g; simp only [eFun, mcoef]; ring
  simp only [h2]
  rw [integral_const_mul, h]
  have := fdeg_ne D
  have h3 : star (inner ℂ (D.ι v) w) = inner ℂ w (D.ι v) := inner_conj_symm _ _
  rw [h3]
  field_simp

theorem opE_self (D : DSRep T) (v : D.HK.V) (hi : Integrable (eFun D v) T.haar) (u : D.U.H) :
    opE T D.U.π (eFun D v) u = inner ℂ (D.ι v) u • D.ι v := by
  refine ext_inner_left ℂ fun w => ?_
  rw [inner_opE D.U hi (continuous_eFun D v), integral_eFun_mul, inner_smul_right]

theorem opE_selfAdjoint (D : DSRep T) (v : D.HK.V) (hi : Integrable (eFun D v) T.haar) (πU : URep T)
    (x y : πU.H) :
    inner ℂ (opE T πU.π (eFun D v) x) y = inner ℂ x (opE T πU.π (eFun D v) y) := by
  haveI := (GlobalTheory.HolDS.haar_unimodular p q T).2
  rw [← inner_conj_symm, inner_opE πU hi (continuous_eFun D v), inner_opE πU hi (continuous_eFun D v),
    ← integral_conj, ← integral_inv_eq_self]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [map_mul, inner_conj_symm, inner_pi_left, inv_inv, eFun_inv]
  simp

theorem eFun_conv (D : DSRep T) (v : D.HK.V) (x h : T.G) :
    ∫ g, eFun D v g * eFun D v (x⁻¹ * (g⁻¹ * h)) ∂T.haar = mcoef D v x * eFun D v h := by
  have h2 : ∀ g, eFun D v g * eFun D v (x⁻¹ * (g⁻¹ * h)) =
      (D.fdeg : ℂ) * (eFun D v g * inner ℂ (D.U.π h (D.ι v)) (D.U.π g (D.U.π x (D.ι v)))) := by
    intro g
    have : eFun D v (x⁻¹ * (g⁻¹ * h)) =
        (D.fdeg : ℂ) * inner ℂ (D.U.π h (D.ι v)) (D.U.π g (D.U.π x (D.ι v))) := by
      simp only [eFun, mcoef]
      rw [pi_mul, pi_mul, ← inner_pi_left, ← inner_pi_left]
      congr 1
      exact inner_conj_symm _ _
    rw [this]; ring
  simp only [h2]
  rw [integral_const_mul, integral_eFun_mul]
  simp only [eFun, mcoef]
  have h3 : star (inner ℂ (D.ι v) (D.U.π h (D.ι v))) = inner ℂ (D.U.π h (D.ι v)) (D.ι v) :=
    inner_conj_symm _ _
  rw [h3]; ring

theorem opE_pi_opE (D : DSRep T) (v : D.HK.V) (hi : Integrable (eFun D v) T.haar) (πU : URep T)
    (x : T.G) (y : πU.H) :
    opE T πU.π (eFun D v) (πU.π x (opE T πU.π (eFun D v) y)) =
      mcoef D v x • opE T πU.π (eFun D v) y := by
  have hc := continuous_eFun D v
  refine ext_inner_left ℂ fun z => ?_
  rw [inner_smul_right, inner_opE πU hi hc, inner_opE πU hi hc z y, ← integral_const_mul]
  have h1 : ∀ g, eFun D v g * inner ℂ z (πU.π g (πU.π x (opE T πU.π (eFun D v) y))) =
      ∫ h, eFun D v g * eFun D v (x⁻¹ * (g⁻¹ * h)) * inner ℂ z (πU.π h y) ∂T.haar := by
    intro g
    have e1 : inner ℂ z (πU.π g (πU.π x (opE T πU.π (eFun D v) y))) =
        inner ℂ (πU.π (g * x)⁻¹ z) (opE T πU.π (eFun D v) y) := by
      rw [inner_pi_left, inv_inv, pi_mul]
    rw [e1, inner_opE πU hi hc, ← integral_const_mul, ← integral_mul_left_eq_self _ (g * x)⁻¹]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    simp only
    rw [pi_mul, inner_pi_pi, mul_inv_rev, mul_assoc x⁻¹, mul_assoc]
  simp only [h1]
  have hi' : Integrable (fun k => eFun D v (x⁻¹ * k)) T.haar := hi.comp_mul_left x⁻¹
  have hp := ((measurePreserving_prod_inv_mul T.haar T.haar).integrable_comp_of_integrable
    (hi.mul_prod hi'))
  have hcont : Continuous fun h : T.G × T.G => inner ℂ z (πU.π h.2 y) :=
    (continuous_const.inner (πU.cont y)).comp continuous_snd
  have hp2 := hp.mul_bdd (c := ‖z‖ * ‖y‖) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun h => by
      simpa [πU.isom] using norm_inner_le_norm (𝕜 := ℂ) z (πU.π h.2 y))
  rw [integral_integral_swap hp2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only
  rw [integral_mul_const, eFun_conv, mul_assoc]

theorem dense_orbit (D : DSRep T) (u : D.U.H) (hu : u ≠ 0) :
    DenseRange (Finsupp.linearCombination ℂ fun g : T.G => D.U.π g u) := by
  have : Dense ((LinearMap.range (Finsupp.linearCombination ℂ fun g : T.G => D.U.π g u) :
      Submodule ℂ D.U.H) : Set D.U.H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
      Submodule.eq_bot_iff]
    intro w hw
    have h := ext_orbit D u hu (innerSL ℂ w) 0 fun g => by
      refine Submodule.inner_left_of_mem_orthogonal ?_ hw
      exact ⟨Finsupp.single g 1, by simp⟩
    have h2 := congrArg (fun f : D.U.H →L[ℂ] ℂ => f w) h
    simpa using h2
  exact this

theorem exists_intertwiner (D : DSRep T) (v : D.HK.V) (hv : ‖D.ι v‖ = 1) (πU : URep T) (ξ : πU.H)
    (hξ : ∀ g, inner ℂ ξ (πU.π g ξ) = mcoef D v g * inner ℂ ξ ξ) :
    ∃ io : D.U.H →L[ℂ] πU.H, IsHomG D πU io ∧ io (D.ι v) = ξ ∧ ∀ x, ‖io x‖ = ‖ξ‖ * ‖x‖ := by
  have hu : D.ι v ≠ 0 := by
    intro h; rw [h, norm_zero] at hv; exact zero_ne_one hv
  set A := Finsupp.linearCombination ℂ fun g : T.G => D.U.π g (D.ι v) with hA
  set B := Finsupp.linearCombination ℂ fun g : T.G => πU.π g ξ with hB
  have hd : DenseRange A := dense_orbit D _ hu
  have hgram : ∀ g h, inner ℂ (πU.π g ξ) (πU.π h ξ) =
      inner ℂ (D.U.π g (D.ι v)) (D.U.π h (D.ι v)) * inner ℂ ξ ξ := by
    intro g h
    rw [inner_pi_left, inner_pi_left, ← pi_mul, ← pi_mul, hξ, mcoef]
  have hn : ∀ c, ‖B c‖ = ‖ξ‖ * ‖A c‖ := by
    intro c
    have h : inner ℂ (B c) (B c) = inner ℂ (A c) (A c) * inner ℂ ξ ξ := by
      simp only [hA, hB, Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
        inner_smul_left, inner_smul_right, hgram, Finset.sum_mul, mul_assoc]
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    have h' : ‖B c‖ ^ 2 = (‖ξ‖ * ‖A c‖) ^ 2 := by
      rw [mul_pow, mul_comm]; exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h'
  have hT : ∀ c, B.extendOfNorm A (A c) = B c :=
    LinearMap.extendOfNorm_eq hd ⟨‖ξ‖, fun c => (hn c).le⟩
  have hg : ∀ g, B.extendOfNorm A (D.U.π g (D.ι v)) = πU.π g ξ := fun g => by
    simpa [hA, hB] using hT (Finsupp.single g 1)
  refine ⟨B.extendOfNorm A, fun g => ext_orbit D _ hu _ _ fun h => ?_, ?_, fun x => ?_⟩
  · show B.extendOfNorm A (D.U.π g (D.U.π h (D.ι v))) = πU.π g (B.extendOfNorm A (D.U.π h (D.ι v)))
    rw [← pi_mul, hg, hg, pi_mul]
  · simpa using hg 1
  · refine hd.induction_on (p := fun x => ‖B.extendOfNorm A x‖ = ‖ξ‖ * ‖x‖) x
      (isClosed_eq (by fun_prop) (by fun_prop)) fun c => ?_
    rw [hT, hn]

theorem projector_of_integrable_coefficient :
    ∀ (p q : ℕ) (T : GrpData p q) (D : DSRep T) (v : D.HK.V), ‖D.ι v‖ = 1 → MeasureTheory.Integrable (eFun D v) T.haar → (∀ u, opE T D.U.π (eFun D v) u = inner ℂ (D.ι v) u • D.ι v) ∧ ∀ πU : URep T, (∀ x y, inner ℂ (opE T πU.π (eFun D v) x) y = inner ℂ x (opE T πU.π (eFun D v) y)) ∧ (∀ g x, opE T πU.π (eFun D v) (πU.π g (opE T πU.π (eFun D v) x)) = mcoef D v g • opE T πU.π (eFun D v) x) ∧ ∀ ξ, opE T πU.π (eFun D v) ξ = ξ → ∃ io : D.U.H →L[ℂ] πU.H, IsHomG D πU io ∧ io (D.ι v) = ξ ∧ ∀ x, ‖io x‖ = ‖ξ‖ * ‖x‖ := by
  intro p q T D v hv hi
  refine ⟨opE_self D v hi, fun πU => ⟨opE_selfAdjoint D v hi πU, opE_pi_opE D v hi πU, fun ξ hξ => ?_⟩⟩
  refine exists_intertwiner D v hv πU ξ fun g => ?_
  have h1 := opE_selfAdjoint D v hi πU ξ (πU.π g (opE T πU.π (eFun D v) ξ))
  rw [opE_pi_opE D v hi, hξ, inner_smul_right] at h1
  exact h1

end GlobalTheory.CoefProjector
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem pushout_quotient_map_eq_quotient_map_ideal : ∀ (R C E : Type) [CommRing R] [CommRing C] [CommRing E] (c : Ideal R) (f : R →+* C) (π : C →+* E) (χ : R ⧸ c →+* E), IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom (Ideal.Quotient.mk c)) (CommRingCat.ofHom π) (CommRingCat.ofHom χ) → Function.Surjective π ∧ RingHom.ker π = c.map f := by
  intro R C E _ _ _ c f π χ h
  have hw' : ∀ r, π (f r) = χ (Ideal.Quotient.mk c r) := fun r => by
    have := congrArg (fun g => g.hom r) h.w
    simpa using this
  have hle : c.map f ≤ RingHom.ker π := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    simp [RingHom.mem_ker, hw', Ideal.Quotient.eq_zero_iff_mem.mpr hr]
  let q : C →+* C ⧸ c.map f := Ideal.Quotient.mk _
  let qm : R ⧸ c →+* C ⧸ c.map f := Ideal.quotientMap (c.map f) f Ideal.le_comap_map
  let φ : C ⧸ c.map f →+* E := Ideal.Quotient.lift _ π (fun x hx => hle hx)
  have hcomm : CommRingCat.ofHom f ≫ CommRingCat.ofHom q =
      CommRingCat.ofHom (Ideal.Quotient.mk c) ≫ CommRingCat.ofHom qm := by
    ext r; rfl
  let ψ := h.desc (CommRingCat.ofHom q) (CommRingCat.ofHom qm) hcomm
  have h1 : CommRingCat.ofHom π ≫ ψ = CommRingCat.ofHom q := h.inl_desc _ _ _
  have h2 : CommRingCat.ofHom χ ≫ ψ = CommRingCat.ofHom qm := h.inr_desc _ _ _
  have hid : ψ ≫ CommRingCat.ofHom φ = 𝟙 _ := by
    apply h.hom_ext
    · rw [← Category.assoc, h1, Category.comp_id]
      ext x; rfl
    · rw [← Category.assoc, h2, Category.comp_id]
      ext r
      change φ (qm (Ideal.Quotient.mk c r)) = χ (Ideal.Quotient.mk c r)
      rw [← hw']
      rfl
  have hφsurj : Function.Surjective φ := fun e =>
    ⟨ψ e, by
      have := congrArg (fun g => g.hom e) hid
      simpa using this⟩
  refine ⟨?_, ?_⟩
  · intro e
    obtain ⟨y, hy⟩ := hφsurj e
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨x, hy⟩
  · refine le_antisymm ?_ hle
    intro x hx
    have hx1 : ψ.hom (π x) = q x := by
      rw [← CommRingCat.hom_ofHom q, ← h1]; rfl
    rw [RingHom.mem_ker] at hx
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change q x = 0
    rw [← hx1, hx, map_zero]

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem relations_lift_vanishing : (∀ (R R' ν : Type) [CommRing R] [CommRing R'] [Algebra R R'] (c : Ideal R), (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ G ∈ (c.map (algebraMap R R')).map (MvPolynomial.C : R' →+* MvPolynomial ν R'), ∃ H : MvPolynomial ν R, MvPolynomial.map (Ideal.Quotient.mk c) H = 0 ∧ MvPolynomial.map (algebraMap R R') H = G) → ∀ (R R' C' D E ν : Type) [CommRing R] [CommRing R'] [CommRing C'] [CommRing D] [CommRing E] [Algebra R R'] [Algebra R' C'] (c : Ideal R) [Algebra (R ⧸ c) D], (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (π : C' →+* E) (ψ : D →+* E) (ζ : ν → D) (ξ : ν → C'), RingHom.ker π = c.map ((algebraMap R' C').comp (algebraMap R R')) → ψ.comp ((algebraMap (R ⧸ c) D).comp (Ideal.Quotient.mk c)) = (π.comp (algebraMap R' C')).comp (algebraMap R R') → (∀ s, π (ξ s) = ψ (ζ s)) → Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') → ∀ f : MvPolynomial ν (R ⧸ c), MvPolynomial.aeval ζ f = 0 → ∃ F : MvPolynomial ν R, MvPolynomial.map (Ideal.Quotient.mk c) F = f ∧ MvPolynomial.aeval ξ (MvPolynomial.map (algebraMap R R') F) = 0 := by
  intro hH R R' C' D E ν _ _ _ _ _ _ _ c _ hc π ψ ζ ξ hker hcomm hξ hsurj f hf
  obtain ⟨F₀, rfl⟩ := MvPolynomial.map_surjective (Ideal.Quotient.mk c) Ideal.Quotient.mk_surjective f
  have hπ : π (MvPolynomial.aeval ξ (MvPolynomial.map (algebraMap R R') F₀)) = 0 := by
    have h1 : π (MvPolynomial.aeval ξ (MvPolynomial.map (algebraMap R R') F₀))
        = ψ (MvPolynomial.aeval ζ (MvPolynomial.map (Ideal.Quotient.mk c) F₀)) := by
      rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval₂_map,
        MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left, ← RingHom.comp_assoc, hcomm]
      congr 1
      funext s
      exact hξ s
    rw [h1, hf, map_zero]
  have hmem : MvPolynomial.aeval ξ (MvPolynomial.map (algebraMap R R') F₀) ∈
      ((c.map (algebraMap R R')).map (MvPolynomial.C : R' →+* MvPolynomial ν R')).map
        (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') := by
    rw [Ideal.map_map]
    change _ ∈ Ideal.map ((MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') : MvPolynomial ν R' →+* C') _
    rw [Ideal.map_map]
    have : ((MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') : MvPolynomial ν R' →+* C').comp
        ((MvPolynomial.C : R' →+* MvPolynomial ν R').comp (algebraMap R R'))
        = (algebraMap R' C').comp (algebraMap R R') := by
      ext x; simp
    rw [this, ← hker]
    exact hπ
  obtain ⟨G, hG, hGe⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).1 hmem
  obtain ⟨H, hH0, hHG⟩ := hH R R' ν c hc G hG
  refine ⟨F₀ - H, ?_, ?_⟩
  · rw [map_sub, hH0, sub_zero]
  · rw [map_sub, hHG, map_sub, hGe, sub_self]

end GlobalTheory.Pinch
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_mvPolynomial_lift_of_mem_conductor :
    ∀ (R R' ν : Type) [CommRing R] [CommRing R'] [Algebra R R'] (c : Ideal R), (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ G ∈ (c.map (algebraMap R R')).map (MvPolynomial.C : R' →+* MvPolynomial ν R'), ∃ H : MvPolynomial ν R, MvPolynomial.map (Ideal.Quotient.mk c) H = 0 ∧ MvPolynomial.map (algebraMap R R') H = G := by
  intro R R' ν _ _ _ c hc G hG
  have key : ∀ z ∈ c.map (algebraMap R R'), ∃ y ∈ c, algebraMap R R' y = z := by
    intro z hz
    refine Submodule.span_induction (p := fun z _ => ∃ y ∈ c, algebraMap R R' y = z)
      ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · exact ⟨0, c.zero_mem, map_zero _⟩
    · rintro _ _ _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨a + b, c.add_mem ha hb, map_add _ _ _⟩
    · rintro r _ _ ⟨a, ha, rfl⟩
      obtain ⟨y, hy, h⟩ := hc a ha r
      exact ⟨y, hy, by rw [h, smul_eq_mul, mul_comm]⟩
  rw [MvPolynomial.mem_map_C_iff] at hG
  choose y hy hyG using fun m => key _ (hG m)
  refine ⟨∑ m ∈ G.support, MvPolynomial.monomial m (y m), ?_, ?_⟩

  · rw [map_sum]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [MvPolynomial.map_monomial, Ideal.Quotient.eq_zero_iff_mem.mpr (hy m), map_zero]

  · rw [map_sum]
    conv_rhs => rw [G.as_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.map_monomial, hyG]

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.mem_preimage_sup_of_stalk_krullDim_le_one_flat : ∀ (X S : Scheme.{0}) [IsIntegral S] (f : X ⟶ S) [Flat f] [GeometricallyIntegral f] (V : X.Opens) (U : S.Opens), (∀ s : S, ∃ x ∈ V, f x = s) → (U : Set S).Nonempty → (∀ z : X, ringKrullDim ((X).presheaf.stalk z) ≤ 1 → z ∈ f ⁻¹ᵁ U ⊔ V) := by
  first | exact @GlobalTheory.CodimOne.mem_preimage_sup_of_ringKrullDim_stalk_le_one | exact GlobalTheory.CodimOne.mem_preimage_sup_of_ringKrullDim_stalk_le_one | (intros; apply GlobalTheory.CodimOne.mem_preimage_sup_of_ringKrullDim_stalk_le_one <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.geometricallyIntegral_comp_of_isOpenImmersion_surjective : ∀ (O Z T : Scheme.{0}) (j : O ⟶ Z) (f : Z ⟶ T) [IsOpenImmersion j] [GeometricallyIntegral f], Surjective (j ≫ f) → GeometricallyIntegral (j ≫ f) := by
  first | exact @GlobalTheory.geometricallyIntegral_of_isOpenImmersion_comp_surjective | exact GlobalTheory.geometricallyIntegral_of_isOpenImmersion_comp_surjective | (intros; apply GlobalTheory.geometricallyIntegral_of_isOpenImmersion_comp_surjective <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.surjective_inf_comp_of_geometricallyIntegral : ∀ (Z T : Scheme.{0}) (f : Z ⟶ T) [GeometricallyIntegral f] (O O' : Z.Opens), Surjective (O.ι ≫ f) → Surjective (O'.ι ≫ f) → Surjective ((O ⊓ O').ι ≫ f) := by
  first | exact @GlobalTheory.surjective_inf_of_geometricallyIntegral | exact GlobalTheory.surjective_inf_of_geometricallyIntegral | (intros; apply GlobalTheory.surjective_inf_of_geometricallyIntegral <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_basicOpen_le_of_app_eq_one_of_isClosedImmersion :
    ∀ (X' Z' : Scheme.{0}) (i' : Z' ⟶ X') [IsClosedImmersion i'] (Y' : X'.Opens), IsAffineOpen Y' →
    ∀ (N : X'.Opens), (∀ z : Z', i' z ∈ Y' → i' z ∈ N) →
    ∃ b : Γ(X', Y'), (i'.app Y').hom b = 1 ∧ X'.basicOpen b ≤ N := by
  intro X' Z' i' _ Y' hY N hN
  classical
  let K : Ideal Γ(X', Y') :=
    { carrier := {f | X'.basicOpen f ≤ N}
      add_mem' hf hg := (X'.basicOpen_add_le _ _).trans (sup_le hf hg)
      zero_mem' := by simp
      smul_mem' c f hf := by
        change X'.basicOpen (c * f) ≤ N
        rw [Scheme.basicOpen_mul]
        exact inf_le_right.trans hf }
  have hmem (z : Spec Γ(X', Y')) (f : Γ(X', Y')) :
      hY.fromSpec z ∈ X'.basicOpen f ↔ f ∉ z.asIdeal := by
    change z ∈ hY.fromSpec ⁻¹ᵁ X'.basicOpen f ↔ _
    rw [hY.fromSpec_preimage_basicOpen]
    rfl
  have hJ : RingHom.ker (i'.app Y').hom ⊔ K = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal _ h
    let z : Spec Γ(X', Y') := ⟨m, hm.isPrime⟩
    have hyY : hY.fromSpec z ∈ Y' := hY.range_fromSpec.le ⟨z, rfl⟩
    by_cases hy : hY.fromSpec z ∈ Set.range i'
    · obtain ⟨w, hw⟩ := hy
      have hwN : hY.fromSpec z ∈ N := hw ▸ hN w (hw ▸ hyY)
      obtain ⟨f, hfN, hf⟩ := hY.exists_basicOpen_le (V := N) ⟨_, hwN⟩ hyY
      exact (hmem z f).mp hf (hJm (Ideal.mem_sup_right hfN))
    · have h1 : hY.fromSpec z ∉ (i'.ker.support : Set X') := by
        rw [Scheme.Hom.support_ker, i'.isClosedEmbedding.isClosed_range.closure_eq]
        exact hy
      have h2 : hY.fromSpec z ∉ X'.zeroLocus (U := Y') (i'.ker.ideal ⟨Y', hY⟩ : Set Γ(X', Y')) :=
        fun h ↦ h1 ((i'.ker.coe_support_inter ⟨Y', hY⟩).ge ⟨h, hyY⟩).1
      rw [Scheme.mem_zeroLocus_iff] at h2
      push_neg at h2
      obtain ⟨a, ha, hya⟩ := h2
      have ha' : a ∈ RingHom.ker (i'.app Y').hom := by
        rw [Scheme.Hom.ker_apply] at ha
        exact ha
      exact (hmem z a).mp hya (hJm (Ideal.mem_sup_left ha'))
  have h1 : (1 : Γ(X', Y')) ∈ RingHom.ker (i'.app Y').hom ⊔ K := hJ ▸ Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
  refine ⟨b, ?_, hb⟩
  have ha0 : (i'.app Y').hom a = 0 := ha
  calc (i'.app Y').hom b = (i'.app Y').hom (a + b) := by rw [map_add (f := _), ha0, zero_add]
    _ = 1 := by rw [hab, map_one]

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.flat_preimage_contains_codim_le_one_points : ∀ (X Y : Scheme.{0}) (q : Y ⟶ X) [Flat q] (W : X.Opens), (∀ z : X, ringKrullDim ((X).presheaf.stalk z) ≤ 1 → z ∈ W) → (∀ z : Y, ringKrullDim ((Y).presheaf.stalk z) ≤ 1 → z ∈ q ⁻¹ᵁ W) := by
  first | exact @GlobalTheory.FlatCodimOne.preimage_contains_codim_le_one | exact GlobalTheory.FlatCodimOne.preimage_contains_codim_le_one | (intros; apply GlobalTheory.FlatCodimOne.preimage_contains_codim_le_one <;> assumption)
end
