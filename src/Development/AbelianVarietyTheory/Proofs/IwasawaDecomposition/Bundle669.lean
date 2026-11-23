module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.SubsingletonOfLeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle664
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueIndependentNormalForm
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle014
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle652
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle653
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFrameOrbitUnipotentOrderTwo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicFrameOrbitIsotropicVectorShort
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle627
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle662
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle628
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle656
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ThetaQuasiPeriods.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

section

noncomputable section

open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.PolFan.ConeSub

theorem eq_zero_of_self_eq_zero {X : Type} [AddCommGroup X] (γ : LinearMap.BilinForm ℤ X)
    (hs : ∀ y z, γ y z = γ z y) (hp : ∀ y, 0 ≤ γ y y) {u : X} (hu : γ u u = 0) (w : X) : γ u w = 0 := by
  have key : ∀ t : ℤ, 0 ≤ γ w w + 2 * t * γ u w := by
    intro t
    have h := hp (w + t • u)
    simp only [map_add (f := _), map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hu, hs w u] at h
    linarith
  by_contra h
  have h1 := key (-(γ w w + 1) * γ u w)
  have h2 : 0 < γ u w * γ u w := mul_self_pos.2 h
  have h3 := hp w
  nlinarith

theorem sum_expand {X₁ ι : Type} [AddCommGroup X₁] [Fintype ι] (B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ) (b : ι → X₁) (z : ι → ℤ) :
    ∑ k, ∑ l, (z k : ℝ) * z l * B (b k) (b l) = B (∑ k, z k • b k) (∑ l, z l • b l) := by

  simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem sum_smul_toReal_mem_psdCone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type)
    [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ),
    (∀ i, γ i ∈ balForms bar X) → (∀ i y, 0 ≤ γ i y y) → (∀ i, 0 ≤ c i) →
    ∑ i, c i • toReal (γ i) ∈ psdCone (bar := bar) (X := X) := by
  intro O _ _ _ _ bar X _ _ _ m γ c hbal hpsd hc
  classical
  set S : Finset (Fin m) := Finset.univ.filter (fun i => 0 < c i) with hSdef
  have hcS : ∀ i, i ∉ S → c i = 0 := fun i hi =>
    le_antisymm (not_lt.1 fun h => hi (by simp [hSdef, h])) (hc i)
  by_cases hS : S.Nonempty
  swap
  · have h0 : ∑ i, c i • toReal (γ i) = 0 := Finset.sum_eq_zero fun i _ => by
      rw [hcS i fun h => hS ⟨i, h⟩, zero_smul]
    rw [h0]
    exact zero_mem_psdCone
  set B := ∑ i, c i • toReal (γ i) with hBdef
  have hBapp : ∀ a b, B a b = ∑ i, c i * (γ i a b : ℝ) := fun a b => by
    simp [hBdef, LinearMap.sum_apply]
  have hBreal : B ∈ realForms bar X :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (toReal_mem (hbal i))

  let R : Submodule O X :=
    { carrier := {y | ∀ i ∈ S, ∀ z, γ i y z = 0}
      add_mem' := fun {y y'} hy hy' i hi z => by rw [map_add (f := _), LinearMap.add_apply, hy i hi, hy' i hi, add_zero]
      zero_mem' := fun i _ z => by simp
      smul_mem' := fun a y hy i hi z => by
        change γ i (a • y) z = 0
        rw [(hbal i).2 a y z]; exact hy i hi _ }
  have hmemR : ∀ y, y ∈ R ↔ ∀ i ∈ S, ∀ z, γ i y z = 0 := fun y => Iff.rfl
  have hBR1 : ∀ y ∈ R, ∀ z, B y z = 0 := fun y hy z => by
    rw [hBapp]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i ∈ S
    · rw [(hmemR y).1 hy i hi z]; simp
    · rw [hcS i hi, zero_mul]
  have hBsymm : ∀ y z, B y z = B z y := hBreal.1
  have hBR2 : ∀ y ∈ R, ∀ z, B z y = 0 := fun y hy z => by rw [hBsymm]; exact hBR1 y hy z

  have hZ : ∀ n : ℤ, n ≠ 0 → ∀ y, n • y ∈ R → y ∈ R := fun n hn y hy i hi z => by
    have h := (hmemR _).1 hy i hi z
    rw [map_zsmul, LinearMap.smul_apply, smul_eq_mul] at h
    exact (mul_eq_zero.1 h).resolve_left hn
  have hO : ∀ a : O, a ≠ 0 → ∀ y, a • y ∈ R → y ∈ R := by
    intro a ha y hy
    have hne : (Ideal.span {a}).comap (algebraMap ℤ O) ≠ ⊥ :=
      Ideal.comap_ne_bot_of_integral_mem ha (Ideal.mem_span_singleton_self a) (Algebra.IsIntegral.isIntegral a)
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hn)
    refine hZ n hn0 y fun i hi z => ?_
    have h := (hmemR _).1 hy i hi (bar a' • z)
    rw [← (hbal i).2 a' (a • y) z, smul_smul, ha', algebraMap_int_eq, eq_intCast, Int.cast_smul_eq_zsmul] at h
    exact h
  have htor : Submodule.torsion O (X ⧸ R) = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun u hu => ?_
    obtain ⟨⟨a, ha⟩, hau⟩ := (Submodule.mem_torsion_iff u).1 hu
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective R u
    rw [Submonoid.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hau
    rw [Submodule.Quotient.mk_eq_zero]
    exact hO a (nonZeroDivisors.ne_zero ha) y hau
  have : Module.Flat O (X ⧸ R) := IsDedekindDomain.flat_iff_torsion_eq_bot.2 htor
  have : Module.FinitePresentation O (X ⧸ R) := Module.finitePresentation_of_finite _ _
  have hproj : Module.Projective O (X ⧸ R) := Module.Flat.projective_of_finitePresentation
  have : Module.Finite ℤ (X ⧸ R) := Module.Finite.trans O (X ⧸ R)
  have : Module.IsTorsionFree ℤ (X ⧸ R) := by
    refine ⟨fun {n} hn a b hab => ?_⟩
    induction a using Submodule.Quotient.induction_on with | H x => ?_
    induction b using Submodule.Quotient.induction_on with | H y => ?_
    simp only at hab
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hab
    rw [Submodule.Quotient.eq]
    refine hZ n (isRegular_iff_ne_zero.mp hn) (x - y) ?_
    rw [smul_sub]; exact hab
  have : Module.Free ℤ (X ⧸ R) := Module.free_of_finite_type_torsion_free'

  have hBq : ∀ x x' y y', Submodule.Quotient.mk (p := R) x = Submodule.Quotient.mk x' →
      Submodule.Quotient.mk (p := R) y = Submodule.Quotient.mk y' → B x y = B x' y' := by
    intro x x' y y' hx hy
    rw [Submodule.Quotient.eq] at hx hy
    have e1 : B x y = B (x - x') y + B x' (y - y') + B x' y' := by
      simp only [map_sub, LinearMap.sub_apply]; ring
    rw [e1, hBR1 _ hx, hBR2 _ hy, zero_add, zero_add]
  let s := Function.surjInv (Submodule.Quotient.mk_surjective R)
  have hs : ∀ u, Submodule.Quotient.mk (p := R) (s u) = u := Function.surjInv_eq _
  let B₁ := (AddMonoidHom.mk' (fun u => (AddMonoidHom.mk' (fun v => B (s u) (s v)) (fun v v' => by
      rw [← map_add (f := _)]; exact hBq _ _ _ _ rfl (by rw [hs, Submodule.Quotient.mk_add, hs, hs]))).toIntLinearMap)
    (fun u u' => by
      ext v
      change B (s (u + u')) (s v) = B (s u) (s v) + B (s u') (s v)
      rw [← LinearMap.add_apply, ← map_add (f := _)]
      exact hBq _ _ _ _ (by rw [hs, Submodule.Quotient.mk_add, hs, hs]) rfl)).toIntLinearMap
  have hB₁ : ∀ u v, B₁ u v = B (s u) (s v) := fun u v => rfl
  have hBB₁ : ∀ a b, B a b = B₁ (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) := fun a b =>
    hBq _ _ _ _ (hs _).symm (hs _).symm
  have hreal₁ : B₁ ∈ realForms bar (X ⧸ R) := by
    refine ⟨fun u v => by rw [hB₁, hB₁, hBsymm], fun a u v => ?_⟩
    rw [hB₁, hB₁]
    calc B (s (a • u)) (s v) = B (a • s u) (s v) := hBq _ _ _ _ (by rw [hs, Submodule.Quotient.mk_smul, hs]) rfl
      _ = B (s u) (bar a • s v) := hBreal.2 a _ _
      _ = B (s u) (s (bar a • v)) := hBq _ _ _ _ rfl (by rw [hs, Submodule.Quotient.mk_smul, hs])
  set cmin := S.inf' hS c with hcmin
  have hcmin0 : 0 < cmin := (Finset.lt_inf'_iff hS).2 fun i hi => (Finset.mem_filter.1 hi).2
  have hint : ∀ u : X ⧸ R, u ≠ 0 → cmin ≤ B₁ u u := by
    intro u hu
    obtain ⟨i, hi, hpos⟩ : ∃ i ∈ S, 0 < γ i (s u) (s u) := by
      by_contra hne
      push_neg at hne
      apply hu
      rw [← hs u, Submodule.Quotient.mk_eq_zero]
      exact fun i hi z => eq_zero_of_self_eq_zero (γ i) (hbal i).1 (hpsd i)
        (le_antisymm (hne i hi) (hpsd i _)) z
    rw [hB₁, hBapp]
    have h1 : (1 : ℝ) ≤ γ i (s u) (s u) := by exact_mod_cast hpos
    calc cmin ≤ c i := Finset.inf'_le _ hi
      _ ≤ c i * (γ i (s u) (s u) : ℝ) := le_mul_of_one_le_right (hc i) h1
      _ ≤ ∑ j, c j * (γ j (s u) (s u) : ℝ) :=
        Finset.single_le_sum (f := fun j => c j * (γ j (s u) (s u) : ℝ))
          (fun j _ => mul_nonneg (hc j) (by exact_mod_cast hpsd j _)) (Finset.mem_univ i)
  have hdef : IsPosDef B₁ := by
    let b := Module.Free.chooseBasis ℤ (X ⧸ R)
    rw [isPosDef_iff_basis b]
    intro x hx
    refine GlobalTheory.PointLawsEdge.real_pos_of_int_ge (fun k l => B₁ (b k) (b l)) (fun k l => hreal₁.1 _ _) hcmin0
      (fun z hz => ?_) x hx
    show cmin ≤ ∑ k, ∑ l, (z k : ℝ) * z l * B₁ (b k) (b l)
    rw [sum_expand]
    refine hint _ fun h0 => hz ?_
    exact funext (Fintype.linearIndependent_iff.1 b.linearIndependent z h0)
  exact ⟨X ⧸ R, inferInstance, inferInstance, hproj, R.mkQ, B₁, Submodule.mkQ_surjective R, hreal₁, hdef,
    fun a b => hBB₁ a b⟩
end ConeSub
end PolFan
end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_complexPointDerivation_separating_params_charZero : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ), SmoothOfRelativeDimension n p → ∀ (x₀ : CxPts p σ) (U : Y.affineOpens) (hy : x₀.1 (IsLocalRing.closedPoint ℂ) ∈ U.1) (m : ℕ) (f : Fin m → Γ(Y, U.1)), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ))) m (fun i => Y.presheaf.germ U.1 _ hy (f i)) → ∀ l : Fin m → ℂ, l ≠ 0 → ∃ δ : Γ(Y, U.1) →+ ℂ, (∀ a : k, δ (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U.1 a) = 0) ∧ (∀ g h : Γ(Y, U.1), δ (g * h) = CxPts.ev p σ U.1 g x₀ * δ h + CxPts.ev p σ U.1 h x₀ * δ g) ∧ ∑ i, l i * δ (f i) ≠ 0 := by
  first | exact @GlobalTheory.PtDerivSep.exists_ptDer_sep | exact GlobalTheory.PtDerivSep.exists_ptDer_sep | (intros; apply GlobalTheory.PtDerivSep.exists_ptDer_sep <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw GlobalTheory.KeyCl GlobalTheory.LocM
open Filter Topology Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WeilStd


open ReciprocityTheory.PTheta Matrix in
theorem im_hermForm_per {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g))
    (k k' : Fin g → ℤ) {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (ρ : (Fin g → ℂ) → ℂ) (hρd : Differentiable ℂ ρ) (hρ0 : ∀ z, ρ z ≠ 0)
    (χ : (Fin g ⊕ Fin g → ℤ) → ℂ) (hχ : ∀ r, χ r ≠ 0)
    (h : ∀ r z, ρ (z + per τ r) * (χ r * Complex.exp (Real.pi * hermForm Hm (F z) (F (per τ r)) +
        Real.pi / 2 * hermForm Hm (F (per τ r)) (F (per τ r)))) * theta (Key.halfVec k) (Key.halfVec k') z τ =
      ρ z * theta (Key.halfVec k) (Key.halfVec k') (z + per τ r) τ)
    (p q : Fin g ⊕ Fin g → ℤ) :
    (hermForm Hm (F (per τ p)) (F (per τ q))).im = omegaStd p q := by

  classical
  have hper : ∀ r : Fin g ⊕ Fin g → ℤ, per τ r =
      τ *ᵥ ofIntVec (fun i => r (Sum.inl i)) + ofIntVec (fun i => r (Sum.inr i)) := fun r => rfl
  have qp : ∀ r z, theta (Key.halfVec k) (Key.halfVec k') (z + per τ r) τ =
      autFactor (Key.halfVec k) (Key.halfVec k') τ (fun i => r (Sum.inl i)) (fun i => r (Sum.inr i)) z *
        theta (Key.halfVec k) (Key.halfVec k') z τ := fun r z => by
    rw [hper, ← add_assoc]
    exact thetaQuasiPeriod_holds (Fin g) _ _ z τ _ _ hτ.1
  choose c₁ hc₁ using fun r : Fin g ⊕ Fin g → ℤ =>
    NormalUnique.autFactor_eq_exp (Key.halfVec k) (Key.halfVec k') τ (fun i => r (Sum.inl i)) (fun i => r (Sum.inr i))
  let lin₁ : (Fin g ⊕ Fin g → ℤ) → (Fin g → ℂ) →ₗ[ℂ] ℂ := fun r =>
    { toFun := fun v => -(2 * Real.pi * Complex.I) * (ofIntVec (fun i => r (Sum.inl i)) ⬝ᵥ v)
      map_add' := fun v w => by simp only [dotProduct_add]; ring
      map_smul' := fun s v => by simp only [dotProduct_smul, smul_eq_mul, RingHom.id_apply]; ring }
  let lin₂ : (Fin g ⊕ Fin g → ℤ) → (Fin g → ℂ) →ₗ[ℂ] ℂ := fun r =>
    { toFun := fun v => (Real.pi : ℂ) * hermForm Hm (F v) (F (per τ r))
      map_add' := fun v w => by simp only [map_add (f := _), hermForm, add_dotProduct]; ring
      map_smul' := fun s v => by simp only [map_smul, hermForm, smul_dotProduct, smul_eq_mul, RingHom.id_apply]; ring }
  let c₂ : (Fin g ⊕ Fin g → ℤ) → ℂ := fun r =>
    Complex.log (χ r) + Real.pi / 2 * hermForm Hm (F (per τ r)) (F (per τ r))
  have e1 : ∀ r v, Complex.exp (lin₁ r v + c₁ r) =
      autFactor (Key.halfVec k) (Key.halfVec k') τ (fun i => r (Sum.inl i)) (fun i => r (Sum.inr i)) v := fun r v => by
    rw [hc₁]; rfl
  have e2 : ∀ r v, Complex.exp (lin₂ r v + c₂ r) = χ r * Complex.exp (Real.pi * hermForm Hm (F v) (F (per τ r)) +
      Real.pi / 2 * hermForm Hm (F (per τ r)) (F (per τ r))) := fun r v => by
    rw [show lin₂ r v + c₂ r = Complex.log (χ r) + (Real.pi * hermForm Hm (F v) (F (per τ r)) +
      Real.pi / 2 * hermForm Hm (F (per τ r)) (F (per τ r))) from by
        show (Real.pi : ℂ) * hermForm Hm (F v) (F (per τ r)) + (Complex.log (χ r) +
          Real.pi / 2 * hermForm Hm (F (per τ r)) (F (per τ r))) = _
        ring, Complex.exp_add, Complex.exp_log (hχ r)]
  have hfac : ∀ r v, Complex.exp (lin₁ r v + c₁ r) * ρ v = Complex.exp (lin₂ r v + c₂ r) * ρ (v + per τ r) := by
    intro r v
    have d₁ : Differentiable ℂ fun z => Complex.exp (lin₁ r z + c₁ r) * ρ z -
        Complex.exp (lin₂ r z + c₂ r) * ρ (z + per τ r) :=
      ((((LinearMap.toContinuousLinearMap (lin₁ r)).differentiable.add_const (c₁ r)).cexp).mul hρd).sub
        ((((LinearMap.toContinuousLinearMap (lin₂ r)).differentiable.add_const (c₂ r)).cexp).mul
          (hρd.comp (differentiable_id.add_const _)))
    rcases entire_eq_zero_or_eq_zero_of_mul_eq_zero _ (fun z => theta (Key.halfVec k) (Key.halfVec k') z τ) d₁
      (differentiable_theta hτ _ _) (fun z => by
        simp only [e1, e2]
        have h1 := h r z
        have h2 := qp r z
        linear_combination (-ρ z) * h2 - h1) with h0 | h0
    · exact sub_eq_zero.1 (h0 v)
    · exact absurd (funext h0) (theta_ne_zero hτ _ _)
  have key := alternating_eq_of_equivalent_factors (per τ) lin₁ lin₂ c₁ c₂ hρd.continuous hρ0 hfac p q
  set X := hermForm Hm (F (per τ p)) (F (per τ q)) with hX
  have k2 : -(2 * Real.pi * Complex.I) * (ofIntVec (fun i => p (Sum.inl i)) ⬝ᵥ per τ q) -
      -(2 * Real.pi * Complex.I) * (ofIntVec (fun i => q (Sum.inl i)) ⬝ᵥ per τ p) =
      (Real.pi : ℂ) * hermForm Hm (F (per τ q)) (F (per τ p)) - (Real.pi : ℂ) * X := key
  rw [hermForm_conj_symm_of_isHermitian Hm hH, ← hX, hper, hper, dotProduct_add, dotProduct_add] at k2
  have sym : ofIntVec (fun i => p (Sum.inl i)) ⬝ᵥ τ *ᵥ ofIntVec (fun i => q (Sum.inl i)) =
      ofIntVec (fun i => q (Sum.inl i)) ⬝ᵥ τ *ᵥ ofIntVec (fun i => p (Sum.inl i)) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hτ.1.eq, dotProduct_comm]
  have sc : X - star X = 2 * (X.im : ℂ) * Complex.I := by
    have := Complex.sub_conj X
    push_cast at this
    exact this
  have om : ((omegaStd p q : ℤ) : ℂ) = ofIntVec (fun i => p (Sum.inl i)) ⬝ᵥ ofIntVec (fun i => q (Sum.inr i)) -
      ofIntVec (fun i => q (Sum.inl i)) ⬝ᵥ ofIntVec (fun i => p (Sum.inr i)) := by
    simp only [omegaStd, ofIntVec, dotProduct, ← Finset.sum_sub_distrib]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have G : (2 * Real.pi * Complex.I) * (((omegaStd p q : ℤ) : ℂ) - (X.im : ℂ)) = 0 := by
    rw [om]
    linear_combination -k2 - (2 * Real.pi * Complex.I) * sym + (Real.pi : ℂ) * sc
  rcases mul_eq_zero.1 G with h0 | h0
  · exact absurd h0 Complex.two_pi_I_ne_zero
  · exact_mod_cast (sub_eq_zero.1 h0).symm

end GlobalTheory.WeilStd

namespace GlobalTheory.WeilStd


open GlobalTheory.NormalUnique in
theorem weilIs_per : ∀ (x : KeyIn ℂ) (g : ℕ) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ),
    x.P.g = g → τ.IsSymm → (τ.map Complex.im).PosDef → charHalf g a b → c ≠ 0 →
    (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) →
    u.IsFn x.th (fun z => c * thetaChar τ a b z) →
    ∀ (n : ℕ) (p q : Fin g ⊕ Fin g → ℤ) (e : ℂˣ), 0 < n →
      (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd p q : ℂ) / n) →
      Out.WeilIs x.P.A x.P.L n (u.ex ((n : ℂ)⁻¹ • per τ p)) (u.ex ((n : ℂ)⁻¹ • per τ q)) (unitOn e) := by
  intro x g u τ a b c hg hτs hτp hab hc hΛ hfn n p q e hn he
  subst hg
  obtain ⟨u₁, Hm, χ, Ef, hA, -, h1, h2, -, -, hE, -, hW⟩ := thetaUnifAV_all x.P x.rig x.rig_gen
  obtain ⟨F, hF, hFl, -, -⟩ := HomLinear.exists_linear_of_isMonHom x.P.A x.P.A x.P.isAb x.P.isAb x.P.L x.P.L
    x.P.g x.P.g u u₁ h1 h2 (𝟙 x.P.A) inferInstance
  simp only [Category.comp_id] at hF
  obtain ⟨ρ, hρd, hρ0, -, hρ⟩ := NormalUnique.exists_frame_ratio x.P.isLB u₁ u F hF
  obtain ⟨θ₁, hθ₁⟩ := exists_isFn x.P.isLB u₁ x.th
  have hT := (isThetaFn_and_ne_zero_of_isFn x u₁ Hm χ θ₁ hA hθ₁).1
  have hrel : ∀ z, c * thetaChar τ a b z = ρ z * θ₁ (F z) := hρ x.th θ₁ _ hθ₁ hfn
  have hmem : ∀ r, F (per τ r) ∈ u₁.Λ := fun r => hFl _ ((hΛ _).2
    ⟨fun i => r (Sum.inr i), fun i => r (Sum.inl i), by simp only [per]; rw [add_comm]⟩)
  obtain ⟨k, rfl⟩ : ∃ k : Fin x.P.g → ℤ, a = fun i => (k i : ℂ) / 2 :=
    ⟨fun i => if a i = 0 then 0 else 1, funext fun i => by rcases hab.1 i with h | h <;> simp [h]⟩
  obtain ⟨k', rfl⟩ : ∃ k : Fin x.P.g → ℤ, b = fun i => (k i : ℂ) / 2 :=
    ⟨fun i => if b i = 0 then 0 else 1, funext fun i => by rcases hab.2 i with h | h <;> simp [h]⟩
  simp only [SpMove.thetaChar_half] at hrel
  have hχ : ∀ l, χ l ≠ 0 := fun l => norm_ne_zero_iff.1 (by rw [hA.2.2.1]; exact one_ne_zero)
  have key := WeilStd.im_hermForm_per (τ := τ) ⟨hτs, hτp⟩ k k' hA.1 F ρ hρd hρ0 (fun r => χ ⟨_, hmem r⟩)
    (fun r => hχ _) (fun r z => by
      have eA := hrel (z + per τ r)
      have eB := hT.2 ⟨_, hmem r⟩ (F z)
      have eC := hrel z
      rw [pow_one] at eB
      rw [map_add (f := _)] at eA
      apply mul_left_cancel₀ hc
      linear_combination (ρ (z + per τ r) * (χ ⟨_, hmem r⟩ * Complex.exp (Real.pi * hermForm Hm (F z) (F (per τ r)) +
        Real.pi / 2 * hermForm Hm (F (per τ r)) (F (per τ r))))) * eC - ρ z * eA - ρ z * ρ (z + per τ r) * eB) p q
  have hEf : Ef ⟨_, hmem p⟩ ⟨_, hmem q⟩ = omegaStd p q := by
    have := hE ⟨_, hmem p⟩ ⟨_, hmem q⟩
    rw [key] at this
    exact_mod_cast this
  have hw := hW n ⟨_, hmem p⟩ ⟨_, hmem q⟩ e hn (by rw [he, hEf])
  have e1 : u.ex ((n : ℂ)⁻¹ • per τ p) = u₁.ex ((n : ℂ)⁻¹ • F (per τ p)) := by rw [← map_smul, hF]
  have e2 : u.ex ((n : ℂ)⁻¹ • per τ q) = u₁.ex ((n : ℂ)⁻¹ • F (per τ q)) := by rw [← map_smul, hF]
  rw [e1, e2]
  exact hw

end GlobalTheory.WeilStd
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cubicalWeilPairing_torsion_const_holomorphic_family : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : ReciprocityTheory.ChartRestriction.G.Semi.RigLB G) (c : ReciprocityTheory.ChartRestriction.G.Semi.CubicalStr G L) (m N : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (x x' : ∀ b, Over.mk (y b) ⟶ G) (ζ : ℂˣ) (b₀ b₁ : Fin m → ℂ), 0 < N → IsOpen B → IsPreconnected B → IsHolTo B (fun b => (x b).left) → IsHolTo B (fun b => (x' b).left) → (∀ b ∈ B, x b ^ N = 1 ∧ x' b ^ N = 1) → b₀ ∈ B → b₁ ∈ B → GlobalTheory.UU.CubWeil c N (x b₀) (x' b₀) (unitOn ζ) → GlobalTheory.UU.CubWeil c N (x b₁) (x' b₁) (unitOn ζ) := by
  first | exact @GlobalTheory.TorsionPairFam.cubWeil_const_of_isHolTo | exact GlobalTheory.TorsionPairFam.cubWeil_const_of_isHolTo | (intros; apply GlobalTheory.TorsionPairFam.cubWeil_const_of_isHolTo <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.continuousOn_keySection_complexValue : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : _root_.GlobalTheory.FrameUnif.ModelsOf F r) (T : ∀ k, ThetaData e F M k) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)), Formalism.L2.PjFree.GoodEmb c σ → ModelBase M → NegXi M → (∀ k, IsNormUn (T k) (un k)) → FramesOK e F M un → ∀ (A : Type) [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)) (ρ : (Fin m → ℂ) → ℂ), IsOpen B → (∀ a, DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (φ b a)) B) → (∀ b ∈ B, FrMap (φ b) yA (y b)) → (∀ b ∈ B, RootVal (unfOf e F M un) (y b) (ρ b)) → ContinuousOn ρ B := by
  first | exact @GlobalTheory.KeyFourth.continuousOn_rootVal | exact GlobalTheory.KeyFourth.continuousOn_rootVal | (intros; apply GlobalTheory.KeyFourth.continuousOn_rootVal <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

theorem _root_.GlobalTheory.T.exists_holomorphicFrameOrbit_unipotent_order_two : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (x : ℂ → Frame X.Ψ N), IsOrbit X T M γ x → ∃ (M' : ℕ) (γ' : GL (Fin N) E), IsOrbit X T M' γ' x ∧ ((γ' : Matrix (Fin N) (Fin N) E) - 1) ^ 2 = 0 := by
  first | exact @GlobalTheory.ShFam.OrbitUnip.exists_isOrbit_unipotent | exact GlobalTheory.ShFam.OrbitUnip.exists_isOrbit_unipotent | (intros; apply GlobalTheory.ShFam.OrbitUnip.exists_isOrbit_unipotent <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

theorem _root_.GlobalTheory.T.holomorphicFrameOrbit_isotropic_vector_short : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (x : ℂ → Frame X.Ψ N), IsOrbit X T M γ x → ((γ : Matrix (Fin N) (Fin N) E) - 1) ^ 2 = 0 → γ ≠ 1 → ∃ (ξ : Fin N → E) (c : ℝ), X.IsIso ξ ∧ 0 < c ∧ ∀ w : ℂ, T + 1 < w.im → ∀ τ, c * (w.im - T) ≤ X.tt ξ (x w) τ := by
  first | exact @GlobalTheory.orbit_unipotent_short | exact GlobalTheory.orbit_unipotent_short | (intros; apply GlobalTheory.orbit_unipotent_short <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

theorem _root_.GlobalTheory.T.carriesFlags_iff_adaptedFrame_at_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (S : Fr (ratOf C.Y) Dw.mult Dw.mult) (A₀ : Mat Dw.mult C.Y.Fn) (K : Type) [Field K] (φ : c.F →+* K) (x : Sp K ⟶ Z.X) (g : EigFrame Z φ x) (p : Sp K ⟶ C.Y.X), Tied e C.Y C.π C.f0 S A₀ → (C.Carries p g ↔ ∃ A ∈ S.S (p (IsLocalRing.closedPoint K)), ∃ (φ₁ : c.F →+* C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) (f₁ : EigFrame Z φ₁ (stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z)) (h : Mat Dw.mult K), f₁.Coord (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) C.f0 (A₀ * A⁻¹) ∧ f₁.Coord (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom g h ∧ Par Dw.mult ⊤ h) := by
  first | exact @GlobalTheory.ShFam.CarriesAt.carries_iff | exact GlobalTheory.ShFam.CarriesAt.carries_iff | (intros; apply GlobalTheory.ShFam.CarriesAt.carries_iff <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.boundaryExtension_independent_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Z' : Model Xo c β') (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Algebra c.F K] (φ : c.F →+* V) (y : FrPt Xo c K), (algebraMap V K).comp φ = algebraMap c.F K → BdExt Z' φ y → BdExt Z φ y := by
  first | exact @GlobalTheory.CuspFrom.bdExt_of_bdExt | exact GlobalTheory.CuspFrom.bdExt_of_bdExt | (intros; apply GlobalTheory.CuspFrom.bdExt_of_bdExt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

theorem _root_.GlobalTheory.T.compact_normal_noetherian_of_flagCell_cover : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (T : Type) [Finite T] (m : T → ℕ) (B : Type) [Finite B] (V : B → X.affineOpens) (F : Scheme.{0}) (i : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ F)), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → (∀ b w, IsOpenImmersion (i b w)) → (∀ x : F, ∃ b w, x ∈ Set.range (i b w)) → CompactSpace F ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme F ∧ TopologicalSpace.NoetherianSpace F := by
  first | exact @GlobalTheory.FlagEmb.compact_normal_noetherian_of_cells | exact GlobalTheory.FlagEmb.compact_normal_noetherian_of_cells | (intros; apply GlobalTheory.FlagEmb.compact_normal_noetherian_of_cells <;> assumption)
end
