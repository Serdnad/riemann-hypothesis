module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2721
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2720
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2760
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2719
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2691
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2758
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1520
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1436
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle249
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.degenerationData_of_monomial_even_bimultiplicative : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (m : ℕ) (r : Fin m → R) (β : Fin m → LinearMap.BilinForm ℤ D.X), D.PsiEven → D.TauBimult → IsMonomial D r β → (∀ i, r i ∈ maximalIdeal R) → (∀ i y z, β i y z = β i z y) → (∀ y, y ≠ 0 → ∃ i, 0 < β i y y) → ∃ DD : DegData R (maximalIdeal R), DD.toPre = D := by
  first | exact @GlobalTheory.DegFromMonomial.main | exact GlobalTheory.DegFromMonomial.main | (intros; apply GlobalTheory.DegFromMonomial.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.exists_complete_regular_local_meet_of_flat_maps : ∀ (O R₁ R' Ω : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R₁] [IsRegularLocalRing R₁] [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'] [Field Ω] (φ₁ : O →+* R₁) (φ' : O →+* R') (u : R₁ →+* Ω) (u' : R' →+* Ω), φ₁.Flat → IsLocalHom φ₁ → IsAdicComplete (maximalIdeal R') R' → IsEtaleCompletion φ' → ((residue R').comp φ').FormallyUnramified → RingHom.ker u = maximalIdeal R₁ → RingHom.ker u' = maximalIdeal R' → u.comp φ₁ = u'.comp φ' → ∃ (E : Type) (_ : CommRing E) (_ : IsRegularLocalRing E) (_ : IsDomain E) (a : R₁ →+* E) (b : R' →+* E) (v : E →+* Ω), a.Flat ∧ b.Flat ∧ a.comp φ₁ = b.comp φ' ∧ RingHom.ker v = maximalIdeal E ∧ v.comp a = u ∧ v.comp b = u' ∧ (maximalIdeal R₁).map a = maximalIdeal E ∧ IsAdicComplete (maximalIdeal E) E := by
  first | exact @GlobalTheory.exists_complete_regular_meet | exact GlobalTheory.exists_complete_regular_meet | (intros; apply GlobalTheory.exists_complete_regular_meet <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.monomialBoundaryFamily_param_ne_zero : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {m : ℕ} (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), IsMonomial Q t gam → LinearIndependent ℤ gam → (∀ i y z, gam i y z = gam i z y) → ∀ i, t i ≠ 0 := by
  first | exact @GlobalTheory.MonoParam.t_ne_zero | exact GlobalTheory.MonoParam.t_ne_zero | (intros; apply GlobalTheory.MonoParam.t_ne_zero <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
open GlobalTheory.LocM GlobalTheory.PolFan ReciprocityTheory.AnForm.R
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartDer

theorem _root_.GlobalTheory.T.exists_closedBoundaryPoint_maximalIdeal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), SmoothOfRelativeDimension Dw.dim (genStr Y) → ∀ (U : Y.X.affineOpens) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → ∀ x : Y.X, x ∉ interior Y → x ∈ U.1 → (∀ f ∈ m, x ∉ Y.X.basicOpen f) → ∃ x' : gen Y, genι Y x' = x ∧ x' ∈ genBd Y ∧ IsClosed ({x'} : Set (gen Y)) := by
  first | exact @GlobalTheory.BoundaryPoint.exists_closed_boundary_point | exact GlobalTheory.BoundaryPoint.exists_closed_boundary_point | (intros; apply GlobalTheory.BoundaryPoint.exists_closed_boundary_point <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartDer

theorem logDer_extend_chartRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), ∀ (U : Y.X.affineOpens) (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → (ReciprocityTheory.AnForm.R.FinalTheorems.stalkId (genBdIdeal Y) (ξ (closedPoint _))).map (Scheme.stalkClosedPointTo ξ).hom = Ideal.span {∏ i, bdParam k m d i} → ∃ D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d), (∀ r, D' (((Scheme.stalkClosedPointTo ξ).hom.comp (((gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) (ξ (closedPoint _)) hx).hom.comp ((genι Y).app U.1).hom)) r) = ((Scheme.stalkClosedPointTo ξ).hom.comp (((gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) (ξ (closedPoint _)) hx).hom.comp ((genι Y).app U.1).hom)) (D.1 r)) ∧ ∀ i, D' (bdParam k m d i) ∈ Ideal.span {bdParam k m d i} := by
  intro E _ _ _ H Dw l Xo c Y U D k _ m d ξ hx hE hI
  have hiso : IsIso (genι Y) := isIso_fst Y
  set x := ξ (closedPoint _) with hxdef
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.exists_derivation_stalk_extend_of_app _ _ (genι Y) U D.1 x hx
  set g := ((gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) x hx).hom.comp ((genι Y).app U.1).hom with hg
  have hZ : ((genBd Y : TopologicalSpace.Closeds (gen Y)) : Set (gen Y)) = (genι Y) ⁻¹' ((interior Y).compl : Set Y.X) := by
    ext z
    simp only [TopologicalSpace.Opens.coe_compl, Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe]
    rw [mem_genBd]
    unfold GlobalTheory.LogKS.interior Model.j
    have hc : ∀ w, (Y.jQ ≫ pullback.fst Y.s (spMap (RingHom.id c.F))) w = genι Y (Y.jQ w) := fun w => rfl
    simp only [Scheme.Hom.coe_opensRange, Set.mem_range, hc]
    constructor
    · rintro h ⟨w, hw⟩
      exact h ⟨w, (genι Y).isOpenEmbedding.injective hw⟩
    · rintro h ⟨w, hw⟩
      exact h ⟨w, by rw [← hw]; rfl⟩
  have hJ := GlobalTheory.T.stalkIdeal_vanishingIdeal_preimage_iso _ _ (genι Y) _ (genBd Y) hZ U x hx
  have hstab : ∀ a ∈ ((Scheme.IdealSheafData.vanishingIdeal (interior Y).compl).ideal U).map g,
      δ a ∈ ((Scheme.IdealSheafData.vanishingIdeal (interior Y).compl).ideal U).map g := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨r, hr, rfl⟩ := hy
      have := hδ r
      simp only [hg, RingHom.comp_apply] at this ⊢
      rw [this]
      exact Ideal.mem_map_of_mem _ (D.2.2 r hr)
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact Ideal.add_mem _ hy hz
    | smul c y hy' hy =>
      rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_right _ _ hy')
  have hC : CharZero (ChartRing k m d) :=
    (Spec.preimage (ξ ≫ genStr Y)).hom.charZero_iff (RingHom.injective _) |>.1 inferInstance
  have hk : CharZero k := (RingHom.charZero_iff (MvPowerSeries.C_injective (σ := Fin m ⊕ Fin d) (R := k))).2 hC
  obtain ⟨D', hD'⟩ := GlobalTheory.T.exists_derivation_extension_completedEtaleChart _ k m d (Scheme.stalkClosedPointTo ξ).hom hE δ
  refine ⟨D', fun r => ?_, GlobalTheory.T.toricChart_derivation_boundaryParam_mem_span _ k m d _ δ D' _ hstab hD' (by rw [← hJ]; exact hI)⟩
  simp only [RingHom.comp_apply]
  rw [hD']
  exact congrArg _ (hδ r)

end GlobalTheory.ChartDer
end

section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem leadingTerm_unique : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (d : ℕ) (X : Type) [AddCommGroup X]
    [Module O X] [Module.Finite O X] [Module.Projective O X] [Module.Free ℤ X] [Module.Finite ℤ X], IsPolFanOn bar φ X →
    ∀ (r m : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X) (a : Fin m → X), IsCone bar φ γ → Supports bar φ d γ a →
    ∀ (β : LinearMap.BilinForm ℤ X) (k : ℕ) (c : Fin r → ℕ), 0 < k → (∀ j, 0 < c j) → k • β = ∑ j, c j • γ j →
    (∀ x, x ≠ 0 → 0 < β x x) → ∀ (e : X ≃ₗ[O] X) (N : ℕ), 3 ≤ N → (∀ x, CongMod N (e x) x) →
    d * φ.evalZ β = (∑ i, β (e (a i)) (e (a i)) : ℤ) → ∀ x, e x = x := by
  intro O _ bar φ d X _ _ _ _ _ _ hF r m γ a hγ hS β k c hk hc hβ hpos e N hN he hd
  have hkβ : ∀ y z, (k : ℤ) * β y z = ∑ j, (c j : ℤ) * γ j y z := fun y z => by
    have := LinearMap.congr_fun₂ hβ y z
    simpa [LinearMap.sum_apply, nsmul_eq_mul] using this
  have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
  have hbal : β ∈ balForms bar X := by
    refine ⟨fun y z => mul_left_cancel₀ hk0 ?_, fun o y z => mul_left_cancel₀ hk0 ?_⟩
    · rw [hkβ, hkβ]; exact Finset.sum_congr rfl fun j _ => by rw [(hγ.mem j).1]
    · rw [hkβ, hkβ]; exact Finset.sum_congr rfl fun j _ => by rw [(hγ.mem j).2]
  have hbal' : pull e.toLinearMap β ∈ balForms bar X := pull_mem _ hbal
  have hnn' : ∀ y, 0 ≤ pull e.toLinearMap β y y := fun y => by
    rw [pull_apply]
    by_cases h0 : e.toLinearMap y = 0
    · rw [h0]; simp
    · exact (hpos _ h0).le
  obtain ⟨k', c', hk', hβ'⟩ := hS.only _ hbal' hnn' (by rw [evalZ_pull φ e.surjective]; exact hd)
  have hsum : ∑ j, (k' * c j) • pull e.toLinearMap (γ j) = ∑ j, (k * c' j) • γ j := by
    refine LinearMap.ext₂ fun y z => ?_
    have h1 := hkβ (e y) (e z)
    have h2 := LinearMap.congr_fun₂ hβ' y z
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, pull_apply, nsmul_eq_mul, LinearEquiv.coe_coe] at h1 h2 ⊢
    have e1 : ∑ j, ((k' * c j : ℕ) : ℤ) * γ j (e y) (e z) = k' * ∑ j, (c j : ℤ) * γ j (e y) (e z) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by push_cast; ring
    have e2 : ∑ j, ((k * c' j : ℕ) : ℤ) * γ j y z = k * ∑ j, (c' j : ℤ) * γ j y z := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by push_cast; ring
    rw [e1, e2, ← h1, ← h2]; ring
  have hγe : IsCone bar φ fun j => pull e.toLinearMap (γ j) := hγ.pull_equiv e
  choose σ hσ using GlobalTheory.T.smoothCone_face_of_interior_common_point O bar φ X hF r r _ γ hγe hγ (fun j => k' * c j) (fun j => k * c' j)
    (fun j => Nat.mul_pos hk' (hc j)) hsum
  have hσinj : Function.Injective σ := fun i j hij => hγe.injective (by simp only [hσ, hij])
  let σe := Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hσinj)
  have hG : ∀ y z, (∑ j, γ j) (e y) (e z) = (∑ j, γ j) y z := by
    intro y z
    simp only [LinearMap.sum_apply]
    calc ∑ j, γ j (e y) (e z) = ∑ j, γ (σe j) y z :=
          Finset.sum_congr rfl fun j _ => LinearMap.congr_fun₂ (hσ j) y z
      _ = ∑ j, γ j y z := σe.sum_comp (fun j => γ j y z)
  have hGpos : ∀ x, x ≠ 0 → 0 < (∑ j, γ j) x x := by
    intro x hx
    have h2 : 0 < (k : ℤ) * β x x := mul_pos (by exact_mod_cast hk) (hpos x hx)
    rw [hkβ] at h2
    obtain ⟨j, -, hj⟩ := Finset.exists_lt_of_sum_lt (show ∑ j : Fin r, (0 : ℤ) < _ by simpa using h2)
    have hj' : 0 < γ j x x := pos_of_mul_pos_right hj (by positivity)
    simp only [LinearMap.sum_apply]
    exact hj'.trans_le (Finset.single_le_sum (fun i _ => hγ.nonneg i x) (Finset.mem_univ j))
  have key := GlobalTheory.T.isometry_eq_refl_of_congr_mod_ge_three X (∑ j, γ j) hGpos e.toAddEquiv.toIntLinearEquiv (fun y z => hG y z) N hN he
  intro x
  simpa using LinearEquiv.congr_fun key x

end GlobalTheory.Poinc
end

section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc Matrix

namespace GlobalTheory.Poinc

theorem posDef_map_int_of_pos {n : ℕ} (L : Matrix (Fin n) (Fin n) ℤ) (hs : L.IsSymm)
    (hp : ∀ ξ : Fin n → ℤ, ξ ≠ 0 → 0 < ξ ⬝ᵥ (L *ᵥ ξ)) : (L.map (Int.cast : ℤ → ℝ)).PosDef := by
  set M := L.map (Int.cast : ℤ → ℝ) with hM
  have hH : M.IsHermitian := by
    refine Matrix.IsHermitian.ext fun i j => ?_
    simp [M, hs.apply]
  have hdet : L.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hLv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have := hp v hv
    rw [hLv, dotProduct_zero] at this
    exact lt_irrefl _ this
  have hint : ∀ z : Fin n → ℤ, (fun i => (z i : ℝ)) ⬝ᵥ (M *ᵥ fun i => (z i : ℝ)) = ((z ⬝ᵥ (L *ᵥ z) : ℤ) : ℝ) := by
    intro z
    simp [M, dotProduct, mulVec]
  have hrat : ∀ t : Fin n → ℚ, 0 ≤ (fun i => (t i : ℝ)) ⬝ᵥ (M *ᵥ fun i => (t i : ℝ)) := by
    intro t
    obtain ⟨⟨D, hD⟩, hn⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) t
    choose z hz using hn
    have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hD
    have hz' : (fun i => (z i : ℝ)) = (D : ℝ) • fun i => (t i : ℝ) := by
      funext i
      have h1 : (z i : ℚ) = D * t i := by simpa [Submonoid.smul_def] using hz i
      have h2 := congrArg (Rat.cast : ℚ → ℝ) h1
      push_cast at h2
      simpa using h2
    have h0 : 0 ≤ z ⬝ᵥ (L *ᵥ z) := by
      rcases eq_or_ne z 0 with h | h
      · simp [h]
      · exact (hp z h).le
    have h3 := hint z
    rw [hz', mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at h3
    have h4 : 0 ≤ ((D : ℝ) * D) * ((fun i => (t i : ℝ)) ⬝ᵥ (M *ᵥ fun i => (t i : ℝ))) := by
      rw [mul_assoc, h3]; exact_mod_cast h0
    exact (mul_nonneg_iff_of_pos_left (mul_self_pos.2 hD')).1 h4
  have hpsd : M.PosSemidef := by
    refine posSemidef_iff_dotProduct_mulVec.2 ⟨hH, fun y => ?_⟩
    rw [star_trivial]
    have hcl : IsClosed {y : Fin n → ℝ | 0 ≤ y ⬝ᵥ (M *ᵥ y)} :=
      isClosed_le continuous_const
        (Continuous.dotProduct continuous_id (Continuous.matrix_mulVec continuous_const continuous_id))
    exact (DenseRange.piMap fun _ => Rat.denseRange_cast).induction_on y hcl fun t => hrat t
  have hdetM : M.det = (L.det : ℝ) := by
    rw [hM]
    exact ((Int.castRingHom ℝ).map_det L).symm
  refine posDef_iff_dotProduct_mulVec.2 ⟨hH, fun x hx => ?_⟩
  refine lt_of_le_of_ne ((posSemidef_iff_dotProduct_mulVec.1 hpsd).2 x) fun h0 => hdet ?_
  have hk : M *ᵥ x = 0 := hpsd.dotProduct_mulVec_zero_iff.1 (by simpa using h0.symm)
  have : M.det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨x, hx, hk⟩
  rw [hdetM] at this
  exact_mod_cast this

end GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem exists_supports_int : ∀ (φ : InvFun ℤ) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X],
    IsPolFanOn id φ X → ∀ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X), IsCone id φ γ →
      ∃ (d m : ℕ) (a : Fin m → X), 1 ≤ d ∧ Supports id φ d γ a := by
  intro φ X _ _ _ hφ r γ hγ
  classical
  have hstrict := hγ.strict
  unfold IsStrict at hstrict
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hstrict
  let b := Module.finBasis ℤ X
  let S : Fin (Module.finrank ℤ X) → Fin (Module.finrank ℤ X) → LinearMap.BilinForm ℤ X := fun i j =>
    (LinearMap.mul ℤ ℤ).compl₁₂ (b.coord i) (b.coord j) + (LinearMap.mul ℤ ℤ).compl₁₂ (b.coord j) (b.coord i)
  have hS : ∀ i j x y, S i j x y = b.repr x i * b.repr y j + b.repr x j * b.repr y i := by
    intro i j x y; simp [S]
  let L : Matrix (Fin (Module.finrank ℤ X)) (Fin (Module.finrank ℤ X)) ℤ := Matrix.of fun i j => ℓ (S i j)
  have hL : ∀ i j, L i j = ℓ (S i j) := fun _ _ => rfl
  have hexp : ∀ (β : LinearMap.BilinForm ℤ X) x y,
      β x y = ∑ i, ∑ j, b.repr x i * b.repr y j * β (b i) (b j) := by
    intro β x y
    conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]

    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hA : ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) →
      ∑ i, ∑ j, β (b i) (b j) * L i j = 2 * ℓ β := by
    intro β hβ
    have hsum : ∑ i, ∑ j, β (b i) (b j) • S i j = (2 : ℤ) • β := by
      refine LinearMap.ext₂ fun x y => ?_
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hS]
      have e : (2 : ℤ) * β x y = β x y + β y x := by rw [hβ y x]; ring
      rw [e, hexp β x y, hexp β y x, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have := congrArg ℓ hsum

    simp only [map_sum, map_smul, smul_eq_mul] at this
    simpa only [hL] using this
  have hsym : L.IsSymm := Matrix.IsSymm.ext fun i j => by simp only [hL, S, add_comm]
  have hpos : ∀ ξ : Fin (Module.finrank ℤ X) → ℤ, ξ ≠ 0 → 0 < ξ ⬝ᵥ (L *ᵥ ξ) := by
    intro ξ hξ
    let l : X →ₗ[ℤ] ℤ := ∑ i, ξ i • b.coord i
    have hl : ∀ i, l (b i) = ξ i := by
      intro i
      simp [l, Finsupp.single_apply]
    have hsymm : ∀ y z, sqForm l y z = sqForm l z y := fun y z => by simp [mul_comm]
    have hmem : sqForm l ∈ balForms id X := mem_balForms_int.2 hsymm
    have hnn : ∀ y, 0 ≤ sqForm l y y := fun y => by simpa using mul_self_nonneg (l y)
    have hne : sqForm l ≠ 0 := by
      intro h0
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hξ
      have := LinearMap.congr_fun₂ h0 (b i) (b i)
      simp [hl] at this
      exact hi this
    have hφp := hφ.pos _ hmem hnn hne
    have hℓ := h2 _ hmem hnn
    have hℓpos : 0 < ℓ (sqForm l) := by
      have : (0 : ℝ) < ℓ (sqForm l) := lt_of_lt_of_le (mul_pos (by exact_mod_cast hN) hφp) hℓ
      exact_mod_cast this
    have h5 := hA (sqForm l) hsymm
    simp only [sqForm_apply, hl] at h5
    have e : ξ ⬝ᵥ (L *ᵥ ξ) = ∑ i, ∑ j, ξ i * ξ j * L i j := by
      simp only [dotProduct, mulVec, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [e, h5]
    omega
  obtain ⟨D, m, a, hD, hspan, hsum⟩ := GlobalTheory.T.exists_smul_eq_sum_vecMulVec_spanning_family _ L (posDef_map_int_of_pos L hsym hpos)
  let x : Fin m → X := fun k => b.equivFun.symm (a k)
  have hx : ∀ k i, b.repr (x k) i = a k i := fun k i => by
    show b.equivFun (b.equivFun.symm (a k)) i = a k i
    rw [b.equivFun.apply_symm_apply]
  have hB : ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) →
      ∑ k, β (x k) (x k) = 2 * D * ℓ β := by
    intro β hβ
    have hsum' : ∀ i j, (D : ℤ) * L i j = ∑ k, a k i * a k j := by
      intro i j
      have := congrFun (congrFun hsum i) j
      simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using this
    calc ∑ k, β (x k) (x k) = ∑ k, ∑ i, ∑ j, a k i * a k j * β (b i) (b j) :=
          Finset.sum_congr rfl fun k _ => by rw [hexp β]; simp only [hx]
      _ = ∑ i, ∑ j, β (b i) (b j) * ((D : ℤ) * L i j) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hsum' i j, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = D * (2 * ℓ β) := by
          rw [← hA β hβ, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = 2 * D * ℓ β := by ring
  have hspanX : Submodule.span ℤ (Set.range x) = ⊤ := by
    have e : Set.range x = (b.equivFun.symm.toLinearMap : (Fin (Module.finrank ℤ X) → ℤ) →ₗ[ℤ] X) '' Set.range a :=
      Set.range_comp _ _
    rw [e, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  have hD0 : (0 : ℝ) < 2 * D := by have : (1 : ℝ) ≤ D := by exact_mod_cast hD
                                   linarith
  refine ⟨2 * D * N, m, x, Nat.one_le_iff_ne_zero.2 (by positivity), ⟨hspanX, ?_, ?_, ?_⟩⟩
  · intro β hβ hp
    rw [hB β (mem_balForms_int.1 hβ)]
    have := h2 β hβ hp
    push_cast
    nlinarith
  · intro j
    rw [hB (γ j) (mem_balForms_int.1 (hγ.mem j))]
    push_cast
    rw [h1 j]
    ring
  · intro β hβ hp he
    rw [hB β (mem_balForms_int.1 hβ)] at he
    push_cast at he
    refine h3 β hβ hp (mul_left_cancel₀ hD0.ne' ?_)
    linear_combination he

end GlobalTheory.Poinc
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem GlobalTheory.GenNef.isNef_ratFibre : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L : HermLB p, NefFib L → (letI := GlobalTheory.algebraΓOfHom (Limits.pullback.snd (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))); GlobalTheory.IsNef ℚ (L.B.pull (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))))) := by
  intro k _ X _ p D hX L hL
  haveI := hX.finite
  letI := GlobalTheory.algebraΓOfHom (Limits.pullback.snd (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)))
  refine ⟨LB.isLB_pull L.isLB _, fun Z hZ => ?_⟩
  obtain ⟨W, w, z, _, hW, hzw, hpb⟩ := GlobalTheory.T.exists_closure_curve_rationalFibre_arithmeticSurface k X p D hX Z hZ
  have e := GlobalTheory.T.rationalDegree_pullback_eq_reducedIntersectionNumber k X p Z hZ W w z hW hzw hpb L.B L.isLB
  have h0 := NefGeneric.ratDeg_nonneg k W (w ≫ p) (L.pull w rfl) hW
    (ArInt.nefFib_pull k X W p (w ≫ p) hX.isProjOver hW.isProjOver w rfl L hL)
  change 0 ≤ ratDeg (w ≫ p) (L.B.pull w) at h0
  rw [e] at h0
  exact h0
end
