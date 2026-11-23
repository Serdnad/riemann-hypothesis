module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsResEqOfUnitInChart
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusVia
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteExtGeomIntegralLocalization
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle017
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AwayToAwayRightEqOfComp
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section

namespace GlobalTheory.JacSer

section Algebra

open IsLocalRing MvPowerSeries GlobalTheory.SqZero

variable {O : Type} [CommRing O] [IsLocalRing O]

theorem isLocalRing_trivSqZeroExt (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] :
    IsLocalRing (TrivSqZeroExt O M) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact isUnit_or_isUnit_one_sub_self _


omit [IsLocalRing O] in
def dirPt {n : ℕ} (e : MvPowerSeries (Fin n) O →ₐ[O] O) (c : Fin n → O) :
    MvPowerSeries (Fin n) O →ₐ[O] DualNumber O :=
  addDer ((inlS O O).comp e) (TrivSqZeroExt.inrHom O O ∘ₗ
      ∑ j, c j • (e.toLinearMap ∘ₗ (pderiv (R := O) j).toLinearMap))
    (fun a b => by
      ext
      · simp [TrivSqZeroExt.fst_sum]
      · simp [TrivSqZeroExt.snd_sum, Finset.mul_sum, ← Finset.sum_add_distrib, mul_add]
        exact Finset.sum_congr rfl fun _ _ => by ring)
    (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)

omit [IsLocalRing O] in
theorem dirPt_fst {n : ℕ} (e : MvPowerSeries (Fin n) O →ₐ[O] O) (c : Fin n → O) (a : MvPowerSeries (Fin n) O) :
    (dirPt e c a).fst = e a := add_zero (e a)

omit [IsLocalRing O] in
theorem dirPt_snd {n : ℕ} (e : MvPowerSeries (Fin n) O →ₐ[O] O) (c : Fin n → O) (a : MvPowerSeries (Fin n) O) :
    (dirPt e c a).snd = ∑ j, c j * e (pderiv (R := O) j a) :=
  (zero_add _).trans ((TrivSqZeroExt.snd_inr _ _).trans (by simp))

omit [IsLocalRing O] in
theorem dirPt_snd_X {n : ℕ} (e : MvPowerSeries (Fin n) O →ₐ[O] O) (c : Fin n → O) (i : Fin n) :
    (dirPt e c (X i)).snd = c i := by
  simp [dirPt_snd, pderiv_X, Pi.single_apply, apply_ite e]

variable [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]

theorem snd_eq_sum {n : ℕ} (e : MvPowerSeries (Fin n) O →ₐ[O] O) (he : ∀ i, e (X i) ∈ maximalIdeal O)
    (ψ : MvPowerSeries (Fin n) O →ₐ[O] DualNumber O) (hψ : ∀ a, (ψ a).fst = e a) (a : MvPowerSeries (Fin n) O) :
    (ψ a).snd = ∑ j, (ψ (X j)).snd * e (pderiv (R := O) j a) := by
  have := isLocalRing_trivSqZeroExt (O := O) O
  have : Module.Finite O (DualNumber O) := inferInstanceAs (Module.Finite O (O × O))
  have := GlobalTheory.FormalIsogeny.isAdicComplete_maximalIdeal_of_finite O (DualNumber O)
  have h : ψ = dirPt e fun j => (ψ (X j)).snd :=
    mvPowerSeries_algHom_ext_of_isHausdorff (maximalIdeal (DualNumber O))
      (fun i h => he i (hψ _ ▸ TrivSqZeroExt.isUnit_iff_isUnit_fst.1 h))
      (fun i => TrivSqZeroExt.ext (by rw [hψ, dirPt_fst]) (by rw [dirPt_snd_X]))
  exact (congrArg (fun q => (q a).snd) h).trans (dirPt_snd _ _ _)

omit [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] in
theorem isLocalHom_of_X_mem {n : ℕ} (e : MvPowerSeries (Fin n) O →ₐ[O] O) (he : ∀ i, e (X i) ∈ maximalIdeal O) :
    IsLocalHom e.toRingHom := by
  refine ((IsLocalRing.local_hom_tfae _).out 1 4).2 fun g hg => ?_
  have h1 := algHom_sub_constantCoeff_mem e he g
  have h2 := (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff (g := g)).1 hg
  simpa using add_mem h1 h2

end Algebra

section Group

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD isTan_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory.SqZero GlobalTheory.LieComb IsLocalRing MvPowerSeries

attribute [local instance] Over.cartesianMonoidalCategory

variable {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
  {G : Over (Spec (CommRingCat.of O))} [GrpObj G] [IsCommMonObj G] {n : ℕ} {v : Fin n → (epsR O ⟶ G)}

theorem exists_matrix (hv : IsLieBasis v) (j : sp (R₀ := O) (MvPowerSeries (Fin n) O) ⟶ G)
    (inj : ∀ {T : Type} [CommRing T] [Algebra O T] (φ ψ : MvPowerSeries (Fin n) O →ₐ[O] T),
      spMap φ ≫ j = spMap ψ ≫ j → ∀ i, φ (X i) = ψ (X i))
    (z : 𝟙_ _ ⟶ G) (u : MvPowerSeries (Fin n) O →ₐ[O] O) (hu0 : ∀ i, u (X i) ∈ maximalIdeal O)
    (hu : spMap u ≫ j = toUnit _ ≫ z)
    (χ : MvPowerSeries (Fin n) O →ₐ[O] TrivSqZeroExt O (Fin n → O))
    (hχ : spMap χ ≫ j = (toUnit _ ≫ z) * lieExp v (fun i => inr (Pi.single i 1))
      (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)) :
    ∃ C : Matrix (Fin n) (Fin n) O, IsUnit C.det ∧
      ∀ k, ∃ φ : MvPowerSeries (Fin n) O →ₐ[O] DualNumber O, spMap φ ≫ j = (toUnit _ ≫ z) * v k ∧
        ∀ a, (φ a).snd = ∑ i, u (pderiv (R := O) i a) * C i k := by
  have hz : ∀ {T T' : Type} [CommRing T] [Algebra O T] [CommRing T'] [Algebra O T'] (φ : T →ₐ[O] T'),
      spMap φ ≫ toUnit _ ≫ z = toUnit _ ≫ z := fun φ => by
    rw [← Category.assoc, comp_toUnit]
  have hfst : ∀ a, (χ a).fst = u a := by
    refine fun a => (AlgHom.congr_fun (mvPowerSeries_algHom_ext_of_isHausdorff (maximalIdeal O) hu0
      (inj u ((TrivSqZeroExt.fstHom O O _).comp χ) ?_)) a).symm
    rw [← spMap_comp, Category.assoc, hχ, MonObj.comp_mul, hz, comp_lieExp,
      lieExp_eq_one hv.1 _ (fun i => by rfl), mul_one, hu]
  let φ : (Fin n → O) → (MvPowerSeries (Fin n) O →ₐ[O] DualNumber O) := fun c =>
    (vecTo (inlS O O) (fun i => inr (c i)) (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)).comp χ
  have hφ : ∀ c, spMap (φ c) ≫ j = (toUnit _ ≫ z) * tanExp v c := fun c => by
    rw [← spMap_comp, Category.assoc, hχ, MonObj.comp_mul, hz, comp_lieExp]
    exact congrArg _ (lieExp_congr _ (fun i => vecTo_single _ _ _ i) _ _)
  have hφ1 : ∀ c a, (φ c a).fst = u a := fun c a => by
    simp [φ, vecTo_apply, TrivSqZeroExt.fst_sum, hfst]
  have hφ2 : ∀ c a, (φ c a).snd = ∑ k, (χ a).snd k * c k := fun c a => by
    simp [φ, vecTo_apply, TrivSqZeroExt.snd_sum, mul_comm]
  obtain ⟨-, hsurj⟩ := isLieBasisOver_self hv
  have hM : ∀ l : Fin n, ∃ c : Fin n → O, ∀ i, ∑ k, (χ (X i)).snd k * c k = (Pi.single l 1 : Fin n → O) i := by
    intro l
    have h1 : (fstS O O).comp (dirPt u (Pi.single l 1)) = u := AlgHom.ext fun a => dirPt_fst _ _ a
    obtain ⟨c, hc⟩ := hsurj ((toUnit _ ≫ z)⁻¹ * (spMap (dirPt u (Pi.single l 1)) ≫ j)) (by
      rw [IsTanOver, MonObj.comp_mul, GrpObj.comp_inv, hz, ← Category.assoc, spMap_comp, h1, hu,
        inv_mul_cancel])
    have h2 := inj (dirPt u (Pi.single l 1)) (φ c) (by rw [hφ, ← hc, mul_inv_cancel_left])
    exact ⟨c, fun i => by rw [← hφ2, ← h2, dirPt_snd_X]⟩
  choose M hM using hM
  refine ⟨Matrix.of fun i k => (χ (X i)).snd k, ?_, fun k => ⟨φ (Pi.single k 1), ?_, fun a => ?_⟩⟩
  · refine Matrix.isUnit_det_of_right_inverse (B := Matrix.of fun k l => M l k) (Matrix.ext fun i l => ?_)
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact (hM l i).trans (Pi.single_apply _ _ _)
  · rw [hφ, tanExp_single hv.1]
  · rw [snd_eq_sum u hu0 _ (hφ1 _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hφ2, mul_comm]
    simp [Pi.single_apply]

end Group

end GlobalTheory.JacSer

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

theorem GlobalTheory.KeyKa.jac_eq_unit_mul_det_pderiv : ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (x : KeyIn O) (θ : Sp (MvPowerSeries (Fin x.P.g) O) ⟶ x.P.A.left) (z : Pt x) (e : (MvPowerSeries (Fin x.P.g) O) →ₐ[O] O), θ ≫ x.P.A.hom = spMap (algebraMap O (MvPowerSeries (Fin x.P.g) O)) → (∃ (V : x.P.A.left.Opens) (t : Fin x.P.g → Γ(x.P.A.left, V)), ⊤ ≤ θ ⁻¹ᵁ V ∧ ∀ i, valT (T := (MvPowerSeries (Fin x.P.g) O)) θ V (t i) = MvPowerSeries.X i) → (∀ (T : Type) [CommRing T] [IsLocalRing T] [Algebra O T] [IsAdicComplete (IsLocalRing.maximalIdeal T) T] (w : Sp T ⟶ x.P.A.left), w ≫ x.P.A.hom = spMap (algebraMap O T) → w (IsLocalRing.closedPoint T) = θ (IsLocalRing.closedPoint (MvPowerSeries (Fin x.P.g) O)) → ∃ e : (MvPowerSeries (Fin x.P.g) O) →ₐ[O] T, (∀ i, e (MvPowerSeries.X i) ∈ IsLocalRing.maximalIdeal T) ∧ spMap e.toRingHom ≫ θ = w) → (∀ i, e (MvPowerSeries.X i) ∈ IsLocalRing.maximalIdeal O) → spMap e.toRingHom ≫ θ = z.left → ∃ u : Oˣ, ∀ (n : ℕ) (s : Fin x.P.g → RR x n) (c : x.P.L.ι), ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c → jac x s z c = u * e (Matrix.of fun i j => MvPowerSeries.pderiv (R := O) j (valT (T := (MvPowerSeries (Fin x.P.g) O)) θ (x.P.L.U c) ((s i).f c))).det := by
  intro O _ _ _ _ x θ z e hθ ⟨V, t, hV, ht⟩ hlift he hz
  let j : Chart.sp (R₀ := O) (MvPowerSeries (Fin x.P.g) O) ⟶ x.P.A := Over.homMk θ hθ
  have hloc := GlobalTheory.JacSer.isLocalHom_of_X_mem e he
  have hcl : z.left (IsLocalRing.closedPoint O) = θ (IsLocalRing.closedPoint (MvPowerSeries (Fin x.P.g) O)) := by
    rw [← hz, ← IsLocalRing.comap_closedPoint e.toRingHom]
    rfl
  have hu : Chart.spMap e ≫ j = toUnit _ ≫ z := by
    apply Over.OverMorphism.ext
    have e1 : (toUnit (Chart.sp (R₀ := O) O)).left = 𝟙 (Sp O) := by
      rw [Over.toUnit_left]
      exact Spec.map_id _
    rw [Over.comp_left, Over.comp_left, e1]
    exact hz.trans (Category.id_comp _).symm
  have := GlobalTheory.JacSer.isLocalRing_trivSqZeroExt (O := O) (Fin x.P.g → O)
  have : Module.Finite O (TrivSqZeroExt O (Fin x.P.g → O)) :=
    inferInstanceAs (Module.Finite O (O × (Fin x.P.g → O)))
  have := GlobalTheory.FormalIsogeny.isAdicComplete_maximalIdeal_of_finite O (TrivSqZeroExt O (Fin x.P.g → O))
  let w : Chart.sp (R₀ := O) (TrivSqZeroExt O (Fin x.P.g → O)) ⟶ x.P.A :=
    (toUnit _ ≫ z) * GlobalTheory.SqZero.lieExp x.v (fun i => TrivSqZeroExt.inr (Pi.single i 1))
      (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)
  obtain ⟨χ, -, hχ⟩ := hlift (TrivSqZeroExt O (Fin x.P.g → O)) w.left (Over.w w) (by
    have h1 : IsLocalHom (TrivSqZeroExt.fstHom O O (Fin x.P.g → O)).toRingHom :=
      ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩
    have h2 : Chart.spMap (TrivSqZeroExt.fstHom O O (Fin x.P.g → O)) ≫ w = Chart.spMap e ≫ j := by
      rw [hu, MonObj.comp_mul, GlobalTheory.SqZero.comp_lieExp, GlobalTheory.SqZero.lieExp_eq_one x.basis.1 _ (fun i => by rfl),
        _root_.mul_one, ← Category.assoc, comp_toUnit]
    have h3 := congrArg (fun q => q.left (IsLocalRing.closedPoint O)) h2
    rw [← IsLocalRing.comap_closedPoint (TrivSqZeroExt.fstHom O O (Fin x.P.g → O)).toRingHom,
      ← IsLocalRing.comap_closedPoint e.toRingHom]
    exact h3)
  obtain ⟨C, hC, hφ⟩ := GlobalTheory.JacSer.exists_matrix x.basis j (fun φ ψ h i => by
    have h1 : spMap φ.toRingHom ≫ θ = spMap ψ.toRingHom ≫ θ := congrArg (·.left) h
    have h2 := EtBaseChange.valT_spMap φ.toRingHom θ hV (t i)
    rw [h1, EtBaseChange.valT_spMap ψ.toRingHom θ hV, ht] at h2
    exact h2.symm) z e he hu χ (Over.OverMorphism.ext hχ)
  refine ⟨hC.unit, fun n s c hc => ?_⟩
  have hθc : ⊤ ≤ θ ⁻¹ᵁ x.P.L.U c := fun p _ =>
    ((IsLocalRing.specializes_closedPoint p).map θ.continuous).mem_open (x.P.L.U c).isOpen
      (hcl ▸ hc (x := IsLocalRing.closedPoint O) trivial)
  rw [IsUnit.unit_spec, _root_.mul_comm, AlgHom.map_det, ← Matrix.det_mul]
  refine congrArg Matrix.det (Matrix.ext fun i k => ?_)
  obtain ⟨φ, h1, h2⟩ := hφ k
  rw [Matrix.mul_apply, Matrix.of_apply]
  refine Eq.trans (congrArg TrivSqZeroExt.snd ?_) (h2 _)
  exact (congrArg (fun q : epsR O ⟶ x.P.A => valT (T := DualNumber O) q.left (x.P.L.U c) ((s i).f c)) h1.symm).trans
    (EtBaseChange.valT_spMap φ.toRingHom θ hθc _)

end
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

theorem _root_.GlobalTheory.T.exists_normalising_unit_similitude_origin : ∀ (R : Type) [CommRing R] (x : KeyIn R) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (ξ : Fin 4 → Pt x) (mu : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] ![1, -(m : ℤ) ^ 2])) (w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))), m ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → (∀ c, (List.ofFn fun r : Fin 4 => ξ r ^ al r c).prod = 1) → mu.IsGen → w.IsGen → ∃ rho : Rˣ, ∀ (p : (𝟙_ (Over (Sp R))).left) J, Good x.P.L p J → (val w (eSec (Out.powObj x.P.A 4)) p J ^ (m ^ 2) * ∏ r, val mu (ξ r).left p J).val = gs (𝟙_ (Over (Sp R))).hom p ⊤ (cst (𝟙 (Sp R)) ⊤ rho) * (val x.rig (𝟙 _) p J ^ (4 - 4 * (m : ℤ) ^ 3)).val := by
  first | exact @GlobalTheory.SimilUnit.exists_normalising_unit | exact GlobalTheory.SimilUnit.exists_normalising_unit | (intros; apply GlobalTheory.SimilUnit.exists_normalising_unit <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.geom_integral_base_change_and_localization : ∀ (K K' R : Type) [Field K] [Field K'] [Algebra K K'] [CommRing R] [Algebra K R], GeomInt K R → GeomInt K' (K' ⊗[K] R) ∧ ∀ r : R, r ≠ 0 → GeomInt K (Localization.Away r) := by
  first | exact @GlobalTheory.KeyFam.geomInt_baseChange_and_away | exact GlobalTheory.KeyFam.geomInt_baseChange_and_away | (intros; apply GlobalTheory.KeyFam.geomInt_baseChange_and_away <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.lift_idempotent_eq_of_sameComplexComponent : ∀ (K : Type) [Field K] [Algebra K ℂ] (X : Scheme.{0}) (s : X ⟶ Sp K) (R : Type) [CommRing R] [Algebra K R] (i : Sp R ⟶ X) (p q : R →ₐ[K] ℂ), Smooth s → IsOpenImmersion i → i ≫ s = spMap (algebraMap K R) → SameComp s (algebraMap K ℂ) (spMap p.toRingHom ≫ i) (spMap q.toRingHom ≫ i) → ∀ e : ℂ ⊗[K] R, IsIdempotentElem e → Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) p (fun _ _ => Commute.all _ _) e = Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) q (fun _ _ => Commute.all _ _) e := by
  first | exact @GlobalTheory.KeyFam.lift_eq_of_sameComp_of_isIdempotentElem | exact GlobalTheory.KeyFam.lift_eq_of_sameComp_of_isIdempotentElem | (intros; apply GlobalTheory.KeyFam.lift_eq_of_sameComp_of_isIdempotentElem <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.exists_finite_ext_geom_integral_localization : ∀ (K : Type) [Field K] [NumberField K] [Algebra K ℂ] (R : Type) [CommRing R] [Algebra K R] [Algebra.Smooth K R] (p : R →ₐ[K] ℂ), ∃ (k : IntermediateField K ℂ) (e : k ⊗[K] R), FiniteDimensional K k ∧ IsIdempotentElem e ∧ Algebra.TensorProduct.lift k.val p (fun _ _ => Commute.all _ _) e = 1 ∧ GeomInt k (Localization.Away e) := by
  first | exact @GlobalTheory.GeomComp.exists_geomInt_component | exact GlobalTheory.GeomComp.exists_geomInt_component | (intros; apply GlobalTheory.GeomComp.exists_geomInt_component <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyKa
open EtBaseChange

theorem section_ext_of_apply_eq {K : Type} [Field K] {X : Scheme.{0}} (t : X ⟶ Sp K) (a b : Sp K ⟶ X)
    (ha : a ≫ t = 𝟙 _) (hb : b ≫ t = 𝟙 _) (p : Sp K) (h : a p = b p) : a = b := by
  obtain ⟨⟨y, α⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective a
  obtain ⟨⟨y', β⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective b
  simp only [Scheme.SpecToEquivOfField_symm_apply] at ha hb h ⊢
  have hy : y = y' := by simpa using h
  subst hy
  obtain ⟨c, hc⟩ := Spec.map_surjective (X.fromSpecResidueField y ≫ t)
  rw [Category.assoc, ← hc, ← Spec.map_comp, ← Spec.map_id] at ha hb
  have h₁ := Spec.map_injective ha
  have h₂ := Spec.map_injective hb
  have e₁ : ∀ k, α.hom (c.hom k) = k := fun k => congrArg (fun q => q.hom k) h₁
  have e₂ : ∀ k, β.hom (c.hom k) = k := fun k => congrArg (fun q => q.hom k) h₂
  have : α = β := by
    ext k
    have e₃ : c.hom (α.hom k) = k := α.hom.injective (e₁ _)
    exact (e₂ (α.hom k)).symm.trans (congrArg β.hom e₃)
  rw [this]

theorem etZ_of_jac_ne_zero : ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] (x : KeyIn O) (x' : KeyIn K) (f : O →+* K) φ w (n d : ℕ) (hg : x'.P.g = x.P.g) (s : Fin x.P.g → RR x n) (s' : Fin x'.P.g → RR x' n) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), Function.Injective f → KeyVia x' x f φ w → (∀ i, SecVia x' x φ w (s' i) (s (i.cast hg))) → (∀ a, ⊤ ≤ (z a).left ⁻¹ᵁ x.P.L.U (ch a)) → (∀ a i, valT (T := O) (z a).left (x.P.L.U (ch a)) ((s i).f (ch a)) = 0) → (∀ a, jac x s (z a) (ch a) ≠ 0) → Function.Injective z → (∀ y : x.P.A.left, (∃ q : Sp K, spMap f q = x.P.A.hom y) → (∀ i, y ∉ Out.nonzeroLocus (s i)) → ∃ a, ∃ p : Sp O, (z a).left p = y) → ∃ (z' : Fin d → Pt x') (ch' : Fin d → x'.P.L.ι) (u : Fin d → Kˣ), EtZ x' s' z' ch' ∧ ∀ (l : ℕ) (sg : RR x l) (sg' : RR x' l) (a), SecVia x' x φ w sg' sg → valT (T := K) (z' a).left (x'.P.L.U (ch' a)) (sg'.f (ch' a)) * (u a : K) ^ l = f (valT (T := O) (z a).left (x.P.L.U (ch a)) (sg.f (ch a))) := by
  intro O K _ _ _ x x' f φ w n d hg s s' z ch hf ⟨_, _, F, hp, _, _, _, hF₁, hF₂, hv⟩ hs hz₁ hz₂ hz₃ hz₄ hz₅
  have hw : ∀ a, (spMap f ≫ (z a).left) ≫ x.P.A.hom = 𝟙 _ ≫ spMap f := fun a =>
    (Category.assoc _ _ _).trans ((congrArg (spMap f ≫ ·) (Over.w (z a))).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm))
  let z' : Fin d → Pt x' := fun a => Over.homMk (hp.1.lift (spMap f ≫ (z a).left) (𝟙 _) (hw a)) (hp.1.lift_snd _ _ _)
  have hz' : ∀ a, (z' a).left ≫ φ = spMap f ≫ (z a).left := fun a => hp.1.lift_fst _ _ _
  have hch : ∀ a, ∃ i, ⊤ ≤ (z' a).left ⁻¹ᵁ x'.P.L.U i := fun a => by
    obtain ⟨i, hi⟩ := exists_chart x'.P.isLB ((z' a).left (IsLocalRing.closedPoint K))
    exact ⟨i, fun p _ => ((IsLocalRing.specializes_closedPoint p).map (z' a).left.continuous).mem_open
      (x'.P.L.U i).isOpen hi⟩
  choose ch' hch' using hch
  have hφ : ∀ a, ⊤ ≤ ((z' a).left ≫ φ) ⁻¹ᵁ x.P.L.U (ch a) := fun a p _ => by
    rw [hz' a]
    exact hz₁ a (show spMap f p ∈ ⊤ from trivial)
  have hW := fun a => le_inf_pull (T := K) (z' a).left (ch a) (ch' a) (hφ a) (hch' a)
  let u : Fin d → Kˣ := fun a => Units.map (valH (T := K) (z' a).left _ (hW a)).toMonoidHom (w.s (fun _ => ch a, ch' a))
  have hu : ∀ a, valT (T := K) (z' a).left ((x.P.L.pull φ).U (fun _ => ch a) ⊓ x'.P.L.U (ch' a))
      (w.s (fun _ => ch a, ch' a)).val = u a := fun a => valT_eq _ _ (hW a) _
  have hval : ∀ (l : ℕ) (sg : RR x l) (sg' : RR x' l) (a), SecVia x' x φ w sg' sg →
      valT (T := K) (z' a).left (x'.P.L.U (ch' a)) (sg'.f (ch' a)) * (u a : K) ^ l =
        f (valT (T := O) (z a).left (x.P.L.U (ch a)) (sg.f (ch a))) := fun l sg sg' a h => by
    have e := valT_via (T := K) h (z' a).left (ch a) (ch' a) (hφ a) (hch' a)
    rw [hu] at e
    refine (_root_.mul_comm _ _).trans (e.symm.trans ?_)
    exact (congrArg (fun q => valT (T := K) q (x.P.L.U (ch a)) (sg.f (ch a))) (hz' a)).trans
      (valT_spMap f (z a).left (hz₁ a) _)
  have hzero : ∀ a i, valT (T := K) (z' a).left (x'.P.L.U (ch' a)) ((s' i).f (ch' a)) = 0 := fun a i => by
    have e := hval n _ _ a (hs i)
    rw [hz₂, map_zero] at e
    exact ((u a).isUnit.pow n).mul_left_eq_zero.1 e
  have hjac : ∀ a, jac x' s' (z' a) (ch' a) * (u a : K) ^ (x.P.g * n) = f (jac x s (z a) (ch a)) := fun a => by
    have ent : ∀ i k, f (TrivSqZeroExt.snd (valT (T := DualNumber O) ((toUnit (epsR O) ≫ z a) * x.v (k.cast hg)).left
        (x.P.L.U (ch a)) ((s (i.cast hg)).f (ch a)))) = (u a : K) ^ n * TrivSqZeroExt.snd (valT (T := DualNumber K)
          ((toUnit (epsR K) ≫ z' a) * x'.v k).left (x'.P.L.U (ch' a)) ((s' i).f (ch' a))) := fun i k => by
      have c := translate_comp hp F hF₁ (z a) (z' a) (hz' a) (x.v (k.cast hg)) (x'.v k) (hv k)
      have l₁ := translate_le (z a) (x.v (k.cast hg)) (x.basis.1 _) (hz₁ a)
      have l₂ := translate_le (z' a) (x'.v k) (x'.basis.1 _) (hch' a)
      have l₃ : ⊤ ≤ (((toUnit (epsR K) ≫ z' a) * x'.v k).left ≫ φ) ⁻¹ᵁ x.P.L.U (ch a) := fun p _ => by
        rw [c]
        exact l₁ (show spMap F p ∈ ⊤ from trivial)
      have e := valT_via (T := DualNumber K) (hs i) _ (ch a) (ch' a) l₃ l₂
      have e₂ := (congrArg (fun q => valT (T := DualNumber K) q (x.P.L.U (ch a)) ((s (i.cast hg)).f (ch a))) c).trans
        (valT_spMap F _ l₁ _)
      refine (snd_map f F hF₁ hF₂ _).symm.trans ((congrArg TrivSqZeroExt.snd (e₂.symm.trans e)).trans ?_)
      refine (snd_pow_mul _ _ _ ((fst_valT_translate (z' a) (x'.v k) (x'.basis.1 _) (hch' a) _).trans (hzero a i))).trans ?_
      exact congrArg (· ^ n * _) ((fst_valT_translate (z' a) (x'.v k) (x'.basis.1 _) (hW a) _).trans (hu a))
    unfold jac
    rw [RingHom.map_det, ← Matrix.det_submatrix_equiv_self (finCongr hg), _root_.mul_comm, _root_.mul_comm x.P.g n,
      pow_mul]
    have hc : x.P.g = Fintype.card (Fin x'.P.g) := hg.symm.trans (Fintype.card_fin _).symm
    refine (congrArg (fun m => ((u a : K) ^ n) ^ m * _) hc).trans ((Matrix.det_smul _ _).symm.trans ?_)
    congr 1
    ext i k
    exact (ent i k).symm
  refine ⟨z', ch', u, ⟨hch', hzero, fun a => ?_, fun a a' h p e => ?_, fun y hy => ?_⟩, hval⟩
  · have hne : f (jac x s (z a) (ch a)) ≠ 0 := fun h => hz₃ a (hf (h.trans (map_zero f).symm))
    exact isUnit_of_mul_isUnit_left (hjac a ▸ hne.isUnit)
  · have e₀ : (z' a).left = (z' a').left :=
      section_ext_of_apply_eq x'.P.A.hom (z' a).left (z' a').left (Over.w (z' a)) (Over.w (z' a')) p e
    have e₁ : spMap f ≫ (z a).left = spMap f ≫ (z a').left :=
      (hz' a).symm.trans ((congrArg (· ≫ φ) e₀).trans (hz' a'))
    have : IsDominant (spMap f) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot f).1 hf]; exact bot_le)⟩
    have : IsProper x.P.A.hom := x.P.isAb.proper
    exact h (hz₄ (Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Sp O) x.P.A.hom
      ((Over.w (z a)).trans (Over.w (z a')).symm) (spMap f) e₁)))
  · obtain ⟨a, p, hp'⟩ := hz₅ (φ y) ⟨x'.P.A.hom y, (congrArg (fun q => q y) hp.1.w).symm⟩
      fun i h => hy (i.cast hg.symm) (mem_nonzeroLocus_via (hs (i.cast hg.symm)) y h)
    have sq : IsPullback (spMap f) (z' a).left (z a).left φ := by
      refine IsPullback.of_bot (t := hp.1) ?_ (hz' a).symm
      have e₁ : (z' a).left ≫ x'.P.A.hom = 𝟙 _ := Over.w (z' a)
      have e₂ : (z a).left ≫ x.P.A.hom = 𝟙 _ := Over.w (z a)
      rw [e₁, e₂]
      exact IsPullback.of_vert_isIso (fst := spMap f) (snd := 𝟙 (Sp K)) (f := 𝟙 (Sp O)) (g := spMap f) ⟨by simp⟩
    obtain ⟨q, -, hq⟩ := Scheme.exists_preimage_of_isPullback sq p y hp'
    exact ⟨a, q, hq⟩

end GlobalTheory.KeyKa
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

theorem _root_.GlobalTheory.T.exists_enum_ker_transpose_similitude_points : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ), (m : K) ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → ∃ ξ : (Fin 4 → Fin (m ^ x.P.g)) → Fin 4 → Pt x, (∀ I I', I ≠ I' → ∀ p : Sp K, ∃ r, (ξ I r).left p ≠ (ξ I' r).left p) ∧ (∀ I c, (List.ofFn fun r : Fin 4 => ξ I r ^ al r c).prod = 1) := by
  first | exact @GlobalTheory.KeyKa.exists_enum_ker_transpose | exact GlobalTheory.KeyKa.exists_enum_ker_transpose | (intros; apply GlobalTheory.KeyKa.exists_enum_ker_transpose <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.KeyPow

theorem det_blocks {j g G : ℕ} {R : Type*} [CommRing R] (e : Fin j × Fin g ≃ Fin G)
    (M : Matrix (Fin g) (Fin g) R) :
    (Matrix.of fun p q => if (e.symm p).1 = (e.symm q).1 then
        M (e.symm p).2 (e.symm q).2 else 0 : Matrix (Fin G) (Fin G) R).det = M.det ^ j := by
  have h : (Matrix.of fun p q => if (e.symm p).1 = (e.symm q).1 then
        M (e.symm p).2 (e.symm q).2 else 0 : Matrix (Fin G) (Fin G) R) =
      Matrix.reindex ((Equiv.prodComm _ _).trans e) ((Equiv.prodComm _ _).trans e)
        (Matrix.blockDiagonal fun _ : Fin j => M) := by
    ext p q
    simp [Matrix.blockDiagonal_apply]
  rw [h, Matrix.det_reindex_self, Matrix.det_blockDiagonal]
  simp

theorem lattice_blocks {j g G : ℕ} (e : Fin j × Fin g ≃ Fin G) (τ : Matrix (Fin g) (Fin g) ℂ) (z : Fin G → ℂ) :
    (∀ i, ∃ m n : Fin g → ℤ, (fun k => z (e (i, k))) = (fun k => (m k : ℂ)) + τ.mulVec (fun k => (n k : ℂ))) ↔
      ∃ m n : Fin G → ℤ, z = (fun p => (m p : ℂ)) +
        (Matrix.of fun p q => if (e.symm p).1 = (e.symm q).1 then
          τ (e.symm p).2 (e.symm q).2 else 0 : Matrix (Fin G) (Fin G) ℂ).mulVec (fun p => (n p : ℂ)) := by
  constructor
  · intro h
    choose m n h using h
    refine ⟨fun p => m (e.symm p).1 (e.symm p).2, fun p => n (e.symm p).1 (e.symm p).2, ?_⟩
    funext p
    obtain ⟨⟨i, k⟩, rfl⟩ := e.surjective p
    have h₁ := congrFun (ThetaPow.mulVec_blocks e τ (fun p => (n (e.symm p).1 (e.symm p).2 : ℂ)) i) k
    have h₂ := congrFun (h i) k
    simp only [Equiv.symm_apply_apply, Pi.add_apply] at h₁ h₂ ⊢
    rw [h₁, h₂]
  · rintro ⟨m, n, rfl⟩ i
    refine ⟨fun k => m (e (i, k)), fun k => n (e (i, k)), ?_⟩
    rw [← ThetaPow.mulVec_blocks e τ (fun p => (n p : ℂ)) i]
    rfl

theorem normalAt_pow : ∀ (x y : KeyIn ℂ) (j : ℕ) (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℝ) (c : ℂ), GlobalTheory.KeyPow.IsKeyPow y x j → GlobalTheory.KeyPow.NormalAt x τ M (fun k => (a k : ℂ)) (fun k => (b k : ℂ)) c → ∃ (e : Fin j × Fin x.P.g ≃ Fin y.P.g) (τ' M' : Matrix (Fin y.P.g) (Fin y.P.g) ℂ), M'.det = M.det ^ j ∧ GlobalTheory.KeyPow.NormalAt y τ' M' (fun p => (a (e.symm p).2 : ℂ)) (fun p => (b (e.symm p).2 : ℂ)) (c ^ j) := by
  rintro x y j τ M a b c hp ⟨u, hs, hd, hΛ, hr, hf, hv⟩
  obtain ⟨e, u', hΛ', hr', hf', hv'⟩ := GlobalTheory.T.exists_holomorphicUniformisation_powerThetaKeyDatum x y j u _
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ • M) hp hr hf hv
  obtain ⟨hs', hd', hθ⟩ := thetaChar_blockDiagonal j _ τ a b _ e hs hd
  refine ⟨e, _, _, det_blocks e M, u', hs', hd', fun z => ?_, hr', ?_, fun p => ?_⟩
  · rw [hΛ', ← lattice_blocks]
    exact forall_congr' fun i => hΛ _
  · convert hf' using 2 with z
    rw [hθ, Finset.prod_mul_distrib]
    simp
  · convert hv' p using 1
    funext q
    simp only [Pi.smul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp

end GlobalTheory.KeyPow
end
end
