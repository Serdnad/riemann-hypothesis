module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsPrincipalIdealRingOfIsLocalization
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle006
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle007
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UniformiserEval

open GlobalTheory.ChartRing

variable {V : Type} [CommRing V] [IsLocalRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V]

omit [IsAdicComplete (IsLocalRing.maximalIdeal V) V] in
theorem C_add_X_mem {a : V} (ha : a ∈ IsLocalRing.maximalIdeal V) :
    (PowerSeries.C a + PowerSeries.X : PowerSeries V) ∈ IsLocalRing.maximalIdeal (PowerSeries V) :=
  add_mem (C_mem_maximalIdeal_iff.2 ha) X_mem_maximalIdeal

def translate {a : V} (ha : a ∈ IsLocalRing.maximalIdeal V) : PowerSeries V →ₐ[V] PowerSeries V :=
  evalAdic V (IsLocalRing.maximalIdeal (PowerSeries V)) (C_add_X_mem ha)

theorem translate_X {a : V} (ha : a ∈ IsLocalRing.maximalIdeal V) :
    translate ha PowerSeries.X = PowerSeries.C a + PowerSeries.X := evalAdic_X _ _

theorem translate_C {a : V} (ha : a ∈ IsLocalRing.maximalIdeal V) (x : V) :
    translate ha (PowerSeries.C x) = PowerSeries.C x := (translate ha).commutes x

theorem translate_neg_comp {a : V} (ha : a ∈ IsLocalRing.maximalIdeal V) :
    (translate (neg_mem ha)).comp (translate ha) = AlgHom.id V _ := by
  have h : (translate (neg_mem ha)).comp (translate ha) PowerSeries.X = PowerSeries.X := by
    rw [AlgHom.comp_apply, translate_X, map_add (f := _), translate_C, translate_X, map_neg]
    ring
  refine algHom_ext_of_isHausdorff (IsLocalRing.maximalIdeal (PowerSeries V)) ?_ h
  rw [h]
  exact X_mem_maximalIdeal

theorem translate_injective {a : V} (ha : a ∈ IsLocalRing.maximalIdeal V) :
    Function.Injective (translate ha) :=
  Function.LeftInverse.injective (g := translate (neg_mem ha)) fun f =>
    DFunLike.congr_fun (translate_neg_comp ha) f

theorem dvr_admissibleBase_and_powerSeries_evalUniformiser : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → IsAdicComplete (IsLocalRing.maximalIdeal V) V → AdmBase V (Ideal.span {ϖ}) ∧ AdmBase (PowerSeries V) (Ideal.span {PowerSeries.X}) ∧ ∃ ev : PowerSeries V →+* V, (∀ x, ev (PowerSeries.C x) = x) ∧ ev PowerSeries.X = ϖ ∧ ∀ (F : Type) [Field F] (i : V →+* F), Function.Injective i → ∃ σ : PowerSeries V →+* PowerSeries F, Function.Injective σ ∧ (∀ x, σ (PowerSeries.C x) = PowerSeries.C (i x)) ∧ σ PowerSeries.X = PowerSeries.C (i ϖ) + PowerSeries.X ∧ ∀ f, PowerSeries.constantCoeff (σ f) = i (ev f) := by
  intro V _ _ _ ϖ hϖ hc
  have hm : ϖ ∈ IsLocalRing.maximalIdeal V := hϖ.not_isUnit
  refine ⟨⟨inferInstance, inferInstance, inferInstance, hϖ.maximalIdeal_eq ▸ hc⟩,
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
    (PowerSeries.constantCoeff (R := V)).comp (translate hm : PowerSeries V →+* PowerSeries V),
    fun x => ?_, ?_, fun F _ i hi =>
      ⟨(PowerSeries.map i).comp (translate hm : PowerSeries V →+* PowerSeries V), ?_,
        fun x => ?_, ?_, fun f => ?_⟩⟩
  · simp [translate_C]
  · simp [translate_X]
  · exact (PowerSeries.map_injective i hi).comp (translate_injective hm)
  · simp [translate_C]
  · simp [translate_X]
  · simp only [RingHom.comp_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map]

end GlobalTheory.UniformiserEval
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isIntegral_tensor_left_of_smooth_grpObj (S : Scheme.{0}) (B T : Over S) [GrpObj B]
    [Smooth B.hom] [GeometricallyConnected B.hom] [IsIntegral T.left] :
    IsIntegral (T ⊗ B).left :=
  isIntegral_of_isPullback_of_smooth (IsPullback.of_hasPullback T.hom B.hom).flip

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem heisenberg_weightSpace_irreducible : ∀ (F : Type) [Field F] [IsAlgClosed F] (A : Type) [CommGroup A] [Finite A] (E : Type) [AddCommGroup E] [Module F E] [FiniteDimensional F E] (e : A → A → Fˣ) (Φ : A → (E ≃ₗ[F] E)), (Nat.card A : F) ≠ 0 → Module.finrank F E ^ 2 = Nat.card A → (∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v)) → (∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) → (∀ a, (∀ b, e a b = 1) → a = 1) → ∀ (T : Subgroup A) (lam : T →* (E ≃ₗ[F] E)), (∀ t : T, ∃ c : Fˣ, ∀ v, lam t v = (c : F) • Φ t v) → ∀ Wt : (T →* Fˣ) → Submodule F E, (∀ χ v, v ∈ Wt χ ↔ ∀ t, lam t v = (χ t : F) • v) → ∀ (χ : T →* Fˣ) (U : Submodule F E), U ≤ Wt χ → (∀ h : A, (∀ t : T, e t h = 1) → ∀ v ∈ U, Φ h v ∈ U) → U = ⊥ ∨ U = Wt χ := by
  classical
  intro F _ _ A _ _ E _ _ _ e Φ hcard hdim hmul hcomm hnd T lam hlam Wt hWt χ U hU hstab
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  haveI : Nontrivial E := ⟨⟨u, 0, hu0⟩⟩

  have hel : ∀ a b c, e (a * b) c = e a c * e b c := by
    intro a b c
    obtain ⟨k, hk⟩ := hmul a b
    have h1 := hcomm (a * b) c u
    rw [hk, hk, hcomm b c u, map_smul, hcomm a c, map_smul, smul_smul, smul_smul, smul_smul] at h1
    have h2 : Φ c (Φ a (Φ b u)) ≠ 0 := fun h => hu0 (by simpa using h)
    have h3 := smul_left_injective F h2 h1
    apply Units.ext
    have hk0 : (k : F) ≠ 0 := k.ne_zero
    apply mul_left_cancel₀ hk0
    rw [Units.val_mul]
    linear_combination -h3
  have he1 : ∀ c, e 1 c = 1 := by
    intro c
    have := hel 1 1 c
    rw [_root_.mul_one] at this
    exact (mul_eq_left.mp this.symm)
  have hinj : Function.Injective fun a b => (e a b : F) := by
    intro a a' h
    have : a * a'⁻¹ = 1 := by
      apply hnd
      intro b
      have hb : e a b = e a' b := Units.ext (congrFun h b)
      rw [hel, hb, ← hel, mul_inv_cancel, he1]
    exact mul_inv_eq_one.mp this
  have hli : LinearIndependent F fun a => (Φ a : E →ₗ[F] E) :=
    linearIndependent_of_comm_smul _ _ (fun a => (Φ a).injective) (fun a b v => hcomm a b v) hinj
  haveI := Fintype.ofFinite A
  have hspan : Submodule.span F (Set.range fun a => (Φ a : E →ₗ[F] E)) = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank'
    rw [Module.finrank_linearMap, ← sq, hdim, Nat.card_eq_fintype_card]
  refine le_antisymm hU fun v hv => ?_
  obtain ⟨f, hf⟩ : ∃ f : E →ₗ[F] E, f u = v := by
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F hu0
    exact ⟨φ.smulRight v, by simp [hφ]⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp
    (hspan ▸ Submodule.mem_top : f ∈ Submodule.span F (Set.range fun a => (Φ a : E →ₗ[F] E)))
  have hvs : v = ∑ a, c a • Φ a u := by
    rw [← hf, ← hc]; simp
  have hu := (hWt χ u).mp (hU huU)
  have hv' := (hWt χ v).mp hv
  have hlamΦ : ∀ (t : T) a, lam t (Φ a u) = ((χ t : F) * (e t a : F)) • Φ a u := by
    intro t a
    obtain ⟨k, hk⟩ := hlam t
    rw [hk, hcomm, smul_comm, ← map_smul, ← hk, hu, map_smul, smul_smul, mul_comm]
  have hvt : ∀ t : T, v = ∑ a, (c a * (e t a : F)) • Φ a u := by
    intro t
    have h1 := hv' t
    have h0 : (χ t : F) ≠ 0 := (χ t).ne_zero
    apply smul_right_injective E h0
    simp only
    rw [← h1]
    conv_lhs => rw [hvs]

    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, hlamΦ, smul_smul, smul_smul]
    congr 1; ring
  have hT : (Fintype.card T : F) ≠ 0 := by
    intro h
    apply hcard
    rw [← Subgroup.card_mul_index T, Nat.cast_mul, Nat.card_eq_fintype_card, h, zero_mul]
  have hsum : (Fintype.card T : F) • v = ∑ a, (c a * ∑ t : T, (e t a : F)) • Φ a u := by
    have : (Fintype.card T : F) • v = ∑ _t : T, v := by
      rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    rw [this, Finset.sum_congr rfl fun t _ => hvt t, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.sum_smul]
  rw [← U.smul_mem_iff hT, hsum]
  refine U.sum_mem fun a _ => ?_
  by_cases ha : ∀ t : T, e t a = 1
  · exact U.smul_mem _ (hstab a ha u huU)
  · let ψ : T →* F :=
      { toFun := fun t => (e t a : F)
        map_one' := by simp [he1]
        map_mul' := fun s t => by simp [hel] }
    have hψ : ψ ≠ 1 := by
      intro h
      apply ha
      intro t
      apply Units.ext
      exact DFunLike.congr_fun h t
    have := sum_hom_units_eq_zero ψ hψ
    have h2 : ∑ t : T, (e t a : F) = 0 := this
    rw [h2, mul_zero, zero_smul]
    exact U.zero_mem

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_dvr_fraction_order (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] :
    ∃ o : (FractionRing V)ˣ → ℤ, (∀ x y, o (x * y) = o x + o y) ∧
      (∀ (x y : (FractionRing V)ˣ) (u : Vˣ),
        x.val = algebraMap V (FractionRing V) u.val * y.val → o x = o y) ∧
      ∀ x, 0 < o x ↔ ∃ r ∈ IsLocalRing.maximalIdeal V,
        algebraMap V (FractionRing V) r = x.val := by
  let v := (IsDiscreteValuationRing.maximalIdeal V).valuation (FractionRing V)
  have hne : ∀ x : (FractionRing V)ˣ, v x.val ≠ 0 := fun x =>
    (Valuation.ne_zero_iff v).mpr x.ne_zero
  refine ⟨fun x => - WithZero.log (v x.val), ?_, ?_, ?_⟩
  · intro x y
    simp only [Units.val_mul, map_mul]
    rw [WithZero.log_mul (hne x) (hne y)]
    ring
  · intro x y u h
    have hu : v (algebraMap V (FractionRing V) u.val) = 1 := by
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
      simp [IsDiscreteValuationRing.maximalIdeal]
    simp only [h, map_mul, hu, _root_.one_mul]
  · intro x
    show 0 < - WithZero.log (v x.val) ↔ _
    rw [neg_pos, WithZero.log_lt_iff_lt_exp (hne x), WithZero.exp_zero]
    constructor
    · intro h
      obtain ⟨r, hr⟩ := IsDiscreteValuationRing.exists_lift_of_le_one h.le
      refine ⟨r, ?_, hr⟩
      rw [← hr] at h
      exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ r).mp h
    · rintro ⟨r, hr, h⟩
      rw [← h]
      exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ r).mpr hr

theorem cubeRel_scalars_mem_maximalIdeal : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (X : Type) [AddCommGroup X] [Module.Free ℤ X] (a : X → (FractionRing V)ˣ), (∀ x y z, ∃ u : Vˣ, (a (x + y + z) * a x * a y * a z).val = algebraMap V (FractionRing V) u.val * (a (x + y) * a (x + z) * a (y + z)).val) → (∀ x, ∃ u : Vˣ, (a (-x)).val = algebraMap V (FractionRing V) u.val * (a x).val) → {x | ¬ ∃ r ∈ IsLocalRing.maximalIdeal V, algebraMap V (FractionRing V) r = (a x).val}.Finite → ∀ x, x ≠ 0 → ∃ r ∈ IsLocalRing.maximalIdeal V, algebraMap V (FractionRing V) r = (a x).val := by
  intro V _ _ _ X _ _ a hc he hfin x hx
  obtain ⟨o, hmul, hunit, hpos⟩ := exists_dvr_fraction_order V
  rw [← hpos]
  refine even_quadratic_pos_of_finite_nonpos X (fun x => o (a x)) ?_ ?_ ?_ x hx
  · intro x y z
    obtain ⟨u, hu⟩ := hc x y z
    have := hunit _ _ u hu
    simpa only [hmul] using this
  · intro x
    obtain ⟨u, hu⟩ := he x
    exact hunit _ _ u hu
  · refine hfin.subset ?_
    intro x hx
    show ¬ _
    rw [← hpos]
    exact not_lt.mpr hx

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isPrimitiveRoot_residue_of_isUnit {W : Type*} [CommRing W] [IsDomain W] [IsLocalRing W]
    {ζ : W} {N : ℕ} (hζ : IsPrimitiveRoot ζ N) (hN : IsUnit (N : W)) :
    IsPrimitiveRoot (IsLocalRing.residue W ζ) N := by
  refine ⟨by rw [← map_pow, hζ.pow_eq_one, map_one], fun l hl => hζ.dvd_of_pow_eq_one l ?_⟩
  by_contra hne
  have h1 : (ζ ^ l) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have h2 : ∑ i ∈ Finset.range N, (ζ ^ l) ^ i = 0 := by
    have := geom_sum_mul (ζ ^ l) N
    rw [h1, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne)
  have h3 := congrArg (IsLocalRing.residue W) h2

  simp only [map_sum, map_pow, hl, one_pow, map_zero, Finset.sum_const, Finset.card_range,
  nsmul_eq_mul, mul_one] at h3
  have h4 := hN.map (IsLocalRing.residue W)
  rw [map_natCast] at h4
  exact h4.ne_zero (by simpa using h3)

theorem exists_finite_extension_primitive_residue :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V], (∃ n : ℕ, n.Prime ∧ IsUnit (n : V)) ∧ ∀ (n j : ℕ), n.Prime → IsUnit (n : V) → ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (_ : Algebra V W) (φ : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))) (ζ : W), (Module.Finite V W ∧ Module.Free V W ∧ IsDomain W ∧ IsLocalHom (algebraMap V W) ∧ IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W) ∧ Function.Injective φ.left.appTop.hom ∧ IsUnit (n : W) ∧ ζ ^ (n ^ j) = 1 ∧ IsPrimitiveRoot (IsLocalRing.residue W ζ) (n ^ j) := by
  intro V _ _ _ _ _
  refine ⟨?_, fun n j hn hu => ?_⟩
  · have h : IsUnit ((3 : V) + -2) := by norm_num
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h | h
    · exact ⟨3, Nat.prime_three, by exact_mod_cast h⟩
    · exact ⟨2, Nat.prime_two, by exact_mod_cast (IsUnit.neg_iff _).1 h⟩
  · let F := AlgebraicClosure (FractionRing V)
    have hpos : 0 < n ^ j := pow_pos hn.pos j
    have : NeZero (n ^ j) := ⟨hpos.ne'⟩
    have : NeZero ((n ^ j : ℕ) : F) := inferInstance
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F (n ^ j)
    let W : Subalgebra V F := Algebra.adjoin V {z}
    have hzW : z ∈ W := Algebra.subset_adjoin rfl
    have hfin : Module.Finite V W :=
      Algebra.finite_adjoin_simple_of_isIntegral
        ⟨Polynomial.X ^ (n ^ j) - Polynomial.C 1, Polynomial.monic_X_pow_sub_C _ hpos.ne', by
          simp [hz.pow_eq_one]⟩
    have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective V W).2 fun x y h =>
      IsFractionRing.injective V (FractionRing V) ((algebraMap (FractionRing V) F).injective
        (congrArg Subtype.val h))
    have hfree : Module.Free V W := Module.free_of_finite_type_torsion_free'
    have hW : IsLocalRing W := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := V) W
    have hloc : IsLocalHom (algebraMap V W) := inferInstance
    have hc := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isAdicComplete_finite_algebra (R := V) W
    have hζ : IsPrimitiveRoot (⟨z, hzW⟩ : W) (n ^ j) :=
      IsPrimitiveRoot.of_map_of_injective (f := W.val) hz Subtype.val_injective
    have hnW : IsUnit (n : W) := by simpa using hu.map (algebraMap V W)
    refine ⟨W, inferInstance, inferInstance, inferInstance,
      Over.homMk (Spec.map (CommRingCat.ofHom W.val.toRingHom)) ?_, ⟨z, hzW⟩,
      ⟨hfin, hfree, inferInstance, hloc, hc⟩, ?_, hnW, hζ.pow_eq_one,
      isPrimitiveRoot_residue_of_isUnit hζ (by exact_mod_cast hnW.pow j)⟩
    · change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp]
      rfl
    · change Function.Injective (Spec.map (CommRingCat.ofHom W.val.toRingHom)).appTop.hom
      have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom W.val.toRingHom)
      have hi : Function.Injective ((Spec.map (CommRingCat.ofHom W.val.toRingHom)).appTop ≫
          (Scheme.ΓSpecIso _).hom).hom := by
        rw [h, CommRingCat.hom_comp, RingHom.coe_comp]
        exact Subtype.val_injective.comp (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.injective
      rw [CommRingCat.hom_comp, RingHom.coe_comp] at hi
      exact hi.of_comp

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoordLinear

open Geo.Tor

theorem fn_eq_of_levels {R : Type} [CommRing R] (I : Ideal R) [IsHausdorff I R]
    (W : (Spec (CommRingCat.of R)).Opens) (hW : W = ⊤) (a b : Γ(Spec (CommRingCat.of R), W))
    (h : ∀ e, ((thick R I e).app W).hom a = ((thick R I e).app W).hom b) : a = b := by
  subst hW
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
  have key : ∀ (e : ℕ) (c : Γ(Spec (CommRingCat.of R), ⊤)),
      Ideal.Quotient.mk (I ^ (e + 1)) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c) =
        (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I ^ (e + 1)))).hom.hom (((thick R I e).app ⊤).hom c) := fun e c =>
    (congrArg (fun q => q.hom c)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))))).symm
  have := IsHausdorff.StrictMono.funext' I (a := fun n => n + 1) (strictMono_id.add_const 1)
    (f := fun _ : Unit => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a)
    (g := fun _ : Unit => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom b)
    (fun n _ => (key n a).trans ((congrArg _ (h n)).trans (key n b).symm))
  exact congrFun this ()

end GlobalTheory.CoordLinear
end
