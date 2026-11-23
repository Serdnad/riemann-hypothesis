module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle116
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle015
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
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
import Mathlib.RingTheory.PowerSeries.Ideal
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
public import ReciprocityTheory.AdicCompleteness.IsAdicCompleteComapConstantCoeff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle118
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

namespace GlobalTheory.CentredPlace

theorem exists_extension {F K M : Type} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K] [Field M]
    [IsAlgClosed M] (L : IntermediateField F K) (f : L →+* M) : ∃ σ : K →+* M, ∀ x : L, σ x = f x := by
  letI := f.toAlgebra
  let σ : K →ₐ[L] M := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨σ.toRingHom, fun x => σ.commutes x⟩

theorem exists_mem_of_dvr {R₁ : Type} [CommRing R₁] [IsDomain R₁] [CharZero R₁]
    (P : Set (ValuationSubring (AlgebraicClosure (FractionRing R₁))))
    (hP : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (φ : R₁ →+* V)
      (gam : FractionRing R₁ →+* FractionRing V), (∀ r, gam (algebraMap R₁ _ r) = algebraMap V _ (φ r)) →
      ∀ σ : AlgebraicClosure (FractionRing R₁) →+* AlgebraicClosure (FractionRing V),
      (∀ x, σ (algebraMap (FractionRing R₁) _ x) = algebraMap (FractionRing V) _ (gam x)) →
      ∃ S ∈ P, ∀ x (y : FractionRing V), σ x = algebraMap (FractionRing V) _ y →
        (x ∈ S ↔ y ∈ Set.range (algebraMap V (FractionRing V))))
    (L : IntermediateField (FractionRing R₁) (AlgebraicClosure (FractionRing R₁)))
    (W : ValuationSubring L) [IsDiscreteValuationRing W] (hW : ∀ r : R₁, algebraMap R₁ L r ∈ W) :
    ∃ S ∈ P, ∀ x : L, x ∉ W → (x : AlgebraicClosure (FractionRing R₁)) ∉ S := by
  let V := AdicCompletion (maximalIdeal W) W
  have hj : Function.Injective (algebraMap W V) := algebraMap_adicCompletion_injective_of_dvr W
  let j : W →+* FractionRing V := (algebraMap V (FractionRing V)).comp (algebraMap W V)
  have hj' : Function.Injective j := (IsFractionRing.injective V (FractionRing V)).comp hj
  let f : L →+* FractionRing V := IsFractionRing.lift (K := L) hj'
  have hf : ∀ w : W, f (w : L) = j w := fun w => IsFractionRing.lift_algebraMap hj' w
  let φ : R₁ →+* V := (algebraMap W V).comp ((algebraMap R₁ L).codRestrict W hW)
  have hinj : Function.Injective (algebraMap R₁ L) := by
    rw [IsScalarTower.algebraMap_eq R₁ (FractionRing R₁) L]
    exact (algebraMap (FractionRing R₁) L).injective.comp (IsFractionRing.injective R₁ _)
  have hφ : Function.Injective φ := hj.comp fun a b hab => hinj (congrArg Subtype.val hab)
  have hV : CDvr V := ⟨inferInstance, inferInstance, charZero_of_injective_ringHom hφ⟩
  obtain ⟨σ, hσ⟩ := exists_extension L
    ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp f)
  obtain ⟨S, hS, h⟩ := hP V hV φ (f.comp (algebraMap (FractionRing R₁) L))
    (fun r => by
      rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
      exact hf ⟨_, hW r⟩) σ (fun x => hσ (algebraMap (FractionRing R₁) L x))
  refine ⟨S, hS, fun x hx hxS => ?_⟩
  obtain ⟨v, hv⟩ := (h x (f x) (hσ x)).1 hxS
  have hx0 : x ≠ 0 := fun e => hx (e ▸ W.zero_mem)
  have hi : x⁻¹ ∈ W := (W.mem_or_inv_mem x).resolve_left hx
  have hu : IsUnit (algebraMap W V ⟨x⁻¹, hi⟩) := by
    refine IsUnit.of_mul_eq_one v (IsFractionRing.injective V (FractionRing V) ?_)
    rw [map_mul, hv, map_one]
    change j ⟨x⁻¹, hi⟩ * _ = _
    rw [← hf, ← map_mul, inv_mul_cancel₀ hx0, map_one]
  obtain ⟨u, hu'⟩ := isUnit_iff_exists_inv.1 (IsLocalHom.map_nonunit _ hu)
  have : x⁻¹ * u = 1 := congrArg Subtype.val hu'
  have e : (u : L) = x := by rw [eq_inv_of_mul_eq_one_right this, inv_inv]
  exact hx (e ▸ u.2)

theorem isIntegral_inv {R₀ K : Type} [CommRing R₀] [IsLocalRing R₀] [IsNoetherianRing R₀]
    [IsAdicComplete (maximalIdeal R₀) R₀] [Field K] [Algebra R₀ K] (S : ValuationSubring K)
    (h₁ : ∀ r, algebraMap R₀ K r ∈ S) (h₂ : ∀ r ∈ maximalIdeal R₀, algebraMap R₀ K r ∈ S.nonunits)
    {x : K} (hx : IsIntegral R₀ x) (hxS : x ∈ S) (hv : S.valuation x = 1) : IsIntegral R₀ x⁻¹ := by
  let B := Algebra.adjoin R₀ {x}
  have : Module.Finite R₀ B := Algebra.finite_adjoin_simple_of_isIntegral hx
  have : IsLocalRing B := T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := R₀) B
  let S' : Subalgebra R₀ K := { S.toSubring with algebraMap_mem' := h₁ }
  have hB : B ≤ S' := Algebra.adjoin_le (by rintro _ rfl; exact hxS)
  let i : B →+* S := (B.val : B →+* K).codRestrict S fun b => hB b.2
  let p : Ideal B := (maximalIdeal S).comap i
  have hp : (p.comap (algebraMap R₀ B)).IsMaximal := by
    have : maximalIdeal R₀ ≤ p.comap (algebraMap R₀ B) := fun r hr =>
      (ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, h₁ r⟩)).mp (h₂ r hr)
    rw [← (maximalIdeal.isMaximal R₀).eq_of_le (Ideal.IsPrime.ne_top inferInstance) this]
    infer_instance
  have hm : p = maximalIdeal B := eq_maximalIdeal (Ideal.isMaximal_of_isIntegral_of_isMaximal_under p hp)
  have hu : IsUnit (⟨x, Algebra.subset_adjoin rfl⟩ : B) := by
    by_contra hn
    have : (⟨x, Algebra.subset_adjoin rfl⟩ : B) ∈ p := hm ▸ hn
    have h3 : x ∈ S.nonunits := (ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, hxS⟩)).mpr this
    exact (S.mem_nonunits_iff.1 h3).ne hv
  obtain ⟨u, hu'⟩ := isUnit_iff_exists_inv.1 hu
  have : x * u = 1 := congrArg Subtype.val hu'
  rw [← eq_inv_of_mul_eq_one_right this]
  exact (Algebra.IsIntegral.isIntegral (R := R₀) u).map B.val

theorem mem_of_isIntegral {R K : Type} [CommRing R] [Field K] [Algebra R K] (S : ValuationSubring K)
    (h : ∀ r, algebraMap R K r ∈ S) {x : K} (hx : IsIntegral R x) : x ∈ S := by
  letI : Algebra R S := ((algebraMap R K).codRestrict S h).toAlgebra
  have : IsScalarTower R S K := .of_algebraMap_eq fun _ => rfl
  obtain ⟨y, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := S) (K := K)).mp
    (IsIntegral.tower_top (R := R) hx)
  exact y.2

theorem exists_place_detecting_units : ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (ϖ : O'), ArcBase O' ϖ → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁), Function.Injective g → g.Finite → ∀ P : Set (ValuationSubring (AlgebraicClosure (FractionRing R₁))), (∀ S ∈ P, ∀ r : R₁, algebraMap (FractionRing R₁) _ (algebraMap R₁ _ r) ∈ S) → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (φ : R₁ →+* V) (gam : FractionRing R₁ →+* FractionRing V), (∀ r, gam (algebraMap R₁ _ r) = algebraMap V _ (φ r)) → ∀ σ : AlgebraicClosure (FractionRing R₁) →+* AlgebraicClosure (FractionRing V), (∀ x, σ (algebraMap (FractionRing R₁) _ x) = algebraMap (FractionRing V) _ (gam x)) → ∃ S ∈ P, ∀ x (y : FractionRing V), σ x = algebraMap (FractionRing V) _ y → (x ∈ S ↔ y ∈ Set.range (algebraMap V (FractionRing V)))) → ∃ S₀ ∈ P, ∀ x, (∀ S ∈ P, x ∈ S) → S₀.valuation x = 1 → ∀ S ∈ P, S.valuation x = 1 := by
  intro O' _ _ _ ϖ hO R₁ _ _ g hg hfin P hR hP
  obtain ⟨_, _, hc⟩ : ∃ _ : IsLocalRing O', IsPrincipalIdealRing O' ∧ IsAdicComplete (maximalIdeal O') O' := by
    rcases hO with ⟨hF, -⟩ | ⟨hD, hi, hc⟩
    · letI := hF.toField
      refine ⟨inferInstance, inferInstance, ?_⟩
      rw [IsLocalRing.maximalIdeal_eq_bot]
      infer_instance
    · refine ⟨inferInstance, inferInstance, ?_⟩
      rwa [hi.maximalIdeal_eq]
  have hps : IsAdicComplete (maximalIdeal (PowerSeries O')) (PowerSeries O') := ReciprocityTheory.P1.isAdicComplete_ps
  have : CharZero (PowerSeries O') := charZero_of_injective_ringHom (PowerSeries.C_injective (R := O'))
  have : CharZero R₁ := charZero_of_injective_ringHom hg
  letI := g.toAlgebra
  have : Module.Finite (PowerSeries O') R₁ := hfin
  have : IsLocalRing R₁ := T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := PowerSeries O') R₁
  have : IsNoetherianRing R₁ := IsNoetherianRing.of_finite (PowerSeries O') R₁
  have : FaithfulSMul (PowerSeries O') R₁ := (faithfulSMul_iff_algebraMap_injective _ _).2 hg
  have hloc : IsLocalHom (algebraMap (PowerSeries O') R₁) := inferInstance
  have hR' : ∀ S ∈ P, ∀ r : R₁, algebraMap R₁ (AlgebraicClosure (FractionRing R₁)) r ∈ S := fun S hS r => by
    rw [IsScalarTower.algebraMap_apply R₁ (FractionRing R₁)]
    exact hR S hS r
  have hinj : Function.Injective (algebraMap R₁ (AlgebraicClosure (FractionRing R₁))) := by
    rw [IsScalarTower.algebraMap_eq R₁ (FractionRing R₁)]
    exact (algebraMap (FractionRing R₁) _).injective.comp (IsFractionRing.injective R₁ _)
  have hnf : ¬ IsField R₁ := fun h => by
    have hX : ¬ IsUnit (PowerSeries.X : PowerSeries O') := PowerSeries.X_prime.not_isUnit
    refine hX (hloc.1 _ ?_)
    obtain ⟨b, hb⟩ := h.mul_inv_cancel ((map_ne_zero_iff g hg).2 PowerSeries.X_ne_zero)
    exact IsUnit.of_mul_eq_one b hb
  have hint : ∀ x, (∀ S ∈ P, x ∈ S) → IsIntegral R₁ x := fun x hx => by
    by_contra hn
    let L := IntermediateField.adjoin (FractionRing R₁) {x}
    have : FiniteDimensional (FractionRing R₁) L :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
    have : Algebra.EssFiniteType R₁ (FractionRing R₁) := .of_isLocalization _ (nonZeroDivisors R₁)
    have : Algebra.EssFiniteType R₁ L := .comp R₁ (FractionRing R₁) L
    let x' : L := ⟨x, IntermediateField.subset_adjoin _ _ rfl⟩
    have : IsScalarTower R₁ L (AlgebraicClosure (FractionRing R₁)) := .of_algebraMap_eq fun _ => rfl
    have hn' : ¬ IsIntegral R₁ x' := fun h => hn (h.map (IsScalarTower.toAlgHom R₁ L _))
    obtain ⟨W, _, h2, h3⟩ := exists_discreteValuationSubring_dominating_notMem (R := R₁) hn'
    obtain ⟨S, hS, h⟩ := exists_mem_of_dvr P hP L W
      ((localSubring_range_le_valuationSubring_iff _ _).1 h2).1
    exact h x' h3 (hx S hS)
  let L : IntermediateField (FractionRing R₁) (AlgebraicClosure (FractionRing R₁)) := ⊥
  obtain ⟨W, _, h2⟩ := exists_discreteValuationSubring_dominating R₁ (FractionRing R₁) L hnf
  obtain ⟨h2, h3⟩ := (localSubring_range_le_valuationSubring_iff _ _).1 h2
  obtain ⟨S₀, hS₀, h⟩ := exists_mem_of_dvr P hP L W h2
  refine ⟨S₀, hS₀, fun x hx hv S hS => ?_⟩
  have e : ∀ r, algebraMap (PowerSeries O') (AlgebraicClosure (FractionRing R₁)) r = algebraMap R₁ _ (g r) :=
    fun r => IsScalarTower.algebraMap_apply _ R₁ _ r
  have hi : IsIntegral (PowerSeries O') x⁻¹ := by
    refine isIntegral_inv S₀ (fun r => e r ▸ hR' S₀ hS₀ (g r)) (fun r hr => ?_)
      (isIntegral_trans x (hint x hx)) (hx S₀ hS₀) hv
    have h4 := h3 (g r) (fun hu => hr (hloc.1 r hu))
    rw [e]
    rw [ValuationSubring.mem_nonunits_iff_or] at h4 ⊢
    exact h4.imp (fun e => congrArg Subtype.val e) (fun e => h _ e)
  have h5 : x⁻¹ ∈ S := mem_of_isIntegral S (hR' S hS) hi.tower_top
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hv
  refine le_antisymm ((S.valuation_le_one_iff x).2 (hx S hS)) ?_
  have h6 := (S.valuation_le_one_iff _).2 h5
  rwa [map_inv₀, inv_le_one₀ (by simpa [Valuation.pos_iff] using hx0)] at h6

end GlobalTheory.CentredPlace
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.ThetaLine
open GlobalTheory.Points

variable {B : Scheme.{0}} (A : Over B) (L : LB A.left) (a : ℤ)

theorem le_chart {T : Over B} {K : Type} [CommRing K] (q : Sp K ⟶ (T ⊗ A).left) (j : L.ι)
    (h : Set.range (q ≫ (snd T A).left) ⊆ L.U j) : ⊤ ≤ q ⁻¹ᵁ (LPow A L a T).U (fun _ => j) :=
  fun y _ => Set.mem_iInter.2 fun _ => h ⟨y, rfl⟩

theorem valR_pull [GrpObj A] {T T' : Over B} {h : T' ⊗ A ⟶ T ⊗ A} {hh : h ≫ snd T A = snd T' A}
    {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')} (H : IsPullSec A L a h hh s s')
    {K : Type} [CommRing K] (q : Sp K ⟶ (T' ⊗ A).left) (j : Fin 1 → L.ι) (hq : ⊤ ≤ q ⁻¹ᵁ (LPow A L a T').U j) :
    valR q _ (s'.f j) = valR (q ≫ h.left) _ (s.f j) := by
  rw [H j, valR_res q _ hq, valR_comp]

theorem valR_of_basis {Ω : Type} [CommRing Ω] (t : Sp Ω ⟶ B) {m : ℕ} (hm : m = 1)
    {b : Fin m → LB.Sec (LPow A L a (Over.mk t))} (hb : IsSecBasis _ b) :
    ∃ b₀ : LB.Sec (LPow A L a (Over.mk t)), ∀ s : LB.Sec (LPow A L a (Over.mk t)), ∃ c : Ω,
      ∀ (K : Type) [CommRing K] (β : Ω →+* K) (q : Sp K ⟶ (Over.mk t ⊗ A).left) (j : Fin 1 → L.ι),
        q ≫ (fst (Over.mk t) A).left = spMap β → ⊤ ≤ q ⁻¹ᵁ (LPow A L a (Over.mk t)).U j →
        valR q _ (s.f j) = β c * valR q _ (b₀.f j) := by
  subst hm
  refine ⟨b 0, fun s => ?_⟩
  obtain ⟨r, hr, -⟩ := hb s
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom (r 0), fun K _ β q j hq hj => ?_⟩
  rw [hr j, Fin.sum_univ_one, valR_mul q _ hj, valR_res q _ hj]
  congr 1
  have e := valR_comp q (fst (Over.mk t) A).left ⊤ (r 0)
  refine e.symm.trans ?_
  rw [hq]
  have e2 := valR_specMap (C := K) (A := CommRingCat.of Ω) (CommRingCat.ofHom β)
    ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom (r 0))
  refine Eq.trans ?_ e2
  exact congrArg (valR (spMap β) ⊤) ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom_inv_id_apply (r 0)).symm

theorem valR_ne_zero [GrpObj A] {T : Over B} {s : LB.Sec (LPow A L a T)} {z : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (H : IsValueAt A L a s z τ v) {K : Type} [Field K] (x : Sp K ⟶ T.left) (j : L.ι)
    (hj : Set.range (x ≫ z.left) ⊆ L.U j) (hv : valR x ⊤ v ≠ 0) :
    valR (x ≫ (ptSecT A z).left) _ (s.f fun _ => j) ≠ 0 := by
  have hx : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => z.left) (fun _ => j) :=
    fun y _ => Set.mem_iInter.2 fun _ => hj ⟨y, rfl⟩
  have e := congrArg (valR x _) (H fun _ => j)
  rw [valR_res x _ hx, valR_mul x _ hx, valR_res x _ hx] at e
  rw [valR_comp]
  refine e.trans_ne (mul_ne_zero hv ?_)
  rw [valR_eq x _ hx]
  exact ((τ.s fun _ => j).isUnit.map _).ne_zero

end GlobalTheory.ZH.ThetaLine


open GlobalTheory.Points GlobalTheory.ZH.ThetaLine in
theorem GlobalTheory.ZH.sec_generic_eq_mul_theta : Laws → Laws2 → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (s : LB.Sec (LPow ρ.P.A ρ.P.L 1 (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)))), ∃ c : Ω, ∀ (K : Type) [Field K] (β : Ω →+* K) (q : Sp K ⟶ ((Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ⊗ ρ.P.A).left) (r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left) (jP : ρ.P.L.ι), q ≫ (fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left = spMap β → r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = q ≫ (snd (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left → Set.range (q ≫ (snd (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left) ⊆ ρ.P.L.U jP → valF q _ (s.f fun _ => jP) = β c * valF r _ (ρ.th₁.f fun _ => jP) := by
  intro _ hL2 o Ω _ _ _ _ S ρ s
  let t₀ : Sp Ω ⟶ Sp S.R := spMap S.R.val.toRingHom
  let h : (Over.mk t₀ : Over (Sp S.R)) ⟶ baseOver (Sp S.R) := Over.homMk t₀ (Category.comp_id t₀)
  obtain ⟨th, hth⟩ : ∃ th, IsPullSec ρ.P.A ρ.P.L 1 (h ▷ ρ.P.A) (whiskerRight_snd h ρ.P.A) ρ.th₁ th :=
    (GlobalTheory.LN.PolFrames.exists_pullSec ρ.P.A ρ.P.L 1 h ρ.th₁).imp fun _ H => H.1
  obtain ⟨b, hb⟩ := GlobalTheory.PowBasis.exists_basis_pow hL2.secTwist ρ.P 1 le_rfl Ω t₀
  obtain ⟨b₀, hb₀⟩ := valR_of_basis ρ.P.A ρ.P.L 1 t₀ (one_pow _) hb
  obtain ⟨c, hc⟩ := hb₀ s
  obtain ⟨d, hd⟩ := hb₀ th
  have hd0 : d ≠ 0 := by
    obtain ⟨a, ha⟩ := S.th_ne
    obtain ⟨j, hj⟩ := exists_chart ρ.P.isLB ((t₀ ≫ (ρ.pt a).left) (IsLocalRing.closedPoint Ω))
    have hj' : Set.range (t₀ ≫ (ρ.pt a).left) ⊆ ρ.P.L.U j := by
      rintro _ ⟨y, rfl⟩
      rw [Subsingleton.elim y (IsLocalRing.closedPoint Ω)]
      exact hj
    have hne := valR_ne_zero ρ.P.A ρ.P.L 1 (ρ.th_val a) t₀ j hj'
      ((valR_specMap (C := Ω) (A := CommRingCat.of S.R) (CommRingCat.ofHom S.R.val.toRingHom) _).trans_ne ha)
    let x : Sp Ω ⟶ ((Over.mk t₀ : Over (Sp S.R)) ⊗ ρ.P.A).left := (ptSecT ρ.P.A (h ≫ ρ.pt a)).left
    have hx1 : x ≫ (fst (Over.mk t₀ : Over (Sp S.R)) ρ.P.A).left = spMap (RingHom.id Ω) :=
      (congrArg CommaMorphism.left (lift_fst (𝟙 (Over.mk t₀ : Over (Sp S.R))) (h ≫ ρ.pt a))).trans (Spec.map_id _).symm
    have hx2 : x ≫ (snd (Over.mk t₀ : Over (Sp S.R)) ρ.P.A).left = t₀ ≫ (ρ.pt a).left :=
      congrArg CommaMorphism.left (lift_snd (𝟙 (Over.mk t₀ : Over (Sp S.R))) (h ≫ ρ.pt a))
    have hx3 : x ≫ (h ▷ ρ.P.A).left = t₀ ≫ (ptSecT ρ.P.A (ρ.pt a)).left := by
      have : ptSecT ρ.P.A (h ≫ ρ.pt a) ≫ h ▷ ρ.P.A = h ≫ ptSecT ρ.P.A (ρ.pt a) := by
        simp [ptSecT]
      exact congrArg CommaMorphism.left this
    have hxj := le_chart ρ.P.A ρ.P.L 1 x j (hx2 ▸ hj')
    rintro rfl
    apply hne
    rw [← hx3, ← valR_pull ρ.P.A ρ.P.L 1 hth x _ hxj, hd Ω _ x _ hx1 hxj, map_zero, zero_mul]
  refine ⟨c / d, fun K _ β q r j hq hr hj => ?_⟩
  have hqj := le_chart ρ.P.A ρ.P.L 1 q j hj
  have hrq : r = q ≫ (h ▷ ρ.P.A).left := by
    have h2 : r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left =
        (q ≫ (h ▷ ρ.P.A).left) ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left := by
      rw [hr, Category.assoc, ← Over.comp_left, whiskerRight_snd]
    have w : (fst (baseOver (Sp S.R)) ρ.P.A).left =
        (snd (baseOver (Sp S.R)) ρ.P.A).left ≫ ρ.P.A.hom :=
      (Category.comp_id _).symm.trans (pullback.condition (f := 𝟙 (Sp S.R)) (g := ρ.P.A.hom))
    refine pullback.hom_ext (f := 𝟙 (Sp S.R)) (g := ρ.P.A.hom) ?_ h2
    change r ≫ (fst (baseOver (Sp S.R)) ρ.P.A).left = _ ≫ (fst (baseOver (Sp S.R)) ρ.P.A).left
    rw [w, ← Category.assoc, h2]
    simp only [Category.assoc]
  change valR q _ _ = β (c / d) * valR r _ _
  rw [hrq, ← valR_pull ρ.P.A ρ.P.L 1 hth q _ hqj, hc K β q _ hq hqj, hd K β q _ hq hqj, map_div₀,
    ← _root_.mul_assoc, div_mul_cancel₀ _ ((map_ne_zero β).2 hd0)]

end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.LN.Cmp

theorem Oφ_baseChange {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {φ : R →+* V} {D : DegPre R}
    {D' : DegPre V} {β : D'.P.A.left ⟶ D.P.A.left} (pb : IsGrpPullback D'.P.A D.P.A (spMap φ) β) {x' : D'.X} {x : D.X}
    (hc : (D'.c x').left ≫ β = spMap φ ≫ (D.c x).left)
    {T : Over (Spec (CommRingCat.of R))} {T' : Over (Spec (CommRingCat.of V))}
    (p : T ⟶ D.P.A) (p' : T' ⟶ D'.P.A) (h : T'.left ⟶ T.left) (hp : p'.left ≫ β = h ≫ p.left) (κ : Fin 4) :
    D'.Oφ p' x' κ ≫ β = h ≫ D.Oφ p x κ := by
  have hb : h ≫ T.hom = T'.hom ≫ spMap φ := by
    rw [← Over.w p, ← Category.assoc, ← hp, Category.assoc, pb.1.w, ← Category.assoc, Over.w]
  let U : Over.mk (T'.hom ≫ spMap φ) ⟶ T := Over.homMk h hb
  have e : pushPt pb.1.w p' = U ≫ p := Over.OverMorphism.ext hp
  have c : pushPt pb.1.w (toUnit T' ≫ D'.c x') = toUnit _ ≫ D.c x := Over.OverMorphism.ext (by
    show (T'.hom ≫ (D'.c x').left) ≫ β = (T'.hom ≫ spMap φ) ≫ (D.c x).left
    rw [Category.assoc, hc, ← Category.assoc])
  refine Eq.trans ?_ (WeightPf.Oφ_comp U p x κ).symm
  rw [← e]
  fin_cases κ
  · exact congrArg (fun q => q.left) ((map_mul (pushHom pb T') p' (toUnit T' ≫ D'.c x')).trans
      (congrArg (pushPt pb.1.w p' * ·) c))
  · exact congrArg (fun q => q.left) c
  · rfl
  · exact congrArg (fun q => q.left) (map_one (pushHom pb T'))

theorem exists_comp_id : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V) (D : DegPre R) (D₁ D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (A₁ A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U₁ : PreU I' D₁ A₁ G') (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (C₁ : Cmp φ U U₁ F) (C₂ : Cmp (RingHom.id V) U₁ U' (𝟙 G'.left)) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull F)), IsCPMap U'.P U.P (spMap φ) F C₁.pb.1.w wL → (∀ (Z : Scheme.{0}) (r : Z ⟶ G'.left) (z : Z) (j : U.P.L.L.ι) (i : U₁.P.L.L.ι) (k : U'.P.L.L.ι), F (r z) ∈ U.P.L.L.U j → r z ∈ U₁.P.L.L.U i → r z ∈ U'.P.L.L.U k → gw wL r z j k = gw C₁.wL r z j i * gw C₂.wL r z i k) → ∃ C : Cmp φ U U' F, C.wL = wL := by
  intro R V _ _ _ _ I I' φ D D₁ D' A A₁ A' G _ _ G' _ _ U U₁ U' F C₁ C₂ wL hmap hw
  have g₁ := (isGen_iff _).1 C₁.v_gen
  have g₂ := (isGen_iff _).1 C₂.v_gen
  obtain ⟨v, T⟩ := exists_comp D₁.P.isLB C₁.v C₂.v g₁ g₂ D.P.isLB D'.P.isLB
  have pbB : IsGrpPullback D'.P.A D.P.A (spMap φ) (C₂.β ≫ C₁.β) := by
    have h := C₂.pbB.comp C₁.pbB
    rwa [spMap_ringHom_id, Category.id_comp] at h
  refine ⟨{
    pb := C₁.pb
    wL := wL
    wL_map := hmap
    β := C₂.β ≫ C₁.β
    pbB := pbB
    v := v
    v_gen := (isGen_iff _).2 (T.pgen_comp D₁.P.isLB g₁ g₂)
    xe := C₂.xe.trans C₁.xe
    c_pr := fun x => by
      rw [← Category.assoc, C₂.c_pr, spMap_ringHom_id, Category.id_comp, C₁.c_pr]
      rfl
    lev := fun e Z x' x hx => ?_
    map_le := C₁.map_le }, rfl⟩
  obtain ⟨a₁, b₁⟩ := C₁.lev e Z x' x hx
  obtain ⟨a₂, b₂⟩ := C₂.lev e Z x' x' (by rw [Category.comp_id])
  refine ⟨by rw [← a₁, reassoc_of% a₂], fun z J J' hJ hJ' => ?_⟩
  obtain ⟨J₁, hJ₁⟩ := exists_good_pt D₁.P.isLB z
  obtain ⟨c₁, d₁⟩ := b₁ z J J₁ hJ hJ₁
  obtain ⟨c₂, d₂⟩ := b₂ z J₁ J' hJ₁ hJ'
  have tri : ∀ f : Z ⟶ D'.P.A.left, gw v f z (J (f ≫ C₂.β ≫ C₁.β)) (J' f) =
      gw C₁.v (f ≫ C₂.β) z (J (f ≫ C₂.β ≫ C₁.β)) (J₁ (f ≫ C₂.β)) * gw C₂.v f z (J₁ (f ≫ C₂.β)) (J' f) :=
    fun f => T Z f z _ _ _ (hJ (f ≫ C₂.β ≫ C₁.β)) (hJ₁ (f ≫ C₂.β)) (hJ' f)
  refine ⟨fun χ => ?_, fun k k' hk hk' => ?_⟩
  · have hp : (U'.gt e).pG.left ≫ C₂.β = 𝟙 _ ≫ (U₁.gt e).pG.left := by
      have := (C₂.lev e _ (𝟙 _) (𝟙 _) (by rw [Category.comp_id])).1
      rwa [Category.id_comp] at this
    have o : ∀ κ, D'.Oφ (U'.gt e).pG χ κ ≫ C₂.β = D₁.Oφ (U₁.gt e).pG (C₂.xe χ) κ := fun κ =>
      (Oφ_baseChange C₂.pbB (C₂.c_pr χ) _ _ _ hp κ).trans (Category.id_comp _)
    refine (c₁ (C₂.xe χ)).trans ?_
    rw [c₂ χ, _root_.mul_assoc, ← Finset.prod_mul_distrib]
    refine congrArg _ (Finset.prod_congr rfl fun κ _ => ?_)
    have t := tri (x' ≫ D'.Oφ (U'.gt e).pG χ κ)
    simp only [Category.assoc] at t
    rw [t, mul_zpow, mul_comm, ← o κ]
    simp only [Category.assoc]
  · obtain ⟨i, hi⟩ := exists_chart U₁.P.L.isLB ((fstG I' e G').left (x' z))
    have t := tri (x' ≫ (U'.gt e).pG.left)
    simp only [Category.assoc] at t
    have a : x' ≫ (U'.gt e).pG.left ≫ C₂.β ≫ C₁.β = x ≫ (U.gt e).pG.left := by rw [← a₁, reassoc_of% a₂]
    rw [a, a₂] at t
    have hk₂ : F ((x' ≫ (fstG I' e G').left) z) ∈ U.P.L.L.U k := by
      have : F ((x' ≫ (fstG I' e G').left) z) = (fstG I e G).left (x z) :=
        (congrArg (fun q : Z ⟶ G.left => q z) hx).symm
      rw [this]; exact hk
    rw [t, hw Z (x' ≫ (fstG I' e G').left) z k i k' hk₂ hi hk', _root_.mul_assoc, d₂ i k' hi hk',
      ← _root_.mul_assoc, d₁ k i hk hi, _root_.mul_assoc]

end GlobalTheory.LN.Cmp
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.LN.PreForm

theorem gs_comp_stalk {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (h : Y ⟶ X) (z : Z) (U : X.Opens) (hU : h (r z) ∈ U)
    (a : Γ(X, U)) : gs (r ≫ h) z U a = (r.stalkMap z).hom (gs h (r z) U a) := by
  rw [← gs_pull r h z U hU, gs_eq r z (h ⁻¹ᵁ U) hU, gs_eq h (r z) U hU]
  exact (Scheme.Hom.germ_stalkMap_apply r (h ⁻¹ᵁ U) z hU _).symm

theorem sval_comp_stalk {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval s (r ≫ h) z J = (r.stalkMap z).hom (sval s h (r z) (fun ψ => J (r ≫ ψ))) := by
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gs_comp_stalk r h z _ (Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)) _

theorem sval_eq_of_id {X Y Y' : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y' ⟶ X)} {ε' : K' → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L φ' ε')) (h : Y' ⟶ Y)
    (H : ∀ y J, Good L y J → sval s' (𝟙 Y') y J = sval s h y J)
    (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) :
    sval s' r z J = sval s (r ≫ h) z J := by
  have e := sval_comp_stalk s' (𝟙 Y') r z hJ
  rw [Category.comp_id] at e
  rw [e, sval_comp_stalk s h r z hJ, H (r z) (fun ψ => J (r ≫ ψ)) (fun ψ => hJ (r ≫ ψ))]

theorem under_iff_match {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    (U : PreU I D.toPre A G) (U₀ : UnifPre I D A G) : Under U U₀ ↔ GlobalTheory.UU.Match U U₀ :=
  ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨a.symm, b.symm, c.symm, d.symm, e.symm, f.symm⟩,
    fun ⟨a, b, c, d, e, f⟩ => ⟨a.symm, b.symm, c.symm, d.symm, e.symm, f.symm⟩⟩

theorem under_exists_and_expands : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → (∀ U₀ : UnifPre I D A G, ∃ U : PreU I D.toPre A G, Under U U₀) ∧ (∀ U : PreU I D.toPre A G, ∃ U₀ : UnifPre I D A G, Under U U₀) ∧ ∀ (U : PreU I D.toPre A G) (U₀ : UnifPre I D A G), Under U U₀ → ∀ (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D.toPre (𝟙_ _) k α) (σ₀ : H0 U₀.LG.L k) (f₀ : ∀ α, D.toPre.SecB k α), (∀ σ₁ : H0 U.P.L.L k, HEq σ₁ σ₀ → ∀ z J, Good U.P.L.L z J → sval σ (𝟙 _) z J = sval σ₁ (snd (𝟙_ _) G).left z J) → (∀ α z J, Good D.toPre.P.L z J → sval (f α) (𝟙 _) z J = sval (f₀ α) (snd (𝟙_ _) D.toPre.P.A).left z J) → (U.ExpT (𝟙_ _) k σ f ↔ ∀ e, U₀.ExpandsAt e k σ₀ f₀) := by
  intro hL _ R _ _ I D A G _ _ hG
  refine ⟨fun U₀ => ?_, fun U => ?_, fun U U₀ hU k σ f σ₀ f₀ hσ hf => ?_⟩
  · obtain ⟨w, hw⟩ := U₀.ext
    obtain ⟨U, hU, -⟩ := GlobalTheory.ValueForm.exists_preU_match hL.globalFns R I D A G U₀ hG w hw
    exact ⟨U, (under_iff_match U U₀).2 hU⟩
  · obtain ⟨U₀, hU⟩ := GlobalTheory.UU.ToChart.exists_match R I D A G U
    exact ⟨U₀, (under_iff_match U U₀).2 hU⟩
  · have hM := (under_iff_match U U₀).1 hU
    have ht : H0 U₀.LG.L k = H0 U.P.L.L k := by rw [hM.LG]
    have hc : HEq (cast ht σ₀) σ₀ := cast_heq ht σ₀
    have sG : SameG (cast ht σ₀) σ := fun Z r z J hJ => sval_eq_of_id _ _ _ (hσ _ hc) Z r z J hJ
    have sB : SameB f₀ f := fun α Z r z J hJ => sval_eq_of_id _ _ _ (hf α) Z r z J hJ
    exact ⟨expandsAt_of_expT R I D A G U U₀ hM k σ₀ _ σ f₀ f hc.symm sG sB,
      expT_of_expandsAt R I D A G U U₀ hM k σ₀ _ σ f₀ f hc.symm sG sB⟩

end GlobalTheory.LN.PreForm
end
end
