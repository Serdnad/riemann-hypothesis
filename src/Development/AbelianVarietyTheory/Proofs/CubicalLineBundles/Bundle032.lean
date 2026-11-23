module

public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
public import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementB
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle017
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle037
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle002
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle027
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.IntCoord

section General

variable {R : Type} [CommRing R]

def sc (c : R) : epsR R ⟶ epsR R := Over.homMk (spMap (epsScaleR c)) (LieCombBaseChange.epsScale_over c)

theorem sc_comm (a b : R) : sc a ≫ sc b = sc b ≫ sc a := by
  refine Over.OverMorphism.ext ?_
  refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)
  congr 1
  refine RingHom.ext fun x => ?_
  ext <;> simp [epsScaleR, mul_left_comm]

theorem sc_one : sc (1 : R) = 𝟙 _ := by
  refine Over.OverMorphism.ext ?_
  refine Eq.trans ?_ (Spec.map_id (CommRingCat.of (DualNumber R)))
  show spMap _ = spMap (RingHom.id _)
  congr 1
  refine RingHom.ext fun x => ?_
  ext <;> simp [epsScaleR]

variable {G : Over (Sp R)} [GrpObj G]

theorem isLieComb_iff {n : ℕ} (c : Fin n → R) (v : Fin n → (epsR R ⟶ G)) (w : epsR R ⟶ G) :
    IsLieComb c v w ↔ w = (List.ofFn fun i => sc (c i) ≫ v i).prod := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    congr 2
    exact funext fun i => Over.OverMorphism.ext (hu i)
  · rintro rfl
    exact ⟨_, fun _ => rfl, rfl⟩

theorem isLieComb_one_iff (c : R) (v w : epsR R ⟶ G) : IsLieComb ![c] ![v] w ↔ w = sc c ≫ v := by
  rw [isLieComb_iff]
  simp

theorem isLieComb_mul (v w : epsR R ⟶ G) : IsLieComb ![1, 1] ![v, w] (v * w) := by
  rw [isLieComb_iff]
  simp [sc_one]

theorem isLieComb_nil : IsLieComb (![] : Fin 0 → R) (![] : Fin 0 → (epsR R ⟶ G)) 1 := by
  rw [isLieComb_iff]
  simp

theorem eq_of_isVecOver {R' : Type} [CommRing R'] {f : R →+* R'} (hf : Function.Injective f) {A : Over (Sp R)}
    [IsSeparated A.hom] {A' : Over (Sp R')} {φ : A'.left ⟶ A.left} {u u' : epsR R ⟶ A} {w : epsR R' ⟶ A'}
    (h : IsVecOver f φ u w) (h' : IsVecOver f φ u' w) : u = u' := by
  have : IsSchemeTheoreticallyDominant (spMap (Chart.dualMapR f)) := by
    refine (schemeDominant_specMap_iff _).2 fun x y e => ?_
    have e1 := congrArg TrivSqZeroExt.fst e
    have e2 := congrArg TrivSqZeroExt.snd e
    simp [Chart.dualMapR] at e1 e2
    exact TrivSqZeroExt.ext (hf e1) (hf e2)
  refine Over.OverMorphism.ext ?_
  exact hom_ext_of_isSchemeTheoreticallyDominant (spMap (Chart.dualMapR f)) A.hom (h.symm.trans h')
    ((Over.w u).trans (Over.w u').symm)

end General

variable {K : Type} [Field K] [NumberField K] {P : Out.PolAV (Sp (𝓞 K))} (F : GenFib P)

theorem isCoord_comb {n : ℕ} {u : Fin n → (epsR (𝓞 K) ⟶ P.A)} {c : Fin n → Fin F.P₀.g → K}
    (h : ∀ i, F.IsCoord (u i) (c i)) {a : Fin n → 𝓞 K} {u' : epsR (𝓞 K) ⟶ P.A} (ha : IsLieComb a u u') :
    F.IsCoord u' (∑ i, a i • c i) := by
  have := P.isAb.comm
  have := F.P₀.isAb.comm
  choose ht w hw hc using h
  obtain ⟨w', hw', -⟩ := existsUnique_isVecOver F.fib.2.1.1 u'
  refine ⟨(LieComb.lieComb_algebra _ _ _ u ht).2.1 a u' ha, w', hw', ?_⟩
  exact (LieComb.lieComb_algebra _ _ _ F.v F.basis.1).2.2.1 n c w _ w' hc
    ((lieComb_baseChange _ _ _ _ _ _ F.fib.2.1 n u u' a w w' hw ha).1 hw')

theorem isCoord_one : F.IsCoord 1 0 := by
  simpa using isCoord_comb F (c := ![]) (fun i => i.elim0) isLieComb_nil

theorem isCoord_mul {u u' : epsR (𝓞 K) ⟶ P.A} {c c' : Fin F.P₀.g → K} (h : F.IsCoord u c) (h' : F.IsCoord u' c') :
    F.IsCoord (u * u') (c + c') := by
  simpa using isCoord_comb F (c := ![c, c']) (fun i => by fin_cases i; exacts [h, h']) (isLieComb_mul u u')

theorem isCoord_smul {u u' : epsR (𝓞 K) ⟶ P.A} {c : Fin F.P₀.g → K} {r : 𝓞 K} (h : F.IsCoord u c)
    (h' : IsLieComb ![r] ![u] u') : F.IsCoord u' (r • c) := by
  simpa using isCoord_comb F (c := ![c]) (fun i => by fin_cases i; exact h) h'

theorem mem_span_iff (p : (epsR (𝓞 K) ⟶ P.A) → Prop) (h1 : p 1) (hm : ∀ u u', p u → p u' → p (u * u'))
    (hs : ∀ r u, p u → p (sc r ≫ u)) (c : Fin F.P₀.g → K) :
    c ∈ Submodule.span (𝓞 K) {c | ∃ u, F.IsCoord u c ∧ p u} ↔ ∃ u, F.IsCoord u c ∧ p u := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨1, isCoord_one F, h1⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, hu, pu⟩ := hx
    obtain ⟨u', hu', pu'⟩ := hy
    exact ⟨_, isCoord_mul F hu hu', hm _ _ pu pu'⟩
  | smul r x _ hx =>
    obtain ⟨u, hu, pu⟩ := hx
    exact ⟨_, isCoord_smul F hu ((isLieComb_one_iff r u _).2 rfl), hs _ _ pu⟩

end GlobalTheory.CM.IntCoord

namespace GlobalTheory.CM

open IntCoord

theorem integral_tangent_coordinates : ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P), (∀ u, IsTangent u → ∃! c, F.IsCoord u c) ∧ (∀ u u' c, F.IsCoord u c → F.IsCoord u' c → u = u') ∧ (∀ u u' c c', F.IsCoord u c → F.IsCoord u' c' → F.IsCoord (u * u') (c + c')) ∧ (∀ u u' c (r : 𝓞 K), F.IsCoord u c → IsLieComb ![r] ![u] u' → F.IsCoord u' (r • c)) ∧ (∀ c, c ∈ F.lieLat ↔ ∃ u, F.IsCoord u c) ∧ ∀ (O : Type) [CommRing O] (act : OAct O P.A) (τ : O →+* 𝓞 K) c, c ∈ F.eigLat act τ ↔ ∃ u, F.IsCoord u c ∧ ∀ a, IsLieComb ![τ a] ![u] (u ≫ act.act a) := by
  intro K _ _ P F
  refine ⟨fun u hu => ?_, fun u u' c h h' => ?_, fun u u' c c' => isCoord_mul F, fun u u' c r => isCoord_smul F,
    fun c => ?_, fun O _ act τ c => ?_⟩
  · obtain ⟨w, hw, hw'⟩ := existsUnique_isVecOver F.fib.2.1.1 u
    obtain ⟨c, hc, hc'⟩ := F.basis.2 w (hw.isTangent F.fib.2.1 hu)
    exact ⟨c, ⟨hu, w, hw, hc⟩, fun c' ⟨_, w', h₁, h₂⟩ => hc' c' (hw' w' h₁ ▸ h₂)⟩
  · obtain ⟨-, w, hw, hc⟩ := h
    obtain ⟨-, w', hw', hc'⟩ := h'
    obtain rfl : w = w' := ((isLieComb_iff _ _ _).1 hc).trans ((isLieComb_iff _ _ _).1 hc').symm
    have := P.isAb.proper
    exact eq_of_isVecOver (IsFractionRing.injective (𝓞 K) K) hw hw'
  · simpa [GenFib.lieLat] using mem_span_iff F (fun _ => True) trivial (fun _ _ _ _ => trivial) (fun _ _ _ => trivial) c
  · refine mem_span_iff F (fun u => ∀ a, IsLieComb ![τ a] ![u] (u ≫ act.act a)) (fun a => ?_)
      (fun u u' h h' a => ?_) (fun r u h a => ?_) c
    · have := act.hom a
      rw [isLieComb_one_iff, MonObj.comp_one, MonObj.one_comp]
    · have := act.hom a
      rw [isLieComb_one_iff, MonObj.comp_mul, MonObj.mul_comp, (isLieComb_one_iff _ _ _).1 (h a),
        (isLieComb_one_iff _ _ _).1 (h' a)]
    · rw [isLieComb_one_iff, Category.assoc, (isLieComb_one_iff _ _ _).1 (h a), ← Category.assoc, sc_comm,
        Category.assoc]

end GlobalTheory.CM
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section
namespace GlobalTheory.LamF.KeyArch

theorem pos_of_isArchNorm (hU : ThetaUnifAV) (x : KeyIn ℂ) {nth nη : ℝ} (h : KeyPow.IsArchNorm x nth nη) :
    0 < nth ∧ 0 < nη := by
  obtain ⟨u, Hm, W, χ, θ, Fd, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := h
  obtain ⟨u', τ, M, a, b, c, -, -, -, -, -, -, -, -, -, -, e⟩ :=
    keyIn_normal_form_and_archimedean_constant hU x u Hm W χ θ Fd nth nη h₁ h₂ h₃ h₄ h₅ h₆ h₇
  have p₁ : 0 ≤ nth :=
    h₆ ▸ div_nonneg (MeasureTheory.integral_nonneg fun z => by positivity) ENNReal.toReal_nonneg
  have p₂ : 0 ≤ nη := h₇ ▸ by positivity
  have hne : ‖M.det ^ 4 / c ^ 8‖ * nth ^ 4 * nη ^ 2 ≠ 0 := by
    rw [e]; have := Real.pi_pos; positivity
  have q₁ := right_ne_zero_of_mul (left_ne_zero_of_mul hne)
  have q₂ := right_ne_zero_of_mul hne
  exact ⟨p₁.lt_of_ne' fun h0 => q₁ (by rw [h0]; norm_num), p₂.lt_of_ne' fun h0 => q₂ (by rw [h0]; norm_num)⟩

theorem exists_pos_keyArchAt : ThetaUnifAV → ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (σ : K →+* ℂ), ∃ t n : ℝ, 0 < t ∧ 0 < n ∧ ∀ T abelian₂ : MLine K, T.n σ = t → abelian₂.n σ = n → KeyArchAt x T abelian₂ σ := by
  intro hU K _ _ x σ
  obtain ⟨x', hx⟩ := KeyPow.exists_keyPB x σ
  obtain ⟨nth, nη, h⟩ := KeyPow.exists_isArchNorm hU x'
  obtain ⟨p₁, p₂⟩ := pos_of_isArchNorm hU x' h
  obtain ⟨u, Hm, W, χ, θ, Fd, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := h
  refine ⟨Real.sqrt nth, Real.sqrt nη⁻¹, Real.sqrt_pos.2 p₁, Real.sqrt_pos.2 (inv_pos.2 p₂), fun T abelian₂ hT hL =>
    ⟨x', u, Hm, W, χ, θ, Fd, hx, h₁, h₂, h₃, h₄, h₅, ?_, ?_⟩⟩
  · rw [hT, Real.sq_sqrt p₁.le, h₆]
  · rw [hL, Real.sq_sqrt (inv_pos.2 p₂).le, h₇, inv_div]

end GlobalTheory.LamF.KeyArch
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem mem_range_iff_valuation_le_one {R K Γ : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (hR : ∀ r : R, v (algebraMap R K r) ≤ 1) {π : K} (hπ0 : v π ≠ 0) (hπ : v π < 1) (y : K) :
    y ∈ Set.range (algebraMap R K) ↔ v y ≤ 1 := by
  refine ⟨fun ⟨r, hr⟩ => hr ▸ hR r, fun hy => ?_⟩
  have hu : ∀ u : Rˣ, v (algebraMap R K u) = 1 := fun u => by
    refine le_antisymm (hR _) ?_
    have h1 : v (algebraMap R K u) * v (algebraMap R K (u⁻¹ : Rˣ)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    calc (1 : Γ) = _ := h1.symm
      _ ≤ v (algebraMap R K u) * 1 := mul_le_mul_right (hR _) _
      _ = _ := _root_.mul_one _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hlt : v (algebraMap R K ϖ) < 1 := by
    refine lt_of_le_of_ne (hR _) fun h => ?_
    rcases ValuationRing.isInteger_or_isInteger R π with ⟨r, hr⟩ | ⟨r, hr⟩
    · have hr0 : r ≠ 0 := by
        rintro rfl
        rw [map_zero] at hr
        exact hπ0 (by rw [← hr, map_zero])
      obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hϖ
      rw [← hr, map_mul, map_mul, hu, map_pow, map_pow, h, one_pow, _root_.mul_one] at hπ
      exact lt_irrefl _ hπ
    · have := hR r
      rw [hr, map_inv₀, inv_le_one₀ (zero_lt_iff.2 hπ0)] at this
      exact absurd hπ (not_lt.2 this)
  rcases ValuationRing.isInteger_or_isInteger R y with h | ⟨r, hr⟩
  · exact h
  · by_cases hy0 : y = 0
    · exact ⟨0, by rw [hy0, map_zero]⟩
    by_cases hr' : IsUnit r
    · obtain ⟨u, rfl⟩ := hr'
      refine ⟨(u⁻¹ : Rˣ), ?_⟩
      rw [← inv_inv y, ← hr]
      exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
    · exfalso
      have hm : r ∈ IsLocalRing.maximalIdeal R := hr'
      rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
      obtain ⟨s, rfl⟩ := hm
      have h1 : v y⁻¹ < 1 := by
        rw [← hr, map_mul, map_mul]
        calc _ ≤ v (algebraMap R K ϖ) * 1 := mul_le_mul_right (hR _) _
          _ < 1 := by rwa [_root_.mul_one]
      rw [map_inv₀, inv_lt_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff v).2 hy0))] at h1
      exact absurd hy (not_le.2 h1)

theorem keyLocAt_of_isLocalModel : ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (p : HeightOneSpectrum (𝓞 K)) (a : K) (M : Matrix (Fin x.P.g) (Fin x.P.g) K), KeyPow.IsLocalModel x p a M → IsLocGen p a T.I → IsLocGen p M.det abelian₂.I → KeyLocAt x T abelian₂ p := by
  intro K _ _ x T abelian₂ p a M hM ha hd
  obtain ⟨R, _, _, _, _, _, y, th', hth', v', hv', hR, h1, h2, h3⟩ := hM
  obtain ⟨π, hπ⟩ := p.valuation_exists_uniformizer K
  refine ⟨K, inferInstance, inferInstance, R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    RingHom.id K, x, a, M.det, a, M.det, 1, 1, GlobalTheory.keyPB_id K x, ⟨th', hth', v', hv', M, y, h1, h2, rfl, h3⟩,
    fun z => ?_, by simp, by simp, ha, hd⟩
  refine mem_range_iff_valuation_le_one (p.valuation K) hR (π := π) (hπ ▸ WithZero.exp_ne_zero) ?_ z
  rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  decide

end GlobalTheory.LamF
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory IsLocalRing Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM
open scoped nonZeroDivisors ComplexOrder

namespace GlobalTheory

theorem isLocGen_pow_div_pow {K : Type} [Field K] [NumberField K] {p : HeightOneSpectrum (𝓞 K)} {ca cd : K}
    {A B : FractionalIdeal (𝓞 K)⁰ K} (m n : ℕ) (hA : A ≠ 0) (hB : B ≠ 0) (ha : IsLocGen p ca A) (hb : IsLocGen p cd B) :
    IsLocGen p (ca ^ m / cd ^ n) (A ^ m * (B ^ n)⁻¹) := by
  refine ⟨div_ne_zero (pow_ne_zero _ ha.1) (pow_ne_zero _ hb.1), ?_⟩
  have hsa : FractionalIdeal.spanSingleton (𝓞 K)⁰ ca ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact ha.1
  have hsb : FractionalIdeal.spanSingleton (𝓞 K)⁰ cd ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact hb.1
  have hs : FractionalIdeal.spanSingleton (𝓞 K)⁰ (ca ^ m / cd ^ n) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ ca ^ m * (FractionalIdeal.spanSingleton (𝓞 K)⁰ cd ^ n)⁻¹ := by
    rw [FractionalIdeal.spanSingleton_pow, FractionalIdeal.spanSingleton_pow, FractionalIdeal.spanSingleton_inv,
      FractionalIdeal.spanSingleton_mul_spanSingleton, div_eq_mul_inv]
  rw [hs, FractionalIdeal.count_mul K p (pow_ne_zero _ hsa) (inv_ne_zero (pow_ne_zero _ hsb)),
    FractionalIdeal.count_mul K p (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hB)),
    FractionalIdeal.count_inv, FractionalIdeal.count_inv, FractionalIdeal.count_pow, FractionalIdeal.count_pow,
    FractionalIdeal.count_pow, FractionalIdeal.count_pow, ha.2, hb.2]

theorem thetaLine_dual_deg_of_keyFormulaPow : GlobalTheory.KeyFormulaPow → ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K)
    (T abelian₂ : MLine K), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) →
    T.dual.deg = (1 / 2) * abelian₂.dual.deg + (x.P.g : ℝ) / 4 * (Module.finrank ℚ K : ℝ) * Real.log (2 * Real.pi) := by
  intro hKF K _ _ x T abelian₂ hT hL hloc harch
  obtain ⟨N, hN, κ, hH, hF, hU1, -, hU2⟩ := hKF
  obtain ⟨n, hn⟩ : ∃ n, n = N x.P.g := ⟨_, rfl⟩
  have hn1 : 1 ≤ n := hn ▸ hN _
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  set k : K := (κ K x : K) with hkdef
  have hk : k ≠ 0 := (κ K x).ne_zero
  have hloc' : ∀ p : HeightOneSpectrum (𝓞 K), ∃ ca cd : K, IsLocGen p ca T.I ∧ IsLocGen p cd abelian₂.I ∧
      p.valuation K k ≤ p.valuation K (ca ^ (8 * n) / cd ^ (4 * n)) ∧
      p.valuation K k⁻¹ ≤ p.valuation K (ca ^ (8 * n) / cd ^ (4 * n))⁻¹ := by
    intro p
    obtain ⟨K', _, _, R, _, _, _, _, _, f, x', a, d, ca, cd, ua, ud, hPB, hInt, hval, ha, hd, hca, hcd⟩ := hloc p
    obtain ⟨th', hth', v', hv', M, xR, hth'eq, hv'eq, hMdet, hPBR⟩ := hInt
    have hFx : (κ K' x' : K') = f k := hF K K' f x x' hPB
    have hg : x'.P.g = x.P.g := by obtain ⟨-, -, -, hg, -⟩ := hPB; exact hg
    have hn2 : N x'.P.g = n := by rw [hg, hn]
    have hHx : a ^ (8 * N x'.P.g) * (κ K' ⟨x'.P, x'.g_pos, x'.rig, x'.rig_gen, th', hth', v', hv'⟩ : K') =
        M.det ^ (4 * N x'.P.g) * (κ K' x' : K') :=
      hH K' x'.P x'.g_pos x'.rig x'.rig_gen x'.th x'.th_ne x'.v x'.basis th' hth' v' hv' a M hth'eq hv'eq
    obtain ⟨u, hu, -⟩ := hU1 R K' xR _ hPBR
    rw [hn2, hu, hFx, hMdet, ha, hd] at hHx
    generalize 8 * n = r at hHx ⊢
    generalize 4 * n = s at hHx ⊢
    have hfa : f ca ≠ 0 := (map_ne_zero f).2 hca.1
    have hfd : f cd ≠ 0 := (map_ne_zero f).2 hcd.1
    have hD : algebraMap R K' (ud : R) ≠ 0 := (ud.isUnit.map (algebraMap R K')).ne_zero
    have hc : ca ^ r / cd ^ s ≠ 0 := div_ne_zero (pow_ne_zero _ hca.1) (pow_ne_zero _ hcd.1)
    have hfk : f k = (f ca * algebraMap R K' (ua : R)) ^ r * algebraMap R K' (u : R) /
        (f cd * algebraMap R K' (ud : R)) ^ s := by
      rw [eq_div_iff (pow_ne_zero _ (mul_ne_zero hfd hD)), hHx]; ring
    have hw : f (k / (ca ^ r / cd ^ s)) = algebraMap R K' ((ua ^ r * u * ud⁻¹ ^ s : Rˣ) : R) := by
      rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_mul, map_mul,
        map_pow, map_pow, map_units_inv, map_div₀, map_div₀, map_pow, map_pow, hfk, mul_pow, mul_pow, inv_pow]
      field_simp
    have hw' : f (k⁻¹ / (ca ^ r / cd ^ s)⁻¹) = algebraMap R K' (((ua ^ r * u * ud⁻¹ ^ s)⁻¹ : Rˣ) : R) := by
      rw [inv_div_inv, ← inv_div, map_inv₀, hw, map_units_inv]
    exact ⟨ca, cd, hca, hcd, valuation_le_of_eq_algebraMap p f hval hc _ hw,
      valuation_le_of_eq_algebraMap p f hval (inv_ne_zero hc) _ hw'⟩
  have hJ : T.I ^ (8 * n) * (abelian₂.I ^ (4 * n))⁻¹ ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hT.1) (inv_ne_zero (pow_ne_zero _ hL.1))
  have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ k = T.I ^ (8 * n) * (abelian₂.I ^ (4 * n))⁻¹ := by
    have hsk : FractionalIdeal.spanSingleton (𝓞 K)⁰ k ≠ 0 := by
      rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact hk
    refine eq_of_count_eq hsk hJ (fun p => ?_)
    obtain ⟨ca, cd, h1, h2, h3, h4⟩ := hloc' p
    have h5 := isLocGen_pow_div_pow (8 * n) (4 * n) hT.1 hL.1 h1 h2
    rw [count_eq_of_valuation_le p hk h5.1 h3 h4, h5.2]
  have hNT : ((FractionalIdeal.absNorm T.I : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.2 hT.1)
  have hNL : ((FractionalIdeal.absNorm abelian₂.I : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.2 hL.1)
  have hNk : Real.log ((FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ k) : ℚ) : ℝ) =
      n * (8 * Real.log ((FractionalIdeal.absNorm T.I : ℚ) : ℝ) -
        4 * Real.log ((FractionalIdeal.absNorm abelian₂.I : ℚ) : ℝ)) := by
    rw [hspan, map_mul, map_inv₀, map_pow, map_pow]
    push_cast
    rw [Real.log_mul (pow_ne_zero _ hNT) (inv_ne_zero (pow_ne_zero _ hNL)), Real.log_inv, Real.log_pow,
      Real.log_pow]
    push_cast
    ring
  have harch' : ∀ σ : K →+* ℂ, Real.log ‖σ k‖ + 8 * n * Real.log (T.n σ) - 4 * n * Real.log (abelian₂.n σ) =
      2 * (x.P.g : ℝ) * n * Real.log (2 * Real.pi) := by
    intro σ
    obtain ⟨xσ, u, Hm, W, χ, θ, Fd, hPB, hAH, hRig, hFn, hDiff, hFD, hTn, hLn⟩ := harch σ
    have hFσ : (κ ℂ xσ : ℂ) = σ k := hF K ℂ σ x xσ hPB
    obtain ⟨_, _, _, hg, _⟩ := hPB
    have he : (volume Fd).toReal / (Real.pi ^ xσ.P.g * ‖W.det‖ ^ 2) = (abelian₂.n σ ^ 2)⁻¹ := by
      rw [hLn, inv_div]
    have hU := hU2 xσ u Hm W χ θ Fd _ _ hAH hRig hFn hDiff hFD hTn rfl
    rw [he, hFσ, hg, ← hn] at hU
    have hsk0 : 0 < ‖σ k‖ := norm_pos_iff.2 ((map_ne_zero σ).2 hk)
    have ht := hT.2 σ
    have hl := hL.2 σ
    have := congrArg Real.log hU
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)] at this
    simp only [Real.log_pow, Real.log_inv] at this
    push_cast at this
    linarith
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (K →+* ℂ))) rfl (fun σ _ => harch' σ)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, NumberField.Embeddings.card K ℂ, nsmul_eq_mul, sum_log_norm_embeddings hk, hNk] at hsum
  simp only [MLine.deg, MLine.dual, map_inv₀, Rat.cast_inv, Real.log_inv, Finset.sum_neg_distrib]
  refine mul_left_cancel₀ hn' ?_
  linarith

end GlobalTheory
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

theorem curve_lattice_baseChange : ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (Lf : (R →+* ℂ) → PeriodPair) (R₁ : Type) [CommRing R₁] (f : R →+* R₁) (P₁ : Out.PolAV (Sp R₁)) (φ : P₁.A.left ⟶ P.A.left) (v₁ : epsR R₁ ⟶ P₁.A), (P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : R →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : R →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (Lf s').lattice ↔ z • w' ∈ u'.Λ)) → IsPolFibre f P P₁ φ → IsVecOver f φ v v₁ → (P₁.g = 1 ∧ IsLieBasis ![v₁] ∧ (∀ (R' : Type) [CommRing R'] (f' : R₁ →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P₁.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P₁ P' φ' → IsVecOver f' φ' v₁ v' → IsLieBasis ![v']) ∧ ∀ s' : R₁ →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P₁.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P₁ P' φ' → IsVecOver s' φ' v₁ v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ ((fun s : R₁ →+* ℂ => Lf (s.comp f)) s').lattice ↔ z • w' ∈ u'.Λ)) := by
  intro R _ P v Lf R₁ _ f P₁ φ v₁ ⟨hg, _, hfib, hlat⟩ hP₁ hv₁

  have up : ∀ (R' : Type) [CommRing R'] (f' : R₁ →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P₁.A.left)
      (v' : epsR R' ⟶ P'.A), IsPolFibre f' P₁ P' φ' → IsVecOver f' φ' v₁ v' →
      IsPolFibre (f'.comp f) P P' (φ' ≫ φ) ∧ IsVecOver (f'.comp f) (φ' ≫ φ) v v' := by
    intro R' _ f' P' φ' v' hP' hv'
    exact ⟨PolFibre.comp hP₁ hP', (PolFibre.vec_iff hP₁.2.1.1 hP'.2.1.1.w hv₁).1 hv'⟩
  refine ⟨hP₁.1.trans hg, hfib R₁ f P₁ φ v₁ hP₁ hv₁, ?_, ?_⟩
  · intro R' _ f' P' φ' v' hP' hv'
    obtain ⟨h₁, h₂⟩ := up R' f' P' φ' v' hP' hv'
    exact hfib R' (f'.comp f) P' (φ' ≫ φ) v' h₁ h₂
  · intro s' P' φ' v' u' w' hP' hv' hd
    obtain ⟨h₁, h₂⟩ := up ℂ s' P' φ' v' hP' hv'
    exact hlat (s'.comp f) P' (φ' ≫ φ) v' u' w' h₁ h₂ hd

end GlobalTheory
end
end
