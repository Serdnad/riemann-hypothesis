module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulOriginSec
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle026
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RigidifiedOfChart
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle051
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DiagZEqNegAddY
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AwayToAwayRightEqOfComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

theorem _root_.GlobalTheory.T.originLineBundle_polarisation : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R) [GrpObj (schemeOver W)], IsCommMonObj (schemeOver W) → η[schemeOver W].left = zero W → Out.Rigidified (schemeOver W) (originLB W) ∧ Out.Sym (schemeOver W) (originLB W) ∧ Out.RelAmple (schemeOver W) (originLB W) ∧ Out.KTriv (schemeOver W) (originLB W) := by
  first | exact @GlobalTheory.WeierstrassCurve.originLB_polarisation | exact GlobalTheory.WeierstrassCurve.originLB_polarisation | (intros; apply GlobalTheory.WeierstrassCurve.originLB_polarisation <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

section
variable {E K K' : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Field K'] [NumberField K']

theorem ringOfIntegers_hom_injective (τ : 𝓞 E →+* 𝓞 K) : Function.Injective τ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  have : (RingHom.ker τ).IsPrime := RingHom.ker_isPrime τ
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [eq_bot_iff]
  intro n hn
  rw [Ideal.mem_comap, RingHom.mem_ker] at hn
  simpa using hn

theorem existsUnique_extend_ringOfIntegers_hom (τ : 𝓞 E →+* 𝓞 K) :
    ∃! τ' : E →+* K, ∀ a : 𝓞 E, τ' a = τ a := by
  have hi : Function.Injective ((algebraMap (𝓞 K) K).comp τ) :=
    (RingOfIntegers.coe_injective).comp (ringOfIntegers_hom_injective τ)
  have hl : ∀ a : 𝓞 E, (IsFractionRing.lift hi : E →+* K) (algebraMap (𝓞 E) E a) = algebraMap (𝓞 K) K (τ a) :=
    fun a => IsFractionRing.lift_algebraMap (A := 𝓞 E) (K := E) hi a
  generalize (IsFractionRing.lift hi : E →+* K) = σ₀ at hl
  refine ⟨σ₀, hl, fun σ hσ => ?_⟩
  refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => ?_)
  exact (hσ a).trans (hl a).symm

theorem mapRingHom_bijective :
    Function.Bijective fun σ : E →+* K => (RingOfIntegers.mapRingHom σ : 𝓞 E →+* 𝓞 K) := by
  constructor
  · intro σ σ' h
    refine (existsUnique_extend_ringOfIntegers_hom (RingOfIntegers.mapRingHom σ)).unique (fun a => rfl) fun a => ?_
    have h' : RingOfIntegers.mapRingHom σ = RingOfIntegers.mapRingHom σ' := h
    rw [h']
    rfl
  · intro τ
    obtain ⟨σ, hσ⟩ := (existsUnique_extend_ringOfIntegers_hom τ).exists
    exact ⟨σ, RingHom.ext fun a => RingOfIntegers.ext (hσ a)⟩

theorem splits_iff_card : Splits E K ↔ Nat.card (E →+* K) = Module.finrank ℚ E := by
  rw [Splits, ← Nat.card_eq_of_bijective _ (mapRingHom_bijective (E := E) (K := K))]

theorem card_ringHom_le_finrank : Nat.card (E →+* K) ≤ Module.finrank ℚ E := by
  rw [Nat.card_congr (RingHom.equivRatAlgHom E K)]
  exact card_algHom_le_finrank ℚ E K

theorem comp_bijective_of_splits (j : K →+* K') (h : Splits E K) :
    Function.Bijective fun σ : E →+* K => j.comp σ := by
  have : Finite (E →+* K') := Finite.of_equiv _ (RingHom.equivRatAlgHom E K').symm
  have hi : Function.Injective fun σ : E →+* K => j.comp σ := fun σ σ' e =>
    RingHom.ext fun a => j.injective (DFunLike.congr_fun e a)
  refine hi.bijective_of_nat_card_le ?_
  rw [splits_iff_card.1 h]
  exact card_ringHom_le_finrank

end

theorem splits_basic : ∀ (E : Type) [Field E] [NumberField E], (∃ k : IntermediateField ℚ ℂ, FiniteDimensional ℚ k ∧ ∀ (τ : E →+* ℂ) a, τ a ∈ k) ∧ (∀ (k : IntermediateField ℚ ℂ) [NumberField k], (∀ (τ : E →+* ℂ) a, τ a ∈ k) → Splits E k) ∧ ∀ (K : Type) [Field K] [NumberField K], (Splits E K ↔ Nat.card (E →+* K) = Module.finrank ℚ E) ∧ (∀ τ : 𝓞 E →+* 𝓞 K, ∃! τ' : E →+* K, ∀ a : 𝓞 E, τ' a = τ a) ∧ ∀ (K' : Type) [Field K'] [NumberField K'] (j : K →+* K'), Splits E K → Splits E K' ∧ Function.Bijective fun τ : 𝓞 E →+* 𝓞 K => (RingOfIntegers.mapRingHom j).comp τ := by
  intro E _ _
  refine ⟨⟨IntermediateField.normalClosure ℚ E ℂ, inferInstance, fun τ a => ?_⟩, fun k _ hk => ?_,
    fun K _ _ => ⟨splits_iff_card, existsUnique_extend_ringOfIntegers_hom, fun K' _ _ j h => ⟨?_, ?_⟩⟩⟩
  · exact AlgHom.fieldRange_le_normalClosure τ.toRatAlgHom ⟨a, rfl⟩
  · rw [splits_iff_card, ← Embeddings.card E ℂ, ← Nat.card_eq_fintype_card]
    refine Nat.card_eq_of_bijective (fun σ => (algebraMap k ℂ).comp σ) ⟨fun σ σ' e => ?_, fun τ => ?_⟩
    · exact RingHom.ext fun a => (algebraMap k ℂ).injective (DFunLike.congr_fun e a)
    · exact ⟨τ.codRestrict k (hk τ), RingHom.ext fun a => rfl⟩
  · rw [splits_iff_card, ← Nat.card_eq_of_bijective _ (comp_bijective_of_splits j h)]
    exact splits_iff_card.1 h
  · have e : ((fun τ : 𝓞 E →+* 𝓞 K => (RingOfIntegers.mapRingHom j).comp τ) ∘
        fun σ : E →+* K => (RingOfIntegers.mapRingHom σ : 𝓞 E →+* 𝓞 K)) =
        (fun σ : E →+* K' => (RingOfIntegers.mapRingHom σ : 𝓞 E →+* 𝓞 K')) ∘ fun σ : E →+* K => j.comp σ := by
      funext σ
      exact RingHom.ext fun a => rfl
    rw [← Function.Bijective.of_comp_iff _ (mapRingHom_bijective (E := E) (K := K)), e]
    exact mapRingHom_bijective.comp (comp_bijective_of_splits j h)

end GlobalTheory.CM
end

section

open NumberField

namespace GlobalTheory.CMGeneratorSquare

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cm_generator_sq_quadratic_eq (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    H.w0 * H.w0 = H.w0 - (((H.d + 1) / 4 : ℕ) : 𝓞 E) := by
  have hd : (H.d + 1) = 4 * ((H.d + 1) / 4) := by
    have := H.d_mod; omega
  have h1 : (4 : 𝓞 E) * (H.w0 * H.w0) = 4 * (H.w0 - (((H.d + 1) / 4 : ℕ) : 𝓞 E)) := by
    have h2 := H.two_weight_eq_one_add_root
    have h3 := H.rt_sq
    have h4 : ((H.d + 1 : ℕ) : 𝓞 E) = 4 * (((H.d + 1) / 4 : ℕ) : 𝓞 E) := by
      conv_lhs => rw [hd]
      rw [Nat.cast_mul, Nat.cast_ofNat]
    have h5 : (4 : 𝓞 E) * (H.w0 * H.w0) = (2 * H.w0) ^ 2 := by ring
    rw [h5, h2, mul_sub, ← h4]
    push_cast
    linear_combination h3 - 2 * h2
  have h4ne : (4 : 𝓞 E) ≠ 0 := by exact_mod_cast (by norm_num : (4 : ℕ) ≠ 0)
  exact mul_left_cancel₀ h4ne h1

theorem main : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {a : NumberField.RingOfIntegers E}, a ∈ GlobalTheory.CM.OK H →
    ∃ (u : ℤ) (v : ℤ), a = (↑u : NumberField.RingOfIntegers E) + (↑v : NumberField.RingOfIntegers E) *
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.w0 H := by
  intro E _ _ _ H a ha
  set k : ℤ := (((H.d + 1) / 4 : ℕ) : ℤ) with hk
  have hsq : H.w0 * H.w0 = H.w0 - (k : 𝓞 E) := by rw [cm_generator_sq_quadratic_eq H, hk, Int.cast_natCast]
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by rw [hx]; push_cast; ring⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, v, rfl⟩ := hx
    obtain ⟨u', v', rfl⟩ := hy
    exact ⟨u + u', v + v', by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, v, rfl⟩ := hx
    obtain ⟨u', v', rfl⟩ := hy
    refine ⟨u * u' - v * v' * k, u * v' + v * u' + v * v', ?_⟩
    push_cast
    linear_combination (v * v' : 𝓞 E) * hsq

end GlobalTheory.CMGeneratorSquare
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem map_rt_eq_neg_iff {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {R : Type} [CommRing R]
    [CharZero R] {ρ : R} (hρ : ρ ^ 2 = -(H.d : R)) {k : Type} [Field k] (β : R →+* k) (hβ : Function.Injective β)
    (τ : 𝓞 E →+* k) : τ H.rt = β (-ρ) ↔ τ H.rt ≠ β ρ := by
  have h1 : (τ H.rt) ^ 2 = (β ρ) ^ 2 := by
    rw [← map_pow, ← map_pow, H.rt_sq, hρ]; simp
  have h2 : β (-ρ) ≠ β ρ := by
    intro h
    have h3 : -ρ = ρ := hβ h
    have h4 : ((2 * H.d : ℕ) : R) = 0 := by
      push_cast
      linear_combination 2 * hρ + ρ * h3
    have h5 : 2 * H.d = 0 := Nat.cast_eq_zero.mp h4
    have := H.d_prime.pos
    omega
  constructor
  · intro h h'
    exact h2 (h.symm.trans h')
  · intro h
    rw [map_neg]
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp h1).resolve_left h

theorem hasType_neg_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [CharZero R] (G : Over (Sp R)) [GrpObj G] (act : OAct (𝓞 E) G) (ρ : R) (p q : ℕ), ρ ^ 2 = -(H.d : R) → (HasType H act ρ p q ↔ HasType H act (-ρ) q p) := by
  intro E _ _ _ H R _ _ G _ act ρ p q hρ
  unfold HasType
  refine forall_congr' fun k => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun β =>
    forall_congr' fun hβ => forall_congr' fun τ => ?_
  have h := map_rt_eq_neg_iff H hρ β hβ τ
  rw [ne_eq (τ H.rt) (β (-ρ)), h, not_not]
  exact and_comm

end GlobalTheory.CM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM.EllConj

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem bar_mem (H : Host E) (a : OK H) : H.bar (a : 𝓞 E) ∈ OK H := by
  obtain ⟨a, ha⟩ := a
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain rfl : x = H.w0 := hx
    rw [GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator]
    exact sub_mem (one_mem _) (wK H).2
  | algebraMap r =>
    have : H.bar (algebraMap ℤ (𝓞 E) r) = algebraMap ℤ (𝓞 E) r := by simp
    show H.bar (algebraMap ℤ (𝓞 E) r) ∈ OK H
    rw [this]
    exact Subalgebra.algebraMap_mem _ r
  | add x y hx hy h₁ h₂ => exact (map_add H.bar x y) ▸ add_mem h₁ h₂
  | mul x y hx hy h₁ h₂ => exact (map_mul H.bar x y) ▸ mul_mem h₁ h₂

def barK (H : Host E) : OK H →+* OK H where
  toFun a := ⟨H.bar (a : 𝓞 E), bar_mem H a⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

theorem barK_wK_add (H : Host E) : barK H (wK H) + wK H = 1 :=
  Subtype.ext (by
    show H.bar H.w0 + H.w0 = 1
    rw [GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, sub_add_cancel])

theorem isLieComb_one_sub {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (v : epsR R ⟶ G)
    (hv : IsTangent v) (ω : R) (f g : G ⟶ G) (hfg : g * f = 𝟙 G) (h : IsLieComb ![ω] ![v] (v ≫ f)) :
    IsLieComb ![1 - ω] ![v] (v ≫ g) := by
  have hv' : ∀ i, IsTangent (![v] i) := fun i => by fin_cases i; exact hv
  rw [GlobalTheory.LieComb.isLieComb_iff_tanExp] at h ⊢
  have e₁ : (v ≫ g) * (v ≫ f) = v := by rw [← MonObj.comp_mul, hfg, Category.comp_id]
  have e₂ := map_add (GlobalTheory.LieComb.combHom hv') ![1 - ω] ![ω]
  have e₃ : (![1 - ω] + ![ω] : Fin 1 → R) = Pi.single 0 1 := by
    funext i
    fin_cases i
    simp
  rw [e₃] at e₂
  have e₄ : v = GlobalTheory.SqZero.tanExp ![v] ![1 - ω] * GlobalTheory.SqZero.tanExp ![v] ![ω] :=
    (GlobalTheory.LieComb.tanExp_single hv' 0).symm.trans (congrArg Additive.toMul e₂)
  rw [← h] at e₄
  exact mul_right_cancel (e₁.trans e₄)


open GlobalTheory.PrimNorm in
theorem lbIso_of_adj {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {M : LB B.left} (hM : M.IsLB)
    {f g : B ⟶ B} (h : LamEq M f (𝟙 B) M (𝟙 B) g) : LBIso (cubeLB B ![𝟙 B, g] M) (cubeLB B ![𝟙 B, f] M) := by
  have h' : LBIso (cubeLB B ![fst B B ≫ f, snd B B] M) (cubeLB B ![fst B B, snd B B ≫ g] M) := by
    simpa only [LamEq, Category.comp_id] using h
  have e := diff₂_ptCls_adj hM h' (𝟙 B) (𝟙 B)
  rw [Category.id_comp, Category.id_comp, diff₂_comm] at e
  exact (lbIso_iff hM _ _ _ _).2 ((prod_square_id _ _ (cls M)).trans (e.symm.trans (prod_square_id _ _ (cls M)).symm))

theorem exists_conj_action (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R]
    (ω : R) (C : Ell H R ω) :
    ∃ a : OAct (OK H) C.P.A, (∀ x y : OK H, (y : 𝓞 E) = H.bar x → a.act x = C.act.act y) ∧
      IsLieComb ![1 - ω] ![C.v] (C.v ≫ a.act (wK H)) ∧
      (∀ x y : OK H, (y : 𝓞 E) = H.bar x → LamEq C.P.L (a.act x) (𝟙 C.P.A) C.P.L (𝟙 C.P.A) (a.act y)) ∧
      LBIso C.P.L (cubeLB C.P.A ![𝟙 C.P.A, a.act (wK H)] C.P.L) := by
  refine ⟨Serre.comapAct C.act (barK H), fun x y h => ?_, ?_, fun x y h => ?_, ?_⟩
  · exact congrArg C.act.act (Subtype.ext h.symm)
  · exact isLieComb_one_sub C.v (C.basis.1 0) ω (C.act.act (wK H)) _
      (by rw [Serre.comapAct_act, ← C.act.add, barK_wK_add, C.act.one]) C.eig
  · exact C.adj _ _ (congrArg H.bar h)
  · exact LBIso.trans C.P.isLB (DVR.linComb_isLB _ C.P.isLB _ _) (DVR.linComb_isLB _ C.P.isLB _ _) C.prim
      (lbIso_of_adj C.P.isLB (C.adj (barK H (wK H)) (wK H) (GlobalTheory.HostModel.bar_bar H _).symm))

end GlobalTheory.CM.EllConj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM.PairingIso

open GlobalTheory.KerPow

theorem exists_gen_of_lbIso {X : Scheme.{0}} {P Q : LB X} (hP : P.IsLB) (hQ : Q.IsLB) (h : LBIso P Q)
    (H : ∃ t : LB.Gen P, t.IsGen) : ∃ t : LB.Gen Q, t.IsGen := by
  obtain ⟨w, hw⟩ := h.chartPull (chartPullId P) (Geo.Tor.chartPullPull Q (𝟙 X) (𝟙 X) rfl)
  obtain ⟨t, ht⟩ := H
  obtain ⟨a, ha⟩ := gen_chartPull (Geo.Tor.chartPullPull P (𝟙 X) (𝟙 X) rfl) t ht
  obtain ⟨c, hc, -⟩ := exists_up ((isGen_iff w).1 hw) hQ hP a ha
  exact gen_chartPull (chartPullUnpull Q _ (Category.id_comp _)) c hc

theorem locGen_base {X Y B : Scheme.{0}} {L : LB X} (hL : L.IsLB) (π : Y ⟶ B) (a : B ⟶ X) {b : Y ⟶ X}
    (e : b = π ≫ a) : LocGen L π (fun _ : PUnit => b) (fun _ => 1) := by
  subst e
  intro p
  obtain ⟨i, hi⟩ := exists_chart hL (a p)
  exact ⟨a ⁻¹ᵁ L.U i, hi, ChartRig.exists_gen_pull L _ i hL fun y _ => y.2⟩

theorem eq_one_of_comp_eq_one {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]
    {L : LB A.left} {M : LB B.left} {Φ : A ⟶ B} (hL : L.IsLB) (hM : M.IsLB) (hK : Out.KTriv A L)
    (h : LamEq M Φ Φ L (𝟙 A) (𝟙 A)) {T : Over S} (x : T ⟶ A) (hx : x ≫ Φ = 1) : x = 1 := by
  have h' : LBIso (cubeLB B ![1, snd T A ≫ Φ] M) (cubeLB A ![fst T A ≫ x, snd T A] L) :=
    LBIso.chartPull
      (PrimNorm.chartSquare M (lift (fst T A ≫ x) (snd T A))
        (by rw [lift_fst_assoc, Category.assoc, hx, MonObj.comp_one]) (by rw [lift_snd_assoc]))
      (PrimNorm.chartSquare L (lift (fst T A ≫ x) (snd T A)) (by simp) (by simp)) h
  have g₁ : ∃ t : LB.Gen (cubeLB B ![1, snd T A ≫ Φ] M), t.IsGen :=
    hasGen_of_trivial hM fun U _ k => (PrimNorm.prod_square_id _ _ k).trans (by simp [PrimNorm.diff₂])
  have g₂ : HasGen L _ _ :=
    exists_gen_of_lbIso (DVR.linComb_isLB _ hM _ _) (DVR.linComb_isLB _ hL _ _) h' g₁
  have g₃ : LocGen L (fst T A).left
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum A ![fst T A ≫ x, snd T A] I.down).left)
      (fun I => (-1) ^ (2 - I.down.card)) := fun _ => ⟨⊤, trivial, g₂.pull _ fun _ => rfl⟩
  have b₁ := locGen_base hL (fst T A).left x.left (b := (fst T A ≫ x).left) rfl
  have b₀ := locGen_base hL (fst T A).left (1 : T ⟶ A).left (b := (1 : T ⊗ A ⟶ A).left)
    (congrArg (fun q : T ⊗ A ⟶ A => q.left) (MonObj.comp_one (fst T A) : fst T A ≫ (1 : T ⟶ A) = 1).symm)
  have b := b₀.comb hL b₁ (φ'' := ![(1 : T ⊗ A ⟶ A).left, (fst T A ≫ x).left]) (ε'' := ![1, -1])
    fun U _ k => by simp [Fin.prod_univ_two]
  refine eq_one_of_locGen hK x (g₃.comb hL b fun U _ k => ?_)
  rw [PrimNorm.prod_square_id, Fin.prod_univ_two, Fin.prod_univ_two]
  show k ((fst T A ≫ x) * snd T A).left * (k (fst T A ≫ x).left)⁻¹ * (k (snd T A).left)⁻¹ * k (1 : T ⊗ A ⟶ A).left *
    (k (1 : T ⊗ A ⟶ A).left ^ (1 : ℤ) * k (fst T A ≫ x).left ^ (-1 : ℤ))⁻¹ =
    k ((fst T A ≫ x) * snd T A).left ^ (1 : ℤ) * k (snd T A).left ^ (-1 : ℤ)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem isIso_of_lamEq : ∀ (S : Scheme.{0}) [IsReduced S] (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (Φ : A ⟶ B), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → IsMonHom Φ → Out.KTriv A L → LamEq M Φ Φ L (𝟙 A) (𝟙 A) → Surjective Φ.left → IsIso Φ := by
  intro S _ A B _ _ L M Φ hA hB hL hM hΦ hK h hs
  have := hA.comm
  have := hB.comm
  have := hA.proper
  have := hB.proper
  have := hB.smooth
  have : Mono Φ := ⟨fun {T} x y e => mul_inv_eq_one.1 (eq_one_of_comp_eq_one hL hM hK h (x * y⁻¹) (by
    rw [MonObj.mul_comp, GrpObj.inv_comp, e, mul_inv_cancel]))⟩
  have : Mono Φ.left := inferInstanceAs (Mono ((Over.forget S).map Φ))
  have : IsReduced B.left := GlobalTheory.isReduced_of_smooth_of_isReduced B.hom
  have : IsProper (Φ.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper Φ.left := IsProper.of_comp Φ.left B.hom
  have : IsClosedImmersion Φ.left := (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨‹_›, ‹_›⟩
  have : IsIso Φ.left := isIso_of_isClosedImmersion_of_surjective _
  have : IsIso ((Over.forget _).map Φ) := ‹_›
  exact isIso_of_reflects_iso Φ (Over.forget _)

end GlobalTheory.CM.PairingIso
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem PAT.exists_of_sabMap :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (f : S' ⟶ S) (T : PAT H S) (t' : SAB H S') (m : SABMap t' T.t f), (∃ T' : PAT H S', T'.t = t' ∧ T'.g = T.g) ∧ LBIso (T.t.PP.L.pull m.φ) t'.PP.L := by
  intro E _ _ _ H S S' f T t' m
  have e : LBIso t'.PP.L (T.t.PP.L.pull m.φ) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  obtain ⟨h₁, h₂, h₃⟩ := PolPull.pol_pull_of_relAmple_local AmpleLocal.relAmple_of_locally S S' T.t.G t'.G f m.φ
    T.t.PP.L t'.PP.L T.t.PP.isLB t'.PP.isLB T.ab m.cart e
  have hs : Out.Sym t'.G t'.PP.L := by
    obtain ⟨-, w, hw, -⟩ := t'.sym
    exact fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff w).1 hw) _⟩
  have hd : SmoothOfRelativeDimension T.g t'.G.hom :=
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} T.g
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension T.g) m.cart.1 T.dim
  exact ⟨⟨⟨t', h₁, T.g, hd, hs, h₂ T.ample, h₃ T.ktriv⟩, rfl, rfl⟩, LBIso.symm e⟩

end GlobalTheory.CM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.CM

theorem hasType_of_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (G G' : Over (Sp R)) [GrpObj G] [GrpObj G'] (a : OAct (𝓞 E) G) (a' : OAct (𝓞 E) G') (e : G ≅ G') (ρ : R) (p q : ℕ), Serre.IsLinearHom a a' e.hom → HasType H a' ρ p q → HasType H a ρ p q := by
  intro E _ _ _ H R _ G G' _ _ a a' e ρ p q he h k _ _ β hβ τ
  have := he.isMonHom
  have key : ∀ n, LieMult a (spMap β) τ n ↔ LieMult a' (spMap β) τ n := fun n => by
    have := LiePull.lieMult_pull _ _ _ G' G (𝟙 _) e.hom.left a' a (isGrpPullback_of_iso e)
      (fun c => congrArg (fun z => z.left) (he.comm c)) k (spMap β) τ n
    rwa [Category.comp_id] at this
  rw [key, key]
  exact h k β hβ τ

end GlobalTheory.CM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem kTriv_of_lamEq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L L' : LB A.left), L.IsLB → L'.IsLB → LamEq L' (𝟙 A) (𝟙 A) L (𝟙 A) (𝟙 A) → Out.KTriv A L → Out.KTriv A L' := by
  intro S A _ _ L L' hL hL' h hK R _ t x hx
  have hu : ∃ u : LB.Gen (abelian₂ A (LB.div L L')), u.IsGen := by
    simp only [LamEq, Category.comp_id] at h
    obtain ⟨w, hw⟩ := h
    exact gen_chartPull (GlobalTheory.DescendedPrincipal.chartPullDiv L L' _ _) w hw
  exact hK R t x ((GlobalTheory.UU.KTwist.inK_div_iff (x := x) hL hL' hx).1 (GlobalTheory.UU.KTwist.inK_of_lam (LB.isLB_div hL hL') hu x))

end GlobalTheory.CM
end
