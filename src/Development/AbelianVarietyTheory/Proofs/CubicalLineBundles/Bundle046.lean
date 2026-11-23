module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle041
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle036
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle037
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle030
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle039
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle022
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle034
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle040
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle052
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.HermNorm

section Form

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] (h : HermFam K V) (s : K →+* ℂ)

theorem form_sum_right {J : Type} (t : Finset J) (x : V) (c : J → K) (y : J → V) :
    h.form s x (∑ j ∈ t, c j • y j) = ∑ j ∈ t, s (c j) * h.form s x (y j) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using h.smul_right s 0 x 0
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.add_right, h.smul_right, ih]

theorem form_sum_left {J : Type} (t : Finset J) (c : J → K) (x : J → V) (y : V) :
    h.form s (∑ i ∈ t, c i • x i) y = ∑ i ∈ t, starRingEnd ℂ (s (c i)) * h.form s (x i) y := by

  rw [← h.conj_symm, form_sum_right, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, h.conj_symm]

end Form

theorem hermForm_sum_sum {g n : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a : Fin n → ℂ) (W : Fin n → Fin g → ℂ) :
    hermForm Hm (∑ i, a i • W i) (∑ i, a i • W i) =
      ∑ i, starRingEnd ℂ (a i) * ∑ j, a j * hermForm Hm (W j) (W i) := by
  simp only [hermForm, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul,
    sum_dotProduct, smul_dotProduct, smul_eq_mul, Complex.star_def]

theorem form_eq {K : Type} [Field K] {g n : ℕ} (h : HermFam K (Fin n → K)) (s : K →+* ℂ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (W : Fin n → Fin g → ℂ) (r : ℂ)
    (e : ∀ i j, h.form s (Pi.single i 1) (Pi.single j 1) = r * hermForm Hm (W j) (W i)) (c : Fin n → K) :
    h.form s c c = r * hermForm Hm (∑ i, s (c i) • W i) (∑ i, s (c i) • W i) := by
  have hc : c = ∑ i, c i • (Pi.single i 1 : Fin n → K) := pi_eq_sum_univ' c
  rw [hermForm_sum_sum, Finset.mul_sum]
  conv_lhs => rw [hc, form_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [form_sum_right, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [e]; ring

theorem isLieNormSq_form : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (h : HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (s : K →+* ℂ) u c, F.IsCoord u c → IsLieNormSq P u (s.comp (algebraMap (𝓞 K) K)) (h.form s c c).re := by
  rintro - - K _ _ P F h hh s u c ⟨-, w, hw, hc⟩
  obtain ⟨Q, ψ, v', U, Hm, χ, W, hQ, hA, hv, e⟩ := hh s
  refine (EllComp.isLieNormSq_iff F.fib hw s _).1 ?_
  obtain ⟨w', hw', -⟩ := existsUnique_isVecOver hQ.2.1.1 w
  have hc' := (lieComb_baseChange _ _ s _ _ ψ hQ.2.1 _ F.v w c v' w' (fun i => (hv i).1) hc).1 hw'
  refine ⟨Q, ψ, w', U, Hm, χ, ∑ i, s (c i) • W i, hQ, hw', hA,
    UnifDifferential.isDiff_of_isLieComb _ _ _ _ U W v' _ w'
      (fun i => (hv i).1.isTangent hQ.2.1 (F.basis.1 i)) (fun i => (hv i).2) hc', ?_⟩
  rw [form_eq h s Hm W _ e, Complex.re_ofReal_mul]

end GlobalTheory.CM.HermNorm
end
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF.LieType

theorem repr_eq_zero {k O V J : Type} [Field k] [CommRing O] [AddCommGroup V] [Module k V] [Module O V]
    [SMulCommClass O k V] (b : Module.Basis J k V) (χ : J → (O →+* k)) (hb : ∀ i a, a • b i = χ i a • b i)
    (ψ : O →+* k) (w : V) (hw : ∀ a : O, a • w = ψ a • w) (j : J) (hj : χ j ≠ ψ) : b.repr w j = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, χ j a ≠ ψ a := by
    by_contra h
    push Not at h
    exact hj (RingHom.ext h)
  have e : (b.coord j).comp (DistribSMul.toLinearMap k V a) = χ j a • b.coord j := b.ext fun i => by
    by_cases h : i = j
    · subst h
      simp [hb]
    · simp [hb, Finsupp.single_eq_of_ne' h]
  have e' := LinearMap.congr_fun e w
  simp only [LinearMap.comp_apply, DistribSMul.toLinearMap_apply, hw, map_smul, LinearMap.smul_apply, smul_eq_mul,
    Module.Basis.coord_apply] at e'
  exact (mul_eq_mul_right_iff.1 e').resolve_left ha.symm

theorem lieMult_of_eigenbasis {k O : Type} [Field k] [CommRing O] {G : Over (Sp k)} [GrpObj G] [IsCommMonObj G]
    (a : OAct O G) {n : ℕ} {v : Fin n → (epsR k ⟶ G)} (hv : IsLieBasis v) (χ : Fin n → (O →+* k))
    (hχ : Function.Injective χ) (h : ∀ x i, IsLieComb (Pi.single i (χ i x)) v (v i ≫ a.act x)) :
    (∀ i, LieMult a (𝟙 _) (χ i) 1) ∧ ∀ ψ, (∀ i, χ i ≠ ψ) → LieMult a (𝟙 _) ψ 0 := by
  let b := Serre.Lie.basis a hv
  have hb : ∀ i x, x • b i = χ i x • b i := fun i x => by
    have h1 := h x i
    obtain e : v = fun i => (b i).hom := funext fun i => (Serre.Lie.hom_basis hv i).symm
    rw [e, Serre.Lie.isLieComb_iff] at h1
    refine (Serre.Lie.ext h1 : x • b i = _).trans ?_
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp), Pi.single_eq_same]
  refine ⟨fun i => ?_, fun ψ hψ => ?_⟩
  · have e : Serre.Lie.eig a (χ i) = Submodule.span k {b i} := by
      refine le_antisymm (fun w hw => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 (hb i))
      rw [← b.sum_repr w, Finset.sum_eq_single i (fun j _ hj => by
        rw [repr_eq_zero b χ hb (χ i) w hw j (hχ.ne hj), zero_smul]) (by simp)]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    rw [Serre.Lie.lieMult_id_iff, e]
    exact ⟨Module.finBasisOfFinrankEq _ _ (finrank_span_singleton (b.ne_zero i))⟩
  · have e : Serre.Lie.eig a ψ = ⊥ := by
      refine eq_bot_iff.2 fun w hw => ?_
      rw [Submodule.mem_bot, ← b.sum_repr w]
      exact Finset.sum_eq_zero fun j _ => by rw [repr_eq_zero b χ hb ψ w hw j (hψ j), zero_smul]
    rw [Serre.Lie.lieMult_id_iff, e]
    exact ⟨Module.Basis.empty _⟩

theorem exists_label {E K k : Type} [Field E] [NumberField E] [Field K] [CharZero K] [Field k] [IsAlgClosed k]
    (j : K →+* k) (lab : (E →+* ℂ) → (E →+* K)) (hl : Function.Injective lab) (τ : 𝓞 E →+* k) :
    ∃ t, τ = j.comp ((lab t).comp (algebraMap (𝓞 E) E)) := by
  have : CharZero k := j.charZero_iff j.injective |>.1 inferInstance
  have hτ : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_under_eq_bot (R := ℤ) ?_
    change Ideal.comap (algebraMap ℤ (𝓞 E)) (RingHom.ker τ) = ⊥
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  have hi : Function.Injective fun t => j.comp (lab t) := fun t t' e =>
    hl (RingHom.ext fun x => j.injective (RingHom.congr_fun e x))
  have hs := ((Fintype.bijective_iff_injective_and_card _).2
    ⟨hi, (Embeddings.card E ℂ).trans (Embeddings.card E k).symm⟩).2
  obtain ⟨t, ht⟩ := hs (IsFractionRing.lift hτ : E →+* k)
  refine ⟨t, RingHom.ext fun a => ?_⟩
  exact ((RingHom.congr_fun ht _).trans (IsFractionRing.lift_algebraMap hτ a)).symm

theorem hasType_of_isLieType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ) (oa : A.OAct (𝓞 E)) (act : OAct (𝓞 E) A.A) (S : Set (E →+* ℂ)) (τ : Fin x.P.g ≃ S) (lab : (E →+* ℂ) → (E →+* K)) (ρ : 𝓞 K), act.act = oa.act → Function.Injective lab → (∀ t, t ∈ S ↔ lab t (H.rt : E) = (ρ : K)) → IsLieType A oa x φ τ lab → HasType H act ρ 1 0 := by
  intro E _ _ _ _ H K _ _ A x φ hf oa act S τ lab ρ hact hl hS hT k _ _ β hβ σ
  obtain ⟨act', e⟩ := ellPull_exists_oAct hf.2.1 act
  have := x.P.isAb.comm
  have := x.P.smoothDim
  have : Smooth x.P.A.hom := SmoothOfRelativeDimension.smooth x.P.g _
  let res : (E →+* ℂ) → (𝓞 E →+* K) := fun t => (lab t).comp (algebraMap (𝓞 E) E)
  have hres : Function.Injective res := fun t t' h => hl (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) h)
  obtain ⟨h1, h0⟩ := lieMult_of_eigenbasis act' x.basis (fun i => res (τ i))
    (hres.comp (Subtype.val_injective.comp τ.injective)) fun a i => by
      obtain ⟨w, hw, ew⟩ := hT a i
      obtain rfl : w = x.v i ≫ act'.act a := by
        refine Over.OverMorphism.ext (hf.2.1.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
        rw [← ew, Over.comp_left, Category.assoc, e, hact]
      exact hw
  let j : K →+* k := IsFractionRing.lift hβ
  have hj : ∀ a : 𝓞 K, j a = β a := IsFractionRing.lift_algebraMap hβ
  obtain ⟨t, rfl⟩ := exists_label j lab hl σ
  have key : ∀ n, LieMult act' (𝟙 _) (res t) n → LieMult act (spMap β) (j.comp (res t)) n := fun n h => by
    rw [← LieExt.lieMult_extend_iff j, LiePull.lieMult_pull _ _ _ _ _ _ _ act act' hf.2.1 e,
      spMap_comp_spMap] at h
    convert h using 2
    exact (RingHom.ext hj).symm
  have ht : t ∈ S ↔ j.comp (res t) H.rt = β ρ := by
    rw [hS, ← hj]
    exact j.injective.eq_iff.symm
  refine ⟨fun h => key _ ?_, fun h => key _ (h0 _ fun i hi => h (ht.1 ?_))⟩
  · simpa using h1 (τ.symm ⟨t, ht.2 h⟩)
  · rw [← hres hi]
    exact (τ i).2

end GlobalTheory.LamF.LieType
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF


theorem _root_.GlobalTheory.T.exists_dvrModel_lieBasis_at_prime : Out.SecTwistSt → ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left), IsFibreOf A x (gmap K) φ → ∀ p : HeightOneSpectrum (𝓞 K), ∃ M, IsModelAt A x φ p M := by
  first | exact @GlobalTheory.LamF.exists_isModelAt | exact GlobalTheory.LamF.exists_isModelAt | (intros; apply GlobalTheory.LamF.exists_isModelAt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM


open GlobalTheory.TensorDet GlobalTheory.Serre in
theorem lieMult_tensor_of_finrank {O O' M R k : Type} [CommRing O] [CommRing O'] [Algebra O O'] [AddCommGroup M]
    [Module O M] [Module O' M] [IsScalarTower O O' M] [Module.Finite O M] [Module.Projective O M] [CommRing R]
    [Field k] [Algebra O k] {G A : Over (Sp R)} [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A]
    (hs : Smooth G.hom) (v : epsR R ⟶ G) (hv : IsLieBasis ![v]) (a : OAct O G) (κ : O →+* R) (b₀ : OAct O' A)
    (τ : IsTensor A (comapAct b₀ (algebraMap O O')) G a M)
    (hκ : ∀ c, IsLieComb ![κ c] ![v] (v ≫ a.act c)) (hlin : ∀ (x : O') m, τ.tmul (x • m) = τ.tmul m ≫ b₀.act x)
    (β : R →+* k) (hβ : ∀ c, algebraMap O k c = β (κ c)) (χ : O' →+* k) (n : ℕ)
    (hn : Module.finrank k (EigenSplit.eigenSub (rightAction k O O' M) χ) = n) : LieMult b₀ (spMap β) χ n := by
  letI : (Over.pullback (spMap β)).Monoidal := (Over.instBraidedPullback (f := (spMap β))).toMonoidal
  letI : GrpObj ((Over.pullback (spMap β)).obj G) :=
    Functor.grpObjObj (F := Over.pullback (spMap β))
  have hG := isGrpPullback_pullback G (spMap β)
  have hA := isGrpPullback_pullback A (spMap β)
  obtain ⟨v', hv', hvv⟩ := exists_isLieBasis_baseChange R k β G ((Over.pullback (spMap β)).obj G) _ hG hs 1 ![v] hv
  have ev : ![v' 0] = v' := by
    funext i
    fin_cases i
    rfl
  have hv₁ : (v' 0).left ≫ pullback.fst G.hom (spMap β) = spMap (Chart.dualMapR β) ≫ v.left := hvv 0
  have hb : IsLieBasis ![v' 0] := ev.symm ▸ hv'
  generalize v' 0 = v₁ at hv₁ hb
  have hL := isLinearPullback_pullback (comapAct b₀ (algebraMap O O')) (spMap β)
  let b : OAct O ((Over.pullback (spMap β)).obj A) := comapAct (b₀.pullback (spMap β) A) (algebraMap O O')
  let τ₁ : IsTensor _ b _ (a.pullback (spMap β) G) M :=
    τ.baseChange (isLinearPullback_pullback a (spMap β)) ⟨hA, hL.2⟩
  have ht : ∀ m, τ₁.tmul m = (Over.pullback (spMap β)).map (τ.tmul m) := fun m => τ.pullback_tmul (spMap β) m
  obtain ⟨Φ, inj, tan, add, smul, -, eqv⟩ := SerreLie.exists_lie_tensor k _ O M _ _ b τ₁ v₁ hb (fun c => by
    have h := (lieComb_baseChange R k β G _ _ hG 1 ![v] (v ≫ a.act c) ![κ c] ![v₁]
      (v₁ ≫ (a.pullback (spMap β) G).act c) (fun j => by fin_cases j; exact hv₁) (hκ c)).1 (by
        rw [Over.comp_left, Category.assoc, (isLinearPullback_pullback a (spMap β)).2, ← Category.assoc]
        exact (congrArg (· ≫ (a.act c).left) hv₁).trans (Category.assoc _ _ _))
    convert h using 2 with i
    fin_cases i
    exact hβ c)
  have : Module.Finite k (k ⊗[O] M) := inferInstance
  have := lieMult_of_param (b₀.pullback (spMap β) A) (rightAction k O O' M) Φ inj tan add smul
    (fun x y => by
      rw [rightAction_apply, eqv]
      congr 1
      have := (b₀.pullback (spMap β) A).hom x
      refine τ₁.hom_ext fun m => ?_
      rw [IsTensor.tmul_mapLeft, ht, ht]
      exact (congrArg _ (hlin x m)).trans (Functor.map_comp _ _ _)) χ hn
  have h2 := (LiePull.lieMult_pull _ _ _ _ _ _ _ b₀ (b₀.pullback (spMap β) A) hA
    (isLinearPullback_pullback b₀ (spMap β)).2 k (𝟙 _) χ n).1 this
  rwa [Category.id_comp] at h2


open GlobalTheory.TensorDet GlobalTheory.Serre in
theorem hasType_of_isTen : Out.PolBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [CharZero R] (ω : R) (C : Ell H R ω) (D : Datum H) (h : D.La → D.La → OK H) (T : PAT H (Sp R)), Nonempty (IsTen C D h T) → HasType H T.t.act (2 * ω - 1) (D.p + D.q) 0 := by
  set_option synthInstance.maxHeartbeats 400000 in
    rintro - E _ _ _ H R _ _ ω C D h T ⟨t⟩ k _ _ β hβ χ
    have : CharZero k := β.charZero_iff hβ |>.1 inferInstance
    obtain ⟨κ, hκw, hκ⟩ := LieChar.ell_char E H R ω C
    obtain ⟨-, hgen, -, -, -, hM⟩ := OK_isDedekindDomain_and_projective E H
    obtain ⟨_, _, -⟩ := hM D.La D.fin D.proj
    let _ : Algebra (OK H) k := (β.comp κ).toAlgebra
    have := C.P.smoothDim
    have key := lieMult_tensor_of_finrank (SmoothOfRelativeDimension.smooth C.P.g C.P.A.hom) C.v C.basis C.act κ
      T.t.act t.ten hκ t.lin β (fun _ => rfl) χ
    have hw : algebraMap (OK H) (𝓞 E) (wK H) = H.w0 := rfl
    have hrt : algebraMap (OK H) (𝓞 E) (2 * wK H - 1) = H.rt := by
      rw [map_sub, map_mul, hw, map_ofNat, H.two_weight_eq_one_add_root, map_one, add_sub_cancel_left]
    have hr : β (2 * ω - 1) = algebraMap (OK H) k (2 * wK H - 1) := by
      change _ = β (κ _)
      simp only [map_sub, map_mul, map_ofNat, map_one, hκw]
    rw [hr]
    refine ⟨fun h => key _ ((finrank_eigenSub χ (RingHom.ext fun c => ?_)).trans D.rank), fun h => ?_⟩
    · have hw' : χ (algebraMap (OK H) (𝓞 E) (wK H)) = algebraMap (OK H) k (wK H) := by
        rw [← hrt] at h
        simp only [map_sub, map_mul, map_ofNat, map_one] at h
        linear_combination h / 2
      obtain ⟨m, rfl, -⟩ := hgen c
      simp only [RingHom.comp_apply, map_add (f := _), map_mul, map_intCast, hw']
    · refine key _ (Submodule.finrank_eq_zero.2 ((Submodule.eq_bot_iff _).2 fun y hy => ?_))
      have h1 := EigenSplit.mem_eigenSub.1 hy H.rt
      have h2 : rightAction k (OK H) (𝓞 E) D.La H.rt = algebraMap (OK H) k (2 * wK H - 1) • LinearMap.id := by
        ext m
        simp only [TensorProduct.AlgebraTensorModule.curry_apply,
          TensorProduct.curry_apply, LinearMap.coe_restrictScalars, rightAction_tmul, LinearMap.smul_apply,
          LinearMap.id_apply]
        rw [← hrt, algebraMap_smul, TensorProduct.tmul_smul, ← algebraMap_smul k]
      rw [h2] at h1
      have h3 : (χ H.rt - algebraMap (OK H) k (2 * wK H - 1)) • y = 0 := by
        rw [sub_smul, ← h1]; exact sub_self _
      exact (smul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 h)

end GlobalTheory.CM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

noncomputable def blockDetPoly (K : Type) [CommRing K] {B : Type} (m : B → ℕ) (b : B) :
    MvPolynomial (FrVar m) K :=
  (Matrix.of fun i k : Fin (m b) => (MvPolynomial.X ⟨b, (k, i)⟩ : MvPolynomial (FrVar m) K)).det

theorem evalFr_map_blockDetPoly {K S : Type} [CommRing K] [CommRing S] (φ : K →+* S) {B : Type}
    [Fintype B] (m : B → ℕ) (b : B) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) S) :
    evalFr (MvPolynomial.map φ (blockDetPoly K m b)) X = (X b).det := by
  unfold evalFr blockDetPoly
  rw [RingHom.map_det, RingHom.map_det]
  congr 1
  ext i k
  simp

theorem evalFr_blockDetPoly {K : Type} [CommRing K] {B : Type}
    [Fintype B] (m : B → ℕ) (b : B) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) :
    evalFr (blockDetPoly K m b) X = (X b).det := by
  have := evalFr_map_blockDetPoly (RingHom.id K) m b X
  rwa [MvPolynomial.map_id] at this

theorem exists_eq_prod_blockDetPoly_pow_mul (K : Type) [Field K] [Infinite K] (B : Type) [Fintype B]
    [DecidableEq B] (m : B → ℕ) (a : ∀ b, Fin (m b) → ℕ) (s : ℕ) :
    ∀ (n : B → ℕ), ∑ b, n b = s → ∀ (P : MvPolynomial (FrVar m) K),
      (∀ (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) (b : B) (t : Matrix (Fin (m b)) (Fin (m b)) K),
        (∀ b', (X b').det ≠ 0) → t.det ≠ 0 → t.BlockTriangular id →
        evalFr P (Function.update X b (X b * t)) = (∏ i, t i i ^ (a b i + n b)) * evalFr P X) →
      ∃ G : MvPolynomial (FrVar m) K, P = (∏ b, blockDetPoly K m b ^ n b) * G := by
  induction s with
  | zero =>
    intro n hn P _
    have h0 : ∀ b, n b = 0 := fun b =>
      (Finset.sum_eq_zero_iff.1 hn) b (Finset.mem_univ b)
    exact ⟨P, by simp [h0]⟩
  | succ s ih =>
    intro n hn P hP
    obtain ⟨b₀, -, hb₀⟩ : ∃ b ∈ (Finset.univ : Finset B), n b ≠ 0 :=
      Finset.exists_ne_zero_of_sum_ne_zero (by omega)
    obtain ⟨Q, hQ⟩ := GlobalTheory.T.det_dvd_equivariant_framePolynomial K B m P (fun b i => a b i + n b) hP b₀ (fun i => by omega)
    change P = blockDetPoly K m b₀ * Q at hQ
    set n' : B → ℕ := Function.update n b₀ (n b₀ - 1) with hn'
    have hn'0 : n' b₀ + 1 = n b₀ := by simp only [hn', Function.update_self]; omega
    have hn'1 : ∀ b, b ≠ b₀ → n' b = n b := fun b hb => by
      simp only [hn', Function.update_of_ne hb]
    have hsum : ∑ b, n' b = s := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b₀)] at hn ⊢
      have : ∑ b ∈ Finset.univ.erase b₀, n' b = ∑ b ∈ Finset.univ.erase b₀, n b :=
        Finset.sum_congr rfl fun b hb => hn'1 b (Finset.ne_of_mem_erase hb)
      omega
    have hev : ∀ X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K,
        evalFr P X = (X b₀).det * evalFr Q X := fun X => by
      rw [← evalFr_blockDetPoly m b₀ X, hQ]
      simp only [evalFr, map_mul]
    obtain ⟨G, hG⟩ := ih n' hsum Q (by
      intro X b t hX ht htri
      have h := hP X b t hX ht htri
      rw [hev, hev] at h
      by_cases hb : b = b₀
      · subst hb
        rw [Function.update_self, Matrix.det_mul] at h
        have hd : t.det = ∏ i, t i i := Matrix.det_of_upperTriangular htri
        have hp : (∏ i, t i i ^ (a b i + n b)) = t.det * ∏ i, t i i ^ (a b i + n' b) := by
          rw [hd, ← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [← hn'0]; ring
        rw [hp] at h
        apply mul_left_cancel₀ (mul_ne_zero (hX b) ht)
        rw [h]; ring
      · rw [Function.update_of_ne (Ne.symm hb)] at h
        rw [hn'1 b hb]
        apply mul_left_cancel₀ (hX b₀)
        rw [h]; ring)
    refine ⟨G, ?_⟩
    rw [hQ, hG, ← Finset.mul_prod_erase _ _ (Finset.mem_univ b₀),
      ← Finset.mul_prod_erase _ (fun b => blockDetPoly K m b ^ n b) (Finset.mem_univ b₀)]
    have : ∏ b ∈ Finset.univ.erase b₀, blockDetPoly K m b ^ n' b
        = ∏ b ∈ Finset.univ.erase b₀, blockDetPoly K m b ^ n b :=
      Finset.prod_congr rfl fun b hb => by rw [hn'1 b (Finset.ne_of_mem_erase hb)]
    rw [this, ← hn'0]; ring

theorem evalFr_eq_prod_det_pow_mul : ∀ (K : Type) [Field K] [Infinite K] (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (P : MvPolynomial (FrVar m) K) (a : ∀ b, Fin (m b) → ℕ) (N : ℕ), (∀ (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) (b : B) (t : Matrix (Fin (m b)) (Fin (m b)) K), (∀ b', (X b').det ≠ 0) → t.det ≠ 0 → t.BlockTriangular id → evalFr P (Function.update X b (X b * t)) = (∏ i, t i i ^ (a b i + N)) * evalFr P X) → ∃ G : MvPolynomial (FrVar m) K, ∀ (S : Type) [CommRing S] (φ : K →+* S) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) S), evalFr (MvPolynomial.map φ P) X = (∏ b, (X b).det) ^ N * evalFr (MvPolynomial.map φ G) X := by
  intro K _ _ B _ _ m P a N hP
  obtain ⟨G, hG⟩ := exists_eq_prod_blockDetPoly_pow_mul K B m a _ (fun _ => N) rfl P hP
  refine ⟨G, fun S _ φ X => ?_⟩
  rw [hG, ← Finset.prod_pow]
  simp only [← evalFr_map_blockDetPoly φ m _ X]
  simp only [evalFr, map_mul, map_prod, map_pow]

end GlobalTheory.LamT
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem lact_one_frame {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Ψ : Finset (E →+* ℂ)}
    (y : FD.Frame Ψ r) : FD.lact (1 : GL (Fin r) E) y = y := by
  funext τ
  simp [FD.lact, FD.mat]
  rfl

theorem exists_ortho_frBor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U → ∀ y : FrPt Xo c (CAt σ), ∃ (k : U.Comp) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), (U.X k).IsOrtho x.1 ∧ FrBor t (U.un k x) y := by
  intro E _ _ _ H Dw l Xo c σ r U hU y
  obtain ⟨-, -, h3, h4, -⟩ := hU
  obtain ⟨k, x, t, ht⟩ := h3 y
  obtain ⟨b, hb, ho⟩ := (FD.orthonormalFlagTranslate_holds r (U.X k)).1 x.1 x.2
  have hd := FD.OrthogonalFrameDomain.rmul_mem_dom (U.X k) x.2 hb
  obtain ⟨t', ht'⟩ := (h4 k k x ⟨_, hd⟩).2 ⟨1, (U.X k).Γ.one_mem, b, hb, by rw [lact_one_frame]⟩
  have hi := (frBor_calculus E H Dw l Xo c (CAt σ) (U.un k x) (U.un k ⟨_, hd⟩) y).2.2.2 t' ht'
  exact ⟨k, ⟨_, hd⟩, t * t'⁻¹, ho,
    (frBor_calculus E H Dw l Xo c (CAt σ) (U.un k ⟨_, hd⟩) (U.un k x) y).2.2.1 _ _ hi ht⟩

end GlobalTheory.LamT
end
