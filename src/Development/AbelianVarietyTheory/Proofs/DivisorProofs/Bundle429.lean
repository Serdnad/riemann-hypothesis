module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle041
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import GroundTheory.AutomorphicForms.AdelicGLn
public import GroundTheory.GlobalFields.TateThesis.AdelicChar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle002
public import GroundTheory.ProfiniteCohomology.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle370
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle046
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle036
public import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle237
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Azumaya.Defs
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.Algebra.Module.Projective
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.FinitePresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle371
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Algebra.DualNumber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle372
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle340
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

noncomputable section

open MeasureTheory Complex
open scoped Matrix Real RealInnerProductSpace InnerProductSpace

namespace GlobalTheory.RealWeil

variable {l : Type} [Fintype l]

omit [Fintype l] in
theorem continuous_pPart : Continuous (pPart : (l ⊕ l → ℝ) → EuclideanSpace ℝ l) := by
  unfold pPart
  fun_prop

omit [Fintype l] in
theorem continuous_qPart : Continuous (qPart : (l ⊕ l → ℝ) → EuclideanSpace ℝ l) := by
  unfold qPart
  fun_prop

theorem continuous_inner_rho_schwartz (φ f : Sch l) :
    Continuous fun w : l ⊕ l → ℝ => ⟪φ.toLp 2, rho w (f.toLp 2)⟫_ℂ := by
  have e : ∀ w : l ⊕ l → ℝ, ⟪φ.toLp 2, rho w (f.toLp 2)⟫_ℂ = ∫ x, starRingEnd ℂ (φ x) * rhoFun w f x := by
    intro w
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [φ.coeFn_toLp 2 volume, coeFn_rho w (f.toLp 2),
      rhoFun_congr w (f.coeFn_toLp 2 volume)] with x h1 h2 h3
    rw [h1, h2, h3]
    simp [mul_comm]
  simp only [e]
  refine continuous_of_dominated (bound := fun x => ‖φ x‖ * SchwartzMap.seminorm ℝ 0 0 f) (fun w => ?_)
    (fun w => .of_forall fun x => ?_) ((φ.integrable (μ := volume)).norm.mul_const _) (.of_forall fun x => ?_)
  · exact ((continuous_star.comp φ.continuous).mul
      ((continuous_phase w).mul (f.continuous.comp (continuous_add_const _)))).aestronglyMeasurable
  · rw [norm_mul, RCLike.norm_conj, rhoFun, norm_mul, norm_phase, one_mul]
    exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ f _) (norm_nonneg _)
  · simp only [rhoFun, phase]
    have := continuous_pPart (l := l)
    have := continuous_qPart (l := l)
    fun_prop

theorem continuous_rho_schwartz (f : Sch l) : Continuous fun w : l ⊕ l → ℝ => rho w (f.toLp 2) := by
  rw [continuous_iff_continuousAt]
  intro w₀
  set v : L2 l := f.toLp 2 with hv
  set g : L2 l := (rhoSch w₀ f).toLp 2 with hg
  have h0 : rho w₀ v = g := by
    refine Lp.ext ?_
    filter_upwards [coeFn_rho w₀ (f.toLp 2), rhoFun_congr w₀ (f.coeFn_toLp 2 volume),
      (rhoSch w₀ f).coeFn_toLp 2 volume] with x h1 h2 h3
    rw [h1, h2, h3, coe_rhoSch]
  have hsq : ∀ w, ‖rho w v - rho w₀ v‖ ^ 2 =
      2 * ‖v‖ ^ 2 - 2 * (⟪g, rho w v⟫_ℂ).re := by
    intro w
    rw [@norm_sub_sq ℂ, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, inner_re_symm, h0,
      RCLike.re_to_complex]
    ring
  have hc : Continuous fun w => ‖rho w v - rho w₀ v‖ ^ 2 := by
    simp only [hsq]
    exact continuous_const.sub (continuous_const.mul (continuous_re.comp (continuous_inner_rho_schwartz (rhoSch w₀ f) f)))
  have ht := hc.tendsto w₀
  simp only [sub_self, norm_zero] at ht
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have := (Real.continuous_sqrt.tendsto _).comp ht
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this

theorem continuous_rho_prod : Continuous fun x : L2 l × (l ⊕ l → ℝ) => rho x.2 x.1 := by
  have hd : Dense (Set.range (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure (EuclideanSpace ℝ l)))) :=
    SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  exact continuous_prod_of_dense_continuous_lipschitzWith (fun x : L2 l × (l ⊕ l → ℝ) => rho x.2 x.1) 1 hd
    (by rintro _ ⟨f, rfl⟩; exact continuous_rho_schwartz f) fun w => (rho w).lipschitz

theorem continuous_rho : ∀ (l : Type) [Fintype l] (v : L2 l), Continuous fun w : l ⊕ l → ℝ => rho w v :=
  fun l _ v => (continuous_rho_prod (l := l)).comp (f := fun w : l ⊕ l → ℝ => ((v, w) : L2 l × (l ⊕ l → ℝ)))
    (Continuous.prodMk continuous_const continuous_id)

end GlobalTheory.RealWeil
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

namespace GlobalTheory.PlaneSU.NormSwap

theorem neg_inv_ratio_norm : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (δ : F) (b : Module.Basis (Fin 2) F E), b 0 = 1 → σ (b 1) = -b 1 → b 1 * b 1 = algebraMap F E δ → ∀ f₁ f₂ : F, f₁ ≠ 0 → f₂ ≠ 0 → ∀ (R : Type) [CommRing R] [Algebra F R] (ε : R) (t : R ⊗[F] E), algebraMap R (R ⊗[F] E) ε * (t * sigR R σ t + algebraMap F (R ⊗[F] E) (f₁ / f₂)) = 0 → ∃ p q : R, ε * (algebraMap F R (-(f₂ / f₁)) - (p ^ 2 - algebraMap F R δ * q ^ 2)) = 0 := by
  intro F E _ _ _ σ δ b hb0 hb1 hsq f₁ f₂ hf₁ hf₂ R _ _ ε t hε
  let B := Algebra.TensorProduct.basis R b
  have hB : ∀ i, B i = 1 ⊗ₜ[F] b i := fun i => Algebra.TensorProduct.basis_apply b i
  have h0 : B 0 = 1 := by rw [hB, hb0]; rfl
  have h1 : B 1 * B 1 = algebraMap F R δ • B 0 := by
    rw [hB, hB, Algebra.TensorProduct.tmul_mul_tmul, hsq, hb0, Algebra.algebraMap_eq_smul_one (A := E),
      TensorProduct.tmul_smul, one_mul, algebraMap_smul]
  have hs : ∀ (r : R) (e : E), sigR R σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e := fun r e => rfl
  have key : ∀ x y : R, (x • B 0 + y • B 1) * sigR R σ (x • B 0 + y • B 1) =
      algebraMap R (R ⊗[F] E) (x ^ 2 - algebraMap F R δ * y ^ 2) := by
    intro x y
    have e : sigR R σ (x • B 0 + y • B 1) = x • B 0 - y • B 1 := by
      rw [map_add (f := _), hB, hB, TensorProduct.smul_tmul', TensorProduct.smul_tmul', hs, hs, hb1, hb0,
        map_one, TensorProduct.tmul_neg, sub_eq_add_neg]
    rw [e]
    rw [h0] at h1 ⊢
    generalize algebraMap F R δ = d at h1 ⊢
    simp only [Algebra.smul_def, mul_one, map_sub, map_mul, map_pow] at h1 ⊢
    linear_combination (-(algebraMap R (R ⊗[F] E) y) ^ 2) * h1
  have hz := B.sum_repr t
  rw [Fin.sum_univ_two] at hz
  set p₀ := B.repr t 0
  set q₀ := B.repr t 1
  rw [← hz, key, IsScalarTower.algebraMap_apply F R (R ⊗[F] E), ← map_add (f := _), ← map_mul] at hε
  have hinj : Function.Injective (algebraMap R (R ⊗[F] E)) := by
    have := Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := R) (B := E)
      (algebraMap F E).injective
    intro x y hxy
    apply this
    simpa [Algebra.TensorProduct.algebraMap_apply] using hxy
  have h : ε * (p₀ ^ 2 - algebraMap F R δ * q₀ ^ 2 + algebraMap F R (f₁ / f₂)) = 0 :=
    hinj (by rw [hε, map_zero])
  set c := algebraMap F R (f₂ / f₁)
  have hca : c * algebraMap F R (f₁ / f₂) = 1 := by
    rw [← map_mul, div_mul_div_comm, mul_comm f₂ f₁, div_self (mul_ne_zero hf₁ hf₂), map_one]
  refine ⟨c * p₀, c * q₀, ?_⟩
  rw [map_neg]
  linear_combination (-c ^ 2) * h + ε * c * hca

end GlobalTheory.PlaneSU.NormSwap
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory

namespace GlobalTheory.WhitBump

abbrev Idx (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}

abbrev Vp (E : Type) [Field E] (n : ℕ) : Type := Idx n → Cinf E

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def nu (t : Vp E n) : Matrix (Fin n) (Fin n) (Cinf E) :=
  Matrix.of fun i j => if h : i < j then t ⟨(i, j), h⟩ else if i = j then 1 else 0

def sdM {R : Type} [CommRing R] (x : Matrix (Fin n) (Fin n) R) : R :=
  ∑ i : Fin n, ∑ j : Fin n with j.val = i.val + 1, x i j

theorem superDiag_eq_sdM {R : Type} [CommRing R] (g : GL (Fin n) R) :
    GlobalTheory.Whittaker.superDiag g = sdM (g : Matrix (Fin n) (Fin n) R) := rfl

theorem nu_lower (t : Vp E n) {i j : Fin n} (h : j < i) : nu t i j = 0 := by
  simp [nu, not_lt_of_gt h, ne_of_gt h]

theorem nu_diag (t : Vp E n) (i : Fin n) : nu t i i = 1 := by
  simp [nu]

theorem det_nu (t : Vp E n) : (nu t).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [nu_diag]
  · intro i j h; exact nu_lower t h

def nuGL (t : Vp E n) : GL (Fin n) (Cinf E) :=
  Matrix.nonsingInvUnit (nu t) (by rw [det_nu]; exact isUnit_one)

@[simp] theorem nuGL_val (t : Vp E n) : (nuGL t : Matrix (Fin n) (Fin n) (Cinf E)) = nu t := rfl

theorem nuGL_mem (t : Vp E n) : nuGL t ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n) :=
  (GlobalTheory.SmGL.mem_unipB (Cinf E)).2 ⟨fun _ _ h => nu_lower t h, nu_diag t⟩

variable [_root_.NumberField.IsTotallyComplex E]

def psiInf (z : Cinf E) : ℂ := (GroundTheory.Global.adelicChar E (sInf E z) : ℂ)

def psiFin (a : Af E) : ℂ := (GroundTheory.Global.adelicChar E (sFin E a) : ℂ)

def bumpInf (f : Lie E n → ℝ) (x : Lie E n) : ℂ :=
  ∫ t : Vp E n, (f (toL (nu t * Matrix.of x)) : ℂ) * psiInf (-sdM (nu t))


open Classical in
def bumpFin (g : GL (Fin n) (Af E)) : ℂ :=
  if h : ∃ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n then
    psiFin (GlobalTheory.Whittaker.superDiag h.choose) else 0

end GlobalTheory.WhitBump
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.homogeneousCochains_homology_addEquiv_alt : ∀ (k : Type) [CommRing k] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : Rep.{0} k G) [GroundTheory.ProfCoh.IsDiscreteRep M] (C : CosimplicialObject AddCommGrpCat.{1}) (e : ∀ m : ℕ, C.obj (SimplexCategory.mk m) →+ ((Fin (m + 1) → G) → M)), (∀ m, Function.Injective (e m)) → (∀ m (φ : (Fin (m + 1) → G) → M), (∃ c, e m c = φ) ↔ IsLocallyConstant φ ∧ ∀ (τ : G) (σ : Fin (m + 1) → G), φ (fun i ↦ τ * σ i) = M.ρ τ (φ σ)) → (∀ m (i : Fin (m + 2)) (c : C.obj (SimplexCategory.mk m)) (σ : Fin (m + 2) → G), e (m + 1) (C.δ i c) σ = e m c (σ ∘ i.succAbove)) → ∀ n : ℕ, Nonempty (((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj C).homology n ≃+ GroundTheory.ProfCoh.cohomology M n) := by
  first | exact @GlobalTheory.homogeneousCochains_homology_addEquiv | exact GlobalTheory.homogeneousCochains_homology_addEquiv | (intros; apply GlobalTheory.homogeneousCochains_homology_addEquiv <;> assumption)
end

section

open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.SepRing




theorem isDomain_tensor_of_reg (k K S : Type) [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsPurelyInseparable k K] [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] [Algebra k S]
    (hreg : ∀ (𝔫 : Ideal (S ⊗[k] K)) [𝔫.IsPrime], IsRegularLocalRing (Localization.AtPrime 𝔫)) :
    IsDomain (K ⊗[k] AdicCompletion (maximalIdeal S) S) := by
  have hinj : Function.Injective (algebraMap S (S ⊗[k] K)) :=
    Algebra.TensorProduct.includeLeft_injective (R := k) (S := k) (A := S) (B := K)
      (algebraMap k K).injective
  have hker : RingHom.ker (algebraMap S (S ⊗[k] K)) ≤ maximalIdeal S := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [hinj (hx.trans (map_zero _).symm)]
    exact zero_mem _
  obtain ⟨𝔫, h𝔫max, h𝔫⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := S ⊗[k] K)
    (maximalIdeal S) hker
  haveI := h𝔫max.isPrime
  obtain ⟨S', _, e, -⟩ := GlobalTheory.CompletionFactor.exists_ringEquiv_completion_prod S (S ⊗[k] K)
    (Localization.AtPrime 𝔫) 𝔫 h𝔫
  haveI : IsRegularLocalRing (Localization.AtPrime 𝔫) := hreg 𝔫
  haveI : IsRegularLocalRing (AdicCompletion (maximalIdeal (Localization.AtPrime 𝔫))
      (Localization.AtPrime 𝔫)) := GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion _
  haveI hdom : IsDomain (AdicCompletion (maximalIdeal (Localization.AtPrime 𝔫))
      (Localization.AtPrime 𝔫)) := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain _
  let f : K ⊗[k] AdicCompletion (maximalIdeal S) S ≃+* _ :=
    (Algebra.TensorProduct.comm k K (AdicCompletion (maximalIdeal S) S)).toRingEquiv.trans
    ((Algebra.TensorProduct.cancelBaseChange k S (AdicCompletion (maximalIdeal S) S)
      (AdicCompletion (maximalIdeal S) S) K).symm.toRingEquiv.trans e)
  have hS' : Subsingleton S' := by
    have hid : IsIdempotentElem (f.symm (0, 1)) := by
      show f.symm (0,1) * f.symm (0,1) = f.symm (0,1)
      rw [← map_mul]; simp
    rcases GlobalTheory.T.idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable' k K (AdicCompletion (maximalIdeal S) S) (f.symm (0, 1)) hid with h | h
    · have h2 := congrArg (fun z => (f z).2) h
      simp at h2
      exact subsingleton_of_zero_eq_one h2.symm
    · have h2 := congrArg (fun z => (f z).1) h
      simp at h2
  exact Function.Injective.isDomain ((RingHom.fst _ _).comp f.toRingHom) (by
    intro x y hxy
    apply f.injective
    exact Prod.ext hxy (Subsingleton.elim _ _))

end GlobalTheory.SepRing

namespace GlobalTheory.SepRing




theorem exists_complete_local_geomDomain : ∀ (k k' : Type) [Field k] [CommRing k'] [IsDomain k']
    [Algebra k k'], Module.Finite k k' → ∃ (C : Type) (_ : CommRing C) (_ : IsLocalRing C)
    (_ : IsNoetherianRing C) (_ : Algebra k C), IsAdicComplete (maximalIdeal C) C ∧
    Nonempty (k' →ₐ[k] ResidueField C) ∧ ∀ (K : Type) [Field K] [Algebra k K],
    FiniteDimensional k K → IsPurelyInseparable k K → IsDomain (K ⊗[k] C) := by
  intro k k' _ _ _ _ hfin
  haveI : Algebra.FiniteType k k' := inferInstance
  obtain ⟨r, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp this
  have hk' : IsField k' :=
    (Algebra.IsIntegral.isField_iff_isField (algebraMap k k').injective).mp (Field.toIsField k)
  letI : Field k' := hk'.toField
  let 𝔪 : Ideal (MvPolynomial (Fin r) k) := RingHom.ker φ.toRingHom
  haveI h𝔪 : 𝔪.IsMaximal := RingHom.ker_isMaximal_of_surjective φ.toRingHom hφ
  let S := Localization.AtPrime 𝔪
  haveI : IsNoetherianRing S := IsLocalization.isNoetherianRing 𝔪.primeCompl S inferInstance
  refine ⟨AdicCompletion (maximalIdeal S) S, inferInstance, inferInstance,
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion S _, inferInstance, inferInstance, ?_, ?_⟩
  · let C := AdicCompletion (maximalIdeal S) S
    let g : MvPolynomial (Fin r) k →ₐ[k] ResidueField C :=
      IsScalarTower.toAlgHom k (MvPolynomial (Fin r) k) (ResidueField C)
    have hg : ∀ a ∈ 𝔪, g a = 0 := by
      intro a ha
      have h1 : algebraMap (MvPolynomial (Fin r) k) S a ∈ maximalIdeal S := by
        rw [← Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.mem_map_of_mem _ ha
      have h2 : algebraMap S C (algebraMap _ S a) ∈ maximalIdeal C := by
        rw [AdicCompletion.maximalIdeal_eq_map]; exact Ideal.mem_map_of_mem _ h1
      show algebraMap _ (ResidueField C) a = 0
      rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin r) k) C (ResidueField C),
        IsScalarTower.algebraMap_apply (MvPolynomial (Fin r) k) S C]
      exact (residue_eq_zero_iff _).mpr h2
    exact ⟨(Ideal.Quotient.liftₐ 𝔪 g hg).comp
      (Ideal.quotientKerAlgEquivOfSurjective hφ).symm.toAlgHom⟩
  · intro K _ _ hK hpi
    exact isDomain_tensor_of_reg k K S (fun 𝔫 _ => GlobalTheory.T.isRegularLocalRing_localization_atPrime_tensor_field k K r 𝔪 𝔫)

end GlobalTheory.SepRing
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.span_eq_top_of_stable_of_isFractionRing' : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k K] [Algebra F K] [FiniteDimensional F K] (B : Subalgebra k K) [IsFractionRing B K] (W : Type) [AddCommGroup W] [Module K W] [Module F W] [IsScalarTower F K W] (S : Set W), (∀ c ∈ B, ∀ w ∈ S, (c : K) • w ∈ S) → Submodule.span K S = ⊤ → Submodule.span F S = ⊤ := by
  first | (exact @GlobalTheory.span_eq_top_of_stable_of_isFractionRing) | (exact GlobalTheory.span_eq_top_of_stable_of_isFractionRing) | (intros; apply GlobalTheory.span_eq_top_of_stable_of_isFractionRing  <;> assumption)
end

section


theorem _root_.GlobalTheory.T.azumaya_free_rank_sq_equiv_matrix_over_local : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [IsLocalRing A] [Algebra ℤ_[ℓ] A]
    [Module.Finite ℤ_[ℓ] A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ]
    (n : ℕ), Module.finrank A Λ = n ^ 2 → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  first | (exact @GlobalTheory.AzumayaLocal.azumaya_local_matrix) | (exact GlobalTheory.AzumayaLocal.azumaya_local_matrix) | (intros; apply GlobalTheory.AzumayaLocal.azumaya_local_matrix  <;> assumption)
end

section


theorem _root_.GlobalTheory.T.azumaya_matrix_of_finite_padic_algebra_of_local : (∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [IsLocalRing A] [Algebra ℤ_[ℓ] A]
    [Module.Finite ℤ_[ℓ] A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ]
    (n : ℕ), Module.finrank A Λ = n ^ 2 → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A)) →
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A]
    [Module.Finite ℤ_[ℓ] A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ]
    (n : ℕ), Module.finrank A Λ = n ^ 2 → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  first | (exact @GlobalTheory.AzumayaMatrixReduction.of_local) | (exact GlobalTheory.AzumayaMatrixReduction.of_local) | (intros; apply GlobalTheory.AzumayaMatrixReduction.of_local <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.FilteredElements

theorem preservesFilteredColimits_modules_iff_elements :
    ∀ (Λ : Type 1) [Ring Λ] (N : CommRingCat.{0} ⥤ ModuleCat.{1} Λ), (PreservesFilteredColimitsOfSize.{0, 0} N ↔ PreservesFilteredColimitsOfSize.{0, 0} (N ⋙ forget₂ (ModuleCat.{1} Λ) AddCommGrpCat.{1})) ∧ (PreservesFilteredColimitsOfSize.{0, 0} N ↔ ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → (∀ x : N.obj c.pt, ∃ j y, (N.map (c.ι.app j)).hom y = x) ∧ ∀ j (y : N.obj (D.obj j)), (N.map (c.ι.app j)).hom y = 0 → ∃ (k : J) (f : j ⟶ k), (N.map (D.map f)).hom y = 0) := by
  intro Λ _ N
  have hP : PreservesColimitsOfSize.{0, 0} (forget₂ (ModuleCat.{1} Λ) AddCommGrpCat.{1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{1, 1, 0, 0} Λ
  have h1 : PreservesFilteredColimitsOfSize.{0, 0} N ↔ PreservesFilteredColimitsOfSize.{0, 0} (N ⋙ forget₂ (ModuleCat.{1} Λ) AddCommGrpCat.{1}) := by
    constructor
    · intro h
      exact comp_preservesFilteredColimits N (forget₂ (ModuleCat.{1} Λ) AddCommGrpCat.{1})
    · intro h
      constructor
      intro J _ _
      have hR : ReflectsColimitsOfShape J (forget₂ (ModuleCat.{1} Λ) AddCommGrpCat.{1}) :=
        ModuleCat.reflectsColimitsOfShape.{1, 1, 0, 0} Λ J
      constructor
      intro K
      exact preservesColimit_of_reflects_of_preserves N (forget₂ (ModuleCat.{1} Λ) AddCommGrpCat.{1})
  refine ⟨h1, ?_⟩
  rw [h1, GlobalTheory.T.preservesFilteredColimits_addCommGrp_iff_elements]
  rfl

end GlobalTheory.EtC.FilteredElements
end

section

open CategoryTheory Limits TensorProduct

theorem _root_.GlobalTheory.T.projective_eventually_filteredColimit_algebra : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A],
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Module.Finite c.pt (c.pt ⊗[F.obj j] A) ∧ Module.Projective c.pt (c.pt ⊗[F.obj j] A)) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      Module.Projective (F.obj k) (F.obj k ⊗[F.obj j] A) := by
  first | (exact @GlobalTheory.ProjColim.projective_eventually) | (exact GlobalTheory.ProjColim.projective_eventually) | (intros; apply GlobalTheory.ProjColim.projective_eventually  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_preservesFilteredColimits_iso_on_finiteType : ∀ (𝒜 : Type 2) [Category.{1} 𝒜] [HasColimitsOfSize.{1, 1} 𝒜] (M : CommRingCat.{0} ⥤ 𝒜), ∃ (N : CommRingCat.{0} ⥤ 𝒜) (ε : N ⟶ M), PreservesFilteredColimitsOfSize.{0, 0} N ∧ ∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A) := by
  first
  | exact @GlobalTheory.FinExt.exists_preservesFilteredColimits_isIso
  | exact GlobalTheory.FinExt.exists_preservesFilteredColimits_isIso
  | (intros; apply GlobalTheory.FinExt.exists_preservesFilteredColimits_isIso <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_of_universal_firstOrder_tangent : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (s : X ⟶ Sp B) (d : ℕ), Smooth s → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), ∃ u : Sp (TrivSqZeroExt k (Fin d → k)) ⟶ X, spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ u = x ∧ u ≫ s = spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ x ≫ s ∧ ∀ v : Sp (DualNumber k) ⟶ X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = x → v ≫ s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ s → ∃! c : (Fin d → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u) → SmoothOfRelativeDimension d s := by
  first | exact @GlobalTheory.SmoothDimTangent.smoothOfRelativeDimension_of_universal_tangent | exact GlobalTheory.SmoothDimTangent.smoothOfRelativeDimension_of_universal_tangent | (intros; apply GlobalTheory.SmoothDimTangent.smoothOfRelativeDimension_of_universal_tangent <;> assumption)
end
