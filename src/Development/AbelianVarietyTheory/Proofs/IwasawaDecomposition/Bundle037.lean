module

public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemBasicOpenOfMemClosure
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle028
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerOfNormEq
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle031
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

noncomputable section

namespace GlobalTheory.UpqExpChart

section General

variable {n : Type} [Fintype n] [DecidableEq n]

theorem continuous_matExp : Continuous (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ) := by
  open scoped Matrix.Norms.Operator in
  exact NormedSpace.exp_continuous

theorem exists_chart : ∃ e : OpenPartialHomeomorph (Matrix n n ℂ) (Matrix n n ℂ),
    (e : Matrix n n ℂ → Matrix n n ℂ) = NormedSpace.exp ∧ (0 : Matrix n n ℂ) ∈ e.source := by
  open scoped Matrix.Norms.Operator in
  have h : HasStrictFDerivAt (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ)
      ((ContinuousLinearEquiv.refl ℂ (Matrix n n ℂ) : Matrix n n ℂ ≃L[ℂ] Matrix n n ℂ) :
        Matrix n n ℂ →L[ℂ] Matrix n n ℂ) 0 :=
    hasStrictFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := Matrix n n ℂ)
  open scoped Matrix.Norms.Operator in
  exact ⟨h.toOpenPartialHomeomorph _, rfl, h.mem_toOpenPartialHomeomorph_source⟩

theorem exp_mul_exp_neg (X : Matrix n n ℂ) : NormedSpace.exp X * NormedSpace.exp (-X) = 1 := by
  rw [← Matrix.exp_add_of_commute X (-X) (Commute.refl X).neg_right, add_neg_cancel,
    NormedSpace.exp_zero]

theorem exp_neg_mul_exp (X : Matrix n n ℂ) : NormedSpace.exp (-X) * NormedSpace.exp X = 1 := by
  simpa using exp_mul_exp_neg (-X)

theorem exp_conj_invol {J : Matrix n n ℂ} (hJ : J * J = 1) (X : Matrix n n ℂ) :
    NormedSpace.exp (J * X * J) = J * NormedSpace.exp X * J :=
  Matrix.exp_units_conj (⟨J, J, hJ, hJ⟩ : (Matrix n n ℂ)ˣ) X

theorem exp_unitary {J : Matrix n n ℂ} (hJ : J * J = 1) {X : Matrix n n ℂ}
    (hX : Xᴴ * J + J * X = 0) : (NormedSpace.exp X)ᴴ * J * NormedSpace.exp X = J := by
  have h1 : Xᴴ = J * (-X) * J := by
    have : Xᴴ * J = J * (-X) := by rw [Matrix.mul_neg]; exact eq_neg_of_add_eq_zero_left hX
    rw [← this, Matrix.mul_assoc, hJ, Matrix.mul_one]
  rw [← Matrix.exp_conjTranspose, h1, exp_conj_invol hJ, Matrix.mul_assoc _ J J, hJ,
    Matrix.mul_one, Matrix.mul_assoc, exp_neg_mul_exp, Matrix.mul_one]

theorem exp_twist {J : Matrix n n ℂ} (hJ : J * J = 1) {Z : Matrix n n ℂ}
    (hZ : (NormedSpace.exp Z)ᴴ * J * NormedSpace.exp Z = J) :
    NormedSpace.exp (J * (-Z)ᴴ * J) = NormedSpace.exp Z := by
  rw [exp_conj_invol hJ, Matrix.exp_conjTranspose]
  have h1 : (NormedSpace.exp (-Z))ᴴ * (NormedSpace.exp Z)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, exp_mul_exp_neg, Matrix.conjTranspose_one]
  have h2 : (NormedSpace.exp (-Z))ᴴ * J = J * NormedSpace.exp Z := by
    calc (NormedSpace.exp (-Z))ᴴ * J
        = (NormedSpace.exp (-Z))ᴴ * ((NormedSpace.exp Z)ᴴ * J * NormedSpace.exp Z) := by rw [hZ]
      _ = J * NormedSpace.exp Z := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc, hJ, Matrix.one_mul]

end General

theorem jpq_sq (P Q : ℕ) : Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem mat_unitary {P Q : ℕ} (g : UpqT P Q) :
    (UpqT.mat g)ᴴ * Formalism.UG.Jpq P Q * UpqT.mat g = Formalism.UG.Jpq P Q := g.2

theorem continuous_mat {P Q : ℕ} : Continuous (UpqT.mat : UpqT P Q → _) :=
  Units.continuous_val.comp continuous_subtype_val

end GlobalTheory.UpqExpChart
end
end

section

namespace GlobalTheory.InjectiveSeqNormOne

theorem exists_injective_seq_norm_one {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) :
    ∃ a : ℕ → E, Function.Injective a ∧ ∀ k : ℕ, a k * σ (a k) = 1 := by
  obtain ⟨-, hE, -, hσ⟩ := h
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom
  have hinv : ∀ x, σ (σ x) = x := fun x => τ.injective (by rw [hσ, hσ, star_star])
  have hy : ∃ y, σ y ≠ y := by
    by_contra hcon
    push Not at hcon
    have hc : (NumberField.InfinitePlace.mk τ).IsComplex := hE.isComplex _
    rw [NumberField.InfinitePlace.isComplex_mk_iff] at hc
    apply hc
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have := hσ τ x
    rw [hcon] at this
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    exact this.symm
  obtain ⟨y, hy⟩ := hy
  have h1 : ∀ k : ℕ, (k : E) + y ≠ 0 := by
    intro k hk
    apply hy
    have : y = -(k : E) := by linear_combination hk
    rw [this, map_neg, map_natCast]
  have h2 : ∀ k : ℕ, (k : E) + σ y ≠ 0 := by
    intro k hk
    apply h1 k
    have := congrArg σ hk
    rwa [map_add, map_natCast, hinv, map_zero] at this
  refine ⟨fun k => ((k : E) + y) / ((k : E) + σ y), ?_, ?_⟩
  · intro k m hkm
    have hkm' := (div_eq_div_iff (h2 k) (h2 m)).1 hkm
    have h3 : ((k : E) - m) * (σ y - y) = 0 := by linear_combination hkm'
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact_mod_cast sub_eq_zero.1 h4
    · exact absurd (sub_eq_zero.1 h4) hy
  · intro k
    have a1 := h1 k
    have a2 := h2 k
    simp only [map_div₀, map_add (f := _), map_natCast, hinv]
    field_simp

end GlobalTheory.InjectiveSeqNormOne
end

section

noncomputable section

namespace GlobalTheory.GaugeEx.OrbitQuadric

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal Matrix

section Form

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem hform_eq_dot {A : Type} [CommRing A] (s : A →+* A) (G : Matrix (Fin M) (Fin M) A)
    (x y : Fin M → A) : Formalism.UG.hform s G x y = (fun i => s (x i)) ⬝ᵥ G *ᵥ y := by
  unfold Formalism.UG.hform
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

private theorem hform_mulVec_mulVec_of_cT_mul_mul_eq {A : Type} [CommRing A] (s : A →+* A)
    (G g : Matrix (Fin M) (Fin M) A) (hg : Formalism.UG.cT s g * G * g = G) (x y : Fin M → A) :
    Formalism.UG.hform s G (g *ᵥ x) (g *ᵥ y) = Formalism.UG.hform s G x y := by
  have hc : Formalism.UG.cT s g = (g.map s)ᵀ := by
    unfold Formalism.UG.cT
    first
      | rfl
      | (ext i j; simp)
  rw [hc] at hg
  have hs : (fun i => s ((g *ᵥ x) i)) = (g.map s) *ᵥ (fun i => s (x i)) := by
    funext i
    exact RingHom.map_mulVec s g x i
  rw [hform_eq_dot, hform_eq_dot, hs, Matrix.mulVec_mulVec,
    ← Matrix.vecMul_transpose (g.map s) (fun i => s (x i)),
    ← Matrix.dotProduct_mulVec (fun i => s (x i)) (g.map s)ᵀ ((G * g) *ᵥ y),
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hg]

theorem hR_act (k : HA R σ J) (x y : Fin M → R ⊗[F] E) :
    hR R σ J ((HA.mat R σ J k).1 *ᵥ x) ((HA.mat R σ J k).1 *ᵥ y) = hR R σ J x y := by
  have hk : HA.mat R σ J k ∈ HR R σ J := (k : HR R σ J).2
  unfold HR Formalism.UG.UJ at hk
  have hk' : Formalism.UG.cT (sigR R σ) (HA.mat R σ J k).1 * JR R J * (HA.mat R σ J k).1 = JR R J := hk
  unfold hR
  exact hform_mulVec_mulVec_of_cT_mul_mul_eq (sigR R σ) (JR R J) _ hk' x y

theorem hR_rat (x z : Fin M → E) :
    hR R σ J (fun i => inclR R (x i)) (fun i => inclR R (z i)) = (1 : R) ⊗ₜ[F] hE σ J x z := by
  unfold hR hE JR
  rw [hform_eq_dot, hform_eq_dot]
  show _ = inclR R _
  rw [RingHom.map_dotProduct]
  congr 1
  all_goals funext i
  all_goals first
    | exact (RingHom.map_mulVec (inclR R) J z i).symm
    | simp [sigR, inclR]

end Form

theorem qR_orbit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (a : F), hE σ J (x 0) (x 0) = algebraMap F E a → ∀ g : HA R σ J, qR R σ J ((g • ratTup (F := F) R x) 0) = algebraMap F R a := by
  intro F E _ _ _ _ _ σ hcm R _ _ M J x a hx g
  have hfin : FiniteDimensional F E :=
    Module.finite_of_finrank_pos (by rw [hcm.2.2.1]; norm_num)
  have hact : (g • ratTup (F := F) R x) 0 = (HA.mat R σ J g).1 *ᵥ (fun i => inclR R (x 0 i)) := rfl
  rw [hact]
  unfold qR
  rw [hR_act R σ J g, hR_rat R σ J (x 0) (x 0), hx]
  have h2 : (1 : R) ⊗ₜ[F] algebraMap F E a = algebraMap R (R ⊗[F] E) (algebraMap F R a) := by
    rw [← IsScalarTower.algebraMap_apply F R (R ⊗[F] E)]
    exact (Algebra.TensorProduct.includeRight (R := F) (A := R) (B := E)).commutes a
  rw [h2, Algebra.trace_algebraMap_of_basis
    (Algebra.TensorProduct.basis R (Module.finBasis F E)) (algebraMap F R a),
    Fintype.card_fin, hcm.2.2.1, nsmul_eq_mul, ← mul_assoc]
  have h3 : algebraMap F R (1 / 2) * ((2 : ℕ) : R) = 1 := by
    rw [← map_natCast (algebraMap F R) 2, ← map_mul]
    norm_num
  rw [h3, one_mul]

end GlobalTheory.GaugeEx.OrbitQuadric
end
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ChowLemma

theorem exists_dominant_lift {X X' : Scheme.{0}} (π : X' ⟶ X) {U W : X.Opens} (h : U ≤ W)
    (t : U.toScheme ⟶ X') [IsDominant t] (ht : t ≫ π = U.ι) :
    ∃ σ : U.toScheme ⟶ (π ⁻¹ᵁ W).toScheme, IsDominant σ ∧ σ ≫ (π ⁻¹ᵁ W).ι = t ∧
      σ ≫ π ∣_ W = X.homOfLE h := by
  have hr : Set.range t ⊆ Set.range (π ⁻¹ᵁ W).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change π (t x) ∈ W
    rw [← Scheme.Hom.comp_apply, ht]
    exact h x.2
  have e := IsOpenImmersion.lift_fac (π ⁻¹ᵁ W).ι t hr
  refine ⟨IsOpenImmersion.lift (π ⁻¹ᵁ W).ι t hr, ?_, e, ?_⟩
  · have : IsDominant (IsOpenImmersion.lift (π ⁻¹ᵁ W).ι t hr ≫ (π ⁻¹ᵁ W).ι) := by
      rwa [e]
    exact IsDominant.of_comp_of_isOpenImmersion _ (π ⁻¹ᵁ W).ι
  · rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, reassoc_of% e, ht, X.homOfLE_ι]

theorem exists_isProjOver_isIso_morphismRestrict : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp R) [IsProper f], ∃ (X' : Scheme.{0}) (π : X' ⟶ X) (U : X.Opens), IsProjOver (π ≫ f) ∧ (U : Set X).Nonempty ∧ IsIso (π ∣_ U) := by
  first
  | exact @_root_.GlobalTheory.BasicOpenLocalExtension.chow_integral
  | exact _root_.GlobalTheory.BasicOpenLocalExtension.chow_integral
  | (apply _root_.GlobalTheory.BasicOpenLocalExtension.chow_integral <;> assumption)
  | (intros; apply _root_.GlobalTheory.BasicOpenLocalExtension.chow_integral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.BasicOpenLocalExtension.chow_integral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.BasicOpenLocalExtension.chow_integral ..)

end GlobalTheory.ChowLemma
end

section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory

theorem contDiff_prod_ofFn_coord {A : Type} [NormedRing A] [NormedAlgebra ℝ A] {ι : Type}
    (R : ι → ℝ → A) (hR : ∀ i, ContDiff ℝ ∞ (R i)) (k : ℕ) (I : Fin k → ι) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => (List.ofFn fun a => R (I a) (t a)).prod := by
  induction k with
  | zero => simpa using contDiff_const
  | succ k ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    refine ContDiff.mul ((hR (I 0)).comp (contDiff_apply ℝ (fun _ => ℝ) 0)) ?_
    have h : ContDiff ℝ ∞ fun (t : Fin (k + 1) → ℝ) (a : Fin k) => t a.succ :=
      contDiff_pi.2 fun a => contDiff_apply ℝ (fun _ => ℝ) a.succ
    exact (ih fun a => I a.succ).comp h

theorem smooth_of_finiteDimensional_translation_stable :
    ∀ (G : Type) [Group G] (M : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ M] (ι : Type) (c : ι → ℝ → G), (∀ i s t, c i (s + t) = c i s * c i t) → (∀ i t, ∀ f ∈ M, (fun g => f (g * c i t)) ∈ M) → (∀ i, ∀ f ∈ M, ∀ g, Continuous fun t : ℝ => f (g * c i t)) → (∀ i, ∀ f ∈ M, (fun g => deriv (fun t : ℝ => f (g * c i t)) 0) ∈ M) ∧ ∀ (k : ℕ) (I : Fin k → ι), ∀ f ∈ M, ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun a => c (I a) (t a)).prod) := by
  intro G _ M _ ι c hc hM hcont
  let V := Fin (Module.finrank ℂ M) → ℂ
  let Φ : M ≃L[ℂ] V := (Module.finBasis ℂ M).equivFun.toContinuousLinearEquiv
  let ρ : ι → ℝ → (M →ₗ[ℂ] M) := fun i t =>
    { toFun := fun f => ⟨fun g => f.1 (g * c i t), hM i t f.1 f.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let R : ι → ℝ → (V →L[ℂ] V) := fun i t =>
    LinearMap.toContinuousLinearMap (Φ.toLinearEquiv.toLinearMap ∘ₗ ρ i t ∘ₗ Φ.symm.toLinearEquiv.toLinearMap)
  have hRapp : ∀ i t v, R i t v = Φ (ρ i t (Φ.symm v)) := fun _ _ _ => rfl
  let ev : G → (V →L[ℂ] ℂ) := fun g =>
    LinearMap.toContinuousLinearMap ((LinearMap.proj g : (G → ℂ) →ₗ[ℂ] ℂ) ∘ₗ M.subtype ∘ₗ Φ.symm.toLinearEquiv.toLinearMap)
  have hev : ∀ g v, ev g v = (Φ.symm v).1 g := fun _ _ => rfl
  have hkey : ∀ g i t v, ev g (R i t v) = ev (g * c i t) v := by
    intro g i t v
    rw [hev, hRapp, Φ.symm_apply_apply]
    rfl
  have hsep : ∀ v w : V, (∀ g, ev g v = ev g w) → v = w := by
    intro v w h
    apply Φ.symm.injective
    exact Subtype.ext (funext h)
  have hc0 : ∀ i, c i 0 = 1 := by
    intro i
    have := hc i 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hR : ∀ i, ContDiff ℝ ∞ (R i) := by
    intro i
    refine GlobalTheory.T.contDiff_of_continuous_oneParameter_hom _ (R i) ?_ ?_ ?_
    · refine continuous_clm_apply.2 fun v => ?_
      simp only [hRapp]
      refine Φ.continuous.comp ?_
      exact Continuous.subtype_mk (continuous_pi fun g => hcont i _ (Φ.symm v).2 g) _
    · refine ContinuousLinearMap.ext fun v => hsep _ _ fun g => ?_
      rw [hkey, hc0, mul_one]; rfl
    · intro s t
      refine ContinuousLinearMap.ext fun v => hsep _ _ fun g => ?_
      rw [ContinuousLinearMap.mul_apply, hkey, hkey, hkey, hc, mul_assoc]
  have hf : ∀ f (hf : f ∈ M) g, f g = ev g (Φ ⟨f, hf⟩) := by
    intro f hf g
    rw [hev, Φ.symm_apply_apply]
  refine ⟨fun i f hfM => ?_, fun k I f hfM g => ?_⟩
  · have hd : HasDerivAt (R i) (deriv (R i) 0) 0 :=
      ((hR i).differentiable (by simp) 0).hasDerivAt
    have : (fun g => deriv (fun t : ℝ => f (g * c i t)) 0)
        = (Φ.symm (deriv (R i) 0 (Φ ⟨f, hfM⟩))).1 := by
      funext g
      rw [← hev]
      have h1 : (fun t : ℝ => f (g * c i t)) = fun t => ev g (R i t (Φ ⟨f, hfM⟩)) := by
        funext t
        rw [hkey, ← hf]
      rw [h1]
      let L : (V →L[ℂ] V) →L[ℂ] ℂ := (ev g).comp (ContinuousLinearMap.apply ℂ V (Φ ⟨f, hfM⟩))
      exact ((L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd).deriv
    rw [this]
    exact Subtype.property _
  · have hprod : ∀ (k : ℕ) (I : Fin k → ι) (t : Fin k → ℝ) (g : G) (v : V),
        ev g ((List.ofFn fun a => R (I a) (t a)).prod v)
          = ev (g * (List.ofFn fun a => c (I a) (t a)).prod) v := by
      intro k
      induction k with
      | zero => intro I t g v; simp
      | succ k ih =>
        intro I t g v
        simp only [List.ofFn_succ, List.prod_cons]
        rw [ContinuousLinearMap.mul_apply, hkey, ih (fun a => I a.succ) (fun a => t a.succ),
          mul_assoc]
    have h1 : (fun t : Fin k → ℝ => f (g * (List.ofFn fun a => c (I a) (t a)).prod))
        = fun t => ev g ((List.ofFn fun a => R (I a) (t a)).prod (Φ ⟨f, hfM⟩)) := by
      funext t
      rw [hprod, ← hf]
    rw [h1]
    let L : (V →L[ℂ] V) →L[ℂ] ℂ := (ev g).comp (ContinuousLinearMap.apply ℂ V (Φ ⟨f, hfM⟩))
    exact (L.restrictScalars ℝ).contDiff.comp (contDiff_prod_ofFn_coord R hR k I)

end GlobalTheory
end

section

open Filter
open scoped InnerProductSpace Topology

namespace GlobalTheory.ClosableSchur

theorem inner_eq_of_diag {H E : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (D : Submodule ℂ H) (A A' : H →ₗ[ℂ] E) (c : ℂ)
    (h : ∀ w ∈ D, ⟪A w, A' w⟫_ℂ = c * ⟪w, w⟫_ℂ) :
    ∀ w ∈ D, ∀ w' ∈ D, ⟪A w, A' w'⟫_ℂ = c * ⟪w, w'⟫_ℂ := by
  intro w hw w' hw'
  have h1 := h (w + w') (D.add_mem hw hw')
  have h2 := h (w + Complex.I • w') (D.add_mem hw (D.smul_mem _ hw'))
  have h3 := h w hw
  have h4 := h w' hw'
  simp only [map_add (f := _), map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, Complex.conj_I] at h1 h2
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (1 / 2 : ℂ) * h1 - (Complex.I / 2) * h2 - (1 / 2 - Complex.I / 2) * h3
    - (1 / 2 - Complex.I / 2) * h4
    + (1 / 2 : ℂ) * (⟪A w, A' w'⟫_ℂ - c * ⟪w, w'⟫_ℂ - ⟪A w', A' w⟫_ℂ + c * ⟪w', w⟫_ℂ
      - Complex.I * (⟪A w', A' w'⟫_ℂ - c * ⟪w', w'⟫_ℂ)) * hI

theorem tendsto_zero_of_norm_sq {H E : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (D : Submodule ℂ H) (A : H →ₗ[ℂ] E) (a : ℝ)
    (h : ∀ w ∈ D, ‖A w‖ ^ 2 = a * ‖w‖ ^ 2) (u : ℕ → H) (hu : ∀ i, u i ∈ D)
    (h0 : Tendsto u atTop (𝓝 0)) : Tendsto (fun i => A (u i)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero] at h0 ⊢
  have h1 : Tendsto (fun i => a * ‖u i‖ ^ 2) atTop (𝓝 0) := by
    simpa using (h0.pow 2).const_mul a
  have h2 := h1.sqrt
  rw [Real.sqrt_zero] at h2
  refine h2.congr fun i => ?_
  rw [← h _ (hu i), Real.sqrt_sq (norm_nonneg _)]

theorem inner_eq_pair : ∀ (ι H E : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (ρ : ι → (H →L[ℂ] H)) (D : Submodule ℂ H), (∀ i v, ‖ρ i v‖ = ‖v‖) → (∀ i, ∃ j, (∀ v, ρ j (ρ i v) = v) ∧ ∀ v, ρ i (ρ j v) = v) → (∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ i, ∀ v ∈ S, ρ i v ∈ S) → S = ⊥ ∨ S = ⊤) → (∀ i, ∀ v ∈ D, ρ i v ∈ D) → ∀ A A' : H →ₗ[ℂ] E, (∀ i, ∀ w ∈ D, ‖A (ρ i w)‖ = ‖A w‖) → (∀ i, ∀ w ∈ D, ‖A' (ρ i w)‖ = ‖A' w‖) → (∀ i, ∀ w ∈ D, ⟪A (ρ i w), A' (ρ i w)⟫_ℂ = ⟪A w, A' w⟫_ℂ) → (∀ (u : ℕ → H) (f : E), (∀ i, u i ∈ D) → Tendsto u atTop (𝓝 0) → Tendsto (fun i => A (u i)) atTop (𝓝 f) → f = 0) → (∀ (u : ℕ → H) (f : E), (∀ i, u i ∈ D) → Tendsto u atTop (𝓝 0) → Tendsto (fun i => A' (u i)) atTop (𝓝 f) → f = 0) → ∃ c : ℂ, ∀ w ∈ D, ∀ w' ∈ D, ⟪A w, A' w'⟫_ℂ = c * ⟪w, w'⟫_ℂ := by
  intro ι H E _ _ _ _ _ _ ρ D hn hinv hirr hD A A' hA hA' hAA' hc hc'
  obtain ⟨a, ha⟩ := norm_sq_eq ι H E ρ D hn hinv hirr hD A hA hc
  obtain ⟨a', ha'⟩ := norm_sq_eq ι H E ρ D hn hinv hirr hD A' hA' hc'
  have hexp : ∀ (z : ℂ) (w : H), ‖(z • A + A') w‖ ^ 2 =
      ‖z‖ ^ 2 * ‖A w‖ ^ 2 + 2 * ((starRingEnd ℂ) z * ⟪A w, A' w⟫_ℂ).re + ‖A' w‖ ^ 2 := by
    intro z w
    rw [LinearMap.add_apply, LinearMap.smul_apply, @norm_add_sq ℂ, inner_smul_left, norm_smul,
      mul_pow]
    rfl
  have key : ∀ z : ℂ, ∃ b : ℝ, ∀ w ∈ D, ‖(z • A + A') w‖ ^ 2 = b * ‖w‖ ^ 2 := by
    intro z
    refine norm_sq_eq ι H E ρ D hn hinv hirr hD (z • A + A') ?_ ?_
    · intro i w hw
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), hexp, hexp, hA i w hw, hA' i w hw,
        hAA' i w hw]
    · intro u f hu h0 hf
      have h1 := tendsto_zero_of_norm_sq D A a ha u hu h0
      have h2 := tendsto_zero_of_norm_sq D A' a' ha' u hu h0
      have h3 := (h1.const_smul z).add h2
      rw [smul_zero, add_zero] at h3
      exact tendsto_nhds_unique hf h3
  obtain ⟨b, hb⟩ := key 1
  obtain ⟨b', hb'⟩ := key Complex.I
  refine ⟨⟨(b - a - a') / 2, (b' - a - a') / 2⟩, inner_eq_of_diag D A A' _ fun w hw => ?_⟩
  have e1 := hb w hw
  have e2 := hb' w hw
  rw [hexp, ha w hw, ha' w hw] at e1 e2
  have e3 : ⟪w, w⟫_ℂ = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; simp
  rw [e3]
  simp only [map_one, one_mul, norm_one, one_pow, Complex.norm_I, Complex.conj_I, Complex.mul_re,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im] at e1 e2
  apply Complex.ext
  · rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; linarith
  · rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; linarith

end GlobalTheory.ClosableSchur
end

section


theorem _root_.GlobalTheory.T.isDiscreteValuationRing_localization_of_height_eq_one' : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] (q : Ideal A) [q.IsPrime], q.height = 1 → IsDiscreteValuationRing (Localization.AtPrime q) := by
  first | exact @GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one | exact GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one | (intros; apply GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one <;> assumption)
end
