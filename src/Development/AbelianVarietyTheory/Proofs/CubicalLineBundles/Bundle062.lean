module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle060
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle061
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle058
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle075
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle080
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle008
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.iSup_range_differential_eq_top_of_jointly_onto : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (σ : K →+* ℂ) (I : Type) (Q : I → Out.PolAV (Sp (𝓞 K))) (FQ : ∀ i, GenFib (Q i)) (f : ∀ i, (Q i).A ⟶ P.A) (M : ∀ i, (Fin (FQ i).P₀.g → K) →ₗ[K] (Fin F.P₀.g → K)), Finite I → (∀ i, IsMonHom (f i)) → (∀ i, (FQ i).IsDiffOf F (f i) (M i)) → OntoAt f (spMap (σ.comp (algebraMap (𝓞 K) K))) → ⨆ i, LinearMap.range (M i) = ⊤ := by
  first | exact @GlobalTheory.DiffSpan.iSup_range_diff_eq_top | exact GlobalTheory.DiffSpan.iSup_range_diff_eq_top | (intros; apply GlobalTheory.DiffSpan.iSup_range_diff_eq_top <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.exists_cm_tensor_lattice_curve_principal_triple : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] (ω : R) (C : Ell H R ω) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H), IsKForm D ε h → (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → ∃ T : PAT H (Sp R), Nonempty (IsTen C D h T) ∧ T.g = Module.finrank ℚ E / 2 * (D.p + D.q) := by
  first | exact @GlobalTheory.CM.exists_isTen | exact GlobalTheory.CM.exists_isTen | (intros; apply GlobalTheory.CM.exists_isTen <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.hermitianMetric_differential_eq_of_pairing_relation : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (P' : Out.PolAV (Sp (𝓞 K))) (F' : GenFib P') (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K (Fin F'.P₀.g → K)) (f : P.A ⟶ P'.A) (g : P.A ⟶ P.A) (M : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)) (N : (Fin F.P₀.g → K) →ₗ[K] (Fin F.P₀.g → K)), F.IsHerm h → F'.IsHerm h' → IsMonHom f → IsMonHom g → LamEq P'.L f f P.L g (𝟙 P.A) → F.IsDiffOf F' f M → F.IsDiffOf F g N → ∀ s c c', h'.form s (M c) (M c') = h.form s c (N c') := by
  first | exact @GlobalTheory.HermHom.form_diff_eq | exact GlobalTheory.HermHom.form_diff_eq | (intros; apply GlobalTheory.HermHom.form_diff_eq <;> assumption)
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF.EigLine

theorem ringHom_ext_ringOfIntegers {E K : Type} [Field E] [NumberField E] [Field K] {f g : E →+* K}
    (h : ∀ a : 𝓞 E, f (a : E) = g (a : E)) : f = g :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext h)

theorem forall_apply_eq_smul_iff {K O : Type} [Field K] {n : ℕ} (r : O → Module.End K (Fin n → K)) (χ : Fin n → O → K)
    (hχ : Function.Injective χ) (hr : ∀ a j, r a (Pi.single j 1) = Pi.single j (χ j a)) (i : Fin n) (c : Fin n → K) :
    (∀ a, r a c = χ i a • c) ↔ ∃ s : K, c = Pi.single i s := by
  have hd : ∀ a (d : Fin n → K) j, r a d j = χ j a * d j := fun a d j => by

    conv_lhs => rw [pi_eq_sum_univ' d, map_sum]
    simp only [map_smul, hr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j (fun k _ hk => by simp [Pi.single_eq_of_ne hk.symm]) (by simp), Pi.single_eq_same,
      mul_comm]
  constructor
  · intro h
    refine ⟨c i, funext fun j => ?_⟩
    by_cases hj : j = i
    · rw [hj, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hj]
      by_contra hc
      refine hj (hχ (funext fun a => mul_right_cancel₀ hc ?_))
      rw [← hd, h a, Pi.smul_apply, smul_eq_mul]
  · rintro ⟨s, rfl⟩ a
    funext j
    rw [hd, Pi.smul_apply, smul_eq_mul]
    by_cases hj : j = i
    · rw [hj]
    · rw [Pi.single_eq_of_ne hj, mul_zero, mul_zero]

theorem mem_eigLat_iff : ∀ (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ) (oa : A.OAct (𝓞 E)) (act : OAct (𝓞 E) A.A) (S : Set (E →+* ℂ)) (τ : Fin x.P.g ≃ S) (lab : (E →+* ℂ) → (E →+* K)), act.act = oa.act → Function.Injective lab → IsLieType A oa x φ τ lab → ∀ (i : Fin x.P.g) (t : 𝓞 E →+* 𝓞 K), (∀ a : 𝓞 E, (t a : K) = lab (τ i) (a : E)) → ∀ c, c ∈ (GenFib.mk x.P φ hf x.v x.basis : GenFib A).eigLat act t ↔ c ∈ (GenFib.mk x.P φ hf x.v x.basis : GenFib A).lieLat ∧ ∃ r : K, c = Pi.single i r := by
  intro E _ _ _ K _ _ A x φ hf oa act S τ lab hact hlab hty i t ht c
  obtain ⟨r, hr, he⟩ := GlobalTheory.T.exists_lieRepresentation_eigenLattices K A (GenFib.mk x.P φ hf x.v x.basis) (𝓞 E) act
  have := x.P.isAb.comm
  have halg := LieComb.lieComb_algebra K x.P.A x.P.g x.v x.basis.1
  have hdiag : ∀ (a : 𝓞 E) (j : Fin x.P.g), r a (Pi.single j 1) = Pi.single j (lab (τ j) (a : E)) := fun a j => by
    obtain ⟨-, f₀, -, e, h⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K A (GenFib.mk x.P φ hf x.v x.basis) A (GenFib.mk x.P φ hf x.v x.basis)
      (act.act a) (act.hom a)
    obtain ⟨w, hw, hw'⟩ := hty a j
    have h₁ : IsLieComb (r a (Pi.single j 1)) x.v (x.v j ≫ f₀) := h _ (hr a) _ _ (halg.2.2.2.1 j)
    have e' : f₀.left ≫ φ = φ ≫ (oa.act a).left := by rw [← hact]; exact e
    obtain rfl : x.v j ≫ f₀ = w := Over.OverMorphism.ext (hf.2.1.1.hom_ext
      (by rw [Over.comp_left, Category.assoc, e', hw']) ((Over.w _).trans (Over.w _).symm))
    exact (x.basis.2 _ (halg.2.1 _ _ hw)).unique h₁ hw
  have hχ : Function.Injective fun (j : Fin x.P.g) (a : 𝓞 E) => lab (τ j) (a : E) := fun j k h =>
    τ.injective (Subtype.ext (hlab (ringHom_ext_ringOfIntegers fun a => congrFun h a)))
  refine (he t c).1.trans (and_congr_right fun _ => ?_)
  rw [← forall_apply_eq_smul_iff (fun a => r a) _ hχ hdiag i c]
  refine forall_congr' fun a => ?_
  rw [← ht a, ← algebraMap_smul K (t a) c]

end GlobalTheory.LamF.EigLine
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF


theorem _root_.GlobalTheory.T.lieLetter_integral_of_local_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (l : Level H) (c : Coeff l) (nΨ n' f : ℕ) (o : LamObj c nΨ n') (La : ℝ), LamObjGood o f La → ∀ L : LamLetters o, L.IsGood → ∀ (p : HeightOneSpectrum (𝓞 o.K₁)) (M : Matrix (Fin o.xB.P.g) (Fin o.xB.P.g) o.K₁), IsModelAt o.B o.xB o.φB p M → ∀ (k : Fin o.xB.P.g) (cl : o.K₁), IsLocGen p cl (L.ℓ k).I → ∀ m, p.valuation o.K₁ (Matrix.vecMul (cl • L.U k) M⁻¹ m) ≤ 1 := by
  first | exact @GlobalTheory.LamF.letter_integral_of_isLocGen | exact GlobalTheory.LamF.letter_integral_of_isLocGen | (intros; apply GlobalTheory.LamF.letter_integral_of_isLocGen <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn
open scoped Matrix

namespace GlobalTheory.TransvModel

theorem herm_smul_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r) (S : Set E)
    (hΛ : X.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ S, ∃ u ∈ X.L', v = a • u}) {v : Fin r → E} (hv : v ∈ X.L')
    {x : Fin r → E} (hx : x ∈ X.Λ) : FD.herm X.Gm x v • v ∈ X.Λ := by
  rw [hΛ] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, u, hu, rfl⟩ := hx
    rw [GlobalTheory.TransvLevel.herm_smul_left, mul_smul, hΛ]
    exact Submodule.subset_span ⟨a, ha, _, GlobalTheory.FlagData.smul_mem_of_isIntegral _ (X.L'_int u hu v hv) hv, rfl⟩
  | zero => simp [FD.herm]
  | add x y _ _ hx hy =>
    have : FD.herm X.Gm (x + y) v = FD.herm X.Gm x v + FD.herm X.Gm y v := (X.toData.hermL v).map_add x y
    rw [this, add_smul]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [← algebraMap_smul E c x, GlobalTheory.TransvLevel.herm_smul_left, mul_smul, algebraMap_smul]
    exact Submodule.smul_mem _ c hx

theorem transv_mem_of_span {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r) (S : Set E)
    (hΛ : X.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ S, ∃ u ∈ X.L', v = a • u}) (m : ℕ)
    (hmκ : IsIntegral ℤ ((m : E) * X.κ0)) (v : Fin r → E) (hv : v ∈ X.L') (hiso : FD.herm X.Gm v v = 0) (b : E)
    (hb : cc b = b) (hbi : IsIntegral ℤ b) :
    ∃ γ ∈ X.Γ, ∀ τ : X.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 =
      X.flowMat v τ ((((X.g * m : ℕ) : ℝ) : ℂ) * τ.1 b) := by
  have hξ' : IsCMField.complexConj E X.ξ0 = -X.ξ0 := X.ξ0_im
  have hκc : IsCMField.complexConj E X.κ0 = -X.κ0 := by
    rcases X.κ0_xi with h | h <;> simp [h, hξ', map_ofNat]
  have hb' : IsCMField.complexConj E b = b := hb
  set α : E := ((X.g * m : ℕ) : E) * b * X.κ0 with hαdef
  have hα : cc α = -α := by
    simp [hαdef, cc, hb', hκc]
  have key : ∀ x ∈ X.Λ, (b * ((m : E) * X.κ0)) • (FD.herm X.Gm x v • v) ∈ X.Λ := fun x hx =>
    GlobalTheory.FlagData.smul_mem_of_isIntegral _ (hbi.mul hmκ) (herm_smul_mem X S hΛ hv hx)
  have e : ∀ x, (α * FD.herm X.Gm x v) • v =
      (X.g : E) • ((b * ((m : E) * X.κ0)) • (FD.herm X.Gm x v • v)) := by
    intro x
    rw [smul_smul, smul_smul, hαdef]
    congr 1
    push_cast
    ring
  have key' : ∀ x ∈ X.Λ, (α * FD.herm X.Gm x v) • v ∈ X.Λ := fun x hx => by
    rw [e]
    exact GlobalTheory.FlagData.smul_mem_of_isIntegral _ (isIntegral_natCast _) (key x hx)
  refine ⟨GlobalTheory.FlagData.transv X.Gm hiso α, X.cong _
    ⟨GlobalTheory.FlagData.herm_transvMat X.Gm_herm hiso hα, fun x => ?_⟩ (fun x hx => ?_), fun τ => ?_⟩
  · change x ∈ X.Λ ↔ transvMat X.Gm v α *ᵥ x ∈ X.Λ
    rw [GlobalTheory.FlagData.transvMat_mulVec]
    refine ⟨fun hx => Submodule.add_mem _ hx (key' x hx), fun hx => ?_⟩
    have h := key' _ hx
    rw [GlobalTheory.FlagData.herm_add_smul_left, hiso, mul_zero, add_zero] at h
    simpa using Submodule.sub_mem _ hx h
  · refine ⟨_, key x hx, ?_⟩
    change transvMat X.Gm v α *ᵥ x - x = _
    rw [GlobalTheory.FlagData.transvMat_mulVec, add_sub_cancel_left, e]
  · change (transvMat X.Gm v α).map τ.1 = _
    refine TransvectionPeriodicity.transvMat_map X.toData v τ α _ ?_
    rw [hαdef, map_mul, map_mul, TransvectionPeriodicity.emb_kappa X.toData τ, map_natCast]
    push_cast
    ring

theorem xiR_eq (D : D7) : xiR D = 1 / ((Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d) := by
  have e1 : D.host.φ₀ D.host.xi0 =
      -1 / ((Ideal.absNorm D.host.ccK : ℂ) * D.host.φ₀ D.host.sqrtMinusD) := by
    unfold Formalism.BasicNotions.Host.xi0; simp [map_div₀, map_mul, map_neg, map_natCast]
  have e2 : ‖D.host.φ₀ D.host.sqrtMinusD‖ = Real.sqrt D.host.d := by
    have h0 : (D.host.φ₀ D.host.sqrtMinusD) ^ 2 = -(D.host.d : ℂ) := by
      rw [← map_pow, Formalism.BasicNotions.Host.sqrtMinusD_sq D.host, map_neg, map_natCast]
    rw [← Real.sqrt_sq (norm_nonneg (D.host.φ₀ D.host.sqrtMinusD)), ← norm_pow, h0, norm_neg,
      Complex.norm_natCast]
  unfold xiR; rw [e1, norm_div, norm_neg, norm_one, norm_mul, Complex.norm_natCast, e2]

theorem isIntegral_level_mul_kappa {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : FD.Data E r)
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d) (τ : E →+* ℂ) (hτ : ‖τ X.ξ0‖ = 1 / ((N : ℝ) * Real.sqrt d)) :
    IsIntegral ℤ (((N * d : ℕ) : E) * X.κ0) := by
  have h1 : τ (cc X.ξ0) = (starRingEnd ℂ) (τ X.ξ0) := IsCMField.complexEmbedding_complexConj E τ X.ξ0
  rw [X.ξ0_im, map_neg] at h1
  have h2 := Complex.mul_conj' (τ X.ξ0)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h3 : ‖τ X.ξ0‖ ^ 2 * ((N : ℝ) ^ 2 * d) = 1 := by
    rw [hτ, div_pow, mul_pow, Real.sq_sqrt hd'.le]
    field_simp
  have h4 : ((‖τ X.ξ0‖ : ℝ) : ℂ) ^ 2 * ((N : ℂ) ^ 2 * d) = 1 := by exact_mod_cast h3
  rw [← h1] at h2
  have h5 : X.κ0 ^ 2 = 4 * X.ξ0 ^ 2 := by
    rcases X.κ0_xi with h | h <;> rw [h] <;> ring
  have h6 : (((N * d : ℕ) : E) * X.κ0) ^ 2 = ((-(4 * d : ℤ) : ℤ) : E) := by
    apply τ.injective
    rw [mul_pow, h5, map_mul, map_mul, map_pow, map_pow, map_natCast, map_intCast, map_ofNat]
    push_cast
    linear_combination (-4 * (N : ℂ) ^ 2 * (d : ℂ) ^ 2) * h2 - 4 * (d : ℂ) * h4
  refine IsIntegral.of_pow two_pos ?_
  rw [h6]
  exact isIntegral_algebraMap (R := ℤ)

theorem transv_model : ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ), InR D j → ∀ (k : (T.U j T.σ₀).Comp) (Xx : DataX D.host.E D.R.r), Xx.toData = ((T.U j T.σ₀).X k) → Xx.g = T.Q.l.M → Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u} → ((D.host.g 0 * D.host.g 1 * Ideal.absNorm D.host.ccK * D.host.d : ℕ) : ℝ) * Xx.k0 = 2 * (D.host.g 0 * D.host.g 1 : ℕ) * Real.sqrt D.host.d ∧ ∀ v ∈ Xx.L', FD.herm ((T.U j T.σ₀).X k).Gm v v = 0 → ∀ b : D.host.E, cc b = b → IsIntegral ℤ b → ∃ γ ∈ ((T.U j T.σ₀).X k).Γ, ∀ τ : ((T.U j T.σ₀).X k).Ψ, (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 = ((T.U j T.σ₀).X k).flowMat v τ ((((D.host.g 0 * D.host.g 1 * Ideal.absNorm D.host.ccK * D.host.d : ℕ) : ℝ) : ℂ) * τ.1 b) := by
  intro D T h j hj k Xx hX hg hΛ
  have hM : Xx.g = D.host.g 0 * D.host.g 1 := hg.trans h.pins.2.1.1
  have hN : 0 < Ideal.absNorm D.host.ccK :=
    Nat.pos_of_ne_zero fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hd : 0 < D.host.d := by have := D.host.qd_big.2; omega
  have habs : ∀ τ : D.host.E →+* ℂ,
      ‖τ Xx.ξ0‖ = 1 / ((Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d) := fun τ => by
    rw [← xiR_eq, ← h.xiAbs j hj T.σ₀ T.good_σ₀ k τ, ← hX]
  rw [← hX]
  refine ⟨?_, fun v hv hiso b hb hbi => ?_⟩
  · obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ Xx.Ψ := by
      by_cases h0 : D.host.φ₀ ∈ Xx.Ψ
      · exact ⟨_, h0⟩
      · by_contra hc
        exact h0 ((Xx.cmType _).2 fun h1 => hc ⟨_, h1⟩)
    have h1 := Xx.ξ0_abs ⟨τ, hτ⟩
    rw [habs] at h1
    have hN' : (0 : ℝ) < Ideal.absNorm D.host.ccK := by exact_mod_cast hN
    have hd' : (0 : ℝ) < D.host.d := by exact_mod_cast hd
    have hs := Real.sqrt_pos.2 hd'
    have hk : Xx.k0 = 2 / ((Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d) := by
      rw [div_eq_mul_one_div, h1]; ring
    have hss := Real.mul_self_sqrt hd'.le
    rw [hk]
    push_cast
    field_simp
    linear_combination (-((D.host.g 0 : ℝ) * D.host.g 1)) * hss
  · have := transv_mem_of_span Xx (D.host.AA : Set D.host.E) hΛ (Ideal.absNorm D.host.ccK * D.host.d)
      (isIntegral_level_mul_kappa Xx.toData hN hd D.host.φ₀ (habs _)) v hv hiso b hb hbi
    rwa [hM, ← mul_assoc] at this

end GlobalTheory.TransvModel
end
