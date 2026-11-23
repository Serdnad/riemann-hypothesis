module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle053
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle052
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle040
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle031
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle047
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeCmEqIdealAndCovolume
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle006
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogCovolumeEqMeanClassGroup
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle026
import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.family_identities_descend_field_to_dedekind : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDedekindDomain R] (ω : R) (C : Ell H R ω) (D : Datum H) (h : D.La → D.La → OK H) (T : PAT H (Sp R)) (L : Submodule (𝓞 E) D.La) (ψ : L → (C.P.A ⟶ T.t.G)) (k : Type) [Field k] (ω' : k) (C' : Ell H k ω') (f : R →+* k) (φ : C'.P.A.left ⟶ C.P.A.left) (T' : PAT H (Sp k)) (m : SABMap T'.t T.t (spMap f)) (ψ' : L → (C'.P.A ⟶ T'.t.G)), Function.Injective f → EllMap C' C f φ → (∀ a, (ψ' a).left ≫ m.φ = φ ≫ (ψ a).left) → IsFam C' T' h L ψ' → IsFam C T h L ψ := by
  first | exact @GlobalTheory.FamDescent.isFam_descend | exact GlobalTheory.FamDescent.isFam_descend | (intros; apply GlobalTheory.FamDescent.isFam_descend <;> assumption)
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.DegBound

section Lattice

variable {K : Type} [Field K] [NumberField K] {V V' : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

end Lattice

variable {K : Type} [Field K] [NumberField K] {E : Type} [Field E] [NumberField E] [IsCMField E]


omit [NumberField K] in
theorem eigLat_le {P : Out.PolAV (Sp (𝓞 K))} (F : GenFib P) {O : Type} [CommRing O] (act : OAct O P.A)
    (τ : O →+* 𝓞 K) : F.eigLat act τ ≤ F.lieLat :=
  Submodule.span_mono fun _ ⟨u, hu, _⟩ => ⟨u, hu⟩

theorem eigLat_fg {P : Out.PolAV (Sp (𝓞 K))} (F : GenFib P) {O : Type} [CommRing O] (act : OAct O P.A)
    (τ : O →+* 𝓞 K) : (F.eigLat act τ).FG := by
  have := isNoetherian_of_fg_of_noetherian _ (LieLattice.lieLat_fg_and_span_eq_top K P F).1
  exact Submodule.FG.of_le_of_isNoetherian (eigLat_le F act τ)

end GlobalTheory.CM.DegBound
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.lieLattice_fg_and_span_eq_top_ringOfIntegers : ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P), F.lieLat.FG ∧ Submodule.span K (F.lieLat : Set (Fin F.P₀.g → K)) = ⊤ := by
  first | exact @GlobalTheory.CM.LieLattice.lieLat_fg_and_span_eq_top | exact GlobalTheory.CM.LieLattice.lieLat_fg_and_span_eq_top | (intros; apply GlobalTheory.CM.LieLattice.lieLat_fg_and_span_eq_top <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.cmHermitianForm_sum_of_squares : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H), IsKForm D ε h → (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → ∃ (N m : ℕ) (l : D.La →ₗ[OK H] (Fin m → OK H)) (r : (Fin m → OK H) →ₗ[OK H] D.La), 1 ≤ N ∧ r ∘ₗ l = LinearMap.id ∧ ∀ x y, (N : 𝓞 E) * (h x y : OK H) = ∑ k, ((l x k : OK H) : 𝓞 E) * H.bar (l y k : OK H) := by
  first | exact @GlobalTheory.CM.HermSq.kForm_sum_sq | exact GlobalTheory.CM.HermSq.kForm_sum_sq | (intros; apply GlobalTheory.CM.HermSq.kForm_sum_sq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF.IsogSum

variable {S : Scheme.{0}}

theorem isMonHom_of_points {G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H)
    (h : ∀ (T : Over S) (a b : T ⟶ G), (a * b) ≫ f = a ≫ f * b ≫ f) : IsMonHom f := by
  refine ⟨?_, ?_⟩
  · have h1 := h (𝟙_ _) 1 1
    rw [_root_.mul_one] at h1
    have h2 : (1 : 𝟙_ _ ⟶ G) ≫ f = 1 := by simpa using h1
    simpa [Hom.one_def] using h2
  · simpa only [Hom.mul_def, lift_fst_snd, Category.id_comp, lift_fst_comp_snd_comp]
      using h (G ⊗ G) (fst G G) (snd G G)

theorem comp_prod {T G H : Over S} [GrpObj H] [IsCommMonObj H] {n : ℕ} (x : T ⟶ G)
    (a : Fin n → (G ⟶ H)) : x ≫ ∏ i, a i = ∏ i, x ≫ a i :=
  map_prod (MonoidHom.mk' (fun u : G ⟶ H => x ≫ u) fun _ _ => MonObj.comp_mul _ _ _) a Finset.univ

theorem exists_point {Q G' G H' H T : Over S} [GrpObj G'] [GrpObj G] [GrpObj H'] [GrpObj H] {p q : ℕ}
    (pG : Out.IsPowGrp G' G p) (pH : Out.IsPowGrp H' H q) (u : Q ⟶ G') (v : Q ⟶ H')
    [IsIso (lift u v)] (a : Fin p → (T ⟶ G)) (b : Fin q → (T ⟶ H)) :
    ∃ x : T ⟶ Q, (∀ i, x ≫ u ≫ pG.pr i = a i) ∧ ∀ i, x ≫ v ≫ pH.pr i = b i := by
  have hu : inv (lift u v) ≫ u = fst _ _ := by rw [IsIso.inv_comp_eq, lift_fst]
  have hv : inv (lift u v) ≫ v = snd _ _ := by rw [IsIso.inv_comp_eq, lift_snd]
  obtain ⟨c, hc⟩ : ∃ c : T ⟶ G', ∀ i, c ≫ pG.pr i = a i :=
    ⟨pG.lim.lift (Fan.mk T a), fun i => pG.lim.fac (Fan.mk T a) ⟨i⟩⟩
  obtain ⟨d, hd⟩ : ∃ d : T ⟶ H', ∀ i, d ≫ pH.pr i = b i :=
    ⟨pH.lim.lift (Fan.mk T b), fun i => pH.lim.fac (Fan.mk T b) ⟨i⟩⟩
  refine ⟨lift c d ≫ inv (lift u v), fun i => ?_, fun i => ?_⟩
  · rw [Category.assoc, reassoc_of% hu, lift_fst_assoc, hc]
  · rw [Category.assoc, reassoc_of% hv, lift_snd_assoc, hd]

end GlobalTheory.LamF.IsogSum

namespace GlobalTheory.LamF

theorem exists_inverse_isogeny_of_sum : ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (A A' B : Out.PolAV (Sp (𝓞 K))) (p q : ℕ) (φ : Fin p → (A.A ⟶ B.A)) (φ' : Fin q → (A'.A ⟶ B.A)), (∀ i, IsMonHom (φ i)) → (∀ i, IsMonHom (φ' i)) → B.g = p * A.g + q * A'.g → (∀ y : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ B.A, ∃ (x : Fin p → (Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.A)) (x' : Fin q → (Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A'.A)), y = (List.ofFn fun i => x i ≫ φ i).prod * (List.ofFn fun i => x' i ≫ φ' i).prod) → ∃ (N : ℕ) (ψ : Fin p → (B.A ⟶ A.A)) (ψ' : Fin q → (B.A ⟶ A'.A)), 0 < N ∧ (∀ (Tb : Over (Sp (𝓞 K))) (x : Tb ⟶ B.A), padd B.A (psumPt fun i => x ≫ ψ i ≫ φ i) (psumPt fun i => x ≫ ψ' i ≫ φ' i) = pnsmulPt N x) ∧ ∀ (Tb : Over (Sp (𝓞 K))) (a : Fin p → (Tb ⟶ A.A)) (a' : Fin q → (Tb ⟶ A'.A)), (∀ i, padd B.A (psumPt fun k => a k ≫ φ k) (psumPt fun k => a' k ≫ φ' k) ≫ ψ i = pnsmulPt N (a i)) ∧ ∀ i, padd B.A (psumPt fun k => a k ≫ φ k) (psumPt fun k => a' k ≫ φ' k) ≫ ψ' i = pnsmulPt N (a' i) := by
  intro hU hL hE K _ _ σ A A' B p q φ φ' hφ hφ' hg hs
  obtain ⟨P, pP, hP⟩ := GlobalTheory.T.exists_polarisedAbelianScheme_power (𝓞 K) A p
  obtain ⟨P', pP', hP'⟩ := GlobalTheory.T.exists_polarisedAbelianScheme_power (𝓞 K) A' q
  obtain ⟨Q, u, v, hu, hv, huv, hQ⟩ := GlobalTheory.T.exists_prod_polAV_add_g hL (𝓞 K) P P'
  haveI := pP.hom
  haveI := pP'.hom
  let Φ : Q.A ⟶ B.A := (∏ i, u ≫ pP.pr i ≫ φ i) * ∏ i, v ≫ pP'.pr i ≫ φ' i
  have hΦ : ∀ {T : Over (Sp (𝓞 K))} (x : T ⟶ Q.A),
      x ≫ Φ = (∏ i, (x ≫ u ≫ pP.pr i) ≫ φ i) * ∏ i, (x ≫ v ≫ pP'.pr i) ≫ φ' i := by
    intro T x
    simp only [Φ, MonObj.comp_mul, IsogSum.comp_prod, Category.assoc]
  have hm : IsMonHom Φ := IsogSum.isMonHom_of_points Φ fun T a b => by
    simp only [hΦ, MonObj.mul_comp, Finset.prod_mul_distrib]
    exact mul_mul_mul_comm _ _ _ _
  obtain ⟨N, ψ, hN, hψ, h1, h2⟩ := GlobalTheory.T.exists_inverse_isogeny_of_surjective_points hU hL hE K σ Q B Φ (by rw [hQ, hP, hP', hg]) hm fun y => by
    obtain ⟨a, b, hab⟩ := hs y
    obtain ⟨x, hx, hx'⟩ := IsogSum.exists_point pP pP' u v a b
    refine ⟨x, ?_⟩
    rw [hΦ, hab, List.prod_ofFn, List.prod_ofFn]
    simp only [hx, hx']
  have padd_eq_mul {G T : Over (Sp (𝓞 K))} [GrpObj G] (a b : T ⟶ G) :
      padd G a b = a * b := rfl
  have pnsmulPt_eq_pow {G T : Over (Sp (𝓞 K))} [GrpObj G] (n : ℕ) (a : T ⟶ G) :
      pnsmulPt n a = a ^ n := by
    induction n with
    | zero => rw [pow_zero]; rfl
    | succ n ih => rw [pow_succ, ← ih]; rfl
  have psumPt_eq_prod {G T : Over (Sp (𝓞 K))} [GrpObj G] {n : ℕ} (f : Fin n → (T ⟶ G)) :
      psumPt f = (List.ofFn f).prod := by
    rw [List.prod_eq_foldr]
    rfl
  refine ⟨N, fun i => ψ ≫ u ≫ pP.pr i, fun i => ψ ≫ v ≫ pP'.pr i, hN, fun T x => ?_, fun T a b => ?_⟩
  · rw [padd_eq_mul, pnsmulPt_eq_pow, psumPt_eq_prod, psumPt_eq_prod, List.prod_ofFn, List.prod_ofFn]
    have := hΦ (x ≫ ψ)
    rw [Category.assoc, h2, MonObj.comp_pow, Category.comp_id] at this
    simpa only [Category.assoc] using this.symm
  · obtain ⟨x, hx, hx'⟩ := IsogSum.exists_point pP pP' u v a b
    have key : padd B.A (psumPt fun k => a k ≫ φ k) (psumPt fun k => b k ≫ φ' k) ≫ ψ = x ^ N := by
      have : x ≫ Φ = padd B.A (psumPt fun k => a k ≫ φ k) (psumPt fun k => b k ≫ φ' k) := by
        rw [padd_eq_mul, psumPt_eq_prod, psumPt_eq_prod, List.prod_ofFn, List.prod_ofFn, hΦ]
        simp only [hx, hx']
      rw [← this, Category.assoc, h1, MonObj.comp_pow, Category.comp_id]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · rw [← Category.assoc, key, MonObj.pow_comp, hx, pnsmulPt_eq_pow]
    · rw [← Category.assoc, key, MonObj.pow_comp, hx', pnsmulPt_eq_pow]

end GlobalTheory.LamF
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

theorem exists_periodPair_image_ideal {K : Type} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    {σ : K →+* ℂ} (hσ : ¬ ComplexEmbedding.IsReal σ) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    ∃ L : PeriodPair, ∀ z, z ∈ L.lattice ↔ ∃ a ∈ I, z = σ (a : K) := by
  have hr : Module.finrank ℤ I = 2 :=
    (Ideal.finrank_eq_finrank (RingOfIntegers.basis K) I hI).trans ((RingOfIntegers.rank K).trans hK)
  let b : Module.Basis (Fin 2) ℤ I := Module.finBasisOfFinrankEq ℤ _ hr
  have hs : ∀ x : I, σ ((x : 𝓞 K) : K) =
      b.repr x 0 * σ ((b 0 : 𝓞 K) : K) + b.repr x 1 * σ ((b 1 : 𝓞 K) : K) := by
    intro x
    have := congrArg (fun x : I => σ ((x : 𝓞 K) : K)) (b.sum_repr x)
    rw [Fin.sum_univ_two] at this
    simpa using this.symm
  obtain ⟨a, ha⟩ := CMLattice.exists_im_ne_zero σ hσ
  have hb0 : σ ((b 0 : 𝓞 K) : K) ≠ 0 := by
    rw [map_ne_zero]
    have : (b 0 : 𝓞 K) ≠ 0 := fun h => b.ne_zero 0 (Subtype.ext h)
    exact_mod_cast this
  have h0 : (σ ((b 1 : 𝓞 K) : K) * starRingEnd ℂ (σ ((b 0 : 𝓞 K) : K))).im ≠ 0 := by
    intro h0
    have e := hs ⟨a * b 0, I.mul_mem_left a (b 0).2⟩
    have e' := congrArg (fun z => (z * starRingEnd ℂ (σ ((b 0 : 𝓞 K) : K))).im) e
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul] at e' h0 ha hb0
    rw [add_mul, _root_.mul_assoc, _root_.mul_assoc, _root_.mul_assoc, Complex.mul_conj, Complex.add_im,
      Complex.mul_im, Complex.mul_im, Complex.mul_im, h0] at e'
    simp [ha, hb0] at e'
  refine ⟨⟨σ ((b 0 : 𝓞 K) : K), σ ((b 1 : 𝓞 K) : K), ?_⟩, fun z => ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro x y e
    have e1 := congrArg Complex.re e
    have e2 := congrArg Complex.im e
    simp at e1 e2 h0
    constructor
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ ((b 1 : 𝓞 K) : K)).im * e1 - (σ ((b 1 : 𝓞 K) : K)).re * e2
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ ((b 0 : 𝓞 K) : K)).re * e2 - (σ ((b 0 : 𝓞 K) : K)).im * e1
  · rw [PeriodPair.mem_lattice]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨_, (m • b 0 + n • b 1).2, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, _, (hs ⟨x, hx⟩).symm⟩

theorem mean_log_lieNormSq_eq_mean_log_eta :
    ThetaUnifAV → Out.PolBaseChangeSt → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (σ₀ : K →+* ℂ), ¬ ComplexEmbedding.IsReal σ₀ → ∀ (𝔟 : ClassGroup (𝓞 K) → nonZeroDivisors (Ideal (𝓞 K))), (∀ C, ClassGroup.mk0 (𝔟 C) = C) → ∀ (M : IntermediateField ℚ ℂ) [NumberField M] (κ : K →+* M) (P : Out.PolAV (Sp (𝓞 M))) (v : epsR (𝓞 M) ⟶ P.A) (L₀ : (𝓞 M →+* ℂ) → PeriodPair) (Q : ClassGroup (𝓞 K) → Out.PolAV (Sp (𝓞 M))) (t : ∀ C, epsR (𝓞 M) ⟶ (Q C).A) (L : ClassGroup (𝓞 K) → (𝓞 M →+* ℂ) → PeriodPair) (δ : ClassGroup (𝓞 K) → (𝓞 M)ˣ), (∀ a, (κ a : ℂ) = σ₀ a) ∧ (P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : (𝓞 M) →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (L₀ s').lattice ↔ z • w' ∈ u'.Λ)) ∧ (∀ C, ((Q C).g = 1 ∧ IsLieBasis ![(t C)] ∧ (∀ (R' : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ (Q C).A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' (Q C) P' φ' → IsVecOver f' φ' (t C) v' → IsLieBasis ![v']) ∧ ∀ s' : (𝓞 M) →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ (Q C).A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' (Q C) P' φ' → IsVecOver s' φ' (t C) v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (L C s').lattice ↔ z • w' ∈ u'.Λ))) ∧ (∀ C s, (L C s).g₂ ^ 3 - 27 * (L C s).g₃ ^ 2 = s (δ C : 𝓞 M)) ∧ (∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice ↔ ∃ a : 𝓞 K, z = c * σ₀ (a : K)) → (∃ β : ClassGroup (𝓞 K) → M, (∀ C, β C ≠ 0) ∧ (∀ a : 𝓞 K, (∀ (P₁ Q₁ : Out.PolAV (Sp M)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ P.A.left) (v₁ : epsR M ⟶ P₁.A) (t₁ : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M) M) P P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M) M) P Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M) M) φ₁ v v₁ → IsVecOver (algebraMap (𝓞 M) M) ψ₁ v t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![κ (a : K)] ![t₁] (v₁ ≫ f₁))) ∧ (∀ C (x : K), (∀ b ∈ (𝔟 C : Ideal (𝓞 K)), IsIntegral ℤ (x * (b : K))) → (∀ (P₁ Q₁ : Out.PolAV (Sp M)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ (Q C).A.left) (v₁ : epsR M ⟶ P₁.A) (t₁ : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M) M) P P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M) M) (Q C) Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M) M) φ₁ v v₁ → IsVecOver (algebraMap (𝓞 M) M) ψ₁ (t C) t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![β C * κ x] ![t₁] (v₁ ≫ f₁))) ∧ ∀ C, ∀ y ∈ (𝔟 C : Ideal (𝓞 K)), (∀ (P₁ Q₁ : Out.PolAV (Sp M)) (φ₁ : P₁.A.left ⟶ (Q C).A.left) (ψ₁ : Q₁.A.left ⟶ P.A.left) (v₁ : epsR M ⟶ P₁.A) (t₁ : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M) M) (Q C) P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M) M) P Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M) M) φ₁ (t C) v₁ → IsVecOver (algebraMap (𝓞 M) M) ψ₁ v t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![(β C)⁻¹ * κ (y : K)] ![t₁] (v₁ ≫ f₁))) → ∀ n : (M →+* ℂ) → ℝ, (∀ s, IsLieNormSq P v (s.comp (algebraMap (𝓞 M) M)) (n s)) → ∀ (σ : K →+* ℂ) (τ : ClassGroup (𝓞 K) → ℍ), (∀ C, IsIdealClassPoint σ C (τ C)) → (∑ s, Real.log (n s)) / Module.finrank ℚ M = (∑ C, -Real.log (4 * Real.pi * (τ C).im * ‖ModularForm.eta (τ C)‖ ^ 4)) / classNumber K := by
  intro hU hB hN K _ _ hK σ₀ h₀ 𝔟 h𝔟 M _ κ P v L₀ Q t L δ ⟨_, ⟨hPg, hv, hvb, hPL⟩, hQ, hδ, _⟩
    ⟨β, hβ, hEnd, h1, h2⟩ n hn σ τ hτ
  let _ : Algebra K M := κ.toAlgebra
  have hvt : IsTangent v := hv.1 0
  have htt : ∀ C, IsTangent (t C) := fun C => (hQ C).2.1.1 0
  obtain ⟨P₀, φ, hφ⟩ := exists_isPolFibre hB (algebraMap (𝓞 M) M) P
  obtain ⟨v₀, hv₀, -⟩ := existsUnique_isVecOver hφ.2.1.1 v
  choose Q₀ ψ hψ using fun C => exists_isPolFibre hB (algebraMap (𝓞 M) M) (Q C)
  choose t₀ ht₀ using fun C => (existsUnique_isVecOver (hψ C).2.1.1 (t C)).exists
  choose Lc hLc using fun C => exists_periodPair_image_ideal hK h₀ (nonZeroDivisors.coe_ne_zero (𝔟 C))
  have key := mean_log_covolume_eq_mean_classGroup K M hK σ₀ h₀ 𝔟 Lc h𝔟 hLc
    (fun s => L₀ (s.comp (algebraMap (𝓞 M) M))) (fun C s => L C (s.comp (algebraMap (𝓞 M) M))) δ β
    (fun s a => by
      obtain ⟨f, hf, hc⟩ := hEnd a P₀ P₀ φ φ v₀ v₀ hφ hφ hv₀ hv₀
      exact (EllipticHom.multiplier_iff_exists_hom hU hB _ P P v v _ _ _ _ hPg hPg hvt hvt (hPL _) (hPL _)).2
        (hom_deriv_baseChange _ P P v v _ _ P₀ P₀ φ φ v₀ v₀ f _ hφ hφ hv₀ hv₀ hf hc ℂ s))
    (fun C s => hδ C _) hβ
    (fun C x hx => ⟨T.isIntegral_derivative_curve_hom_good_reduction hN hB M P (Q C) v (t C) _ hvt (hQ C).2.2.1 (h1 C x hx), fun s => by
      obtain ⟨f, hf, hc⟩ := h1 C x hx P₀ (Q₀ C) φ (ψ C) v₀ (t₀ C) hφ (hψ C) hv₀ (ht₀ C)
      exact (EllipticHom.multiplier_iff_exists_hom hU hB _ P (Q C) v (t C) _ _ _ _ hPg (hQ C).1 hvt (htt C) (hPL _) ((hQ C).2.2.2 _)).2
        (hom_deriv_baseChange _ P (Q C) v (t C) _ _ _ _ _ _ _ _ f _ hφ (hψ C) hv₀ (ht₀ C) hf hc ℂ s)⟩)
    (fun C y hy => ⟨T.isIntegral_derivative_curve_hom_good_reduction hN hB M (Q C) P (t C) v _ (htt C) hvb (h2 C y hy), fun s => by
      obtain ⟨f, hf, hc⟩ := h2 C y hy (Q₀ C) P₀ (ψ C) φ (t₀ C) v₀ (hψ C) hφ (ht₀ C) hv₀
      exact (EllipticHom.multiplier_iff_exists_hom hU hB _ (Q C) P (t C) v _ _ _ _ (hQ C).1 hPg (htt C) hvt ((hQ C).2.2.2 _) (hPL _)).2
        (hom_deriv_baseChange _ (Q C) P (t C) v _ _ _ _ _ _ _ _ f _ (hψ C) hφ (ht₀ C) hv₀ hf hc ℂ s)⟩)
  rw [← log_pi_sub_mean_log_latticeNormDisc K hK σ₀ h₀ 𝔟 Lc h𝔟 hLc σ τ hτ, ← key]
  have hlog : ∀ s : M →+* ℂ, Real.log (n s) = Real.log Real.pi -
      Real.log |((L₀ (s.comp (algebraMap (𝓞 M) M))).ω₁ *
        starRingEnd ℂ (L₀ (s.comp (algebraMap (𝓞 M) M))).ω₂).im| := by
    intro s
    obtain ⟨hp, hr⟩ := isLieNormSq_iff_eq_pi_div_covolume hU hB _ P v _ _ hPg hvt (hPL (s.comp (algebraMap (𝓞 M) M)))
    rw [(hr _).1 (hn s), Real.log_div Real.pi_ne_zero]
    intro h
    rw [h, div_zero] at hp
    exact lt_irrefl _ hp
  have hM : (Module.finrank ℚ M : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  simp only [hlog, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Embeddings.card, nsmul_eq_mul]
  field_simp

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve
open scoped CategoryTheory.Obj UpperHalfPlane

theorem _root_.GlobalTheory.T.exists_ellipticCurve_polarised_lattice_family : ThetaUnifAV → Out.PolBaseChangeSt → (∀ (R : Type) [CommRing R] (W : WeierstrassCurve R), IsUnit W.Δ → ∃ (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (Lf : (R →+* ℂ) → PeriodPair), (P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : R →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : R →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (Lf s').lattice ↔ z • w' ∈ u'.Λ)) ∧ ∀ s : R →+* ℂ, s W.c₄ = 12 * (Lf s).g₂ ∧ s W.c₆ = 216 * (Lf s).g₃ ∧ s W.Δ = (Lf s).g₂ ^ 3 - 27 * (Lf s).g₃ ^ 2) := by
  first | exact @GlobalTheory.exists_polAV_latticeFamily | exact GlobalTheory.exists_polAV_latticeFamily | (intros; apply GlobalTheory.exists_polAV_latticeFamily <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.exists_completeDVR_completion_integral_iff : ∀ (K : Type) [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)), ∃ (T : CDVR) (iK : K →+* T.Fr), T.FinRes ∧ ∀ y : K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation K y ≤ 1 := by
  first | exact @GlobalTheory.exists_cdvr_completion_integral_iff | exact GlobalTheory.exists_cdvr_completion_integral_iff | (intros; apply GlobalTheory.exists_cdvr_completion_integral_iff <;> assumption)
end
