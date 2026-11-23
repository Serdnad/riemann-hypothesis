module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1111
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1102
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBidualNaturalityDualSheafTranspose
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle002

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

theorem surjective_spMap_of_sq {A B : Type} [CommRing A] [CommRing B] (π : A →+* B) (hπ : Function.Surjective π)
    (hsq : ∀ a ∈ RingHom.ker π, a * a = 0) : Function.Surjective (spMap π) := fun x ↦ by
  have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker π : Set A) := fun a ha ↦
    (x.isPrime.mem_or_mem ((hsq a ha).symm ▸ x.asIdeal.zero_mem)).elim id id
  rw [← range_comap_of_surjective B π hπ] at hx
  exact hx

theorem pt_dual_le_of_fst : ∀ (R : Type) [CommRing R] (H : Over (Sp R)) (D : Type) [CommRing D] [Algebra R D]
      (Z : Over.mk (spMap (algebraMap R (DualNumber D))) ⟶ H) (U : H.left.Opens),
      ⊤ ≤ (spOver (TrivSqZeroExt.fstHom R D D) ≫ Z).left ⁻¹ᵁ U → ⊤ ≤ Z.left ⁻¹ᵁ U := by
  intro R _ H D _ _ Z U h x _
  have hs : Function.Surjective (spMap ((TrivSqZeroExt.fstHom R D D : DualNumber D →ₐ[R] D) : DualNumber D →+* D)) :=
    surjective_spMap_of_sq _ (fun d ↦ ⟨TrivSqZeroExt.inl d, rfl⟩) fun a ha ↦ by
      have h0 : a.fst = 0 := ha
      ext <;> simp [h0]
  obtain ⟨y, rfl⟩ := hs x
  have hy := h (show y ∈ (⊤ : (Sp D).Opens) from trivial)
  simpa [Over.comp_left, PDiv.spOver_left] using hy

end GlobalTheory.PtExt
end
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.isPsEff_pull_reduced_closed_of_dim_le : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ), (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k (X := Y)) → topologicalKrullDim Y ≤ (d : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) → ∀ (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ M : LB X, IsNef k M → ∀ Z : Closeds X, IsIrreducible (Z : Set X) → topologicalKrullDim (Z : Set X) ≤ (d : ℕ) → IsPsEff (M.pull (redι Z)) := by
  first | exact @GlobalTheory.IsNef.isPsEff_pull_red_of_dim_le | exact GlobalTheory.IsNef.isPsEff_pull_red_of_dim_le | (intros; apply GlobalTheory.IsNef.isPsEff_pull_red_of_dim_le <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.isPseudoEffective_reducedUniv_of_section_pow : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (M : LB X), M.IsLB → ∀ r : ℕ, 1 ≤ r → HasNonzeroSec (lbPow M r) → ∀ Z : Closeds X, (Z : Set X) = Set.univ → IsPsEff (M.pull (redι Z)) := by
  first | exact @GlobalTheory.isPsEff_pull_redι_univ_of_hasNonzeroSec_pow | exact GlobalTheory.isPsEff_pull_redι_univ_of_hasNonzeroSec_pow | (intros; apply GlobalTheory.isPsEff_pull_redι_univ_of_hasNonzeroSec_pow <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.lineBundleIntersectionNumber_ample_cons_nef_nonneg : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ P : Fin d → LB X, (∀ i, IsNef k (P i)) → 0 ≤ interNum k E P) → ∀ A : LB X, IsAmpleLB A → (∀ P : Fin d → LB X, (∀ i, IsNef k (P i)) → 0 ≤ interNum k (GlobalTheory.structureModule X) (Fin.cons A P : Fin (d + 1) → LB X)) := by
  first | exact @GlobalTheory.interNum_cons_ample_nef_nonneg | exact GlobalTheory.interNum_cons_ample_nef_nonneg | (intros; apply GlobalTheory.interNum_cons_ample_nef_nonneg <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.lineBundleIntersectionNumber_nonneg_of_ample : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∀ P : Fin d → LB X, (∀ i, IsAmpleLB (P i)) → 0 ≤ interNum k F P := by
  first | exact @GlobalTheory.interNum_nonneg_of_isAmpleLB_of_isProjOver | exact GlobalTheory.interNum_nonneg_of_isAmpleLB_of_isProjOver | (intros; apply GlobalTheory.interNum_nonneg_of_isAmpleLB_of_isProjOver <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.sheafCohomologyDim_twist_bound_of_shortExact : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (L : LB X), L.IsLB → ∀ S : ShortComplex X.Modules, S.ShortExact → IsFiniteQC S.X₁ → IsFiniteQC S.X₃ → ∀ (i : ℕ) (e : ℕ → ℕ), (∃ C : ℕ, ∀ m : ℕ, hdim k (twist S.X₁ (lbPow L m)) i ≤ C * e m) → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist S.X₃ (lbPow L m)) i ≤ C * e m) → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist S.X₂ (lbPow L m)) i ≤ C * e m) := by
  first | exact @GlobalTheory.hdim_twist_bound_of_shortExact | exact GlobalTheory.hdim_twist_bound_of_shortExact | (intros; apply GlobalTheory.hdim_twist_bound_of_shortExact <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.multiplication_lifts_square_zero_smooth_lift : FormSt → AxesVanishingExtendedDegOne → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (A₀ : Over (Sp R₀)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → ∀ (X : Over (Sp R)) (i : A₀.left ⟶ X.left), IsPullback i A₀.hom X.hom (spMap π) → Smooth X.hom → ∀ (e : Sp R ⟶ X.left), e ≫ X.hom = 𝟙 _ → (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left ≫ i = spMap π ≫ e → ∀ (l : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left), l ≫ (fst X X).left = (fst A₀ A₀).left ≫ i → l ≫ (snd X X).left = (snd A₀ A₀).left ≫ i → ∃ m : X ⊗ X ⟶ X, l ≫ m.left = (μ[A₀]).left ≫ i := by
  first | exact @GlobalTheory.Obs.mul_lifts | exact GlobalTheory.Obs.mul_lifts | (intros; apply GlobalTheory.Obs.mul_lifts <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.laurentCohomology_vanishing_of_noetherian_henselian : ∀ (q : ℕ) [NeZero q], (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i)) → ∀ (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i) := by
  first | (exact @GlobalTheory.EtC.laurent_vanishing_of_noetherian) | (exact GlobalTheory.EtC.laurent_vanishing_of_noetherian) | (intros; apply GlobalTheory.EtC.laurent_vanishing_of_noetherian  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_unit_kummer_eq_of_picard_torsionFree : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → (∀ c : CommRing.Pic A, c ^ q = 1 → c = 1) → ∀ x : Ht q (sp A) 1 1, ∃ u : (Γ(Spec (CommRingCat.of A), ⊤))ˣ, kum q u = x := by
  first | (exact @GlobalTheory.EtC.kum_surjective) | (exact GlobalTheory.EtC.kum_surjective) | (intros; apply GlobalTheory.EtC.kum_surjective <;> assumption)
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB
open GlobalTheory.Twist (resM resM_resM resM_smul app_resM germ_resM)
open GlobalTheory.QCoh (appLinear appLinear_apply)

namespace GlobalTheory.DualExact

variable {X : Scheme.{0}}

theorem exists_local_section {F G : X.Modules} (φ : F ⟶ G) [Epi φ] {s : ℕ} (hG : IsVB G s)
    {V : X.Opens} {x : X} (hx : x ∈ V) :
    ∃ (U : X.Opens), U ≤ V ∧ x ∈ U ∧
      ∃ σ : ∀ W : X.Opens, W ≤ U → (Γ(G, W) →ₗ[Γ(X, W)] Γ(F, W)),
        (∀ (W W' : X.Opens) (h : W ≤ U) (h' : W' ≤ W) (t : Γ(G, W)),
          σ W' (h'.trans h) (resM G h' t) = resM F h' (σ W h t)) ∧
        ∀ (W : X.Opens) (h : W ≤ U) (t : Γ(G, W)), φ.app W (σ W h t) = t := by
  obtain ⟨U, e, -, hxU, hle, he⟩ := hG.exists_affine hx
  choose T hT hxT a ha using fun i => exists_app_eq_of_epi φ (e i) hxU
  let U' : X.Opens := U ⊓ Finset.univ.inf T
  have hx' : x ∈ U' := ⟨hxU, by rw [Opens.coe_finset_inf]; simpa using hxT⟩
  have hU' (i) : U' ≤ T i := inf_le_right.trans (Finset.inf_le (Finset.mem_univ i))
  have hU : U' ≤ U := inf_le_left
  refine ⟨U', hU.trans hle, hx', fun W h =>
    (he.basis (h.trans hU)).constr Γ(X, W) fun i => resM F (h.trans (hU' i)) (a i),
    fun W W' h h' t => ?_, fun W h t => ?_⟩

  · simp only [Module.Basis.constr_apply_fintype, Module.Basis.equivFun_apply, map_sum,
    resM_smul, resM_resM]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← he.repr_resM (h.trans hU) h']
  · rw [← appLinear_apply]

    simp only [Module.Basis.constr_apply_fintype, Module.Basis.equivFun_apply, map_sum,
    map_smul, appLinear_apply, app_resM, ha, resM_resM]
    conv_rhs => rw [← (he.basis (h.trans hU)).sum_repr t]
    simp only [IsFrame.basis_apply]

theorem exact_of_locally (S : ShortComplex X.Modules)
    (H : ∀ (V : X.Opens) (x : X), x ∈ V → ∃ U : X.Opens, U ≤ V ∧ x ∈ U ∧
      ∀ t : Γ(S.X₂, U), S.g.app U t = 0 → ∃ u, S.f.app U u = t) : S.Exact := by
  refine (QCoh.exact_iff_stalkLinear S).2 fun x t => ⟨fun ht => ?_, ?_⟩
  · obtain ⟨V, hV, t, rfl⟩ := S.X₂.presheaf.exists_germ_eq t
    rw [QCoh.stalkLinear_germ, ← map_zero (S.X₃.presheaf.germ V x hV).hom] at ht
    obtain ⟨V', hV', i₁, i₂, e⟩ := S.X₃.presheaf.germ_eq x hV hV _ _ ht
    have e' : resM S.X₃ i₁.le (S.g.app V t) = 0 := e.trans (map_zero _)
    obtain ⟨U, hU, hxU, HU⟩ := H V' x hV'
    obtain ⟨u, hu⟩ := HU (resM S.X₂ (hU.trans i₁.le) t) (by
      rw [app_resM, ← resM_resM i₁.le hU, e', map_zero])
    exact ⟨S.X₁.presheaf.germ U x hxU u, by rw [QCoh.stalkLinear_germ, hu, germ_resM]⟩
  · rintro ⟨u, rfl⟩
    rw [← LinearMap.comp_apply, ← QCoh.stalkLinear_comp, S.zero, QCoh.stalkLinear_zero,
      LinearMap.zero_apply]

theorem shortExact_dual : ∀ (X : Scheme.{0}) (S : ShortComplex X.Modules) (s : ℕ),
    S.ShortExact → IsVB S.X₃ s → (ShortComplex.mk (dualMap S.g) (dualMap S.f)
      (by rw [← dualMap_comp, S.zero, dualMap_zero])).ShortExact := by
  intro X S s hS h₃
  have := hS.mono_f
  have := hS.epi_g
  have hex (W : X.Opens) (t : Γ(S.X₂, W)) (ht : S.g.app W t = 0) : ∃ u, S.f.app W u = t :=
    (QCoh.exact_app_of_exact_of_mono hS.exact W t).1 ht
  have hz (W : X.Opens) (u : Γ(S.X₁, W)) : S.g.app W (S.f.app W u) = 0 :=
    (QCoh.exact_app_of_exact_of_mono hS.exact W _).2 ⟨u, rfl⟩
  have hinj (W : X.Opens) : Function.Injective (appLinear S.f W) :=
    QCoh.injective_app_of_mono S.f W
  refine ShortComplex.ShortExact.mk' (exact_of_locally _ fun V x hx => ?_)
    (mono_dualMap S.g) (QCoh.epi_of_locally_app_surjective _ fun V x hx => ?_)
  · obtain ⟨U, hU, hxU, σ, hσ, hg⟩ := exists_local_section S.g h₃ hx
    refine ⟨U, hU, hxU, fun (l : Γ(dual S.X₂, U)) (hl : (dualMap S.f).app U l = 0) =>
      ⟨dualMk (fun W h => dualApp l h ∘ₗ σ W h) fun W W' h h' t => ?_, ?_⟩⟩
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, hσ W W' h h', dualApp_resM]
    · refine dual_ext fun W h t => ?_
      change dualApp l h (σ W h (S.g.app W t)) = _
      obtain ⟨u, hu⟩ := hex W (t - σ W h (S.g.app W t)) (by rw [map_sub, hg, sub_self])
      have := dualApp_dualMap S.f l h u
      rw [hl, hu, map_sub, dualApp_zero, LinearMap.zero_apply, eq_comm, sub_eq_zero] at this
      exact this.symm
  · obtain ⟨U, hU, hxU, σ, hσ, hg⟩ := exists_local_section S.g h₃ hx
    let ρ (W : X.Opens) (h : W ≤ U) : Γ(S.X₂, W) →ₗ[Γ(X, W)] Γ(S.X₁, W) :=
      LinearMap.codRestrictOfInjective (LinearMap.id - σ W h ∘ₗ appLinear S.g W)
        (appLinear S.f W) (hinj W) fun t => hex W _ (by
          change S.g.app W (t - σ W h (S.g.app W t)) = 0
          rw [map_sub, hg, sub_self])
    have hρ (W : X.Opens) (h : W ≤ U) (t : Γ(S.X₂, W)) :
        S.f.app W (ρ W h t) = t - σ W h (S.g.app W t) :=
      LinearMap.codRestrictOfInjective_comp_apply _ (appLinear S.f W) _ _ t
    refine ⟨U, hxU, hU, fun (l : Γ(dual S.X₁, U)) =>
      ⟨dualMk (fun W h => dualApp l h ∘ₗ ρ W h) fun W W' h h' t => ?_, ?_⟩⟩
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, ← dualApp_resM]
      congr 1
      apply hinj W'
      rw [appLinear_apply, appLinear_apply, app_resM, hρ, hρ, map_sub, app_resM, hσ W W' h h']
    · refine dual_ext fun W h u => ?_
      change dualApp l h (ρ W h (S.f.app W u)) = _
      congr 1
      apply hinj W
      rw [appLinear_apply, appLinear_apply, hρ, hz, map_zero, sub_zero]

end GlobalTheory.DualExact
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (appLinear appLinear_apply)

namespace GlobalTheory.VBExt

section Algebra

variable {R A B C : Type} [CommRing R] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module R A] [Module R B] [Module R C] {f : A →ₗ[R] B} {g : B →ₗ[R] C}
  {ι κ : Type} [Fintype ι] [Fintype κ]

theorem bijective_sumElim (hfg : Function.Exact f g) (hf : Function.Injective f)
    (a : Module.Basis ι R A) (c : Module.Basis κ R C) (t : κ → B) (ht : ∀ k, g (t k) = c k) :
    Function.Bijective (Fintype.linearCombination R (Sum.elim (fun i => f (a i)) t)) := by
  have hg (x : ι ⊕ κ → R) : g (Fintype.linearCombination R (Sum.elim (fun i => f (a i)) t) x) =
      ∑ k, x (.inr k) • c k := by
    simp [Fintype.linearCombination_apply, Fintype.sum_sum_type, hfg.apply_apply_eq_zero, ht]
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    have h2 : ∀ k, x (.inr k) = 0 :=
      Fintype.linearIndependent_iff.1 c.linearIndependent _ (by rw [← hg, hx, map_zero])
    have h1 : ∀ i, x (.inl i) = 0 :=
      Fintype.linearIndependent_iff.1 a.linearIndependent _ (hf (by
        simpa [Fintype.linearCombination_apply, Fintype.sum_sum_type, h2] using hx))
    funext j
    rcases j with i | k
    exacts [h1 i, h2 k]
  · intro y
    obtain ⟨z, hz⟩ := (hfg (y - ∑ k, c.repr (g y) k • t k)).1 (by
      simp [ht])
    refine ⟨Sum.elim (a.repr z) (c.repr (g y)), ?_⟩
    have : ∑ i, a.repr z i • f (a i) = f z := by
      conv_rhs => rw [← a.sum_repr z]

      simp only [map_sum, map_smul]
    simp [Fintype.linearCombination_apply, Fintype.sum_sum_type, this, hz]

theorem det_sumElim [DecidableEq ι] [DecidableEq κ] (hfg : ∀ x, g (f x) = 0)
    (a : Module.Basis ι R A) (c : Module.Basis κ R C) (b : Module.Basis (ι ⊕ κ) R B)
    (hb : ∀ i, b (.inl i) = f (a i)) (hc : ∀ k, g (b (.inr k)) = c k) (a' : ι → A) (t' : κ → B) :
    b.det (Sum.elim (fun i => f (a' i)) t') = a.det a' * c.det fun k => g (t' k) := by
  have h1 (x : A) : ⇑(b.repr (f x)) = Sum.elim (a.repr x) 0 := by
    have : f x = ∑ j, Sum.elim (a.repr x) 0 j • b j := by
      conv_lhs => rw [← a.sum_repr x]

      simp only [Fintype.sum_sum_type, hb, map_sum, map_smul, Sum.elim_inl, Sum.elim_inr,
      Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
    rw [this, b.repr_sum_self]
  have h2 (y : B) (k : κ) : b.repr y (.inr k) = c.repr (g y) k := by
    have : g y = ∑ k, b.repr y (.inr k) • c k := by
      conv_lhs => rw [← b.sum_repr y]

      simp only [Fintype.sum_sum_type, hb, hc, hfg, map_sum, map_smul, map_add (f := _), smul_zero,
      Finset.sum_const_zero, zero_add]
    rw [this, c.repr_sum_self]
  rw [Module.Basis.det_apply, Module.Basis.det_apply, Module.Basis.det_apply,
    ← Matrix.det_fromBlocks_zero₂₁ _ (Matrix.of fun i k => b.repr (t' k) (.inl i))]
  congr 1
  ext (i | i) (j | j) <;> simp [Module.Basis.toMatrix_apply, h1, h2, hfg]

end Algebra

variable {X : Scheme.{0}} {S : ShortComplex X.Modules} {U U' V : X.Opens} {r s : ℕ}

theorem isFrame_sumElim (hS : S.ShortExact) {ι κ : Type} [Fintype ι] [Fintype κ]
    {e : ι → Γ(S.X₁, U)} {t : κ → Γ(S.X₂, U)} (he : IsFrame e)
    (ht : IsFrame fun k => S.g.app U (t k)) :
    IsFrame (Sum.elim (fun i => S.f.app U (e i)) t) := fun V h => by
  have := hS.mono_f
  have key := bijective_sumElim (f := appLinear S.f V) (g := appLinear S.g V)
    (QCoh.exact_app_of_exact_of_mono hS.exact V) (QCoh.injective_app_of_mono S.f V)
    (he.basis h) (ht.basis h) (fun k => resM _ h (t k))
    (fun k => by rw [IsFrame.basis_apply, appLinear_apply, app_resM])
  convert key using 3
  funext j
  rcases j with i | k
  · simp only [Sum.elim_inl, IsFrame.basis_apply, appLinear_apply, app_resM]
  · rfl

theorem detUnit_sumElim (hS : S.ShortExact) {e : Fin r → Γ(S.X₁, U)} {t : Fin s → Γ(S.X₂, U)}
    (he : IsFrame e) (ht : IsFrame fun k => S.g.app U (t k)) {e' : Fin r → Γ(S.X₁, U')}
    {t' : Fin s → Γ(S.X₂, U')} (he' : IsFrame e') (ht' : IsFrame fun k => S.g.app U' (t' k))
    (h : V ≤ U) (h' : V ≤ U') :
    ((isFrame_sumElim hS he ht).comp_equiv finSumFinEquiv.symm).detUnit
      ((isFrame_sumElim hS he' ht').comp_equiv finSumFinEquiv.symm) h h' =
      he.detUnit he' h h' * ht.detUnit ht' h h' := by
  have := hS.mono_f
  refine Units.ext ?_
  have e₁ : ((isFrame_sumElim hS he ht).comp_equiv finSumFinEquiv.symm).basis h =
      ((isFrame_sumElim hS he ht).basis h).reindex finSumFinEquiv :=
    DFunLike.ext _ _ fun k => by simp
  have key := det_sumElim (f := appLinear S.f V) (g := appLinear S.g V)
    (QCoh.exact_app_of_exact_of_mono hS.exact V).apply_apply_eq_zero
    (he.basis h) (ht.basis h) ((isFrame_sumElim hS he ht).basis h)
    (fun i => by simp only [Sum.elim_inl, IsFrame.basis_apply, appLinear_apply, app_resM])
    (fun i => by simp only [Sum.elim_inr, IsFrame.basis_apply, appLinear_apply, app_resM])
    (fun i => resM _ h' (e' i)) (fun k => resM _ h' (t' k))
  simp only [appLinear_apply, app_resM] at key
  rw [Units.val_mul, IsFrame.val_detUnit, IsFrame.val_detUnit, IsFrame.val_detUnit, e₁,
    Module.Basis.det_reindex, ← key]
  congr 1
  funext j
  rcases j with i | k <;> simp

theorem exists_lifts {F G : X.Modules} (φ : F ⟶ G) [Epi φ] {κ : Type} [Fintype κ]
    (c : κ → Γ(G, U)) {x : X} (hx : x ∈ U) :
    ∃ (W : X.Opens) (h : W ≤ U), x ∈ W ∧ ∃ t : κ → Γ(F, W), ∀ k, φ.app W (t k) = resM G h (c k) := by
  choose W hW hxW t ht using fun k => exists_app_eq_of_epi φ (c k) hx
  have hV (k : κ) : U ⊓ Finset.univ.inf W ≤ W k :=
    inf_le_right.trans (Finset.inf_le (Finset.mem_univ k))
  refine ⟨U ⊓ Finset.univ.inf W, inf_le_left, ⟨hx, by
    rw [Opens.coe_finset_inf]; simpa using hxW⟩, fun k => resM F (hV k) (t k), fun k => ?_⟩
  rw [app_resM, ht, resM_resM]


variable (S r s) in
structure AdaptedChart where

  U : X.Opens

  e : Fin r → Γ(S.X₁, U)

  t : Fin s → Γ(S.X₂, U)

  he : IsFrame e

  ht : IsFrame fun k => S.g.app U (t k)

theorem exists_adaptedChart (hS : S.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) (x : X) :
    ∃ c : AdaptedChart S r s, x ∈ c.U := by
  have := hS.epi_g
  obtain ⟨U, e, hx, he⟩ := h₁ x
  obtain ⟨U', c, -, hx', hle, hc⟩ := h₃.exists_affine hx
  obtain ⟨W, h, hxW, t, ht⟩ := exists_lifts S.g c hx'
  exact ⟨⟨W, _, t, he.res (h.trans hle), by rw [funext ht]; exact hc.res h⟩, hxW⟩

theorem isVB_and_cls_det_of_shortExact (X : Scheme.{0}) (S : ShortComplex X.Modules) (r s : ℕ)
    (hS : S.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) :
    ∃ h₂ : IsVB S.X₂ (r + s),
      CechPic.cls _ h₂.isLB_det = CechPic.cls _ h₁.isLB_det + CechPic.cls _ h₃.isLB_det := by
  have hb (c : AdaptedChart S r s) := (isFrame_sumElim hS c.he c.ht).comp_equiv finSumFinEquiv.symm
  let L : LB X :=
    { ι := AdaptedChart S r s
      U := fun c => c.U
      g := fun c c' => (hb c).detUnit (hb c') inf_le_left inf_le_right }
  have hL : L.IsLB := by
    refine ⟨top_le_iff.1 fun x _ => ?_, fun c => ?_, fun c c' c'' => ?_⟩
    · exact Opens.mem_iSup.2 (exists_adaptedChart hS h₁ h₃ x)
    · exact (IsFrame.res_detUnit _ _ _ _ _).trans ((hb c).detUnit_self _ _)
    · exact (congrArg₂ (· * ·) (IsFrame.res_detUnit _ _ _ _ _)
        (IsFrame.res_detUnit _ _ _ _ _)).trans
        ((IsFrame.detUnit_mul _ _ _ _ _ _).trans (IsFrame.res_detUnit _ _ _ _ _).symm)
  obtain ⟨h₂, hi⟩ := lbIso_det_of_frames hL _ hb fun _ _ => rfl
  have hT := CechPic.isLB_tens h₁.isLB_det h₃.isLB_det
  have hj : LBIso L (CechPic.tens (det S.X₁ r) (det S.X₃ s)) := CechPic.iso_of_chart hT
    ⟨fun c => (⟨c.U, c.e, c.he⟩, ⟨c.U, _, c.ht⟩), fun _ _ h => ⟨h, h⟩, fun y c c' hc hc' =>
      ((congrArg _ (detUnit_sumElim hS c.he c.ht c'.he c'.ht _ _)).trans (map_mul _ _ _)).trans
        (CechPic.gm_tens (det S.X₁ r) (det S.X₃ s) (𝟙 X) y (⟨c.U, c.e, c.he⟩, ⟨c.U, _, c.ht⟩)
          (⟨c'.U, c'.e, c'.he⟩, ⟨c'.U, _, c'.ht⟩) ⟨hc, hc⟩ ⟨hc', hc'⟩).symm⟩
  exact ⟨h₂, ((CechPic.cls_eq_iff hL _).2 hi).symm.trans ((CechPic.cls_eq_iff hL hT).2 hj)⟩

end GlobalTheory.VBExt
end
end

section

open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory

noncomputable section

namespace GlobalTheory.DetInv

open GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta (epsTate epsEquiv epsPairing toO pairingO bQuot Realizes)

section Group

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (G : PDivGroup p O)

theorem pairing_dual_bidual (t : G.Tate) (u : G.dual.Tate) :
    pairing G.dual O u (tateMap G G.dual.dual O G.bidual.hom t) = pairing G O t u :=
  muRoot_ext fun n => by
    rw [muRoot_pairing, muRoot_pairing]
    have h1 : charElem (G := G.dual) (tateMap G G.dual.dual O G.bidual.hom t) n =
        WithConv.toConv (t.pt n).toLinearMap :=
      (charHom_app_muT _ n).symm.trans (dualChar_app_muT t n)
    rw [h1]
    exact (apply_charElem u n _).symm

end Group

end GlobalTheory.DetInv
end
end
