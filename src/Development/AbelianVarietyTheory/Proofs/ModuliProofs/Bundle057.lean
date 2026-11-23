module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle052
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle049
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomFromSpecResidueField
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle008
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle053
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

namespace GlobalTheory.ZM.NearBuild

theorem exists_smul_mem_range_of_unique_point (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
    [Module.Finite R B] [Algebra.FormallyUnramified R B] (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K)
    (y : B →+* K) (hy : y.comp (algebraMap R B) = x) (hu : ∀ z : B →+* K, z.comp (algebraMap R B) = x → z = y) :
    ∃ f : R, f ∉ RingHom.ker x ∧ ∀ b : B, ∃ a : R, algebraMap R B a = algebraMap R B f * b := by
  let _ : Algebra R K := x.toAlgebra
  let yA : B →ₐ[R] K := { y with commutes' := fun r => RingHom.congr_fun hy r }
  let φ : K ⊗[R] B →ₐ[K] K :=
    Algebra.TensorProduct.lift (Algebra.ofId K K) yA (fun _ _ => Commute.all _ _)
  have hall : ∀ ψ : K ⊗[R] B →ₐ[K] K, ∀ (a : K) (b : B), ψ (a ⊗ₜ[R] b) = a * y b := by
    intro ψ a b
    have hz : ((ψ.restrictScalars R).comp Algebra.TensorProduct.includeRight).toRingHom = y := by
      apply hu
      ext r
      exact ((ψ.restrictScalars R).comp Algebra.TensorProduct.includeRight).commutes r
    have h1 : ψ ((1 : K) ⊗ₜ[R] b) = y b := by
      have := RingHom.congr_fun hz b
      simpa using this
    have h2 : a ⊗ₜ[R] b = a • ((1 : K) ⊗ₜ[R] b) := by
      rw [TensorProduct.smul_tmul']
      simp
    rw [h2, map_smul, h1, _root_.smul_eq_mul]
  have huniq : ∀ ψ : K ⊗[R] B →ₐ[K] K, ψ = φ := by
    intro ψ
    refine AlgHom.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rw [hall ψ, hall φ]
    | add s t hs ht => rw [map_add (f := _), map_add (f := _), hs, ht]
  have hsurj := algebraMap_surjective_of_unramified_of_unique_point K (K ⊗[R] B) φ huniq
  set N : Submodule R B := LinearMap.range (Algebra.linearMap R B) with hN
  have hone : N.mkQ (1 : B) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr ⟨1, by simp⟩
  have hzero : ∀ t : K ⊗[R] (B ⧸ N), t = 0 := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rfl
    | tmul a c =>
      obtain ⟨b, rfl⟩ := N.mkQ_surjective c
      obtain ⟨c', hc'⟩ := hsurj (a ⊗ₜ[R] b)
      rw [← LinearMap.lTensor_tmul, ← hc', Algebra.TensorProduct.algebraMap_apply, LinearMap.lTensor_tmul, hone,
        TensorProduct.tmul_zero]
    | add s t hs ht => rw [hs, ht, add_zero]
  let p : PrimeSpectrum R := ⟨RingHom.ker x, RingHom.ker_isPrime x⟩
  have hns : p ∉ Module.support R (B ⧸ N) := by
    intro h
    have hnt := nontrivial_tensor_of_mem_support R (B ⧸ N) K p rfl h
    obtain ⟨s, t, hst⟩ := hnt.exists_pair_ne
    exact hst ((hzero s).trans (hzero t).symm)
  rw [Module.mem_support_iff_of_finite] at hns
  obtain ⟨f, hf, hfp⟩ := Set.not_subset.mp hns
  refine ⟨f, hfp, fun b => ?_⟩
  have hfb : f • N.mkQ b = 0 := Module.mem_annihilator.mp hf _
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hfb
  obtain ⟨a, ha⟩ := hfb
  exact ⟨a, by rw [← Algebra.smul_def, ← ha, Algebra.linearMap_apply]⟩

theorem exists_retraction_away (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
    (hinj : Function.Injective (algebraMap R B)) (f : R)
    (hf : ∀ b : B, ∃ a : R, algebraMap R B a = algebraMap R B f * b) :
    ∃ r : B →+* Localization.Away f, r.comp (algebraMap R B) = loc f := by
  choose a ha using hf
  set g : Localization.Away f := IsLocalization.Away.invSelf f with hg
  have hfg : loc f f * g = 1 := IsLocalization.Away.mul_invSelf f
  have ha_zero : a 0 = 0 := hinj (by simp only [ha, MulZeroClass.mul_zero, map_zero])
  have ha_one : a 1 = f := hinj (by simp only [ha, _root_.mul_one])
  have ha_add : ∀ b c, a (b + c) = a b + a c := fun b c => hinj (by simp only [ha, map_add (f := _)]; ring)
  have ha_mul : ∀ b c, f * a (b * c) = a b * a c := fun b c => hinj (by simp only [ha, map_mul]; ring)
  have ha_alg : ∀ c, a (algebraMap R B c) = f * c := fun c => hinj (by simp only [ha, map_mul])
  have h_one : loc f (a 1) * g = 1 := by rw [ha_one, hfg]
  have h_mul : ∀ b c, loc f (a (b * c)) * g = loc f (a b) * g * (loc f (a c) * g) := by
    intro b c
    have h := congrArg (loc f) (ha_mul b c)
    rw [map_mul, map_mul] at h
    linear_combination (-(loc f (a (b * c)) * g)) * hfg + g * g * h
  have h_zero : loc f (a 0) * g = 0 := by rw [ha_zero, map_zero, MulZeroClass.zero_mul]
  have h_add : ∀ b c, loc f (a (b + c)) * g = loc f (a b) * g + loc f (a c) * g := by
    intro b c
    rw [ha_add, map_add (f := _), add_mul]
  let r : B →+* Localization.Away f :=
    { toFun := fun b => loc f (a b) * g
      map_one' := h_one
      map_mul' := h_mul
      map_zero' := h_zero
      map_add' := h_add }
  refine ⟨r, ?_⟩
  · ext c
    show loc f (a (algebraMap R B c)) * g = loc f c
    rw [ha_alg, map_mul]
    linear_combination (loc f c) * hfg

theorem exists_retraction_near_of_unique_point :
    ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] [Module.Finite R B] [Algebra.FormallyUnramified R B] (P : Set (Ideal R)), DenseP P → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K), RingHom.ker x = q ∧ ∃! y : B →+* K, y.comp (algebraMap R B) = x) → ∀ q₀ ∈ P, ∃ f : R, f ∉ q₀ ∧ ∃ r : B →+* Localization.Away f, r.comp (algebraMap R B) = loc f ∧ ∀ (T : Type) [CommRing T] (x : Localization.Away f →+* T) (y : B →+* T), y.comp (algebraMap R B) = x.comp (loc f) → y = x.comp r := by
  intro R B _ _ _ _ _ P hD hP q₀ hq₀
  obtain ⟨K, _, _, x, hker, y, hy, hu⟩ := hP q₀ hq₀
  obtain ⟨f, hfk, hfB⟩ := exists_smul_mem_range_of_unique_point R B K x y hy hu
  have hinj : Function.Injective (algebraMap R B) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    refine hD a fun p hp _ => ?_
    obtain ⟨K', _, _, x', hker', y', hy', -⟩ := hP p hp
    rw [← hker', RingHom.mem_ker, ← hy', RingHom.comp_apply, ha, map_zero]
  obtain ⟨r, hr⟩ := exists_retraction_away R B hinj f hfB
  refine ⟨f, hker ▸ hfk, r, hr, fun T _ x' y' hxy => ?_⟩
  ext b
  obtain ⟨a, ha⟩ := hfB b
  have h1 : y' (algebraMap R B a) = x' (loc f a) := RingHom.congr_fun hxy a
  have h2 : y' (algebraMap R B f) = x' (loc f f) := RingHom.congr_fun hxy f
  have h3 : loc f a = loc f f * r b := by
    rw [← RingHom.congr_fun hr a, ← RingHom.congr_fun hr f, RingHom.comp_apply, RingHom.comp_apply, ha, map_mul]
  have hU : IsUnit (x' (loc f f)) := (IsLocalization.Away.algebraMap_isUnit f).map x'
  apply hU.mul_left_cancel
  rw [RingHom.comp_apply, ← map_mul, ← h3, ← h1, ha, map_mul, h2]

end GlobalTheory.ZM.NearBuild
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

theorem _root_.GlobalTheory.T.exists_unique_factor_through_etale_isogeny_reduced : ∀ (S : Scheme.{0}) [IsReduced S] (A B B' : Over S) [GrpObj A] [GrpObj B] [GrpObj B'] (ψ : A ⟶ B) (g : A ⟶ B'), IsAbelianScheme A → IsAbelianScheme B → IsSeparated B'.hom → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → IsMonHom g → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (x : Over.mk t ⟶ A), x ≫ ψ = 1 → x ≫ g = 1) → ∃ g' : B ⟶ B', IsMonHom g' ∧ ψ ≫ g' = g ∧ ∀ g'' : B ⟶ B', ψ ≫ g'' = g → g'' = g' := by
  first | exact @GlobalTheory.HkFactor.exists_unique_factor | exact GlobalTheory.HkFactor.exists_unique_factor | (intros; apply GlobalTheory.HkFactor.exists_unique_factor <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.AmpleFibre

open TopologicalSpace GlobalTheory.MulFinite

theorem exists_fn {X Z : Scheme.{0}} (L : LB X) (hL : L.IsLB) (N : ℕ)
    (s : LB.Sec (LB.LinComb L (K := Fin N) (fun _ => 𝟙 X) (fun _ => 1))) (r : Z ⟶ X)
    (t : (L.pull r).Gen) (ht : t.IsGen) :
    ∃ a : Γ(Z, ⊤), Z.basicOpen a = r ⁻¹ᵁ Out.nonzeroLocus s := by
  let V : L.ι → Z.Opens := fun j => r ⁻¹ᵁ L.U j
  have l₁ : ∀ j, V j ≤ r ⁻¹ᵁ LB.wchart L (K := Fin N) (fun _ => 𝟙 X) (fun _ => j) :=
    fun j z hz => Set.mem_iInter.2 fun _ => hz
  have l₂ : ∀ j, V j ≤ LB.wchart L (K := PUnit) (fun _ => r) (fun _ => j) :=
    fun j z hz => Set.mem_iInter.2 fun _ => hz
  obtain ⟨u, hu⟩ : ∃ u : ∀ j, Γ(Z, V j), ∀ j z, z ∈ V j → gs (𝟙 Z) z (V j) (u j) =
      gs r z (LB.wchart L (K := Fin N) (fun _ => 𝟙 X) (fun _ => j)) (s.f (fun _ => j)) *
        ((gm (𝟙 Z) z (LB.wchart L (K := PUnit) (fun _ => r) (fun _ => j)) (t.s (fun _ => j)))⁻¹).val ^ N := by
    refine ⟨fun j => (r.appLE _ _ (l₁ j)).hom (s.f (fun _ => j)) *
      (Z.presheaf.map (homOfLE (l₂ j)).op).hom ((t.s (fun _ => j))⁻¹).val ^ N, fun j z hz => ?_⟩
    refine (gs_mul (𝟙 Z) z (V j) hz _ _).trans (congrArg₂ (· * ·) (gs_appLE r z _ _ _ hz _)
      ((gs_pow (𝟙 Z) z (V j) hz _ _).trans ?_))
    erw [gs_res (𝟙 Z) z (l₂ j) hz, gs_unit (𝟙 Z) z _ (l₂ j hz)]
    exact congrArg (fun x : (Z.presheaf.stalk z)ˣ => x.val ^ N)
      (map_inv (gm (𝟙 Z) z _ ) (t.s (fun _ => j)))
  have hcov : (⊤ : Z.Opens) ≤ iSup V := fun z _ => by
    obtain ⟨j, hj⟩ := exists_chart hL (r z)
    exact Opens.mem_iSup.2 ⟨j, hj⟩
  obtain ⟨a, ha, -⟩ := Z.sheaf.existsUnique_gluing' V ⊤ (fun j => homOfLE le_top) hcov u
    (fun j j' => fn_ext (V := V j ⊓ V j') fun z hz => by
      refine (gs_res (𝟙 Z) z inf_le_left hz _).trans (Eq.trans ?_ (gs_res (𝟙 Z) z inf_le_right hz _).symm)
      rw [hu j z hz.1, hu j' z hz.2, sec_trans s r z (l₁ j hz.1) (l₁ j' hz.2),
        gen_trans ht (𝟙 Z) z (l₂ j hz.1) (l₂ j' hz.2)]
      have t₁ : trF (L := L) (K := Fin N) (fun _ => 𝟙 X) (fun _ => 1) r z (fun _ => j) (fun _ => j') =
          gm r z (L.U j ⊓ L.U j') (L.g j j') ^ N := by simp [trF]
      have t₂ : trF (L := L) (K := PUnit) (fun _ => r) (fun _ => 1) (𝟙 Z) z (fun _ => j) (fun _ => j') =
          gm r z (L.U j ⊓ L.U j') (L.g j j') := by simp [trF]
      rw [t₁, t₂]
      simpa only [pow_one] using pow_aux _ _ _ 1 N)
  refine ⟨a, ?_⟩
  ext z
  obtain ⟨j, hj⟩ := exists_chart hL (r z)
  have k₁ : gs (𝟙 Z) z ⊤ a = gs (𝟙 Z) z (V j) (u j) :=
    (gs_res (𝟙 Z) z le_top hj a).symm.trans (congrArg (gs (𝟙 Z) z (V j)) (ha j))
  have k₂ : z ∈ Z.basicOpen (show Γ(Z, ⊤) from a) ↔
      IsUnit (gs r z (LB.wchart L (K := Fin N) (fun _ => 𝟙 X) (fun _ => j)) (s.f (fun _ => j))) := by
    refine (isUnit_gs (𝟙 Z) z ⊤ trivial a).symm.trans ?_
    rw [k₁, hu j z hj, ← Units.val_pow_eq_pow_val, Units.isUnit_mul_units]
  refine k₂.trans ⟨fun h => ?_, fun h => ?_⟩
  · exact Opens.mem_iSup.2 ⟨fun _ => j, (isUnit_gs r z _ (l₁ j hj) _).1 h⟩
  · obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (show r z ∈ Out.nonzeroLocus s from h)
    have hk' : r z ∈ LB.wchart L (K := Fin N) (fun _ => 𝟙 X) k := X.basicOpen_le _ hk
    rw [sec_trans s r z (l₁ j hj) hk']
    exact (Units.isUnit _).mul ((isUnit_gs r z _ hk' _).2 hk)

theorem isAffineHom_of_field {k : Type} [Field k] {Y : Scheme.{0}} (y : Sp k ⟶ Y) : IsAffineHom y := by
  refine ⟨fun U _ => ?_⟩
  have : Subsingleton ↥(Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  by_cases h : ∃ p, p ∈ y ⁻¹ᵁ U
  · obtain ⟨p, hp⟩ := h
    have : y ⁻¹ᵁ U = ⊤ := top_unique fun x _ => by rwa [Subsingleton.elim x p]
    rw [this]; exact isAffineOpen_top _
  · have : y ⁻¹ᵁ U = ⊥ := bot_unique fun x hx => (h ⟨x, hx⟩).elim
    rw [this]; exact isAffineOpen_bot _

theorem exists_integral_closedImmersion {P : Scheme.{0}} (Z : Set P) (hc : IsClosed Z)
    (hi : IsIrreducible Z) :
    ∃ (C : Scheme.{0}) (_ : IsIntegral C) (i : C ⟶ P), IsClosedImmersion i ∧ Set.range i = Z := by
  let I := Scheme.IdealSheafData.vanishingIdeal (X := P) ⟨Z, hc⟩
  have hr : Set.range I.subschemeι = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    simp [I]
  have : IsReduced I.subscheme := ReducedSubgroup.isReduced_subscheme_vanishingIdeal _
  have : IrreducibleSpace I.subscheme := by
    have e := I.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph
    have : IrreducibleSpace (Set.range I.subschemeι) := by
      rw [hr]; exact Subtype.irreducibleSpace hi
    exact e.irreducibleSpace_iff.2 this
  exact ⟨I.subscheme, isIntegral_of_irreducibleSpace_of_isReduced _, I.subschemeι, inferInstance, hr⟩

theorem locallyQuasiFinite_of_trivial_on_fibres :
    ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) (A : LB X), IsProper f → A.IsLB → (∀ x : X, ∃ (d : ℕ) (s : LB.Sec (LB.LinComb A (K := Fin d) (fun _ => 𝟙 X) (fun _ => 1))), x ∈ Out.nonzeroLocus s ∧ IsAffineOpen (Out.nonzeroLocus s)) → (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Y) (C : Scheme.{0}) [IsIntegral C] (i : C ⟶ pullback f y), IsFinite i → ∃ t : (A.pull (i ≫ pullback.fst f y)).Gen, t.IsGen) → LocallyQuasiFinite f := by
  intro X Y f A hf hA hs ht
  refine LocallyQuasiFinite.of_finite_preimage_singleton f fun y ↦ ?_
  let Ω := AlgebraicClosure (Y.residueField y)
  let y' : Sp Ω ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) Ω)) ≫ Y.fromSpecResidueField y
  have hy : y ∈ Set.range y' := by
    obtain ⟨z⟩ : Nonempty ↥(Spec (.of Ω)) := inferInstance
    exact ⟨z, (Scheme.Hom.comp_apply _ _ z).trans (Scheme.fromSpecResidueField_apply y _)⟩
  clear_value y'
  have hy' := isAffineHom_of_field y'
  have h₁ : IsAffineHom (pullback.fst f y') :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom.{0})
      (IsPullback.of_hasPullback f y').flip hy'
  have h₂ : IsLocallyNoetherian (pullback f y') :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f y')
  have h₃ : CompactSpace ↥(pullback f y') := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f y')
  have h₄ : IsNoetherian (pullback f y') := {}
  have hP : (Set.univ : Set ↥(pullback f y')).Finite := by
    rw [← sUnion_irreducibleComponents]
    refine NoetherianSpace.finite_irreducibleComponents.sUnion fun Z hZ => ?_
    obtain ⟨C, _, i, hi, rfl⟩ := exists_integral_closedImmersion Z
      (isClosed_of_mem_irreducibleComponents Z hZ) hZ.1
    obtain ⟨t, ht⟩ := ht Ω y' C i inferInstance
    choose d s hx ha using hs
    choose a ha' using fun x => exists_fn A hA (d x) (s x) _ t ht
    have : LocallyQuasiFinite (i ≫ pullback.snd f y') := by
      refine locallyQuasiFinite_of_cover (K := Ω) _ a (top_unique fun c _ => ?_) fun x => ?_
      · refine Opens.mem_iSup.2 ⟨(i ≫ pullback.fst f y') c, ?_⟩
        rw [ha']
        exact hx _
      · rw [ha']
        exact (ha x).preimage _
    have : Subsingleton ↥(Sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
    obtain ⟨p⟩ : Nonempty ↥(Sp Ω) := inferInstance
    have hC : Finite C := Set.finite_univ_iff.1
      (((i ≫ pullback.snd f y').finite_preimage_singleton p).subset fun c _ => Subsingleton.elim _ _)
    exact Set.finite_range i
  have := Set.finite_univ_iff.1 hP
  refine (Set.finite_range (pullback.fst f y')).subset ?_
  rw [Scheme.Pullback.range_fst]
  exact Set.preimage_mono (Set.singleton_subset_iff.mpr hy)

end GlobalTheory.AmpleFibre
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SmoothTangent

theorem exists_section_of_ker_sq_eq_bot {k B F : Type*} [CommRing k] [CommRing B] [CommRing F]
    [Algebra k B] [Algebra k F] [Algebra.FormallySmooth k F] (π : B →ₐ[k] F)
    (hπ : Function.Surjective π) (h : RingHom.ker π.toRingHom ^ 2 = ⊥) :
    ∃ g : F →ₐ[k] B, π.comp g = AlgHom.id k F :=
  ⟨_, Algebra.FormallySmooth.comp_liftOfSurjective (AlgHom.id k F) π hπ ⟨2, h⟩⟩

theorem kerCotangentToTensor_injective (k R F : Type*) [CommRing k] [CommRing R] [CommRing F]
    [Algebra k R] [Algebra k F] [Algebra R F] [IsScalarTower k R F] [Algebra.FormallySmooth k F]
    (hs : Function.Surjective (algebraMap R F)) :
    Function.Injective (KaehlerDifferential.kerCotangentToTensor k R F) := by
  have hsurj : Function.Surjective (IsScalarTower.toAlgHom k R F).kerSquareLift :=
    fun x ↦ by
      obtain ⟨y, rfl⟩ := hs x
      exact ⟨Ideal.Quotient.mk _ y, rfl⟩
  have hnil : RingHom.ker (IsScalarTower.toAlgHom k R F).kerSquareLift.toRingHom ^ 2 = ⊥ := by
    rw [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square]
  obtain ⟨g, hg⟩ := exists_section_of_ker_sq_eq_bot _ hsurj hnil
  obtain ⟨l, hl⟩ := (retractionKerCotangentToTensorEquivSection (R := k) hs).symm ⟨g, hg⟩
  exact Function.LeftInverse.injective (g := l) fun x ↦ congr($hl x)

noncomputable def derivationEquivDual (k R C : Type*) [CommRing k] [CommRing R] [CommRing C]
    [Algebra k R] [Algebra k C] [Algebra R C] [IsScalarTower k R C] :
    Derivation k R C ≃ₗ[C] Module.Dual C (C ⊗[R] Ω[R⁄k]) :=
  (({ (KaehlerDifferential.linearMapEquivDerivation k R (M := C)).toAddEquiv with
      map_smul' := fun _ _ ↦ rfl } : (Ω[R⁄k] →ₗ[R] C) ≃ₗ[C] Derivation k R C).symm).trans
    (LinearMap.liftBaseChangeEquiv C)

theorem finrank_cotangent_le_finrank_derivation (k : Type*) [Field k] [PerfectField k]
    {R : Type*} [CommRing R] [Algebra k R] [Algebra.FiniteType k R] (m : Ideal R) [m.IsMaximal]
    (C : Type*) [Field C] [Algebra k C] [Algebra R C] [IsScalarTower k R C]
    [Algebra (R ⧸ m) C] [IsScalarTower R (R ⧸ m) C] :
    Module.finrank (R ⧸ m) m.Cotangent ≤ Module.finrank C (Derivation k R C) := by
  let := Ideal.Quotient.field m
  have : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing _ _
  have : Algebra.FormallyEtale k (R ⧸ m) := Algebra.FormallyEtale.of_isSeparable k _
  have hs : Function.Surjective (algebraMap R (R ⧸ m)) := Ideal.Quotient.mk_surjective
  have hinj := kerCotangentToTensor_injective k R (R ⧸ m) hs
  let e : m.Cotangent →ₗ[R] (R ⧸ m) ⊗[R] Ω[R⁄k] :=
    KaehlerDifferential.kerCotangentToTensor k R (R ⧸ m) ∘ₗ
      (Ideal.Cotangent.equivOfEq _ _ Ideal.mk_ker.symm).toLinearMap
  have he : Function.Injective (e.extendScalarsOfSurjective hs) :=
    hinj.comp (Ideal.Cotangent.equivOfEq _ _ Ideal.mk_ker.symm).injective
  rw [(derivationEquivDual k R C).finrank_eq, Subspace.dual_finrank_eq,
    ← (TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ m) C C Ω[R⁄k]).finrank_eq,
    Module.finrank_baseChange]
  exact LinearMap.finrank_le_finrank_of_injective he

theorem le_height_of_forall_minimalPrimes (k : Type) [Field k] {R : Type} [CommRing R]
    [Algebra k R] [Algebra.FiniteType k R] {d : ℕ}
    (hd : ∀ q ∈ minimalPrimes R, (d : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ q))
    (m : Ideal R) [m.IsMaximal] : (d : ℕ∞) ≤ m.height := by
  obtain ⟨p, hp, hpm⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ m)
  have := hp.1.1
  obtain ⟨n, h₁, h₂⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq k (R ⧸ p)
  have hdn : (d : ℕ∞) ≤ n := by
    have := hd p hp
    rw [h₁] at this
    exact_mod_cast this
  have hψ : Function.Surjective (Ideal.Quotient.mk p) := Ideal.Quotient.mk_surjective
  have hcm : (m.map (Ideal.Quotient.mk p)).comap (Ideal.Quotient.mk p) = m := by
    rw [Ideal.comap_map_of_surjective _ hψ, sup_eq_left]
    exact Ideal.mk_ker.le.trans hpm
  have : (m.map (Ideal.Quotient.mk p)).IsMaximal := by
    refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ hψ inferInstance).resolve_left fun h ↦ ?_
    rw [h, Ideal.comap_top] at hcm
    exact Ideal.IsMaximal.ne_top inferInstance hcm.symm
  have h := height_le_height_comap_of_surjective _ hψ (m.map (Ideal.Quotient.mk p))
  rw [hcm, ReciprocityTheory.CA.height_eq_of_isMaximal_of_trdeg_eq_field n h₂] at h
  exact hdn.trans h

end GlobalTheory.SmoothTangent

namespace GlobalTheory

open SmoothTangent

theorem smoothOfRelativeDimension_of_dim_of_finrank_derivation_le :
    ∀ (k : Type) [Field k] [CharZero k] (e : k →+* ℂ) (R : Type) [CommRing R] [Algebra k R] (d : ℕ),
      Algebra.FiniteType k R →
      (∀ q ∈ minimalPrimes R, (d : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ q)) →
      (∀ [Algebra k ℂ] [Algebra R ℂ] [IsScalarTower k R ℂ], algebraMap k ℂ = e →
        Module.finrank ℂ (Derivation k R ℂ) ≤ d) →
      SmoothOfRelativeDimension d (spMap (algebraMap k R)) := by
  intro k _ _ e R _ _ d _ hd ht
  have : Algebra.FinitePresentation k R := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have key (m : Ideal R) (hm : m.IsMaximal) :
      ∃ f ∉ m, Algebra.IsStandardSmoothOfRelativeDimension d k (Localization.Away f) := by
    have h₁ : (d : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime m) := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)]
      exact_mod_cast le_height_of_forall_minimalPrimes k hd m
    have h₂ : Module.finrank (R ⧸ m) m.Cotangent ≤ d := by
      let := Ideal.Quotient.field m
      have : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing _ _
      let : Algebra k ℂ := e.toAlgebra
      let φ : (R ⧸ m) →ₐ[k] ℂ := (by
        refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
        solve_by_elim* (maxDepth := 2) only [*,
          @_root_.DivisionSemiring.to_moduleIsTorsionFree,
          @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
      let : Algebra (R ⧸ m) ℂ := φ.toRingHom.toAlgebra
      let : Algebra R ℂ := (φ.toRingHom.comp (Ideal.Quotient.mk m)).toAlgebra
      have : IsScalarTower R (R ⧸ m) ℂ := .of_algebraMap_eq fun _ ↦ rfl
      have : IsScalarTower k R ℂ := .of_algebraMap_eq fun x ↦ (φ.commutes x).symm
      exact (finrank_cotangent_le_finrank_derivation k m ℂ).trans (ht rfl)
    obtain ⟨-, -, -, h₃, -, h₄⟩ := isSmoothAt_of_finrank_cotangent_le_of_perfectField k m h₁ h₂
    exact exists_isStandardSmoothOfRelativeDimension_of_isSmoothAt k m h₄
  refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)).mpr ?_
  refine ⟨{f | Algebra.IsStandardSmoothOfRelativeDimension d k (Localization.Away f)}, ?_, ?_⟩
  · by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨f, hf, hs⟩ := key m hm
    exact hf (hle (Ideal.subset_span hs))
  · intro f hf
    have := (RingHom.isStandardSmoothOfRelativeDimension_algebraMap d).mpr hf
    rwa [IsScalarTower.algebraMap_eq k R] at this

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.exists_lineBundle_cocycle_one_add_eps : ∀ (Y Y' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → ∀ Q : LB Y', Q.IsLB → (∃ t : (Q.pull j).Gen, t.IsGen) → ∃ (Q' : LB Y') (k : ∀ i i', Γ(Y, j ⁻¹ᵁ (Q'.U i ⊓ Q'.U i'))), Q'.IsLB ∧ LBIso Q Q' ∧ (∀ i i' (h : Q'.U i ⊓ Q'.U i' ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ (Q'.U i ⊓ Q'.U i'))), (Q'.g i i').val = 1 + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom (k i i')) := by
  first | exact @GlobalTheory.EpsCocycle.exists_cocycle_one_add_eps | exact GlobalTheory.EpsCocycle.exists_cocycle_one_add_eps | (intros; apply GlobalTheory.EpsCocycle.exists_cocycle_one_add_eps <;> assumption)
end
