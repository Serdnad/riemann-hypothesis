module

public import Development.AutomorphicArithmetic.RepresentationRank.RepOfRank
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle001
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle001
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
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
public import Mathlib.Dynamics.Newton
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle001
public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.Etale.StandardEtale

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

private lemma UpperTheory.isPullback_fst_snd_over {S : Scheme.{0}} {T G : Over S} :
    IsPullback (fst T G).left (snd T G).left T.hom G.hom :=
  IsPullback.of_hasPullback T.hom G.hom

theorem UpperTheory.clopProj_finite_etale_of_isClosed :
    ∀ {S : Scheme.{0}} {T G : Over S} (V : (T ⊗ G).left.Opens), IsFinite G.hom → Etale G.hom → IsClosed (V : Set (T ⊗ G).left) → IsFinite (UpperTheory.RepresentationRank.proj V) ∧ Etale (UpperTheory.RepresentationRank.proj V) := by
  intro S T G V hf he hV
  have hpb : IsPullback (snd T G).left (fst T G).left G.hom T.hom := UpperTheory.isPullback_fst_snd_over.flip
  haveI : IsClosedImmersion V.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hV)
  haveI : IsFinite (fst T G).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) hpb hf
  haveI : Etale (fst T G).left :=
    MorphismProperty.of_isPullback (P := @Etale) hpb he
  exact ⟨inferInstanceAs (IsFinite (V.ι ≫ (fst T G).left)),
    inferInstanceAs (Etale (V.ι ≫ (fst T G).left))⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace UpperTheory.TwoTorsionInclusion

private noncomputable abbrev Two (S : Scheme.{0}) : Scheme.{0} := ∐ fun _ : Fin 2 ↦ S

private noncomputable abbrev inc (S : Scheme.{0}) (i : Fin 2) : S ⟶ Two S :=
  Sigma.ι (fun _ : Fin 2 ↦ S) i

private noncomputable abbrev cd (S : Scheme.{0}) : Two S ⟶ S := Sigma.desc fun _ ↦ 𝟙 S

private lemma mem_zero_iff (S : Scheme.{0}) (x : Two S) :
    x ∈ (inc S 0).opensRange ↔ x ∉ (inc S 1).opensRange := by
  obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk (fun _ : Fin 2 ↦ S)).surjective x
  simp only [sigmaMk_mk, Scheme.Hom.mem_opensRange, inc, sigmaι_eq_iff]
  fin_cases i <;> simp

private lemma isClosed_one (S : Scheme.{0}) : IsClosed ((inc S 1).opensRange : Set (Two S)) := by
  rw [← isOpen_compl_iff]
  have : ((inc S 1).opensRange : Set (Two S))ᶜ = ((inc S 0).opensRange : Set (Two S)) := by
    ext x
    exact (mem_zero_iff S x).symm
  rw [this]
  exact (inc S 0).opensRange.isOpen

private lemma restrict_eq {S X Z : Scheme.{0}} (y : X ⟶ Two S) (i : Fin 2) (j : Z ⟶ X)
    (h : ∀ z, y (j z) ∈ (inc S i).opensRange) : j ≫ y = j ≫ y ≫ cd S ≫ inc S i := by
  have hr : Set.range (j ≫ y).base ⊆ Set.range (inc S i).base := by
    rintro _ ⟨z, rfl⟩
    exact h z
  set L := IsOpenImmersion.lift (inc S i) (j ≫ y) hr
  have e : L ≫ inc S i = j ≫ y := IsOpenImmersion.lift_fac _ _ _
  rw [← reassoc_of% e, ← e]
  simp [inc, cd]

private lemma core {S X : Scheme.{0}} (f : X ⟶ S) (W : X.Opens) (hW : IsClosed (W : Set X)) :
    ∃! y : X ⟶ Two S, y ≫ cd S = f ∧ y ⁻¹ᵁ (inc S 1).opensRange = W := by
  let W' : X.Opens := ⟨(W : Set X)ᶜ, hW.isOpen_compl⟩
  have hc : IsCompl W'.ι.opensRange W.ι.opensRange := by
    simp only [Scheme.Opens.opensRange_ι]
    constructor
    · rw [disjoint_iff, ← SetLike.coe_set_eq]
      ext x
      simp [W']
    · rw [codisjoint_iff, ← SetLike.coe_set_eq]
      ext x
      simp [W']
  obtain ⟨hcol⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl W'.ι W.ι hc
  have ext : ∀ {T : Scheme.{0}} (a b : X ⟶ T), W'.ι ≫ a = W'.ι ≫ b → W.ι ≫ a = W.ι ≫ b → a = b :=
    fun a b h0 h1 ↦ BinaryCofan.IsColimit.hom_ext hcol h0 h1
  have key : ∀ y' : X ⟶ Two S, y' ≫ cd S = f → y' ⁻¹ᵁ (inc S 1).opensRange = W →
      W'.ι ≫ y' = W'.ι ≫ f ≫ inc S 0 ∧ W.ι ≫ y' = W.ι ≫ f ≫ inc S 1 := by
    intro y' h1 h2
    constructor
    · rw [restrict_eq y' 0 W'.ι, reassoc_of% h1]
      intro z
      rw [mem_zero_iff]
      intro hz
      have hm : W'.ι z ∈ y' ⁻¹ᵁ (inc S 1).opensRange := hz
      rw [h2] at hm
      have hz' : z.1 ∉ W := z.2
      exact hz' hm
    · rw [restrict_eq y' 1 W.ι, reassoc_of% h1]
      intro z
      have hm : W.ι z ∈ y' ⁻¹ᵁ (inc S 1).opensRange := by
        rw [h2]
        exact z.2
      exact hm
  obtain ⟨y0, hy0, hy1⟩ := BinaryCofan.IsColimit.desc' hcol (W'.ι ≫ f ≫ inc S 0) (W.ι ≫ f ≫ inc S 1)
  obtain ⟨y, rfl⟩ : ∃ y : X ⟶ Two S, y = y0 := ⟨y0, rfl⟩
  change W'.ι ≫ y = _ at hy0
  change W.ι ≫ y = _ at hy1
  refine ⟨y, ⟨ext (y ≫ cd S) f (by rw [reassoc_of% hy0]; simp [inc, cd])
    (by rw [reassoc_of% hy1]; simp [inc, cd]), ?_⟩, ?_⟩
  · ext x
    by_cases hx : x ∈ W
    · obtain ⟨z, rfl⟩ : ∃ z : W.toScheme, W.ι z = x := ⟨⟨x, hx⟩, rfl⟩
      have e : y (W.ι z) = inc S 1 (f (W.ι z)) := by
        rw [show y (W.ι z) = (W.ι ≫ y) z from rfl, hy1] <;> rfl
      refine iff_of_true ?_ hx
      show y (W.ι z) ∈ (inc S 1).opensRange
      rw [e]
      exact ⟨_, rfl⟩
    · obtain ⟨z, rfl⟩ : ∃ z : W'.toScheme, W'.ι z = x := ⟨⟨x, hx⟩, rfl⟩
      have e : y (W'.ι z) = inc S 0 (f (W'.ι z)) := by
        rw [show y (W'.ι z) = (W'.ι ≫ y) z from rfl, hy0] <;> rfl
      refine iff_of_false ?_ hx
      show y (W'.ι z) ∉ (inc S 1).opensRange
      rw [e, ← mem_zero_iff]
      exact ⟨_, rfl⟩
  · rintro y' ⟨h1, h2⟩
    obtain ⟨k0, k1⟩ := key y' h1 h2
    exact ext _ _ (k0.trans hy0.symm) (k1.trans hy1.symm)

private lemma isIso_fst {S : Scheme.{0}} (T : Over S) : IsIso (fst T (Over.mk (𝟙 S))) := by
  have ht : IsTerminal (Over.mk (𝟙 S)) := Over.mkIdTerminal
  refine ⟨⟨lift (𝟙 T) (ht.from T), ?_, by simp⟩⟩
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · exact ht.hom_ext _ _

end UpperTheory.TwoTorsionInclusion

open UpperTheory.TwoTorsionInclusion in
theorem UpperTheory.exists_clopRep_trivial :
    ∀ (S : Scheme.{0}), ∃ (Y : Over S) (U : (Y ⊗ Over.mk (𝟙 S)).left.Opens), UpperTheory.RepresentationRank.Rep (Over.mk (𝟙 S)) Y U ∧ IsFinite Y.hom ∧ Etale Y.hom := by
  intro S
  refine ⟨Over.mk (cd S), (fst (Over.mk (cd S)) (Over.mk (𝟙 S))).left ⁻¹ᵁ (inc S 1).opensRange,
    ⟨(isClosed_one S).preimage (Scheme.Hom.continuous _), ?_⟩,
    (GlobalTheory.FinEt.isSplitOfRank_sigmaDesc S 2).isFinite, (GlobalTheory.FinEt.isSplitOfRank_sigmaDesc S 2).etale⟩
  intro T V hV
  have hiso : IsIso (fst T (Over.mk (𝟙 S))).left := by
    have := isIso_fst T
    exact (inferInstance : IsIso ((Over.forget S).map (fst T (Over.mk (𝟙 S)))))
  set φ := (fst T (Over.mk (𝟙 S))).left with hφ
  have h1 : ∀ x, inv φ (φ x) = x := fun x ↦ by
    rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
    rfl
  have h2 : ∀ t, φ (inv φ t) = t := fun t ↦ by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  have hpre : ∀ (y : T ⟶ Over.mk (cd S)) x,
      x ∈ (y ▷ Over.mk (𝟙 S)).left ⁻¹ᵁ
        ((fst (Over.mk (cd S)) (Over.mk (𝟙 S))).left ⁻¹ᵁ (inc S 1).opensRange) ↔
        y.left (φ x) ∈ (inc S 1).opensRange := by
    intro y x
    show (fst (Over.mk (cd S)) (Over.mk (𝟙 S))).left ((y ▷ Over.mk (𝟙 S)).left x) ∈
      (inc S 1).opensRange ↔ _
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, whiskerRight_fst, Over.comp_left,
      Scheme.Hom.comp_apply]
  let W : T.left.Opens := (inv φ) ⁻¹ᵁ V
  have hW : IsClosed (W : Set T.left) := hV.preimage (Scheme.Hom.continuous _)
  have hiff : ∀ y : T ⟶ Over.mk (cd S), (y ▷ Over.mk (𝟙 S)).left ⁻¹ᵁ
      ((fst (Over.mk (cd S)) (Over.mk (𝟙 S))).left ⁻¹ᵁ (inc S 1).opensRange) = V ↔
      y.left ⁻¹ᵁ (inc S 1).opensRange = W := by
    intro y
    constructor
    · intro h
      refine SetLike.ext fun t ↦ ?_
      show y.left t ∈ (inc S 1).opensRange ↔ inv φ t ∈ V
      rw [← h, hpre, h2]
    · intro h
      refine SetLike.ext fun x ↦ ?_
      rw [hpre]
      show φ x ∈ y.left ⁻¹ᵁ (inc S 1).opensRange ↔ x ∈ V
      rw [h]
      show inv φ (φ x) ∈ V ↔ x ∈ V
      rw [h1]
  obtain ⟨y0, ⟨e0, e1⟩, hu⟩ := core T.hom W hW
  refine ⟨Over.homMk y0 e0, (hiff _).2 e1, fun y hy ↦ ?_⟩
  exact Over.OverMorphism.ext (hu y.left ⟨Over.w y, (hiff y).1 hy⟩)
end

section

noncomputable section
open IsLocalRing UpperTheory.Et

private theorem isUnit_aeval_derivative {S : Type} [CommRing S] {q : ℕ} (hq : IsUnit (q : S)) (hq0 : q ≠ 0)
    {x : S} (hx : IsNilpotent (x ^ q - 1)) :
    IsUnit (Polynomial.aeval x (Polynomial.derivative (Polynomial.X ^ q - 1 : Polynomial ℤ))) := by
  have hxq : IsUnit (x ^ q) := by
    have h := IsNilpotent.isUnit_add_one hx
    simpa using h
  have hxu : IsUnit x := (isUnit_pow_iff hq0).1 hxq
  have h2 : Polynomial.aeval x (Polynomial.derivative (Polynomial.X ^ q - 1 : Polynomial ℤ))
      = (q : S) * x ^ (q - 1) := by
    simp [Polynomial.derivative_X_pow]
  rw [h2]
  exact hq.mul (hxu.pow _)

theorem UpperTheory.roots_of_unity_lift_mod_nilpotent_unique :
    ∀ (S : Type) [CommRing S] (q : ℕ), IsUnit (q : S) → (∀ x : S, IsNilpotent (x ^ q - 1) → ∃ y : S, y ^ q = 1 ∧ IsNilpotent (x - y)) ∧
      ∀ x y : S, x ^ q = 1 → y ^ q = 1 → IsNilpotent (x - y) → x = y := by
  intro S _ q hq
  by_cases hq0 : q = 0
  · subst hq0
    have h01 : (0 : S) = 1 := by simpa using hq
    have : Subsingleton S := subsingleton_of_zero_eq_one h01
    exact ⟨fun x _ => ⟨x, Subsingleton.elim _ _, by simp⟩, fun x y _ _ _ => Subsingleton.elim _ _⟩
  refine ⟨fun x hx => ?_, fun x y hx hy hxy => ?_⟩
  · obtain ⟨y, ⟨hy1, hy2⟩, -⟩ := Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero
      (P := (Polynomial.X ^ q - 1 : Polynomial ℤ)) (x := x) (by simpa using hx)
      (isUnit_aeval_derivative hq hq0 hx)
    refine ⟨y, ?_, hy1⟩
    simpa [sub_eq_zero] using hy2
  · have hx' : IsNilpotent (x ^ q - 1) := by simp [hx]
    have h := Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero
      (P := (Polynomial.X ^ q - 1 : Polynomial ℤ)) (x := x) (by simpa using hx')
      (isUnit_aeval_derivative hq hq0 hx')
    exact h.unique ⟨by simp, by simp [hx]⟩ ⟨hxy, by simp [hy]⟩

end
end

section

noncomputable section
open Polynomial

theorem UpperTheory.exists_polynomial_eq_map_eval_roots_of_perm_invariant :
    ∀ (A : Type) [CommRing A] (N : ℕ) (g : A[X]) (Φ : (MvPolynomial (Fin N) A)[X]), (∀ σ : Equiv.Perm (Fin N), Φ.map (MvPolynomial.rename σ : MvPolynomial (Fin N) A →ₐ[A] _).toRingHom = Φ) →
      ∃ p : A[X], p.natDegree ≤ Φ.natDegree ∧ ∀ (S : Type) [CommRing S] [Algebra A S] (x : Fin N → S), g.map (algebraMap A S) = ∏ i, (X - C (x i)) → p.map (algebraMap A S) = Φ.map (MvPolynomial.aeval x : MvPolynomial (Fin N) A →ₐ[A] S).toRingHom := by
  intro A _ N g Φ hΦ
  have hsym : ∀ n, (Φ.coeff n).IsSymmetric := by
    intro n σ
    have := congrArg (fun q => q.coeff n) (hΦ σ)
    simpa [Polynomial.coeff_map] using this
  choose a ha using fun n => UpperTheory.exists_eval_roots_symmetric_eq_algebraMap A N g (Φ.coeff n) (hsym n)
  refine ⟨∑ n ∈ Finset.range (Φ.natDegree + 1), monomial n (a n), ?_, ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun n hn => ?_)
    exact (natDegree_monomial_le _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn))
  · intro S _ _ x hx
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_map, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial_apply, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_range]
    split_ifs with hn
    · rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ha n S x hx]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      simp

end
end

section

open CategoryTheory Limits AlgebraicGeometry

theorem UpperTheory.isIntegral_sections_of_integralHom_over_affine_chart :
    ∀ (A : Type) [CommRing A] {P Z U L : Scheme.{0}} (u : Z ⟶ L) (l : L ⟶ Spec (CommRingCat.of A)) (f : L ⟶ P),
        IsIntegralHom u → IsPullback f l (terminal.from P) (terminal.from _) →
        ∀ (O : P.Opens), IsAffineOpen O → ∀ (τ : Γ(P, O)), Subring.closure {τ} = ⊤ →
        ∀ (ι : U ⟶ Z) [IsOpenImmersion ι], Set.range ι = ((u ≫ f) ⁻¹ᵁ O : Set Z) →
        ∀ (h : (⊤ : U.Opens) ≤ (ι ≫ u ≫ f) ⁻¹ᵁ O) (x : Γ(U, ⊤)),
          IsIntegral (Subring.closure (Set.range ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (ι ≫ u ≫ l).appTop).hom ∪
            {((ι ≫ u ≫ f).appLE O ⊤ h).hom τ})) x := by
  intro A _ P Z U L u l f hu hpb O hO τ hτ ι _ hι h x
  haveI := hu
  haveI : IsAffineHom f := MorphismProperty.of_isPullback (P := @IsAffineHom) hpb.flip inferInstance
  have hV : IsAffineOpen (f ⁻¹ᵁ O) := hO.preimage f
  have hW : u ⁻¹ᵁ (f ⁻¹ᵁ O) = ι ''ᵁ ⊤ := by
    apply SetLike.coe_injective
    change ((u ≫ f) ⁻¹ᵁ O : Set Z) = _
    rw [← hι]
    simp
  have hb : Function.Surjective (ι.appLE (u ⁻¹ᵁ (f ⁻¹ᵁ O)) ⊤ h).hom := by
    have key : ∀ (W : Z.Opens) (_ : W = ι ''ᵁ ⊤) (e : ⊤ ≤ ι ⁻¹ᵁ W),
        Function.Surjective (ι.appLE W ⊤ e).hom := by
      rintro W rfl e
      have e2 : ι.appLE (ι ''ᵁ ⊤) ⊤ e = (ι.appIso ⊤).hom := (Scheme.Hom.appIso_hom' ι ⊤).symm
      rw [e2]
      exact (ι.appIso ⊤).commRingCatIsoToRingEquiv.surjective
    exact key _ hW h
  have ha : (u.appLE (f ⁻¹ᵁ O) (u ⁻¹ᵁ (f ⁻¹ᵁ O)) le_rfl).hom.IsIntegral := by
    rw [← Scheme.Hom.app_eq_appLE]
    exact IsIntegralHom.isIntegral_app u _ hV
  set φ := u.appLE (f ⁻¹ᵁ O) (u ⁻¹ᵁ (f ⁻¹ᵁ O)) le_rfl ≫ ι.appLE (u ⁻¹ᵁ (f ⁻¹ᵁ O)) ⊤ h with hφ
  have hφi : φ.hom.IsIntegral := by
    rw [hφ, CommRingCat.hom_comp]
    exact RingHom.IsIntegral.trans _ _ ha (RingHom.isIntegral_of_surjective _ hb)
  set S := Subring.closure (Set.range ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
    (ι ≫ u ≫ l).appTop).hom ∪ {((ι ≫ u ≫ f).appLE O ⊤ h).hom τ}) with hS
  have hpo := GroundTheory.Arith.SchemeCoh.isPushout_app_of_isPullback hpb hO
  have e1 : f.app O ≫ φ = (ι ≫ u ≫ f).appLE O ⊤ h := by
    rw [hφ, Scheme.Hom.app_eq_appLE, ← Category.assoc, Scheme.Hom.appLE_comp_appLE]
    exact Scheme.Hom.appLE_comp_appLE ι (u ≫ f) O _ ⊤ _ _
  have c1 : ∀ y, φ.hom ((f.app O).hom y) ∈ S := by
    intro y
    have hy : y ∈ Subring.closure {τ} := hτ ▸ Subring.mem_top y
    have hle : Subring.closure {τ} ≤ (S.comap φ.hom).comap (f.app O).hom := by
      rw [Subring.closure_le, Set.singleton_subset_iff]
      show φ.hom ((f.app O).hom τ) ∈ S
      rw [← CommRingCat.comp_apply, e1]
      exact Subring.subset_closure (Or.inr rfl)
    exact hle hy
  have e2 : l.appLE ⊤ (f ⁻¹ᵁ O) (by simp) ≫ φ = (ι ≫ u ≫ l).appTop := by
    rw [hφ]
    refine ((Scheme.Hom.appLE_comp_appLE_assoc u l ⊤ (f ⁻¹ᵁ O) (u ⁻¹ᵁ (f ⁻¹ᵁ O)) _ _ _).trans
      (Scheme.Hom.appLE_comp_appLE ι (u ≫ l) ⊤ _ ⊤ _ _)).trans ?_
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    first
      | rfl
      | (congr 1; simp)
      | simp [Scheme.Hom.appLE]
  have c2 : ∀ y, φ.hom ((l.appLE ⊤ (f ⁻¹ᵁ O) (by simp)).hom y) ∈ S := by
    intro y
    have hy : φ.hom ((l.appLE ⊤ (f ⁻¹ᵁ O) (by simp)).hom y) =
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (ι ≫ u ≫ l).appTop).hom
          ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom y) := by
      rw [← CommRingCat.comp_apply, e2]
      simp
    rw [hy]
    exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
  set T := S.comap φ.hom with hT
  let g1 := CommRingCat.ofHom ((f.app O).hom.codRestrict T c1)
  let g2 := CommRingCat.ofHom ((l.appLE ⊤ (f ⁻¹ᵁ O) (by simp)).hom.codRestrict T c2)
  have hw : Scheme.Hom.appLE (terminal.from P) ⊤ O (by simp) ≫ g1 =
      Scheme.Hom.appTop (terminal.from (Spec (CommRingCat.of A))) ≫ g2 := by
    ext z
    exact congrArg (fun k => k.hom z) hpo.w
  have hid : hpo.desc g1 g2 hw ≫ CommRingCat.ofHom T.subtype = 𝟙 _ := by
    apply hpo.hom_ext
    · rw [hpo.inl_desc_assoc, Category.comp_id]
      ext z
      rfl
    · rw [hpo.inr_desc_assoc, Category.comp_id]
      ext z
      rfl
  have hall : ∀ y, φ.hom y ∈ S := by
    intro y
    have := congrArg (fun k => k.hom y) hid
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at this
    rw [← this]
    exact ((hpo.desc g1 g2 hw).hom y).2
  obtain ⟨p, hm, hp⟩ := hφi x
  refine ⟨p.map (φ.hom.codRestrict S hall), hm.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  exact hp
end

section

noncomputable section
open IsLocalRing UpperTheory.Et

theorem UpperTheory.exists_section_lift_of_etale_of_henselian :
    ∀ (A E : Type) [CommRing A] [HenselianLocalRing A] [CommRing E] [Algebra A E] [Algebra.Etale A E] (π : E →ₐ[A] ResidueField A), ∃ σ : E →ₐ[A] A, ∀ x, residue A (σ x) = π x := by
  intro A E _ _ _ _ _ π
  classical
  let Q : Ideal E := RingHom.ker π
  haveI : Q.IsPrime := RingHom.ker_isPrime π
  obtain ⟨f, hfQ, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := A) Q
  obtain ⟨P⟩ := hstd.nonempty_standardEtalePresentation
  have hunit : ∀ y : Submonoid.powers f, IsUnit (π y) := by
    rintro ⟨_, n, rfl⟩
    simp only [map_pow]
    exact (isUnit_iff_ne_zero.mpr fun h => hfQ (RingHom.mem_ker.mpr h)).pow n
  let πf : Localization.Away f →ₐ[A] ResidueField A := IsLocalization.liftAlgHom (M := Submonoid.powers f) hunit
  let ι : E →ₐ[A] Localization.Away f := IsScalarTower.toAlgHom A E _
  have hπ : ∀ x, πf (ι x) = π x := fun x => by
    simp [πf, ι]
  let τ : P.Ring →ₐ[A] ResidueField A := πf.comp P.equivRing.symm.toAlgHom
  have hx : P.HasMap (τ P.X) := StandardEtalePair.hasMap_X.map τ
  have key : ∀ b : A, residue A b = τ P.X → ∀ p : Polynomial A, residue A (p.eval b) = Polynomial.aeval (τ P.X) p := by
    intro b hb p
    rw [← hb, ← ResidueField.algebraMap_eq, Polynomial.aeval_algebraMap_apply, Polynomial.coe_aeval_eq_eval]
  obtain ⟨a₀, ha₀⟩ := IsLocalRing.residue_surjective (τ P.X)
  have h1 : P.f.eval a₀ ∈ maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, key a₀ ha₀]
    exact hx.1
  have h2 : IsUnit (P.f.derivative.eval a₀) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, key a₀ ha₀]
    exact hx.isUnit_derivative_f.ne_zero
  obtain ⟨a, ha, ham⟩ := HenselianLocalRing.is_henselian P.f P.monic_f a₀ h1 h2
  have hra : residue A a = τ P.X := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at ham
    rw [ham, ha₀]
  have hA : P.HasMap a := by
    refine ⟨by rw [Polynomial.coe_aeval_eq_eval]; exact ha, ?_⟩
    rw [Polynomial.coe_aeval_eq_eval, ← IsLocalRing.residue_ne_zero_iff_isUnit, key a hra]
    exact hx.2.ne_zero
  let ρ : A →ₐ[A] ResidueField A := IsScalarTower.toAlgHom A A (ResidueField A)
  have hρ : ρ.comp (P.lift a hA) = τ := by
    apply StandardEtalePair.hom_ext
    simp [ρ, hra, ResidueField.algebraMap_eq]
  refine ⟨(P.lift a hA).comp (P.equivRing.toAlgHom.comp ι), fun x => ?_⟩
  have := congrArg (fun φ => φ (P.equivRing (ι x))) hρ
  simp only [AlgHom.comp_apply, ρ, IsScalarTower.coe_toAlgHom', ResidueField.algebraMap_eq, τ, AlgEquiv.coe_toAlgHom, AlgHom.coe_coe, AlgEquiv.symm_apply_apply] at this
  simpa [hπ] using this

end
end
