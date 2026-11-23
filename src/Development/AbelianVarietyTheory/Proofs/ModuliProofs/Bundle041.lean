module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.DedekindDomain.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAwaySurjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle030
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.DenseBasis

variable {Z S : Scheme.{0}}

theorem isOpenImmersion_section (p : Z ⟶ S) [Etale p] (σ : S ⟶ Z) (hσ : σ ≫ p = 𝟙 S) :
    IsOpenImmersion σ := by
  have : Etale (σ ≫ p) := by rw [hσ]; infer_instance
  have : Etale σ := Etale.of_comp σ p
  have : IsSplitMono σ := IsSplitMono.mk' ⟨p, hσ⟩
  exact IsOpenImmersion.of_flat_of_mono σ

theorem comp_section_eq_iff (p : Z ⟶ S) [Etale p] (σ : S ⟶ Z) (hσ : σ ≫ p = 𝟙 S)
    {K : Type} [Field K] (y : Spec (.of K) ⟶ Z) (w : Spec (.of K)) :
    (y ≫ p) ≫ σ = y ↔ y w ∈ Set.range σ := by
  have := isOpenImmersion_section p σ hσ
  constructor
  · intro h
    refine ⟨(y ≫ p) w, ?_⟩
    rw [← Scheme.Hom.comp_apply]
    exact congrArg (fun f : Spec (.of K) ⟶ Z => f w) h
  · intro h
    have hr : Set.range y ⊆ Set.range σ := by
      rintro _ ⟨v, rfl⟩
      rwa [Subsingleton.elim v w]
    rw [← IsOpenImmersion.lift_fac σ y hr]
    simp only [Category.assoc, reassoc_of% hσ]

theorem exists_lift (p : Z ⟶ S) [IsFinite p] [Etale p] {K : Type} [Field K] [IsAlgClosed K]
    (x : Spec (.of K) ⟶ S) (w : Spec (.of K)) (z : Z) (hz : p z = x w) :
    ∃ y : Spec (.of K) ⟶ Z, y ≫ p = x ∧ y w = z := by
  obtain ⟨q, hq₁, hq₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := x) z w hz
  obtain ⟨n, e, he⟩ := GlobalTheory.FinEt.exists_iso_sigma_of_isSepClosed (pullback.snd p x)
  obtain ⟨⟨j, v⟩, hv⟩ : ∃ a, AlgebraicGeometry.sigmaMk _ a = e.inv q :=
    ⟨(AlgebraicGeometry.sigmaMk _).symm (e.inv q), by simp⟩
  rw [AlgebraicGeometry.sigmaMk_mk] at hv
  refine ⟨Sigma.ι (fun _ : Fin n => Spec (.of K)) j ≫ e.hom ≫ pullback.fst p x, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% he]
    simp
  · rw [Subsingleton.elim w v, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hv, ← Scheme.Hom.comp_apply]
    simpa using hq₁

theorem existsUnique_section_of_dense (p : Z ⟶ S) [IsFinite p] [Etale p] {I : Type} [Finite I]
    (σ : I → (S ⟶ Z)) (hσ : ∀ i, σ i ≫ p = 𝟙 S) (D : Set S) (hD : Dense D)
    (h : ∀ t ∈ D, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : Spec (.of K) ⟶ S),
      t ∈ Set.range x ∧ ∀ y : Spec (.of K) ⟶ Z, y ≫ p = x → ∃! i, x ≫ σ i = y)
    (K : Type) [Field K] (x : Spec (.of K) ⟶ S) (y : Spec (.of K) ⟶ Z) (hy : y ≫ p = x) :
    ∃! i, x ≫ σ i = y := by
  have hO : ∀ i, IsOpenImmersion (σ i) := fun i => isOpenImmersion_section p (σ i) (hσ i)
  have hCl : ∀ i, IsClosedImmersion (σ i) := fun i => by
    have : IsClosedImmersion (σ i ≫ p) := by rw [hσ i]; infer_instance
    exact IsClosedImmersion.of_comp (σ i) p
  have hp : ∀ i s, p (σ i s) = s := fun i s => by
    rw [← Scheme.Hom.comp_apply, hσ i]; rfl

  have hdisj : ∀ i j s s', σ i s = σ j s' → i = j := by
    intro i j s s' hss
    have hE : IsOpen ((σ i).base ⁻¹' Set.range (σ j)) :=
      (σ j).isOpenEmbedding.isOpen_range.preimage (σ i).continuous
    obtain ⟨t, htE, htD⟩ := hD.inter_open_nonempty _ hE ⟨s, s', hss.symm⟩
    obtain ⟨K', _, _, x', ⟨w', hw'⟩, hu⟩ := h t htD
    obtain ⟨t', ht'⟩ := htE
    have hsec : ((x' ≫ σ i) ≫ p) ≫ σ j = x' ≫ σ i := by
      rw [comp_section_eq_iff p (σ j) (hσ j)]
      exact ⟨t', by rw [Scheme.Hom.comp_apply, hw']; exact ht'⟩
    simp only [Category.assoc] at hsec
    rw [reassoc_of% (hσ i)] at hsec
    have hl : (x' ≫ σ i) ≫ p = x' := by rw [Category.assoc, hσ i, Category.comp_id]
    exact (hu _ hl).unique rfl hsec

  have hcov : ∀ z : Z, ∃ i, z ∈ Set.range (σ i) := by
    by_contra hne
    push Not at hne
    set C : Set Z := (⋃ i, Set.range (σ i))ᶜ with hCdef
    have hCo : IsOpen C :=
      (isClosed_iUnion_of_finite fun i => (σ i).isClosedEmbedding.isClosed_range).isOpen_compl
    obtain ⟨z₀, hz₀⟩ := hne
    have hz₀C : z₀ ∈ C := by simpa [hCdef] using hz₀
    obtain ⟨t, ⟨z, hzC, rfl⟩, htD⟩ :=
      hD.inter_open_nonempty _ (p.isOpenMap C hCo) ⟨p z₀, z₀, hz₀C, rfl⟩
    obtain ⟨K', _, _, x', ⟨w', hw'⟩, hu⟩ := h (p z) htD
    obtain ⟨y', hy'p, hy'w⟩ := exists_lift p x' w' z hw'.symm
    obtain ⟨i, hi, -⟩ := hu y' hy'p
    apply hzC
    rw [Set.mem_iUnion]
    exact ⟨i, x' w', by rw [← hy'w, ← hi, Scheme.Hom.comp_apply]⟩
  let w : Spec (.of K) := default
  obtain ⟨i, hi⟩ := hcov (y w)
  have hyi : (y ≫ p) ≫ σ i = y := (comp_section_eq_iff p (σ i) (hσ i) y w).2 hi
  rw [hy] at hyi
  refine ⟨i, hyi, fun j hj => ?_⟩
  obtain ⟨s, hs⟩ := hi
  refine hdisj j i (x w) s ?_
  rw [hs, ← hj, Scheme.Hom.comp_apply]

theorem comp_linComb {A T T' : Over S} [GrpObj A] (f : T' ⟶ T) {n : ℕ} (y : Fin n → (T ⟶ A))
    (a : Fin n → ℕ) : f ≫ Out.linComb y a = Out.linComb (fun i => f ≫ y i) a := by
  unfold Out.linComb
  let φ : (T ⟶ A) →* (T' ⟶ A) :=
    { toFun := fun g => f ≫ g, map_one' := MonObj.comp_one f, map_mul' := MonObj.comp_mul f }
  have hφ := map_list_prod φ (List.ofFn fun i => y i ^ a i)
  simpa [φ, List.map_ofFn, Function.comp_def, MonObj.comp_pow] using hφ

theorem linComb_pow_eq_one {A T : Over S} [GrpObj A] [IsCommMonObj A] {n k : ℕ}
    (y : Fin n → (T ⟶ A)) (hy : ∀ i, y i ^ k = 1) (a : Fin n → ℕ) :
    Out.linComb y a ^ k = 1 := by
  unfold Out.linComb
  rw [List.prod_ofFn, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← pow_mul, mul_comm, pow_mul, hy i, one_pow]

end GlobalTheory.DenseBasis

namespace GlobalTheory


open DenseBasis LatticeTorsion in
theorem torsion_basis_of_dense :
    ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (k r : ℕ) (pt : Fin r → (Out.baseOver S ⟶ A)) (Sg : Set S), IsAbelianScheme A → 0 < k → IsUnit (k : Γ(S, ⊤)) → (∀ i, pt i ^ k = 1) → Dense Sg → (∀ p ∈ Sg, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : Sp K ⟶ S), p ∈ Set.range x ∧ ∀ y : Over.mk x ⟶ A, y ^ k = 1 → ∃! c : Fin r → ZMod k, Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ pt i) (fun i => (c i).val) = y) → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ A), y ^ k = 1 → ∃! c : Fin r → ZMod k, Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ pt i) (fun i => (c i).val) = y := by
  intro S A _ k r pt Sg hA hk hku hpt hD hSg K _ _ x y hy
  have : IsCommMonObj A := hA.comm
  have : NeZero k := ⟨hk.ne'⟩
  obtain ⟨Z, et, hZf, hZe, hadd, hkill, huniv⟩ :=
    exists_finiteEtale_latticeTorsionHom S A k ℤ hA hku
  have := hZf
  have := hZe

  have het : ∀ m : ℤ, et m = et 1 ^ m := by
    have h0 : et 0 = 1 := by
      have h00 := hadd 0 0
      rw [add_zero] at h00
      exact left_eq_mul.mp h00
    intro m
    induction m using Int.induction_on with
    | zero => simpa using h0
    | succ n ih => rw [hadd, ih, zpow_add_one]
    | pred n ih =>
      have hn := hadd (-(n : ℤ) - 1) 1
      rw [sub_add_cancel, ih] at hn
      rw [zpow_sub_one, hn, mul_inv_cancel_right]

  have hfac : ∀ (T : Over S) (a : T ⟶ A), a ^ k = 1 → ∃! g : T ⟶ Z, g ≫ et 1 = a := by
    intro T a ha
    obtain ⟨g, hg, hgu⟩ := huniv T (fun m => a ^ m) (fun m c => zpow_add a m c) (fun m => by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow])
    refine ⟨g, by simpa using hg 1, fun g' hg' => hgu g' fun m => ?_⟩
    rw [het m, GrpObj.comp_zpow, hg']
  have hktor : ∀ (T : Over S) (g : T ⟶ Z), (g ≫ et 1) ^ k = 1 := fun T g => by
    rw [← MonObj.comp_pow, hkill 1, MonObj.comp_one]

  have hP : ∀ c : Fin r → ZMod k, Out.linComb pt (fun i => (c i).val) ^ k = 1 :=
    fun c => linComb_pow_eq_one pt hpt _
  choose h hh using fun c => (hfac _ _ (hP c)).exists
  have hsec : ∀ c, (h c).left ≫ Z.hom = 𝟙 S := fun c => by
    rw [Over.w (h c)]
    rfl
  have key : ∀ (K' : Type) [Field K'] (x' : Sp K' ⟶ S) (Y' : Over.mk x' ⟶ Z)
      (c : Fin r → ZMod k),
      Out.linComb (fun i => (Over.homMk x' (by simp) : Over.mk x' ⟶ Out.baseOver S) ≫ pt i)
        (fun i => (c i).val) = Y' ≫ et 1 ↔ x' ≫ (h c).left = Y'.left := by
    intro K' _ x' Y' c
    rw [← comp_linComb, ← hh c, ← Category.assoc]
    constructor
    · intro he
      have he' := (hfac _ (Y' ≫ et 1) (hktor _ Y')).unique he rfl
      rw [← he']
      simp
    · intro he
      have he' : (Over.homMk x' (by simp) : Over.mk x' ⟶ Out.baseOver S) ≫ h c = Y' := by
        ext
        simpa using he
      rw [he']
  have hdense : ∀ t ∈ Sg, ∃ (K' : Type) (_ : Field K') (_ : IsAlgClosed K')
      (x' : Spec (.of K') ⟶ S), t ∈ Set.range x' ∧
        ∀ y' : Spec (.of K') ⟶ Z.left, y' ≫ Z.hom = x' →
          ∃! c, x' ≫ (fun c => (h c).left) c = y' := by
    intro t ht
    obtain ⟨K', _, _, x', hx', H⟩ := hSg t ht
    refine ⟨K', inferInstance, inferInstance, x', hx', fun y' hy' => ?_⟩
    obtain ⟨c, hc1, hc2⟩ := H _ (hktor _ (Over.homMk y' hy' : Over.mk x' ⟶ Z))
    exact ⟨c, (key K' x' _ c).1 hc1, fun c' hc' => hc2 c' ((key K' x' _ c').2 hc')⟩
  obtain ⟨Y', hY', -⟩ := hfac (Over.mk x) y hy
  obtain ⟨c, hc1, hc2⟩ := existsUnique_section_of_dense Z.hom (fun c => (h c).left) hsec Sg hD
    hdense K x Y'.left (by simp [Over.w Y'])
  refine ⟨c, ?_, fun c' hc' => hc2 c' ?_⟩
  · rw [← hY']
    exact (key K x Y' c).2 hc1
  · rw [← hY'] at hc'
    exact (key K x Y' c').1 hc'

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.FiniteImage

open GlobalTheory.DenseFibreIso

theorem exists_isClosedImmersion_restrict {R : Type} [CommRing R] {U Z : Scheme.{0}}
    (s : Z ⟶ Sp R) (u : U ⟶ Z) [IsFinite u] (K : Type) [Field K] [Algebra R K]
    (hc : IsClosedImmersion (pullback.snd u (pullback.fst s (spMap (algebraMap R K)))))
    (x : Z) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) :
    ∃ V : Z.Opens, x ∈ V ∧ IsClosedImmersion (u ∣_ V) := by
  obtain ⟨A, B, ψ, φ, j, j', _, ⟨y, rfl⟩, H, hj⟩ := exists_chart s u x
  let : Algebra R A := ψ.hom.toAlgebra
  let : Algebra A B := φ.hom.toAlgebra
  replace H : IsPullback (spMap (algebraMap A B)) j' j u := H
  replace hj : j ≫ s = spMap (algebraMap R A) := hj
  have H₁ := isPullback_tensor R A K
  obtain ⟨m, hm, -⟩ := Scheme.exists_preimage_of_isPullback H₁ y (⊥ : PrimeSpectrum K) (by
    rw [← hj, Scheme.Hom.comp_apply]
    exact PrimeSpectrum.ext hx.symm)
  have H₂ := (isPullback_tensor A (A ⊗[R] K) B).paste_vert H
  have H₀ := (IsPullback.of_hasPullback u (pullback.fst s (spMap (algebraMap R K)))).flip
  have hw : (spMap (algebraMap A (A ⊗[R] K)) ≫ j) ≫ s =
      spMap (Algebra.TensorProduct.includeRight.toRingHom : K →+* A ⊗[R] K) ≫
        spMap (algebraMap R K) := by
    rw [Category.assoc, hj]; exact H₁.w
  have e : pullback.lift _ _ hw ≫ pullback.fst s _ = _ := pullback.lift_fst _ _ _
  have H₃ := IsPullback.of_bot' (v₁₂ := pullback.lift _ _ hw) (by rw [e]; exact H₂) H₀
  have hi := MorphismProperty.of_isPullback (P := @IsClosedImmersion) H₃.flip hc
  have hs : Function.Surjective
      (Algebra.TensorProduct.includeLeftRingHom : (A ⊗[R] K) →+* (A ⊗[R] K) ⊗[A] B) := by
    have h2 := (IsClosedImmersion.isAffine_surjective_of_isAffine (spMap
      (Algebra.TensorProduct.includeLeftRingHom : (A ⊗[R] K) →+* (A ⊗[R] K) ⊗[A] B))).2
    have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : (A ⊗[R] K) →+* (A ⊗[R] K) ⊗[A] B))
    have h3 := (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of ((A ⊗[R] K) ⊗[A] B))).hom).2.comp h2
    rw [← ConcreteCategory.coe_comp, e, ConcreteCategory.coe_comp] at h3
    exact h3.of_comp
  have h1 : IsFinite (spMap (algebraMap A B)) :=
    MorphismProperty.of_isPullback (P := @IsFinite) H.flip ‹_›
  have : Module.Finite A B := RingHom.finite_algebraMap.1 ((IsFinite.SpecMap_iff _).1 h1)
  obtain ⟨a, ha, ha'⟩ := exists_away_surjective (A ⊗[R] K) hs m
  have hQ := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom _) ha'
  have H₄ := (isPullback_tensor A (Localization.Away a) B).paste_vert H
  let g := spMap (algebraMap A (Localization.Away a)) ≫ j
  refine ⟨g.opensRange, ?_, ?_⟩
  · have hy : y ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away a))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away a) a, ← hm]
      exact ha
    obtain ⟨z, rfl⟩ := hy
    exact ⟨z, Scheme.Hom.comp_apply _ _ _⟩
  · have H' := H₄.of_iso (Iso.refl _) g.isoOpensRange (Iso.refl _) (Iso.refl _)
      (fst' := _ ≫ g.isoOpensRange.hom) (snd' := _) (f' := g.opensRange.ι) (g' := u)
      (Category.id_comp _).symm ((Category.comp_id _).trans (Category.id_comp _).symm)
      (by simp [g]) (by simp)
    have H'' := isPullback_morphismRestrict u g.opensRange
    rw [← H''.isoIsPullback_hom_fst _ _ H',
      MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion,
      MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion]
    exact hQ

theorem restrict_sSup (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q]
    {U Z : Scheme.{0}} (u : U ⟶ Z) :
    Q (u ∣_ sSup {V : Z.Opens | Q (u ∣_ V)}) := by
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict fun x => ?_
  obtain ⟨V, hV, hx⟩ := TopologicalSpace.Opens.mem_sSup.1 x.2
  refine ⟨(sSup {V : Z.Opens | Q (u ∣_ V)}).ι ⁻¹ᵁ V, hx, ?_⟩
  rw [Q.arrow_mk_iso_iff (morphismRestrictRestrict _ _ _)]
  refine (Q.arrow_mk_iso_iff (morphismRestrictEq u ?_)).2 hV
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.2 (le_sSup hV)

theorem dense_of_flat {O : Type} [CommRing O] [IsDomain O] {T : Scheme.{0}} (t : T ⟶ Sp O)
    [Flat t] (W : Set T) (hW : ∀ x : T, (t x).asIdeal = ⊥ → x ∈ W) : Dense W := by
  intro x
  have hsp : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O) ⤳ t x :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (show (⊥ : Ideal O) ≤ _ from bot_le)
  obtain ⟨y, hy, hy'⟩ := Flat.generalizingMap t hsp
  exact hy.mem_closed isClosed_closure (subset_closure (hW y (by rw [hy'])))

theorem main : ∀ (O F : Type) [CommRing O] [IsDedekindDomain O] [Field F] [Algebra O F] [IsFractionRing O F] (U Z : Scheme.{0}) (u : U ⟶ Z) (s : Z ⟶ Sp O), IsFinite u → IsReduced U → Flat (u ≫ s) → LocallyOfFiniteType s → QuasiCompact s → IsClosedImmersion (pullback.snd u (pullback.fst s (spMap (algebraMap O F)))) → ∃ (XX : Scheme.{0}) (u' : U ⟶ XX) (i : XX ⟶ Z) (W : XX.Opens), u' ≫ i = u ∧ IsClosedImmersion i ∧ IsFinite u' ∧ Surjective u' ∧ Dense (W : Set XX) ∧ IsIso (u' ∣_ W) ∧ Dense ((u' ⁻¹ᵁ W : U.Opens) : Set U) ∧ IsReduced XX ∧ Flat (i ≫ s) := by
  intro O F _ _ _ _ _ U Z u s _ _ _ _ _ hc
  let W₀ : Z.Opens := sSup {V : Z.Opens | IsClosedImmersion (u ∣_ V)}
  have hW₀ : IsClosedImmersion (u ∣_ W₀) := restrict_sSup @IsClosedImmersion u
  have hmem : ∀ z : Z, (s z).asIdeal = ⊥ → z ∈ W₀ := fun z hz => by
    obtain ⟨V, hV, hV'⟩ := exists_isClosedImmersion_restrict s u F hc z (by
      rw [hz]; exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective O F))
    exact TopologicalSpace.Opens.mem_sSup.2 ⟨V, hV', hV⟩
  have hfl : Flat (u.imageι ≫ s) := flat_image_of_isDedekindDomain (O := CommRingCat.of O) u s
  have : IsFinite (u.toImage ≫ u.imageι) := by rw [u.toImage_imageι]; infer_instance
  have hfin : IsFinite u.toImage := IsFinite.of_comp _ u.imageι
  refine ⟨u.image, u.toImage, u.imageι, u.imageι ⁻¹ᵁ W₀, u.toImage_imageι, inferInstance, hfin,
    surjective_of_isDominant_of_isClosed_range _ u.toImage.isClosedMap.isClosed_range,
    dense_of_flat (u.imageι ≫ s) _ fun x hx => hmem _ (by rwa [← Scheme.Hom.comp_apply]), ?_,
    dense_of_flat (u ≫ s) _ fun x hx => ?_, inferInstance, hfl⟩
  · have h1 : IsClosedImmersion ((u.toImage ≫ u.imageι) ∣_ W₀) := by
      have : ∀ v : U ⟶ Z, v = u → IsClosedImmersion (v ∣_ W₀) := by rintro _ rfl; exact hW₀
      exact this _ u.toImage_imageι
    rw [morphismRestrict_comp] at h1
    have h2 : IsClosedImmersion (u.toImage ∣_ u.imageι ⁻¹ᵁ W₀) :=
      @IsClosedImmersion.of_comp _ _ _ _ (u.imageι ∣_ W₀) h1 _
    have h3 : IsSchemeTheoreticallyDominant (u.toImage ∣_ u.imageι ⁻¹ᵁ W₀) :=
      IsSchemeTheoreticallyDominant.of_isPullback
        (isPullback_morphismRestrict u.toImage (u.imageι ⁻¹ᵁ W₀)).flip
    exact isIso_of_isClosedImmersion_of_schemeDominant _
  · change u.imageι (u.toImage x) ∈ W₀
    rw [← Scheme.Hom.comp_apply, u.toImage_imageι]
    exact hmem _ (by rwa [← Scheme.Hom.comp_apply])

end GlobalTheory.FiniteImage
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

variable {S : Scheme.{0}} {I : Type} {U : I → S.Opens} {A : Over S} [GrpObj A] {G : ∀ i, Over (U i).toScheme}
  [∀ i, GrpObj (G i)] {ψ : ∀ i, (G i).left ⟶ A.left}

private theorem isGrpPullback_one_left {X' X : Scheme.{0}} {H' : Over X'} [GrpObj H'] {H : Over X} [GrpObj H]
    {g : X' ⟶ X} {φ : H'.left ⟶ H.left} (h : IsGrpPullback H' H g φ) (T : Over X') :
    (1 : Over.mk (T.hom ≫ g) ⟶ H).left = (1 : T ⟶ H').left ≫ φ := by
  have hw : ((1 : T ⟶ H').left ≫ φ) ≫ H.hom = (Over.mk (T.hom ≫ g)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    rfl
  let z : Over.mk (T.hom ≫ g) ⟶ H := Over.homMk ((1 : T ⟶ H').left ≫ φ) hw
  have hz : z * z = z := by
    apply Over.OverMorphism.ext
    rw [h.2 T 1 1 z z rfl rfl, _root_.mul_one]
    rfl
  have hz1 : z = 1 := _root_.mul_eq_left.mp hz
  rw [← hz1]
  rfl

private theorem pow_left_eq_pow_left_comp_of_isGrpPullback {X' X : Scheme.{0}} {H' : Over X'} [GrpObj H'] {H : Over X} [GrpObj H]
    {g : X' ⟶ X} {φ : H'.left ⟶ H.left} (h : IsGrpPullback H' H g φ) {T : Over X'} (y : T ⟶ H')
    (z : Over.mk (T.hom ≫ g) ⟶ H) (hz : z.left = y.left ≫ φ) (n : ℕ) :
    (z ^ n).left = (y ^ n).left ≫ φ := by
  induction n with
  | zero => simpa only [_root_.pow_zero] using isGrpPullback_one_left h T
  | succ n ih =>
    rw [_root_.pow_succ, _root_.pow_succ]
    exact h.2 T _ _ _ _ ih hz

theorem pow_eq_one_of_cover (hU : iSup U = ⊤) (hψ : ∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) (k : ℕ)
    (x : Out.baseOver S ⟶ A) (x' : ∀ i, Out.baseOver (U i).toScheme ⟶ G i)
    (hx : ∀ i, (x' i).left ≫ ψ i = (U i).ι ≫ x.left) (hk : ∀ i, x' i ^ k = 1) : x ^ k = 1 := by
  refine over_ext hU fun i T' r => ?_
  rw [MonObj.comp_pow, MonObj.comp_one]
  have hr : r.left = T'.hom ≫ (U i).ι := by simpa using Over.w r
  let t : T' ⟶ Out.baseOver (U i).toScheme := Over.homMk T'.hom (by simp)
  have hy : (t ≫ x' i) ^ k = 1 := by rw [← MonObj.comp_pow, hk, MonObj.comp_one]
  have key := pow_left_eq_pow_left_comp_of_isGrpPullback (hψ i) (t ≫ x' i) (r ≫ x) (by simp [t, hr, hx]) k
  rw [hy, ← isGrpPullback_one_left (hψ i) T'] at key
  exact Over.OverMorphism.ext key

private theorem mul_comp_of_cover_isGrpPullback_isMonHom (hU : iSup U = ⊤) (hψ : ∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) (f : A ⟶ A)
    (f' : ∀ i, G i ⟶ G i) (hf : ∀ i, (f' i).left ≫ ψ i = ψ i ≫ f.left) (hm : ∀ i, IsMonHom (f' i))
    {T : Over S} (a b : T ⟶ A) : (a * b) ≫ f = (a ≫ f) * (b ≫ f) := by
  refine over_ext hU fun i T' r => ?_
  haveI := hm i
  obtain ⟨a', ha⟩ := exists_lift (hψ i).1 (r ≫ a)
  obtain ⟨b', hb⟩ := exists_lift (hψ i).1 (r ≫ b)
  have e1 := (hψ i).2 T' a' b' (r ≫ a) (r ≫ b) ha hb
  have ha' : (r ≫ a ≫ f).left = (a' ≫ f' i).left ≫ ψ i := by
    have := congrArg (· ≫ f.left) ha
    simp only [Over.comp_left, Category.assoc] at this ⊢
    rw [this, hf]
  have hb' : (r ≫ b ≫ f).left = (b' ≫ f' i).left ≫ ψ i := by
    have := congrArg (· ≫ f.left) hb
    simp only [Over.comp_left, Category.assoc] at this ⊢
    rw [this, hf]
  have e2 := (hψ i).2 T' (a' ≫ f' i) (b' ≫ f' i) (r ≫ a ≫ f) (r ≫ b ≫ f) ha' hb'
  have e3 : (a' * b') ≫ f' i = (a' ≫ f' i) * (b' ≫ f' i) := MonObj.mul_comp _ _ _
  apply Over.OverMorphism.ext
  rw [← Category.assoc, MonObj.comp_mul, MonObj.comp_mul, Over.comp_left, e1, e2, ← e3, Over.comp_left]
  simp only [Category.assoc, hf]

theorem isMonHom_of_cover (hU : iSup U = ⊤) (hψ : ∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) (f : A ⟶ A)
    (f' : ∀ i, G i ⟶ G i) (hf : ∀ i, (f' i).left ≫ ψ i = ψ i ≫ f.left) (hm : ∀ i, IsMonHom (f' i)) :
    IsMonHom f := by
  have hmul : ∀ {T : Over S} (a b : T ⟶ A), (a * b) ≫ f = (a ≫ f) * (b ≫ f) :=
    fun a b => mul_comp_of_cover_isGrpPullback_isMonHom hU hψ f f' hf hm a b
  have hone : ∀ {T : Over S}, (1 : T ⟶ A) ≫ f = 1 := by
    intro T
    have h1 := hmul (1 : T ⟶ A) 1
    rw [_root_.mul_one] at h1
    exact _root_.mul_eq_left.mp h1.symm
  refine ⟨?_, ?_⟩
  · rw [MonObj.one_eq_one]
    exact hone
  · rw [MonObj.mul_eq_mul, hmul, MonObj.comp_mul]
    simp

theorem tors_and_isMonHom_of_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → (∀ (k : ℕ) (x : Out.baseOver S ⟶ A) (x' : ∀ i, Out.baseOver (U i).toScheme ⟶ G i), (∀ i, (x' i).left ≫ ψ i = (U i).ι ≫ x.left) → (∀ i, x' i ^ k = 1) → x ^ k = 1) ∧ ∀ (f : A ⟶ A) (f' : ∀ i, G i ⟶ G i), (∀ i, (f' i).left ≫ ψ i = ψ i ≫ f.left) → (∀ i, IsMonHom (f' i)) → IsMonHom f := by
  intro S I U A _ G _ ψ hU hψ _ _
  exact ⟨fun k x x' hx hk => pow_eq_one_of_cover hU hψ k x x' hx hk,
    fun f f' hf hm => isMonHom_of_cover hU hψ f f' hf hm⟩

end GlobalTheory.CoverGlue
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.torsion_points_descend_field_extension : Out.Laws → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (K Ω : Type) [Field K] [Field Ω] [IsAlgClosed K] (i : K →+* Ω) (x : Sp K ⟶ S), Function.Injective (fun y : Over.mk x ⟶ P.A => (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y) ∧ ∀ (n : ℕ) (z : Over.mk (spMap i ≫ x) ⟶ P.A), (n : K) ≠ 0 → z ^ n = 1 → ∃ y : Over.mk x ⟶ P.A, y ^ n = 1 ∧ (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y = z := by
  first | exact @GlobalTheory.torsion_points_field_extension | exact GlobalTheory.torsion_points_field_extension | (intros; apply GlobalTheory.torsion_points_field_extension <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.rigidified_partialLineBundle_iso_cocycle : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (e : S ⟶ X) (V₁ V₂ V₃ : S.Opens) (M₁ M₂ M₃ : LB X) (w₁₂ : LB.Iso M₂ M₁) (w₂₃ : LB.Iso M₃ M₂) (w₁₃ : LB.Iso M₃ M₁), e ≫ p = 𝟙 S → (∀ (V : S.Opens) (u : Γ(X, p ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (p ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1) → ⨆ a, M₁.U a = p ⁻¹ᵁ V₁ → ⨆ a, M₂.U a = p ⁻¹ᵁ V₂ → ⨆ a, M₃.U a = p ⁻¹ᵁ V₃ → w₁₂.IsGen → w₂₃.IsGen → w₁₃.IsGen → (∀ (x : S) a b c, e x ∈ M₁.U a → e x ∈ M₂.U b → e x ∈ M₃.U c → gm e x (M₁.U a ⊓ M₂.U b) (w₁₂.s (a, b)) * gm e x (M₂.U b ⊓ M₃.U c) (w₂₃.s (b, c)) = gm e x (M₁.U a ⊓ M₃.U c) (w₁₃.s (a, c))) → ∀ (y : X) a b c, y ∈ M₁.U a → y ∈ M₂.U b → y ∈ M₃.U c → gm (𝟙 X) y (M₁.U a ⊓ M₂.U b) (w₁₂.s (a, b)) * gm (𝟙 X) y (M₂.U b ⊓ M₃.U c) (w₂₃.s (b, c)) = gm (𝟙 X) y (M₁.U a ⊓ M₃.U c) (w₁₃.s (a, c)) := by
  first | exact @GlobalTheory.PartialCocycle.cocycle_of_rigid | exact GlobalTheory.PartialCocycle.cocycle_of_rigid | (intros; apply GlobalTheory.PartialCocycle.cocycle_of_rigid <;> assumption)
end
