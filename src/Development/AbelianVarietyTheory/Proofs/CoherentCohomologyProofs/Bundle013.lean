module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsIsoToInterAppPushforwardInclusion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle003
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsGradedMapLinearCombination
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.QuotSMulTop
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsXPowSmulEqZeroOfEqXSubOneSmul
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open scoped Pointwise

namespace GlobalTheory

theorem nonempty_homLoc_singleton_equiv_quotSMulTop : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι), Nonempty (homLoc ℳ {i} 0 ≃ₗ[R] QuotSMulTop (X i - 1 : MvPolynomial ι R) M) := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ i
  obtain ⟨-, h2, h3⟩ := GlobalTheory.X_sub_one_smul_graded ι R M ℳ i
  let K : Submodule (MvPolynomial ι R) M := (X i - 1 : MvPolynomial ι R) • ⊤
  have hK : ∀ y : M, y ∈ K ↔ ∃ w : M, y = (X i - 1 : MvPolynomial ι R) • w := fun y => by
    rw [Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨w, _, h⟩ => ⟨w, h.symm⟩, fun ⟨w, h⟩ => ⟨w, trivial, h.symm⟩⟩
  let φ : ∀ k : ℕ, ℳ (0 + k * (({i} : Finset ι).card : ℤ)) →ₗ[R]
      QuotSMulTop (X i - 1 : MvPolynomial ι R) M :=
    fun k => (K.mkQ.restrictScalars R) ∘ₗ (ℳ _).subtype
  have hφv : ∀ k m, φ k m = Submodule.Quotient.mk (m : M) := fun _ _ => rfl
  have hφ : ∀ (k : ℕ) (m : ℳ (0 + k * (({i} : Finset ι).card : ℤ)))
      (m' : ℳ (0 + (k + 1 : ℕ) * (({i} : Finset ι).card : ℤ))),
      (m' : M) = xProd R {i} • (m : M) → φ (k + 1) m' = φ k m := by
    intro k m m' h
    rw [hφv, hφv, Submodule.Quotient.eq]
    refine (hK _).2 ⟨m, ?_⟩
    rw [h, sub_smul, one_smul, xProd, Finset.prod_singleton]
  refine ⟨LinearEquiv.ofBijective (homLocLift φ hφ) ⟨?_, ?_⟩⟩
  · rw [homLocLift_injective_iff]
    intro k m hm
    rw [hφv, Submodule.Quotient.mk_eq_zero] at hm
    obtain ⟨w, hw⟩ := (hK _).1 hm
    obtain ⟨l, hl⟩ := h2 _ _ w m.2 hw
    exact ⟨l, by rwa [xProd, Finset.prod_singleton]⟩
  · rw [homLocLift_surjective_iff]
    intro t
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ t
    obtain ⟨n₀, hn⟩ := h3 y
    obtain ⟨y', hy', w, hw⟩ := hn (0 + (n₀.toNat : ℕ) * (({i} : Finset ι).card : ℤ))
      (by simp)
    refine ⟨n₀.toNat, ⟨y', hy'⟩, ?_⟩
    rw [hφv, eq_comm, Submodule.Quotient.eq]
    exact (hK _).2 ⟨w, by rw [hw, add_sub_cancel_left]⟩

end GlobalTheory
end

section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry Topology

universe u

noncomputable section

namespace GlobalTheory
namespace AffineVanishing

section Restriction

variable {X Y : TopCat.{u}} {j : Y ⟶ X} (hj : IsOpenEmbedding j)

lemma shortExact_map_sheafPullback {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    (hS : S.ShortExact) [(hj.sheafPullback AddCommGrpCat.{u}).PreservesZeroMorphisms] :
    (S.map (hj.sheafPullback AddCommGrpCat.{u})).ShortExact := by
  have h₁ : PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} j) :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits (Opens.map j) AddCommGrpCat.{u} _ _
  have h₂ : PreservesFiniteLimits (hj.sheafPullback AddCommGrpCat.{u}) :=
    preservesFiniteLimits_of_natIso (hj.sheafPullbackIso _)
  have h₃ : PreservesFiniteColimits (hj.sheafPullback AddCommGrpCat.{u}) :=
    preservesFiniteColimits_of_natIso (hj.sheafPullbackIso _)
  exact hS.map_of_exact _

lemma subsingleton_of_sheafPullback (V : Opens Y) (n : ℕ) (F : X.Sheaf AddCommGrpCat.{u})
    (h : Subsingleton (Sheaf.H'.{u} ((hj.sheafPullback AddCommGrpCat.{u}).obj F) (n + 1) V)) :
    Subsingleton (Sheaf.H'.{u} F (n + 1) (hj.functor.obj V)) := by
  haveI : (hj.sheafPullback AddCommGrpCat.{u}).PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
  induction n generalizing F with
  | zero =>
    have hS := Flasque.injectiveShortComplex_shortExact F
    exact SheafLES.subsingleton₁_one_of_sections_surjective.{u} hS _
      (SheafLES.sections_surjective_of_subsingleton.{u} (shortExact_map_sheafPullback hj hS) V h)
      (Flasque.subsingleton_H'_of_isFlasque _ 0 _)
  | succ n ih =>
    have hS := Flasque.injectiveShortComplex_shortExact F
    have hI : (Flasque.injectiveShortComplex F).X₂.IsFlasque := inferInstance
    have hI' : ((hj.sheafPullback AddCommGrpCat.{u}).obj
        (Flasque.injectiveShortComplex F).X₂).IsFlasque := ⟨fun _ ↦ hI.epi _⟩
    exact SheafLES.subsingleton₁.{u} hS (n + 1) _
      (ih _ (SheafLES.subsingleton₃.{u} (shortExact_map_sheafPullback hj hS) (n + 1) V
        (Flasque.subsingleton_H'_of_isFlasque _ (hF := hI') n V) h))
      (Flasque.subsingleton_H'_of_isFlasque _ (n + 1) _)

end Restriction

variable {X Y : Scheme.{u}}

lemma subsingleton_of_restrict (j : Y ⟶ X) [IsOpenImmersion j] (F : X.Modules) (V : Y.Opens)
    (n : ℕ) (h : Subsingleton (cohOn (F.restrict j) V (n + 1))) :
    Subsingleton (cohOn F (j ''ᵁ V) (n + 1)) :=
  subsingleton_of_sheafPullback j.isOpenEmbedding V n ((toAbSheaf X).obj F) h

abbrev interModule (F : X.Modules) (W : X.Opens) : X.Modules :=
  (Scheme.Modules.pushforward W.ι).obj (F.restrict W.ι)

abbrev toInterModule (F : X.Modules) (W : X.Opens) : F ⟶ interModule F W :=
  (Scheme.Modules.restrictAdjunction W.ι).unit.app F

lemma map_toInterModule_eq_zero (F : X.Modules) (W V : X.Opens) (n : ℕ) (α : cohOn F V n)
    (h : SheafLES.map.{u} ((Kempf.toInter AddCommGrpCat.{u} W).app ((toAbSheaf X).obj F)) n V
      (cohOn.toH' F V n α) = 0) :
    cohOn.map ℤ (toInterModule F W) V n α = 0 :=
  haveI : IsIso ((Kempf.toInter AddCommGrpCat.{u} W).app ((toAbSheaf X).obj (interModule F W))) :=
    Kempf.isIso_toInter_app_pushforward (A := AddCommGrpCat.{u}) W.ι.base W (fun y ↦ y.2)
      ((toAbSheaf W.toScheme).obj (F.restrict W.ι))
  Kempf.map_eq_zero_of_map_toInter_eq_zero.{u} ((toAbSheaf X).map (toInterModule F W)) h

lemma mono_lift_toInterModule (F : X.Modules) {ι : Type u} [Finite ι] (W : ι → X.Opens)
    (hW : ⊤ ≤ iSup W) : Mono (Pi.lift fun i ↦ toInterModule F (W i)) := by
  refine ⟨fun {Z} a b hab ↦ ?_⟩
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  ext s
  refine QCoh.section_eq_of_cover F (fun i ↦ (W i).ι ''ᵁ ((W i).ι ⁻¹ᵁ U))
    (fun i ↦ (W i).ι.image_preimage_le U) (fun x hx ↦ ?_) _ _ fun i ↦ ?_
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hW (Set.mem_univ x))
    exact Opens.mem_iSup.2 ⟨i, ⟨x, hi⟩, hx, rfl⟩
  · have h : a ≫ toInterModule F (W i) = b ≫ toInterModule F (W i) := by
      simpa using hab =≫ Pi.π _ i
    exact congr(($h).app U s)

lemma subsingleton_top [IsAffine X] (n : ℕ)
    (ih : ∀ q, 0 < q → q < n + 1 → ∀ (G : X.Modules) [G.IsQuasicoherent] (U : X.Opens),
      IsAffineOpen U → Subsingleton (cohOn G U q))
    (F : X.Modules) [F.IsQuasicoherent] : Subsingleton (cohOn F ⊤ (n + 1)) := by
  refine subsingleton_of_forall_eq 0 fun α ↦ ?_
  obtain ⟨𝔘, h𝔘, hfin, hsup, h0⟩ := Kempf.exists_finite_cover_map_toInter_eq_zero.{u}
    (X := X) (𝔅 := X.affineOpens) X.isBasis_affineOpens
    (fun B hB B' hB' ↦ IsAffineOpen.inf hB hB') ((toAbSheaf X).obj F) ⊤
    (isAffineOpen_top X).isCompact (Nat.le_add_left 1 n)
    (fun q hq hqn B hB ↦ ih q hq hqn F B hB) (cohOn.toH' F ⊤ (n + 1) α)
  haveI : Finite 𝔘 := hfin
  haveI (W : 𝔘) : IsAffine W.1 := h𝔘 W.2
  let φ : F ⟶ ∏ᶜ (fun W : 𝔘 ↦ interModule F W.1) := Pi.lift fun W ↦ toInterModule F W.1
  haveI : Mono φ := mono_lift_toInterModule F (fun W : 𝔘 ↦ W.1) (by
    rw [← sSup_eq_iSup', hsup])
  have hα : cohOn.map ℤ φ ⊤ (n + 1) α = 0 := by
    apply (cohOn.piEquiv ℤ ⊤ (n + 1) _).injective
    ext W
    simp only [cohOn.piEquiv_apply, cohOn.map_map, map_zero, φ, Pi.lift_comp_π]
    exact map_toInterModule_eq_zero F W.1 ⊤ (n + 1) α (h0 W.1 W.2)
  have hS : (ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)).ShortExact :=
    { exact := ShortComplex.exact_cokernel φ }
  have hT := SheafLES.shortExact_map_toAbSheaf hS
  have hinj : Function.Injective (SheafLES.map.{u} ((toAbSheaf X).map φ) (n + 1) ⊤) := by
    cases n with
    | zero =>
      exact SheafLES.map_f_one_injective_of_sections_surjective.{u} hT ⊤
        (QCoh.surjective_cokernel_π_app φ (isAffineOpen_top X))
    | succ n =>
      refine SheafLES.map_f_injective_of_surjective.{u} hT (n + 1) ⊤ fun y ↦ ⟨0, ?_⟩
      exact @Subsingleton.elim _ (ih (n + 1) n.succ_pos (by omega) (cokernel φ) ⊤
        (isAffineOpen_top X)) _ _
  exact (cohOn.toH' F ⊤ (n + 1)).injective (hinj (hα.trans (by
    rw [map_zero]; exact (map_zero _).symm)))

end AffineVanishing

open AffineVanishing

theorem cohOn.subsingleton_of_isAffineOpen {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} (hn : 0 < n) : Subsingleton (cohOn F U n) := by
  induction n using Nat.strong_induction_on generalizing X with
  | _ n ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
    haveI : IsAffine U := hU
    have h := subsingleton_of_restrict U.ι F ⊤ n
      (subsingleton_top n (fun q hq hqn G _ V hV ↦ ih q hqn G hV hq) (F.restrict U.ι))
    rwa [Scheme.Opens.ι_image_top] at h

theorem coh.subsingleton_of_isAffine {X : Scheme.{u}} [IsAffine X] (F : X.Modules)
    [F.IsQuasicoherent] {n : ℕ} (hn : 0 < n) : Subsingleton (coh F n) :=
  cohOn.subsingleton_of_isAffineOpen F (isAffineOpen_top X) hn

instance coh.subsingleton_succ_of_isAffine {X : Scheme.{u}} [IsAffine X] (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ) : Subsingleton (coh F (n + 1)) :=
  coh.subsingleton_of_isAffine F n.succ_pos

end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem dehomogenising_eq_zero_iff : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) (B : Type) [CommRing B] (π : MvPolynomial ι R →+* B) (P : Type) [AddCommGroup P] [Module B P] (ε : M →ₛₗ[π] P), π (X i) = 1 → (∀ n, ∀ y ∈ ℳ n, ε y = 0 → ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y = 0) → ∀ y, ε y = 0 ↔ ∃ w : M, y = (X i - 1 : MvPolynomial ι R) • w := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ i B _ π P _ _ ε hπ hker y
  have hkill : ∀ w : M, ε ((X i - 1 : MvPolynomial ι R) • w) = 0 := by
    intro w
    rw [ε.map_smulₛₗ, map_sub, hπ, map_one, sub_self, zero_smul]
  constructor
  · intro hy
    obtain ⟨n₀, hn⟩ := exists_homogeneous_add_X_sub_one_smul ℳ i y
    obtain ⟨y', hy', w, rfl⟩ := hn n₀ le_rfl
    have hε : ε y' = 0 := by
      rwa [map_add, hkill, add_zero] at hy
    obtain ⟨k, hk⟩ := hker n₀ y' hy' hε
    refine ⟨w - (∑ j ∈ Finset.range k, (X i : MvPolynomial ι R) ^ j) • y', ?_⟩
    rw [smul_sub, smul_smul, mul_geom_sum, sub_smul ((X i : MvPolynomial ι R) ^ k), hk, one_smul]
    abel
  · rintro ⟨w, rfl⟩
    exact hkill w

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open scoped Pointwise

namespace GlobalTheory

theorem exists_pow_smul_eq_add_sub_one_smul {S M : Type} [CommRing S] [AddCommGroup M]
    [Module S M] (x : S) (k : ℕ) (y : M) : ∃ w : M, x ^ k • y = y + (x - 1) • w := by
  refine ⟨(∑ j ∈ Finset.range k, x ^ j) • y, ?_⟩
  rw [smul_smul, mul_geom_sum, sub_smul, one_smul]
  abel

private lemma comap_ker_inf_smul_whole_eq_smul_whole_of_regular {S F G : Type} [CommRing S] [AddCommGroup F]
    [Module S F] [AddCommGroup G] [Module S G] (u : S) (φ : F →ₗ[S] G)
    (hreg : ∀ z : G, u • z = 0 → z = 0) :
    Submodule.comap (LinearMap.ker φ).subtype (LinearMap.ker φ ⊓ u • (⊤ : Submodule S F)) =
      u • (⊤ : Submodule S (LinearMap.ker φ)) := by
  ext x
  rw [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_inf]
  constructor
  · rintro ⟨-, hx⟩
    obtain ⟨v, -, hv⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    have hvK : v ∈ LinearMap.ker φ := by
      rw [LinearMap.mem_ker]
      apply hreg
      rw [← map_smul, hv]
      exact LinearMap.mem_ker.mp x.2
    have hx' : x = u • (⟨v, hvK⟩ : LinearMap.ker φ) := Subtype.ext hv.symm
    rw [hx']
    exact Submodule.smul_mem_pointwise_smul _ u ⊤ Submodule.mem_top
  · intro hx
    obtain ⟨b, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    refine ⟨(u • b).2, ?_⟩
    rw [Submodule.coe_smul]
    exact Submodule.smul_mem_pointwise_smul (b : F) u ⊤ Submodule.mem_top

private lemma ker_sup_smul_whole_eq_ker_mkQ_comp {S F G : Type} [CommRing S] [AddCommGroup F]
    [Module S F] [AddCommGroup G] [Module S G] (u : S) (φ : F →ₗ[S] G)
    (hker : ∀ (y : F) (w : G), φ y = u • w → ∃ (k v : F), φ k = 0 ∧ y = k + u • v) :
    LinearMap.ker φ ⊔ u • (⊤ : Submodule S F) =
      LinearMap.ker ((u • (⊤ : Submodule S G)).mkQ ∘ₗ φ) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · intro y hy
      rw [LinearMap.mem_ker] at hy ⊢
      rw [LinearMap.comp_apply, hy, map_zero]
    · intro y hy
      obtain ⟨v, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, map_smul]
      exact Submodule.smul_mem_pointwise_smul _ u ⊤ Submodule.mem_top
  · intro y hy
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hy
    obtain ⟨w, -, hw⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
    obtain ⟨k, v, hk, rfl⟩ := hker y w hw.symm
    exact Submodule.add_mem_sup (LinearMap.mem_ker.mpr hk)
      (Submodule.smul_mem_pointwise_smul v u ⊤ Submodule.mem_top)

theorem finite_quotSMulTop_ker_of_regular {S F G : Type} [CommRing S] [AddCommGroup F]
    [Module S F] [AddCommGroup G] [Module S G] (u : S) (φ : F →ₗ[S] G)
    (hreg : ∀ z : G, u • z = 0 → z = 0) [Module.Finite S F]
    [Module.FinitePresentation S (QuotSMulTop u G)]
    (hsurj : ∀ z : G, ∃ (y : F) (w : G), φ y = z + u • w)
    (hker : ∀ (y : F) (w : G), φ y = u • w → ∃ (k v : F), φ k = 0 ∧ y = k + u • v) :
    Module.Finite S (QuotSMulTop u (LinearMap.ker φ)) := by
  let ψ : F →ₗ[S] QuotSMulTop u G := (u • (⊤ : Submodule S G)).mkQ ∘ₗ φ
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective (u • (⊤ : Submodule S G)) z
    obtain ⟨y, w, hy⟩ := hsurj z
    refine ⟨y, ?_⟩
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hy, add_sub_cancel_left]
    exact Submodule.smul_mem_pointwise_smul w u ⊤ Submodule.mem_top
  have hfg : (LinearMap.ker ψ).FG := Module.FinitePresentation.fg_ker ψ hψ
  have hfin : Module.Finite S ↥(LinearMap.ker φ ⊔ u • (⊤ : Submodule S F)) := by
    rw [ker_sup_smul_whole_eq_ker_mkQ_comp u φ hker]
    exact Module.Finite.iff_fg.mpr hfg
  have h2 : Module.Finite S (LinearMap.ker φ ⧸ Submodule.comap (LinearMap.ker φ).subtype
      (LinearMap.ker φ ⊓ u • (⊤ : Submodule S F))) :=
    Module.Finite.equiv (LinearMap.quotientInfEquivSupQuotient (LinearMap.ker φ)
      (u • (⊤ : Submodule S F))).symm
  exact Module.Finite.equiv (Submodule.quotEquivOfEq _ (u • (⊤ : Submodule S (LinearMap.ker φ)))
    (comap_ker_inf_smul_whole_eq_smul_whole_of_regular u φ hreg))

theorem finite_quotSMulTop_ker_of_graded :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (F : Type) [AddCommGroup F] [Module R F] [Module (MvPolynomial ι R) F] [IsScalarTower R (MvPolynomial ι R) F] (ℱ : ℤ → Submodule R F) [PolyGradedSMul ι ℱ] [Decomposition ℱ] (G : Type) [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G] [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [PolyGradedSMul ι 𝒢] [Decomposition 𝒢] (φ : F →ₗ[MvPolynomial ι R] G) (i : ι), IsGradedMap ℱ 𝒢 φ → Module.Finite (MvPolynomial ι R) F → (∀ z : G, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range φ) → Module.FinitePresentation (MvPolynomial ι R) (QuotSMulTop (X i - 1 : MvPolynomial ι R) G) → Module.Finite (MvPolynomial ι R) (QuotSMulTop (X i - 1 : MvPolynomial ι R) (LinearMap.ker φ)) := by
  intro ι _ _ R _ F _ _ _ _ ℱ _ _ G _ _ _ _ 𝒢 _ _ φ i hφ hF hpow hfp
  obtain ⟨hregG, hkillG, -⟩ := X_sub_one_smul_graded ι R G 𝒢 i
  obtain ⟨-, -, hhomF⟩ := X_sub_one_smul_graded ι R F ℱ i
  refine finite_quotSMulTop_ker_of_regular (X i - 1 : MvPolynomial ι R) φ hregG ?_ ?_
  · intro z
    obtain ⟨k, hk⟩ := hpow z
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hk
    obtain ⟨w, hw⟩ := exists_pow_smul_eq_add_sub_one_smul (X i : MvPolynomial ι R) k z
    exact ⟨y, w, hy.trans hw⟩
  · intro y w hyw
    obtain ⟨n₀, hn⟩ := hhomF y
    obtain ⟨y', hy', v₀, hyv⟩ := hn n₀ le_rfl
    have hφy' : φ y' ∈ 𝒢 n₀ := hφ hy'
    have h1 : φ y = φ y' + (X i - 1 : MvPolynomial ι R) • φ v₀ := by
      rw [hyv, map_add (f := _), map_smul]
    have h2 : φ y' = (X i - 1 : MvPolynomial ι R) • (w - φ v₀) := by
      rw [smul_sub, ← hyw, h1]
      abel
    obtain ⟨k, hk⟩ := hkillG n₀ (φ y') (w - φ v₀) hφy' h2
    obtain ⟨w₁, hw₁⟩ := exists_pow_smul_eq_add_sub_one_smul (X i : MvPolynomial ι R) k y'
    refine ⟨(X i : MvPolynomial ι R) ^ k • y', v₀ - w₁, ?_, ?_⟩
    · rw [map_smul, hk]
    · rw [hyv, hw₁, smul_sub]
      abel

end GlobalTheory
end
