module

public import Development.EtaleCohomology.EtaleTrace.Bundle004
public import Development.EtaleCohomology.EtaleTrace.Bundle005
public import Mathlib.Tactic.ENatToNat
public import Development.EtaleCohomology.EtaleTrace.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
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
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

theorem hl_reduced (k : Type) [Field k] (d : ℕ) (P : Ideal (MvPolynomial (Fin (d + 1)) k)) [P.IsPrime] :
    _root_.IsReduced (HomogeneousLocalization.AtPrime (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) P) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨n, hn⟩ := ha
  apply HomogeneousLocalization.val_injective
  have h : a.val ^ n = 0 := by
    rw [← HomogeneousLocalization.val_pow, hn, HomogeneousLocalization.val_zero]
  rw [HomogeneousLocalization.val_zero]
  exact IsReduced.eq_zero _ ⟨n, h⟩

theorem pn_reduced (k : Type) [Field k] (d : ℕ) : IsReduced (PN k d) := by
  have : ∀ x : PN k d, _root_.IsReduced ((PN k d).presheaf.stalk x) := by
    intro x
    haveI : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
    haveI := hl_reduced k d x.asHomogeneousIdeal.toIdeal
    let e := Proj.stalkIso' (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) x
    exact isReduced_of_injective e.toRingHom e.injective
  exact isReduced_of_isReduced_stalk _

theorem mvPolynomial_irrelevantIdeal_not_le_bot_projective (k : Type) [Field k] (d : ℕ) :
    ¬ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) ≤ ⊥ := by
  intro h
  have hm : (X 0 : MvPolynomial (Fin (d + 1)) k) ∈ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) := by
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply]
    exact DirectSum.decompose_of_mem_ne _ ((MvPolynomial.mem_homogeneousSubmodule _ _).2 (isHomogeneous_X k 0)) (by decide)
  have h2 : (X 0 : MvPolynomial (Fin (d + 1)) k) ∈ (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k)).toIdeal := h hm
  rw [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at h2
  exact X_ne_zero _ h2

def gen (k : Type) [Field k] (d : ℕ) : PN k d where
  asHomogeneousIdeal := ⊥
  isPrime := by
    show (⊥ : Ideal (MvPolynomial (Fin (d + 1)) k)).IsPrime
    exact Ideal.isPrime_bot
  not_irrelevant_le := mvPolynomial_irrelevantIdeal_not_le_bot_projective k d

theorem pn_irred (k : Type) [Field k] (d : ℕ) : IrreducibleSpace (PN k d) := by
  rw [irreducibleSpace_def]
  have : (Set.univ : Set (PN k d)) = closure {gen k d} := by
    ext y
    simp only [Set.mem_univ, true_iff]
    exact (ProjectiveSpectrum.le_iff_mem_closure (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) (gen k d) y).1
      (show (gen k d).asHomogeneousIdeal ≤ y.asHomogeneousIdeal from bot_le)
  change IsIrreducible (Set.univ : Set (PN k d))
  rw [this]
  exact isIrreducible_singleton.closure

theorem PNIntegral_of : PNIntegral := fun k _ d => by
  haveI := pn_reduced k d
  haveI := pn_irred k d
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end LateralTheory.EtaleTrace.Cov
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov.GenInPf

variable {k : Type} [Field k] {N : ℕ}

def pg {X : Scheme.{0}} [IsIntegral X] (ι : X ⟶ PN (k := k) N) (U : (PN (k := k) N).Opens)
    (hU : genericPoint X ∈ ι ⁻¹ᵁ U) : Γ(PN (k := k) N, U) →+* X.functionField :=
  (ι.app U ≫ X.presheaf.germ _ (genericPoint X) hU).hom

theorem pg_res {X : Scheme.{0}} [IsIntegral X] (ι : X ⟶ PN (k := k) N) {U V : (PN (k := k) N).Opens} (hVU : V ≤ U)
    (hV : genericPoint X ∈ ι ⁻¹ᵁ V) (hU : genericPoint X ∈ ι ⁻¹ᵁ U) (s : Γ(PN (k := k) N, U)) :
    pg ι V hV ((PN (k := k) N).presheaf.map (homOfLE hVU).op s) = pg ι U hU s := by
  show (((PN (k := k) N).presheaf.map (homOfLE hVU).op ≫ ι.app V) ≫ X.presheaf.germ _ _ hV).hom s = _
  rw [Scheme.Hom.naturality, Category.assoc, TopCat.Presheaf.germ_res]
  rfl

theorem away_eq {X : Scheme.{0}} [IsIntegral X] (ι : X ⟶ PN (k := k) N) {n : ℕ}
    (f : MvPolynomial (Fin (N + 1)) k) (hf : f ∈ A k N n) (h : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) f)
    (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ A k N (m • n)) :
    away ι f hf h m g hg = pg ι _ h (Proj.awayToSection _ f (Away.mk _ hf m g hg)) := rfl

theorem away_identity (x f g : MvPolynomial (Fin (N + 1)) k) {n m : ℕ} (hx : x ∈ A k N 1) (hf : f ∈ A k N n)
    (hg : g ∈ A k N (m • n)) (hf' : f ∈ A k N (n • 1)) (hg' : g ∈ A k N ((m * n) • 1)) :
    awayMap (A k N) hx (show x * f = f * x from mul_comm _ _) (Away.mk _ hf m g hg) *
      awayMap (A k N) hf (show x * f = x * f from rfl) (Away.mk _ hx n f hf') ^ m =
      awayMap (A k N) hf (show x * f = x * f from rfl) (Away.mk _ hx (m * n) g hg') := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow, awayMap_mk,
    Away.val_mk, Localization.mk_pow, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, SubmonoidClass.coe_pow, OneMemClass.coe_one, one_mul]
  ring

theorem away_self_pow (x : MvPolynomial (Fin (N + 1)) k) (hx : x ∈ A k N 1) (n : ℕ)
    (h : x ^ n ∈ A k N (n • 1)) : Away.mk (A k N) hx n (x ^ n) h = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, HomogeneousLocalization.val_one]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp⟩

theorem away_self_pow' (x : MvPolynomial (Fin (N + 1)) k) (hx : x ∈ A k N 1) {m n : ℕ} (hmn : m = n)
    (h : x ^ n ∈ A k N (m • 1)) : Away.mk (A k N) hx m (x ^ n) h = 1 := by
  subst hmn; exact away_self_pow x hx m h

theorem key {X : Scheme.{0}} [IsIntegral X] (ι : X ⟶ PN (k := k) N) (i : Fin (N + 1))
    (hi : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i)) {n : ℕ}
    (f : MvPolynomial (Fin (N + 1)) k) (hf : f ∈ A k N n) (hfη : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) f)
    (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ A k N (m • n))
    (hf' : f ∈ A k N (n • 1)) (hg' : g ∈ A k N ((m * n) • 1)) :
    away ι f hf hfη m g hg * away ι (MvPolynomial.X i) (X_mem k N i) hi n f hf' ^ m =
      away ι (MvPolynomial.X i) (X_mem k N i) hi (m * n) g hg' := by
  have hF : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i * f) := by
    rw [Proj.basicOpen_mul]; exact ⟨hi, hfη⟩
  have e1 : ∀ y, pg ι _ hF (Proj.awayToSection _ (MvPolynomial.X i * f)
      (awayMap (A k N) hf (show MvPolynomial.X i * f = MvPolynomial.X i * f from rfl) y)) =
      pg ι _ hi (Proj.awayToSection _ (MvPolynomial.X i) y) := fun y => by
    have := congr($(Proj.awayMap_awayToSection (A k N) hf
      (show MvPolynomial.X i * f = MvPolynomial.X i * f from rfl)) y)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
    erw [this]
    exact pg_res ι _ hF hi _
  have e2 : ∀ y, pg ι _ hF (Proj.awayToSection _ (MvPolynomial.X i * f)
      (awayMap (A k N) (X_mem k N i) (show MvPolynomial.X i * f = f * MvPolynomial.X i from mul_comm _ _) y)) =
      pg ι _ hfη (Proj.awayToSection _ f y) := fun y => by
    have := congr($(Proj.awayMap_awayToSection (A k N) (X_mem k N i)
      (show MvPolynomial.X i * f = f * MvPolynomial.X i from mul_comm _ _)) y)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
    erw [this]
    exact pg_res ι _ hF hfη _
  rw [away_eq, away_eq, away_eq, ← e2, ← e1, ← e1, ← map_pow, ← map_mul, ← away_identity _ _ _ _ hf hg hf' hg',
    map_mul, map_pow]
  simp only [map_mul, map_pow]

theorem basicOpen_le (i : Fin (N + 1)) {n : ℕ} (hn : 0 < n) (f : MvPolynomial (Fin (N + 1)) k)
    (hf : f ∈ A k N n) (hf' : f ∈ A k N (n • 1)) :
    (PN (k := k) N).basicOpen (Proj.awayToSection (A k N) (MvPolynomial.X i) (Away.mk _ (X_mem k N i) n f hf')) ≤
      Proj.basicOpen (A k N) f := by
  intro y hy
  have hyU : y ∈ Proj.basicOpen (A k N) (MvPolynomial.X i) := (PN (k := k) N).basicOpen_le _ hy
  let y' : (Proj.basicOpen (A k N) (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)).toScheme := ⟨y, hyU⟩
  have h1 : y' ∈ (Proj.basicOpen (A k N) (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)).ι ⁻¹ᵁ
      (PN (k := k) N).basicOpen (Proj.awayToSection (A k N) (MvPolynomial.X i) (Away.mk _ (X_mem k N i) n f hf')) := hy
  rw [← Scheme.Opens.toSpecΓ_preimage_basicOpen, ← SpecMap_preimage_basicOpen] at h1
  have ht : Away.isLocalizationElem (X_mem k N i) hf = Away.mk _ (X_mem k N i) n f hf' := by
    apply val_injective; simp [Away.val_mk]
  have h2 : y' ∈ Proj.basicOpenToSpec (A k N) (MvPolynomial.X i) ⁻¹ᵁ
      PrimeSpectrum.basicOpen (Away.isLocalizationElem (X_mem k N i) hf) := by
    rw [ht]; exact h1
  rw [← Proj.awayι_preimage_basicOpen (A k N) (X_mem k N i) one_pos hf hn, ← Scheme.Hom.comp_preimage,
    ← Proj.basicOpenIsoSpec_inv_ι _ _ (X_mem k N i) one_pos, ← Proj.basicOpenIsoSpec_hom _ _ (X_mem k N i) one_pos,
    Iso.hom_inv_id_assoc] at h2
  exact h2

theorem GenOfAway_of : GenOfAway := by
  intro k _ X _ p N ι hp i h hE n hn f hf
  have hf' : f ∈ A k N (n • 1) := by simpa using hf
  have hfv : away ι (MvPolynomial.X i) (X_mem k N i) h n f hf' = eval₂ (kHom p) (coordAt ι i h) f := hE n f hf'
  refine ⟨⟨fun hfη => ?_, fun hne => ?_⟩, fun m g hg hfη => ?_⟩
  · have hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ^ n ∈ A k N (1 • n) := by
      simpa using SetLike.pow_mem_graded n (X_mem k N i)
    have hx' : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ^ n ∈ A k N ((1 * n) • 1) := by
      simpa using SetLike.pow_mem_graded n (X_mem k N i)
    have h1 : away ι (MvPolynomial.X i) (X_mem k N i) h (1 * n) _ hx' = 1 := by
      rw [away_eq, away_self_pow' _ _ (one_mul n), map_one, map_one]
    have := key ι i h f hf hfη 1 _ hx hf' hx'
    rw [h1, hfv] at this
    intro h0
    rw [h0] at this
    simp at this
  · have hu : IsUnit (X.presheaf.germ _ (genericPoint X) h
        (ι.app _ (Proj.awayToSection _ (MvPolynomial.X i) (Away.mk _ (X_mem k N i) n f hf')))) := by
      rw [← hfv] at hne; exact isUnit_iff_ne_zero.mpr hne
    rw [← Scheme.mem_basicOpen, ← Scheme.preimage_basicOpen] at hu
    exact basicOpen_le i hn f hf hf' hu
  · have hg' : g ∈ A k N ((m * n) • 1) := by simpa using hg
    have := key ι i h f hf hfη m g hg hf' hg'
    rw [hfv, hE (m * n) g hg'] at this
    exact this

end LateralTheory.EtaleTrace.Cov.GenInPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

lemma gub_stalk_inj {X : Scheme.{0}} [IsIntegral X] (x : X) :
    Function.Injective (algebraMap (X.presheaf.stalk x) X.functionField) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq a
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField] at ha
  have := Scheme.germToFunctionField_injective X U (ha.trans (map_zero _).symm)
  rw [this, map_zero]

lemma gub_notMem {k : Type} [Field k] {N : ℕ} (h : MvPolynomial (Fin (N + 1)) k) {d : ℕ}
    (hh : h ∈ homogeneousSubmodule (Fin (N + 1)) k d) (n : ℕ) (f : MvPolynomial (Fin (N + 1)) k)
    (hf : f ∈ homogeneousSubmodule (Fin (N + 1)) k (n • d)) (y : Proj (homogeneousSubmodule (Fin (N + 1)) k))
    (hy : y ∈ (Proj (homogeneousSubmodule (Fin (N + 1)) k)).basicOpen
      (Proj.awayToSection _ h (HomogeneousLocalization.Away.mk _ hh n f hf))) :
    y ∈ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) f := by
  obtain ⟨hyU, hu⟩ := (Scheme.mem_basicOpen'' _ _ _).mp hy
  have hu2 := hu.map (Proj.stalkIso' (homogeneousSubmodule (Fin (N + 1)) k) y)
  erw [Proj.stalkIso'_germ] at hu2
  rw [← HomogeneousLocalization.isUnit_iff_isUnit_val] at hu2
  erw [ProjectiveSpectrum.Proj.awayToSection_apply] at hu2
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk'] at hu2
  rw [Proj.mem_basicOpen]
  have hp : y.asHomogeneousIdeal.toIdeal.IsPrime := y.isPrime
  exact (IsLocalization.AtPrime.isUnit_mk'_iff (hI := hp) _ _ _ _).mp hu2

lemma gub_cover {k : Type} [Field k] {N : ℕ} (y : Proj (homogeneousSubmodule (Fin (N + 1)) k)) :
    ∃ i, y ∈ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) := by
  have hcov : ⨆ i, Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) = ⊤ := by
    apply Proj.iSup_basicOpen_eq_top'
    · exact fun i => ⟨1, (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X k i)⟩
    · rw [eq_top_iff]
      rintro a -
      induction a using MvPolynomial.induction_on with
      | C c =>
        have : (C c : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 0 :=
          (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_C _ c)
        exact Subalgebra.algebraMap_mem _ (⟨_, this⟩ : homogeneousSubmodule (Fin (N + 1)) k 0)
      | add a b ha hb => exact Subalgebra.add_mem _ ha hb
      | mul_X a i ha => exact Subalgebra.mul_mem _ ha (Algebra.subset_adjoin ⟨i, rfl⟩)
  have hm : y ∈ (⊤ : (Proj (homogeneousSubmodule (Fin (N + 1)) k)).Opens) := trivial
  rw [← hcov, TopologicalSpace.Opens.mem_iSup] at hm
  exact hm

theorem GenUseBack_of : GenUseBack := by
  intro k _ X _ p N ι v hG n hn f hf x hne hloc
  obtain ⟨i, hxi⟩ := gub_cover (ι x)
  have hXi : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1 :=
    (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X k i)
  have hxU : x ∈ ι ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) := hxi
  have hη := genUse_generic_mem _ x hxU
  have hvi : eval₂ (kHom p) v (MvPolynomial.X i) ≠ 0 := ((hG 1 one_pos _ hXi).1).mp hη
  have hf' : f ∈ homogeneousSubmodule (Fin (N + 1)) k (n • 1) := by
    rw [smul_eq_mul, mul_one]; exact (mem_homogeneousSubmodule _ _).mpr hf
  have key := (hG 1 one_pos _ hXi).2 n f hf' hη
  have : Nonempty (ι ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)) := ⟨⟨x, hxU⟩⟩
  have hγ : algebraMap _ X.functionField (X.presheaf.germ _ x hxU (ι.app _ (Proj.awayToSection _ (MvPolynomial.X i)
      (HomogeneousLocalization.Away.mk _ hXi n f hf')))) =
      eval₂ (kHom p) v f / eval₂ (kHom p) v (MvPolynomial.X i) ^ n := by
    rw [Scheme.algebraMap_germ_eq_germToFunctionField, eq_div_iff (pow_ne_zero _ hvi)]
    exact key
  have hg : ((MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ^ n).IsHomogeneous n := by
    simpa using (isHomogeneous_X k i).pow n
  obtain ⟨δ, hδ⟩ := hloc _ hg
  have hu : IsUnit (X.presheaf.germ _ x hxU (ι.app _ (Proj.awayToSection _ (MvPolynomial.X i)
      (HomogeneousLocalization.Away.mk _ hXi n f hf')))) := by
    refine isUnit_iff_exists_inv.mpr ⟨δ, gub_stalk_inj x ?_⟩
    rw [map_mul, map_one, hγ, hδ, eval₂_pow]
    have h1 := pow_ne_zero n hvi
    field_simp
  have hmem := (Scheme.mem_basicOpen'' _ _ _).mpr ⟨hxU, hu⟩
  rw [← Scheme.preimage_basicOpen] at hmem
  exact gub_notMem _ hXi n f hf' _ hmem

end LateralTheory.EtaleTrace.Cov
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov.GenInPf

variable {k : Type} [Field k] {N : ℕ}

theorem fromSpec_eq {f : MvPolynomial (Fin (N + 1)) k} {d : ℕ} (hf : f ∈ A k N d) (hd : 0 < d) :
    (Proj.isAffineOpen_basicOpen (A k N) f hf hd).fromSpec =
      Spec.map (Proj.awayToSection (A k N) f) ≫ Proj.awayι (A k N) f hf hd := by
  rw [IsAffineOpen.fromSpec, Iso.inv_comp_eq, Proj.awayι, ← Category.assoc, ← Category.assoc]
  have e : (Proj.isAffineOpen_basicOpen (A k N) f hf hd).isoSpec.hom ≫ Spec.map (Proj.awayToSection (A k N) f) =
      (Proj.basicOpenIsoSpec (A k N) f hf hd).hom := by
    rw [Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec, IsAffineOpen.isoSpec_hom]
  rw [e, Iso.hom_inv_id, Category.id_comp]

theorem constSecC {f : MvPolynomial (Fin (N + 1)) k} {d : ℕ} (hf : f ∈ A k N d) (hd : 0 < d) :
    (Scheme.ΓSpecIso (CommRingCat.of (A k N 0))).inv ≫
      (Proj.toSpecZero (A k N)).appLE ⊤ (Proj.basicOpen (A k N) f) le_top =
      CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom _ _) ≫ Proj.awayToSection (A k N) f := by
  have hU := Proj.isAffineOpen_basicOpen (A k N) f hf hd
  have key : hU.fromSpec ≫ Proj.toSpecZero (A k N) =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom _ _) ≫ Proj.awayToSection (A k N) f) := by
    rw [fromSpec_eq hf hd, Category.assoc, Proj.awayι_toSpecZero, Spec.map_comp]
  have h1 : (Proj.toSpecZero (A k N)).appLE ⊤ (Proj.basicOpen (A k N) f) le_top ≫
      hU.fromSpec.appLE _ ⊤ hU.fromSpec_preimage_self.ge =
      (hU.fromSpec ≫ Proj.toSpecZero (A k N)).appLE ⊤ ⊤ (by simp) := Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  simp only [key] at h1
  have h3 : hU.fromSpec.appLE _ ⊤ hU.fromSpec_preimage_self.ge = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg (_ ≫ ·) ((congrArg _ (Subsingleton.elim _ (𝟙 _))).trans ((Spec _).presheaf.map_id _))).trans
      (Category.comp_id _)
  have h4 : ∀ {R S : CommRingCat.{0}} (g : R ⟶ S) e, (Spec.map g).appLE ⊤ ⊤ e = (Spec.map g).appTop := fun _ _ => rfl
  rw [h3, h4] at h1
  rw [← cancel_mono (Scheme.ΓSpecIso _).inv, Category.assoc, h1, Scheme.ΓSpecIso_inv_naturality]

theorem kHom_eq {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (ι : X ⟶ PN k N) (hp : ι ≫ PNto k N = p)
    (i : Fin (N + 1)) (h : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i)) (c : k) :
    kHom p c = X.presheaf.germ _ (genericPoint X) h ((ι.app _).hom ((Proj.awayToSection (A k N) (MvPolynomial.X i)).hom
      (HomogeneousLocalization.fromZeroRingHom _ _ (algebraMap k (A k N 0) c)))) := by
  subst hp
  have hC := constSecC (X_mem k N i) one_pos
  have e1 : kHom (ι ≫ PNto k N) = ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (ι ≫ PNto k N).appLE ⊤ (ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i)) le_top ≫
      X.presheaf.germ _ (genericPoint X) h).hom := by
    rw [kHom, ← X.presheaf.germ_res (homOfLE (le_top : ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i) ≤ ⊤)) _ h]
    rfl
  have e2 : (ι ≫ PNto k N).appLE ⊤ (ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i)) le_top =
      (PNto k N).appLE ⊤ (Proj.basicOpen (A k N) (MvPolynomial.X i)) le_top ≫
        ι.appLE (Proj.basicOpen (A k N) (MvPolynomial.X i)) _ le_rfl :=
    (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have e3 : (PNto k N).appLE ⊤ (Proj.basicOpen (A k N) (MvPolynomial.X i)) le_top =
      (Spec.map (CommRingCat.ofHom (algebraMap k (A k N 0)))).appTop ≫
        (Proj.toSpecZero (A k N)).appLE ⊤ (Proj.basicOpen (A k N) (MvPolynomial.X i)) le_top :=
    Scheme.Hom.comp_appLE _ _ _ _ _
  have e4 : ι.appLE (Proj.basicOpen (A k N) (MvPolynomial.X i)) _ le_rfl = ι.app _ := Scheme.Hom.appLE_eq_app _
  have e5 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (ι ≫ PNto k N).appLE ⊤ (ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i)) le_top =
      CommRingCat.ofHom (algebraMap k (A k N 0)) ≫ (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom _ _) ≫
        Proj.awayToSection (A k N) (MvPolynomial.X i)) ≫ ι.app _ := by
    rw [e2, e3, e4, ← hC]
    have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k (A k N 0)))
    simp only [Category.assoc] at n ⊢
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) n.symm).trans (by simp only [Category.assoc]))
  rw [e1, ← Category.assoc, e5]
  rfl

theorem eval₂_mul_pow {σ R L : Type} [CommSemiring R] [CommRing L] (F : R →+* L) (a b : σ → L) (t : L)
    (hab : ∀ j, a j * t = b j) {m : ℕ} {g : MvPolynomial σ R} (hg : g.IsHomogeneous m) :
    eval₂ F a g * t ^ m = eval₂ F b g := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]

  rw [← coe_eval₂Hom, map_sum, ← coe_eval₂Hom, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hd := hg (mem_support_iff.mp hs)
  simp only [coe_eval₂Hom, eval₂_monomial, Finsupp.prod]
  rw [mul_assoc]
  congr 1
  have hm : m = ∑ j ∈ s.support, s j := by
    rw [← hd]
    simp [Finsupp.weight_apply, Finsupp.sum]
  rw [hm, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => by rw [← mul_pow, hab]

theorem mk_eq_eval (i : Fin (N + 1)) (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ A k N (m • 1)) :
    HomogeneousLocalization.Away.mk (A k N) (X_mem k N i) m g hg =
      eval₂ ((HomogeneousLocalization.fromZeroRingHom (A k N) _).comp (algebraMap k (A k N 0)))
        (fun j => HomogeneousLocalization.Away.mk (A k N) (X_mem k N i) 1 (X j) (X_mem' k N j)) g := by
  apply HomogeneousLocalization.val_injective
  let vH : HomogeneousLocalization (A k N) (Submonoid.powers (X i : MvPolynomial (Fin (N + 1)) k)) →+*
      Localization (Submonoid.powers (X i : MvPolynomial (Fin (N + 1)) k)) :=
    { toFun := fun y => y.val, map_one' := HomogeneousLocalization.val_one,
      map_mul' := HomogeneousLocalization.val_mul, map_zero' := HomogeneousLocalization.val_zero,
      map_add' := HomogeneousLocalization.val_add }
  change _ = vH _
  rw [eval₂_comp_left]
  have hgh : g.IsHomogeneous m := by simpa using (mem_homogeneousSubmodule _ _).1 hg
  set L := Localization (Submonoid.powers (X i : MvPolynomial (Fin (N + 1)) k))
  have hF : vH.comp ((HomogeneousLocalization.fromZeroRingHom (A k N) _).comp (algebraMap k (A k N 0))) =
      (algebraMap (MvPolynomial (Fin (N + 1)) k) L).comp C := by
    ext c
    simp [vH, HomogeneousLocalization.fromZeroRingHom]
    rfl
  have hab : ∀ j, (vH ∘ fun j => HomogeneousLocalization.Away.mk (A k N) (X_mem k N i) 1 (X j) (X_mem' k N j)) j *
      algebraMap (MvPolynomial (Fin (N + 1)) k) L (X i) = algebraMap (MvPolynomial (Fin (N + 1)) k) L (X j) := by
    intro j
    simp only [Function.comp_apply, vH, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
    simp only [pow_one]
    exact IsLocalization.mk'_spec _ _ _
  have key := eval₂_mul_pow ((algebraMap (MvPolynomial (Fin (N + 1)) k) L).comp C) _ _ _ hab hgh
  rw [hF, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  change _ = _ * algebraMap (MvPolynomial (Fin (N + 1)) k) L (X i ^ m)
  rw [map_pow, key]
  exact (congrArg _ (eval₂_eta g)).symm.trans (eval₂_comp_left _ _ _ _)

theorem GenAwayEval_of : GenAwayEval := by
  intro k _ X _ p N ι hp i h m g hg
  let φ : HomogeneousLocalization.Away (A k N) (MvPolynomial.X i) →+* X.functionField :=
    (X.presheaf.germ _ (genericPoint X) h).hom.comp
      ((ι.app _).hom.comp (Proj.awayToSection (A k N) (MvPolynomial.X i)).hom)
  have e : away ι (MvPolynomial.X i) (X_mem k N i) h m g hg =
      φ (HomogeneousLocalization.Away.mk (A k N) (X_mem k N i) m g hg) := rfl
  rw [e, mk_eq_eval, eval₂_comp_left]
  congr 1
  ext c
  exact (kHom_eq p ι hp i h c).symm

end LateralTheory.EtaleTrace.Cov.GenInPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

theorem RatPtIn_of : RatPtIn := by
  intro k _ _ P r hr V hV
  have := hr
  have : JacobsonSpace P := LocallyOfFiniteType.jacobsonSpace r
  obtain ⟨x, hxV, hxc⟩ := nonempty_inter_closedPoints hV V.isOpen.isLocallyClosed
  refine ⟨⟨pointOfClosedPoint r x hxc, pointOfClosedPoint_comp r x hxc⟩, fun a => ?_⟩
  have h := pointOfClosedPoint_apply r x hxc a
  show (pointOfClosedPoint r x hxc) a ∈ V
  rw [h]; exact hxV

end LateralTheory.EtaleTrace.Cov
end
end
