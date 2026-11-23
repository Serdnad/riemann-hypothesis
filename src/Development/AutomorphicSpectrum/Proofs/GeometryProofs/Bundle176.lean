module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle084
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle017
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle169
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle008
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle003

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.CompanionTheory.Ggeo.DualFibre

theorem exists_complex_point (A : Over (Sp ℂ)) [LocallyOfFiniteType A.hom] (V : A.left.Opens)
    (hV : (V : Set A.left).Nonempty) : ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, ⊤ ≤ x.left ⁻¹ᵁ V := by
  obtain ⟨r, hr, hz⟩ := GlobalTheory.ZH.SecProp.exists_point A.hom V.isOpen.isLocallyClosed hV
  exact ⟨Over.homMk r hr, fun z _ => hz z⟩

section Translate

variable {A : Over (Sp ℂ)} [GrpObj A]

def tr (c : 𝟙_ (Over (Sp ℂ)) ⟶ A) : A ⟶ A := (toUnit A ≫ c) * 𝟙 A

theorem comp_tr (x c : 𝟙_ (Over (Sp ℂ)) ⟶ A) : x ≫ tr c = c * x := by
  rw [tr, MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (x ≫ toUnit A) (𝟙 _),
    Category.id_comp]

theorem tr_comp_tr (c d : 𝟙_ (Over (Sp ℂ)) ⟶ A) : tr c ≫ tr d = tr (d * c) := by
  have h : tr c ≫ toUnit A = toUnit A := toUnit_unique _ _
  change tr c ≫ ((toUnit A ≫ d) * 𝟙 A) = (toUnit A ≫ (d * c)) * 𝟙 A
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, h, MonObj.comp_mul, _root_.mul_assoc]
  rfl

theorem tr_one : tr (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A) = 𝟙 A := by
  change (toUnit A ≫ 1) * 𝟙 A = 𝟙 A
  simp

instance isIso_tr_left (c : 𝟙_ (Over (Sp ℂ)) ⟶ A) : IsIso (tr c).left :=
  ⟨(tr c⁻¹).left, by rw [← Over.comp_left, tr_comp_tr, inv_mul_cancel, tr_one]; rfl,
    by rw [← Over.comp_left, tr_comp_tr, mul_inv_cancel, tr_one]; rfl⟩

theorem exists_affine_mem [PreirreducibleSpace A.left] [LocallyOfFiniteType A.hom]
    (hcomm : ∀ x y : 𝟙_ (Over (Sp ℂ)) ⟶ A, x * y = y * x) (a : 𝟙_ (Over (Sp ℂ)) ⟶ A) :
    ∃ U : A.left.Opens, IsAffineOpen U ∧ ⊤ ≤ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A).left ⁻¹ᵁ U ∧ ⊤ ≤ a.left ⁻¹ᵁ U := by
  obtain ⟨_, ⟨W, hW, rfl⟩, h0, -⟩ := A.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((1 : 𝟙_ (Over (Sp ℂ)) ⟶ A).left (default : PrimeSpectrum ℂ))) isOpen_univ
  have h1 : ⊤ ≤ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A).left ⁻¹ᵁ W := (GlobalTheory.top_le_preimage_iff_mem _ _).2 h0
  have h2 : ⊤ ≤ (a⁻¹).left ⁻¹ᵁ ((tr a).left ⁻¹ᵁ W) := by
    rw [← GlobalTheory.top_le_preimage_comp, ← Over.comp_left, comp_tr, mul_inv_cancel]
    exact h1
  obtain ⟨b, hb⟩ := exists_complex_point A (W ⊓ (tr a).left ⁻¹ᵁ W)
    (nonempty_preirreducible_inter W.isOpen ((tr a).left ⁻¹ᵁ W).isOpen ⟨_, h0⟩
      ⟨_, h2 (Set.mem_univ (default : PrimeSpectrum ℂ))⟩)
  obtain ⟨hb1, hb2⟩ := (GlobalTheory.top_le_preimage_inf _ _ _).1 hb
  refine ⟨(tr b).left ⁻¹ᵁ W, hW.preimage_of_isIso _, ?_, ?_⟩
  · rw [← GlobalTheory.top_le_preimage_comp, ← Over.comp_left, comp_tr, _root_.mul_one]
    exact hb1
  · rw [← GlobalTheory.top_le_preimage_comp, ← Over.comp_left, comp_tr, hcomm, ← comp_tr, Over.comp_left,
      GlobalTheory.top_le_preimage_comp]
    exact hb2

end Translate

section Dual

variable {A : Over (Sp ℂ)}

theorem red_surjective (p : Sp (DualNumber ℂ)) :
    p ∈ Set.range (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
  have h := range_comap_of_surjective ℂ (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom
    (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩)
  have hp : (p : PrimeSpectrum (DualNumber ℂ)) ∈
      PrimeSpectrum.zeroLocus (RingHom.ker (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom : Set (DualNumber ℂ)) := by
    intro a ha
    have h0 : a.fst = 0 := ha
    have h1 : a * a = 0 := by
      ext <;> simp [h0]
    exact (PrimeSpectrum.isPrime p).mul_mem_iff_mem_or_mem.1 (h1 ▸ Ideal.zero_mem _) |>.elim id id
  rw [← h] at hp
  exact hp

def basePt (v : epsR ℂ ⟶ A) : 𝟙_ (Over (Sp ℂ)) ⟶ A :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left) (by
    have h : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap (algebraMap ℂ (DualNumber ℂ)) = 𝟙 _ := by
      rw [← Spec.map_comp, ← Spec.map_id]
      congr 1
    rw [Category.assoc, Over.w v]
    exact h)

theorem top_le_of_basePt (v : epsR ℂ ⟶ A) (U : A.left.Opens) (h : ⊤ ≤ (basePt v).left ⁻¹ᵁ U) :
    ⊤ ≤ v.left ⁻¹ᵁ U := by
  intro p _
  obtain ⟨q, rfl⟩ := red_surjective p
  have := h (Set.mem_univ q)
  simpa [basePt] using this

end Dual

section Germ

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem fderiv_eq_zero_of_affine (D : Fin g → ℂ) (U : A.left.Opens) (hU : IsAffineOpen U)
    (h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U)
    (hD : ∀ f : Γ(A.left, U), fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 D = 0)
    (U₁ : A.left.Opens) (f : Γ(A.left, U₁)) (h1 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U₁) :
    fderiv ℂ (fun z => valAt' (u.ex z).left U₁ f) 0 D = 0 := by
  have m0 := (GlobalTheory.top_le_preimage_iff_mem _ _).1 h0
  have m1 := (GlobalTheory.top_le_preimage_iff_mem _ _).1 h1
  obtain ⟨q, hq1, hq0⟩ := hU.exists_basicOpen_le (V := U₁) ⟨_, m1⟩ m0
  have hBU : A.left.basicOpen q ≤ U := A.left.basicOpen_le q
  have hB0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ A.left.basicOpen q := (GlobalTheory.top_le_preimage_iff_mem _ _).2 hq0
  have hloc := hU.isLocalization_basicOpen q
  obtain ⟨n, p, e⟩ := IsLocalization.Away.surj (S := Γ(A.left, A.left.basicOpen q)) q (resG _ hq1 f)
  have e' : resG _ hq1 f * resG _ hBU (q ^ n) = resG _ hBU p := by
    rw [map_pow]
    exact e
  have hval : ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ A.left.basicOpen q →
      valAt' (u.ex z).left U₁ f * valAt' (u.ex z).left U (q ^ n) = valAt' (u.ex z).left U p := by
    intro z hz
    have := congrArg (valAt' (u.ex z).left (A.left.basicOpen q)) e'
    rwa [GlobalTheory.valAt'_mul, GlobalTheory.valAt'_res _ _ _ hz, GlobalTheory.valAt'_res _ _ _ hz, GlobalTheory.valAt'_res _ _ _ hz] at this
  have hev : ∀ᶠ z in 𝓝 (0 : Fin g → ℂ), ⊤ ≤ (u.ex z).left ⁻¹ᵁ A.left.basicOpen q :=
    (u.hol _ 0).1.mem_nhds hB0
  have df : DifferentiableAt ℂ (fun z => valAt' (u.ex z).left U₁ f) 0 :=
    (u.hol U₁ f).2.differentiableAt ((u.hol U₁ f).1.mem_nhds h1)
  have dqn : DifferentiableAt ℂ (fun z => valAt' (u.ex z).left U (q ^ n)) 0 :=
    (u.hol U (q ^ n)).2.differentiableAt ((u.hol U (q ^ n)).1.mem_nhds h0)
  have H := (df.hasFDerivAt.mul dqn.hasFDerivAt).congr_of_eventuallyEq
    (f₁ := fun z => valAt' (u.ex z).left U p) (hev.mono fun z hz => (hval z hz).symm)
  have H2 := congrArg (fun T => T D) H.fderiv
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, hD, smul_eq_mul, mul_zero,
    zero_add] at H2
  have hne : valAt' (u.ex 0).left U (q ^ n) ≠ 0 := by
    rw [GlobalTheory.valAt'_pow _ h0]
    exact pow_ne_zero _ ((GlobalTheory.top_le_preimage_basicOpen_iff _ U q).1 hB0)
  exact (mul_eq_zero.1 H2.symm).resolve_left hne

end Germ

theorem eq_of_isDiff_of_not_isTangent : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g), SmoothOfRelativeDimension g A.hom → ConnectedSpace A.left → ∀ (v : epsR ℂ ⟶ A), ¬ IsTangent v → ∀ (w w' : Fin g → ℂ), u.IsDiff w v → u.IsDiff w' v → w = w' := by
  intro A _ L g u hs hc v _ w w' h h'
  haveI : Smooth A.hom := SmoothOfRelativeDimension.smooth g A.hom
  haveI : PreirreducibleSpace A.left := ⟨by
    have := GlobalTheory.KeyFam.isPreirreducible_connectedComponent_of_smooth A.hom (Classical.arbitrary A.left)
    rwa [PreconnectedSpace.connectedComponent_eq_univ] at this⟩
  have hcomm : ∀ x y : 𝟙_ (Over (Sp ℂ)) ⟶ A, x * y = y * x := fun x y => by
    obtain ⟨z, rfl⟩ := u.ex_onto x
    obtain ⟨z', rfl⟩ := u.ex_onto y
    rw [← u.ex_add, ← u.ex_add, add_comm]
  obtain ⟨U, hU, h0, ha⟩ := exists_affine_mem hcomm (basePt v)
  have e1 : u.ex 0 = 1 := GlobalTheory.TangentOrigin.ex_zero u
  rw [← e1] at h0
  have hv := top_le_of_basePt v U ha
  have hDU : ∀ f : Γ(A.left, U), fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 (w - w') = 0 := fun f => by
    rw [map_sub, ← h U hv f, ← h' U hv f, sub_self]
  exact sub_eq_zero.1 (GlobalTheory.TorusTransfer.eq_zero_of_fderiv_eq_zero u (w - w')
    fun U₁ f h1 => fderiv_eq_zero_of_affine u _ U hU h0 hDU U₁ f h1)

end GlobalTheory.CompanionTheory.Ggeo.DualFibre
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ggeo.DOpen

theorem isDerivAt0_lift_of_isOpenImmersion :
    ∀ (A T : Scheme.{0}) (φ : A ⟶ T) [IsOpenImmersion φ] (g : ℕ) (W : (Fin g → ℂ) → (Sp ℂ ⟶ A))
      (y : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ T),
      IsDerivAt0 (fun x => W x ≫ φ) y v → ∃ v' : Sp (DualNumber ℂ) ⟶ A, v' ≫ φ = v ∧ IsDerivAt0 W y v' := by
  intro A T φ _ g W y v hv
  have hcl : IsLocalRing.closedPoint (DualNumber ℂ) ∈ v ⁻¹ᵁ φ.opensRange := by
    have h0 : ⊤ ≤ (W 0 ≫ φ) ⁻¹ᵁ φ.opensRange := fun p _ =>
      (show (W 0 ≫ φ) p ∈ Set.range φ from ⟨W 0 p, by simp⟩)
    have hpt : v (IsLocalRing.closedPoint _) = (W 0 ≫ φ) ReciprocityTheory.ChartRestriction.G.PullbackSections.cpt := by
      have hcomp : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = W 0 ≫ φ := hv.1
      rw [← hcomp, Scheme.Hom.comp_apply, spMap, Spec_closedPoint]
    show v (IsLocalRing.closedPoint _) ∈ φ.opensRange
    rw [hpt]
    exact h0 trivial
  have htop : ⊤ ≤ v ⁻¹ᵁ φ.opensRange := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.dual_top_le _ hcl
  have hrange : Set.range v ⊆ Set.range φ := by
    rintro _ ⟨p, rfl⟩
    exact htop (show p ∈ (⊤ : (Sp (DualNumber ℂ)).Opens) from trivial)
  obtain ⟨v', rfl⟩ : ∃ v', v' ≫ φ = v := ⟨IsOpenImmersion.lift φ v hrange, IsOpenImmersion.lift_fac _ _ _⟩
  refine ⟨v', rfl, ?_, fun U' h f' => ?_⟩
  · rw [← cancel_mono φ, Category.assoc]
    exact hv.1
  · have key : ∀ (U : T.Opens) (U' : A.Opens) (e : φ ⁻¹ᵁ U = U') (h : ⊤ ≤ v' ⁻¹ᵁ U') (f : Γ(T, U)),
        TrivSqZeroExt.snd (show DualNumber ℂ from
          (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom
            ((v'.appLE U' ⊤ h).hom (φ.appLE U U' e.ge f))) =
          fderiv ℂ (fun z => valAt' (W z) U' (φ.appLE U U' e.ge f)) 0 y := by
      intro U U' e h f
      subst e
      have hU : ⊤ ≤ (v' ≫ φ) ⁻¹ᵁ U := h
      have happ : φ.appLE U (φ ⁻¹ᵁ U) (le_refl (φ ⁻¹ᵁ U)) f = φ.app U f := by
        rw [Scheme.Hom.app_eq_appLE]
      have hfun : (fun z => valAt' (W z) (φ ⁻¹ᵁ U) (φ.app U f)) =
          fun z => valAt' ((fun x => W x ≫ φ) z) U f :=
        funext fun z => ReciprocityTheory.ChartRestriction.G.PullbackSections.valAt'_comp (W z) φ U f
      erw [happ]
      rw [hfun, ← hv.2 U hU f, Scheme.Hom.comp_appLE]
      rfl
    have hpre : φ ⁻¹ᵁ (φ ''ᵁ U') = U' := φ.preimage_image_eq U'
    have := key (φ ''ᵁ U') U' hpre h ((φ.appIso U').inv f')
    have hf : φ.appLE (φ ''ᵁ U') U' hpre.ge ((φ.appIso U').inv f') = f' := by
      have hh : φ.appLE (φ ''ᵁ U') U' hpre.ge = (φ.appIso U').hom := (Scheme.Hom.appIso_hom' φ U').symm
      rw [hh]
      exact ConcreteCategory.congr_hom (φ.appIso U').inv_hom_id f'
    rwa [hf] at this

end GlobalTheory.CompanionTheory.Ggeo.DOpen
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_torus_extension_finite : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ S), ∃ (L' : Type) (_ : Field L') (_ : Algebra L L'), FiniteDimensional L L' ∧ Nonempty (TorusExtension ((Over.pullback (spMap (algebraMap L L') ≫ z)).obj G)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_finite_torusExtension_fibre | exact GlobalTheory.CompanionTheory.Ar.exists_finite_torusExtension_fibre | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_finite_torusExtension_fibre <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

private theorem gm_unitRes' {S : Scheme} {T : Over S} (V : T.left.Opens) {Z : Scheme}
    (r : Z ⟶ (Out.overRes V).left) (z : Z) (a : (↑(T.left.presheaf.obj (Opposite.op ⊤)))ˣ) :
    gm r z ⊤ (Out.unitRes V a) = gm (r ≫ V.ι) z ⊤ a :=
  gm_pull r V.ι z ⊤ trivial a

private theorem unitOn_units_map {k M : Type} [Field k] [Field M] (j : k →+* M) (c : kˣ) :
    unitOn (Units.map j.toMonoidHom c) = Units.map (spMap j).appTop.hom (unitOn c) := by
  ext
  show (Scheme.ΓSpecIso (CommRingCat.of M)).inv.hom (j c) =
    (Spec.map (CommRingCat.ofHom j)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)
  exact congrArg (fun g => g.hom (c : k)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))

theorem weilIs_fieldExt : ∀ {X : Scheme.{0}} (G : Over X) [GrpObj G] [IsCommMonObj G] (L : LB G.left), L.IsLB → ∀ (k M : Type) [Field k] [Field M] (j : k →+* M) (q : Sp k ⟶ X) (q' : Sp M ⟶ X), q' = spMap j ≫ q → ∀ (n : ℤ) (x y : Over.mk q ⟶ G) (x' y' : Over.mk q' ⟶ G), x'.left = spMap j ≫ x.left → y'.left = spMap j ≫ y.left → ∀ (c : kˣ) (c' : Mˣ), Out.WeilIs G L n x y (unitOn c) → Out.WeilIs G L n x' y' (unitOn c') → c' = Units.map j.toMonoidHom c := by
  intro X G _ _ L hL k M _ _ j q q' hq n x y x' y' hx hy c c' h1 h2
  let p' : (Over.mk q').left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum M)
  obtain ⟨V', hpV', -, H2⟩ := h2 p'
  obtain ⟨V, hpV, ⟨θx₀, θy₀, hθx₀, hθy₀⟩, H1'⟩ := h1 ((spMap j).base p')
  have H1 := H1' θx₀ θy₀ hθx₀ hθy₀
  have key : ∀ I : Ideal k, I.IsPrime → I = ⊥ := fun I _ => Ideal.eq_bot_of_prime I
  have hall : ∀ z : (Over.mk q).left, z ∈ V := by
    intro z
    have hz : z = (spMap j).base p' := by
      apply PrimeSpectrum.ext
      exact (key z.asIdeal z.isPrime).trans (key _ ((spMap j).base p').isPrime).symm
    rw [hz]; exact hpV
  let τ : (Out.overRes V').left ⟶ (Out.overRes V).left :=
    IsOpenImmersion.lift V.ι (V'.ι ≫ spMap j) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨z, rfl⟩
      exact hall _)
  have hτι : τ ≫ V.ι = V'.ι ≫ spMap j := IsOpenImmersion.lift_fac _ _ _
  have hτ : τ ≫ (Out.overRes V).hom = (Out.overRes V').hom ≫ 𝟙 X := by
    change τ ≫ (V.ι ≫ q) = (V'.ι ≫ q') ≫ 𝟙 X
    rw [← Category.assoc, hτι, hq]
    simp
  haveI : IsMonHom (Iso.refl G).hom := by
    show IsMonHom (𝟙 G)
    infer_instance
  have hp : IsGrpPullback G G (𝟙 X) (𝟙 G.left) :=
    (isGrpPullback_of_iso (Iso.refl G)).congr rfl (by simp)
  obtain ⟨w, hw⟩ : LBIso L (L.pull (𝟙 G.left)) :=
    LBIso.chartPull (chartPullId L) (chartPullPull L (𝟙 _) (𝟙 _) rfl) (GlobalTheory.PolBaseChange.lbIso_refl hL)
  have hxpt : τ ≫ θx₀.pt.left = (Out.overResι V' ≫ x').left ≫ 𝟙 G.left := by
    rw [hθx₀]
    change τ ≫ (V.ι ≫ x.left) = (V'.ι ≫ x'.left) ≫ 𝟙 G.left
    rw [hx, Category.comp_id, ← Category.assoc τ, hτι, Category.assoc]
  have hypt : τ ≫ θy₀.pt.left = (Out.overResι V' ≫ y').left ≫ 𝟙 G.left := by
    rw [hθy₀]
    change τ ≫ (V.ι ≫ y.left) = (V'.ι ≫ y'.left) ≫ 𝟙 G.left
    rw [hy, Category.comp_id, ← Category.assoc τ, hτι, Category.assoc]
  obtain ⟨θx, hθx, hPx⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_theta_move hp τ hτ hL hL w hw n (Out.overResι V' ≫ x') θx₀ hxpt
  obtain ⟨θy, hθy, hPy⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_theta_move hp τ hτ hL hL w hw n (Out.overResι V' ≫ y') θy₀ hypt
  have hgm : ∀ (Z : Scheme) (r : Z ⟶ (Out.overRes V').left) (z : Z),
      gm (r ≫ τ) z ⊤ (Out.unitRes V (unitOn c)) =
        gm r z ⊤ (Out.unitRes V' (unitOn (Units.map j.toMonoidHom c))) := by
    intro Z r z
    rw [gm_unitRes', gm_unitRes', unitOn_units_map]
    erw [gm_pull (r ≫ V'.ι) (spMap j) z ⊤ trivial (unitOn c)]
    rw [Category.assoc, hτι, Category.assoc]
  have HC := ReciprocityTheory.ChartRestriction.G.H1.commIsOf_move hp τ hτ hL hL w n θx₀ θy₀ θx θy
    (by rw [hθx]; exact hxpt) (by rw [hθy]; exact hypt) hPx hPy _ _ hgm H1
  have HC2 := H2 θx θy hθx hθy
  have heq := ReciprocityTheory.ChartRestriction.G.H1.commIsOf_unique hL θx θy _ _ HC2 HC
  let pt : (Out.overRes V').left := ⟨p', hpV'⟩
  have e := (gm_unitRes' V' (𝟙 (Out.overRes V').left) pt (unitOn c')).symm.trans
    ((congrArg (gm (𝟙 (Out.overRes V').left) pt ⊤) heq).trans
      (gm_unitRes' V' (𝟙 (Out.overRes V').left) pt _))
  have e' := (gm_val (𝟙 (Out.overRes V').left ≫ V'.ι) pt ⊤ trivial (unitOn c')).symm.trans
    ((congrArg Units.val e).trans
      (gm_val (𝟙 (Out.overRes V').left ≫ V'.ι) pt ⊤ trivial _))
  apply Units.ext
  refine (RingHom.injective
    (((Out.overRes V').left.presheaf.germ ((TopologicalSpace.Opens.map (𝟙 (Out.overRes V').left ≫ V'.ι).base).obj ⊤)
      pt trivial).hom.comp
      (((𝟙 (Out.overRes V').left ≫ V'.ι).app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of M)).inv.hom))) ?_
  have e'' := by simpa [unitOn] using e'
  exact e''

end GlobalTheory.CompanionTheory.Ar
end
end
