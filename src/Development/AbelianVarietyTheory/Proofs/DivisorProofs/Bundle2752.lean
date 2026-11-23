module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SemiabelianExtensionNormalModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle156
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetAbelianLocusOfGoodReduction
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2671
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2673
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.TotallySplit
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models GlobalTheory.CechPic
open scoped CategoryTheory.Obj

namespace GlobalTheory.HodgeGenDesc

theorem exists_iso_of_extensions {U X : Scheme.{0}} [IsLocallyNoetherian X] (j : U ⟶ X)
    (hX : Geo.Tor.IsNormalScheme X) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j]
    {A : Over U} [GrpObj A] {G G' : Over X} [GrpObj G] [GrpObj G'] (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    {φ : A.left ⟶ G.left} {ψ : A.left ⟶ G'.left} (hφ : IsGrpPullback A G j φ) (hψ : IsGrpPullback A G' j ψ) :
    ∃ e : G ≅ G', IsMonHom e.hom := by
  have := GlobalTheory.IsNormalScheme.of_pred hX
  have : IsSchemeTheoreticallyDominant j := .of_isDominant j
  have := hG.smooth
  have := hG'.smooth
  have := hG.separated
  have := hG'.separated
  obtain ⟨a, ha, -⟩ := grpPullback_iso hφ (isGrpPullback_pullback G j)
  obtain ⟨b, hb, -⟩ := grpPullback_iso hψ (isGrpPullback_pullback G' j)
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.HomExtProOpen.existsUnique_hom_extension_of_dvr
    GlobalTheory.homExtension_semiAbelian_dvr X U j hX G G' hG hG' (a.inv ≫ b.hom) inferInstance
  obtain ⟨F₁, ⟨-, hF₁⟩, -⟩ := GlobalTheory.HomExtProOpen.existsUnique_hom_extension_of_dvr
    GlobalTheory.homExtension_semiAbelian_dvr X U j hX G' G hG' hG (b.inv ≫ a.hom) inferInstance
  obtain ⟨h₁, h₂⟩ := ExtUnique.comp_eq_id_of_pullback j (a.symm ≪≫ b) F F₁ hF' hF₁
  exact ⟨⟨F, F₁, h₁, h₂⟩, hF⟩

theorem lbIso_hodge_pull {S T : Scheme.{0}} {G : Over S} {G' : Over T} [GrpObj G] [GrpObj G'] [QuasiSeparated G.hom]
    {f : T ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {g : ℕ} (hg : GlobalTheory.VB.IsVB (GlobalTheory.LieVB.omega G) g) :
    LBIso ((hodge G g).pull f) (hodge G' g) :=
  (hg.lbIso_det_pullback f).trans (pull_isLB hg.isLB_det f) (hg.pullback f).isLB_det
    (GlobalTheory.LieVB.isVB_omega_of_isGrpPullback h hg).isLB_det
    ((hg.pullback f).lbIso_det_of_iso (asIso (GlobalTheory.LieVB.omegaBase h)))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {R : Type} [CommRing R] {ω : R →+* c.F}

end GlobalTheory.HodgeGenDesc

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.GoodVal

theorem GlobalTheory.ChartAbelian.mem_abLocus_of_mem_range : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (j : F.X ⟶ S) [IsOpenImmersion j] (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (ξ : Sp R ⟶ S) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing R) ⟶ F.X) (A₁ : Over (Sp (FractionRing R))) [GrpObj A₁] (i₁ : A₁.left ⟶ G₁.left) (β : A₁.left ⟶ F.univ.A.left), IsSemiAbelian G₁ → IsGrpPullback A₁ G₁ (jK R) i₁ → IsGrpPullback A₁ F.univ.A y β → y ≫ j = jK R ≫ ξ → ∀ p : Sp R, ξ p ∈ Set.range j → p ∈ abLocus G₁ := by
  intro g n F S j _ R _ _ _ ξ G₁ _ _ y A₁ _ i₁ β hG hA hB hy p hp
  have : IsNoetherianRing R := inferInstance
  let K := FractionRing R
  by_cases hp0 : p.asIdeal = ⊥
  · have hAprop : IsProper A₁.hom := MorphismProperty.of_isPullback (P := @IsProper) hB.1 F.univ.ab.proper
    refine abLocusOne _ G₁ hG K (jK R) (by rw [← hA.1.isoPullback_inv_snd]; infer_instance) ⟨(⊥ : PrimeSpectrum K), ?_⟩
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R K) ⊥ = p.asIdeal
    rw [hp0]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)
  · have := p.isPrime
    obtain ⟨T, hT, gT, hg, hgp⟩ := exists_dvr_centre (K := K) (L := K) p.asIdeal hp0
    have hc : spMap (algebraMap T K) ≫ spMap gT = jK R := by
      rw [← spMap_comp, hg]
    have hginj : Function.Injective gT := by
      refine Function.Injective.of_comp (f := algebraMap T K) ?_
      rw [← RingHom.coe_comp, hg]
      exact (algebraMap K K).injective.comp (IsFractionRing.injective R K)
    have hcl : spMap gT (IsLocalRing.closedPoint T) = p := PrimeSpectrum.ext hgp
    have hr : Set.range (spMap gT ≫ ξ) ⊆ Set.range j := by
      rintro _ ⟨q, rfl⟩
      by_cases hq : q.asIdeal = ⊥
      · have hq' : q = spMap (algebraMap T K) (⊥ : PrimeSpectrum K) := by
          apply PrimeSpectrum.ext
          change q.asIdeal = Ideal.comap (algebraMap T K) ⊥
          rw [hq]; exact (Ideal.comap_bot_of_injective _ (IsFractionRing.injective T K)).symm
        refine ⟨y (⊥ : PrimeSpectrum K), ?_⟩
        rw [hq']
        have e : spMap (algebraMap T K) ≫ spMap gT ≫ ξ = y ≫ j := by rw [hy, ← Category.assoc, hc]
        have e' := (congrArg (fun f : Sp K ⟶ S => f (⊥ : PrimeSpectrum K)) e).symm
        first | exact e' | (dsimp only at e'; rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at e'; exact e')
      · have hq' : q = IsLocalRing.closedPoint T :=
          PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hq q.isPrime))
        rw [hq']
        have e : (spMap gT ≫ ξ) (IsLocalRing.closedPoint T) = ξ p := by rw [← hcl]; rfl
        rw [e]; exact hp
    haveI := hT
    let yT : Sp T ⟶ F.X := IsOpenImmersion.lift j (spMap gT ≫ ξ) hr
    have hyT : yT ≫ j = spMap gT ≫ ξ := IsOpenImmersion.lift_fac _ _ _
    have hyK : spMap (algebraMap T K) ≫ yT = y := by
      rw [← cancel_mono j, Category.assoc, hyT, ← Category.assoc, hc, hy]
    have hid : IsPullback (𝟙 F.univ.A.left) F.univ.A.hom F.univ.A.hom (𝟙 F.X) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩
    have := F.univ.ab.smooth
    have := F.univ.ab.proper
    have := F.univ.ab.geomConnected
    obtain ⟨hBs, hB'⟩ := isSemiAbelian_pullback_of_range_subset F.univ.A hid yT (by
      rintro _ ⟨x, rfl⟩; exact ⟨yT x, rfl⟩)
    have hH := IsSemiAbelian.pullback (spMap gT) G₁ hG
    have hPB := ((isGrpPullback_pullback ((Over.pullback yT).obj F.univ.A) (spMap (algebraMap T K))).comp
      (isGrpPullback_pullback F.univ.A yT)).congr hyK rfl
    obtain ⟨a, ha, -⟩ := grpPullback_iso hPB hB
    have hPG := ((isGrpPullback_pullback ((Over.pullback (spMap gT)).obj G₁) (spMap (algebraMap T K))).comp
      (isGrpPullback_pullback G₁ (spMap gT))).congr hc rfl
    obtain ⟨b, hb, -⟩ := grpPullback_iso hA hPG
    have hE : IsMonHom (a ≪≫ b).hom := inferInstanceAs (IsMonHom (a.hom ≫ b.hom))
    obtain ⟨Φ, ⟨-, hΦ⟩, -⟩ := GlobalTheory.homExtension_semiAbelian_dvr T K _ _ hBs hH (a ≪≫ b).hom hE
    obtain ⟨Ψ, ⟨-, hΨ⟩, -⟩ := GlobalTheory.homExtension_semiAbelian_dvr T K _ _ hH hBs (a ≪≫ b).inv inferInstance
    have hx := (abLocus_pullback abLocusOne hG (isGrpPullback_pullback G₁ (spMap gT)).1
      (IsLocalRing.closedPoint T)).2 (abLocus_subset_of_extends hBs hH _ Φ Ψ hΦ hΨ (hB' _))
    rw [hcl] at hx
    exact hx
end

section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SiegelTor GlobalTheory.ZM

namespace GlobalTheory.SiegelTor


open CategoryTheory AlgebraicGeometry Limits NumberField in
theorem _root_.GlobalTheory.SiegelTor.finiteType_cycAway (n : ℕ) : Algebra.FiniteType ℤ (_root_.GlobalTheory.SiegelTor.cycAway n) := by
  have hfg : (Algebra.adjoin ℤ ({_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta n, (n : ℂ)⁻¹} : Set ℂ)).FG := by
    rw [show ({_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta n, (n : ℂ)⁻¹} : Set ℂ) = ↑({_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta n, (n : ℂ)⁻¹} : Finset ℂ) by simp]
    exact Subalgebra.fg_adjoin_finset _
  have h := (Subalgebra.fg_iff_finiteType _).1 hfg
  rw [Algebra.adjoin_int] at h
  exact h


open CategoryTheory AlgebraicGeometry Limits NumberField in
theorem _root_.GlobalTheory.SiegelTor.arBase_cycAway : ∀ n : ℕ, n ≠ 0 → _root_.GlobalTheory.ZM.ArBase (_root_.GlobalTheory.SiegelTor.cycAway n).subtype := by
  intro n _
  exact ⟨_root_.GlobalTheory.CycAwayReg.isDedekindDomain_cycAway n, _root_.GlobalTheory.SiegelTor.finiteType_cycAway n,
    Subtype.val_injective⟩

end GlobalTheory.SiegelTor
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.additive_torsion_families_equal_locus_open : ∀ (m M : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (t : S' ⟶ Sp (cycAway M)) (A : Over S') [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → 1 ≤ M → ∀ (x y : (Fin m ⊕ Fin m → ℤ) → (𝟙_ (Over S') ⟶ A)), (∀ a b, x (a + b) = x a * x b) → (∀ a b, y (a + b) = y a * y b) → (∀ a, x a ^ M = 1) → (∀ a, y a ^ M = 1) → ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → ∀ a, V.ι ≫ (x a).left = V.ι ≫ (y a).left) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S'), (∀ a, g ≫ (x a).left = g ≫ (y a).left) → Set.range g.base ⊆ (U : Set S') := by
  first | (exact @GlobalTheory.torsFamily_eq_isOpen) | (exact GlobalTheory.torsFamily_eq_isOpen) | (intros; apply GlobalTheory.torsFamily_eq_isOpen  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.level_sections_exact_kernel_locus_open : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (M : ℕ) (t : S ⟶ Sp (cycAway M)) (G : Over S) [GrpObj G] [IsCommMonObj G] (h : ℕ) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ G)), IsAbelianScheme G → 3 ≤ M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S), (∀ a, (toUnit (Over.mk x₀) ≫ lev a = 1 ↔ ∃ b, a = M • b)) → ∃ W : S.Opens, Set.range x₀.base ⊆ W ∧ ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ S), Set.range x.base ⊆ W → ∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = M • b) := by
  first | (exact @GlobalTheory.levTriv_locus_open) | (exact GlobalTheory.levTriv_locus_open) | (intros; apply GlobalTheory.levTriv_locus_open  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.isQuasiProjective_of_finite_over_cyclotomicAway_pullback : ∀ (M : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R], IsUnit ((M : ℕ) : R) → ∀ (Y : Scheme.{0}) (s : Y ⟶ Sp (cycAway M)), IsQProjOver s → ∀ (Z : Scheme.{0}) (π : Z ⟶ pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R))), IsFinite π → IsQProjOver (π ≫ pullback.snd _ _) := by
  first | (exact @GlobalTheory.CycAwayQProj.isQProjOver_of_isFinite_pullback) | (exact GlobalTheory.CycAwayQProj.isQProjOver_of_isFinite_pullback) | (intros; apply GlobalTheory.CycAwayQProj.isQProjOver_of_isFinite_pullback  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.siegelFamily_classifyingMap_unique : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (cycAway n)) (c : SiegPre g n (zetaAway n) s') (f f' : S ⟶ F.X), f ≫ F.s = s' → f' ≫ F.s = s' → SiegPB c F.univ f → SiegPB c F.univ f' → f = f' := by
  first | exact @GlobalTheory.SiegUniq.eq_of_siegPB | exact GlobalTheory.SiegUniq.eq_of_siegPB | (intros; apply GlobalTheory.SiegUniq.eq_of_siegPB <;> assumption)
end

section

open GlobalTheory.SiegelTor

namespace GlobalTheory.CycLift

theorem exists_hom_to_field : ∀ (M : ℕ), M ≠ 0 → ∀ (K : Type) [Field K] (y : K), IsPrimitiveRoot y M → IsUnit (M : K) →
    ∃ β : cycAway M →+* K, β (zetaAway M) = y := by
  intro M hM K _ y hy hMK
  obtain ⟨p, hcp⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with hp | rfl
  · haveI : Fact p.Prime := ⟨hp⟩
    haveI : CharZero (WittVector p K) := by
      obtain ⟨q, hq⟩ := CharP.exists (WittVector p K)
      have h1 : ((q : ℕ) : K) = 0 := by
        have := congrArg (WittVector.constantCoeff : WittVector p K →+* K) (CharP.cast_eq_zero (WittVector p K) q)
        rwa [map_natCast, map_zero] at this
      have h2 : p ∣ q := (CharP.cast_eq_zero_iff K p q).1 h1
      rcases CharP.char_is_prime_or_zero (WittVector p K) q with h | h
      · have h3 : p = q := (Nat.prime_dvd_prime_iff_eq hp h).1 h2
        subst h3
        exact absurd (CharP.cast_eq_zero (WittVector p K) p) (WittVector.p_nonzero p K)
      · subst h
        exact CharP.charP_to_charZero _
    let π : WittVector p K →+* K := WittVector.constantCoeff
    have hcc : ∀ x : K, π (WittVector.teichmuller p x) = x := fun x => by simp [π]
    have hu : IsPrimitiveRoot (WittVector.teichmuller p y) M :=
      ⟨by rw [← map_pow, hy.pow_eq_one, map_one], fun l hl => hy.dvd_of_pow_eq_one l (by
        have := congrArg π hl
        rwa [map_pow, hcc, map_one] at this)⟩
    have hnV : IsUnit (M : WittVector p K) := by
      refine WittVector.isUnit_of_coeff_zero_ne_zero _ ?_
      have : π (M : WittVector p K) ≠ 0 := by rw [map_natCast]; exact hMK.ne_zero
      exact this
    obtain ⟨f, -, hfζ⟩ := exists_injective_hom hM hu hnV
    exact ⟨π.comp f, by rw [RingHom.comp_apply, hfζ, hcc]⟩
  · haveI : CharZero K := CharP.charP_to_charZero K
    obtain ⟨f, -, hfζ⟩ := exists_injective_hom hM hy hMK
    exact ⟨f, hfζ⟩

end GlobalTheory.CycLift
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_completeLocalDomain_lift_cyclotomicAway : ∀ (n : ℕ), 3 ≤ n → ∀ (K : Type) [Field K] [IsAlgClosed K] (β : cycAway n →+* K), ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (_ : IsNoetherianRing V) (βV : cycAway n →+* V) (π : V →+* K), IsAdicComplete (IsLocalRing.maximalIdeal V) V ∧ Function.Injective βV ∧ Function.Surjective π ∧ π.comp βV = β := by
  first | exact @GlobalTheory.SiegelTor.CycLift.exists_complete_domain_lift | exact GlobalTheory.SiegelTor.CycLift.exists_complete_domain_lift | (intros; apply GlobalTheory.SiegelTor.CycLift.exists_complete_domain_lift <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.exists_clopen_irreducible_partition_of_normal_proj : ∀ (n : ℕ) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)), IsProjOver z → GlobalTheory.IsNormalScheme Z → ∃ (ι : Type) (_ : Fintype ι) (W : ι → Set Z), (∀ c, IsClopen (W c)) ∧ (∀ c, IsIrreducible (W c)) ∧ ∀ x, ∃! c, x ∈ W c := by
  first | exact @GlobalTheory.irreducibleComponents_clopen_partition | exact GlobalTheory.irreducibleComponents_clopen_partition | (intros; apply GlobalTheory.irreducibleComponents_clopen_partition <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_open_locus_torsion_points_are_level_sections : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (M : ℕ) (t : S ⟶ Sp (cycAway M)) (G : Over S) [GrpObj G] [IsCommMonObj G] (h : ℕ) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ G)), IsAbelianScheme G → 3 ≤ M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S), (∀ g : Over.mk x₀ ⟶ G, g ^ M = 1 → ∃ a, toUnit _ ≫ lev a = g) → ∃ W : S.Opens, Set.range x₀.base ⊆ W ∧ ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ S), Set.range x.base ⊆ W → ∀ g : Over.mk x ⟶ G, g ^ M = 1 → ∃ a, toUnit _ ≫ lev a = g := by
  first | (exact @GlobalTheory.LevSurjOpen.exists_open_levSurj) | (exact GlobalTheory.LevSurjOpen.exists_open_levSurj) | (intros; apply GlobalTheory.LevSurjOpen.exists_open_levSurj  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

theorem _root_.GlobalTheory.T.siegelObject_data_descends_finiteType_subring : ∀ (g n : ℕ), 3 ≤ n → ∀ (R : Type) [CommRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), ∃ (R₁ : Subring R) (β₁ : cycAway n →+* R₁) (A₁ : Over (Sp R₁)) (_ : GrpObj A₁) (P₁ : LB (A₁ ⊗ A₁).left) (lv₁ : Std g n → (𝟙_ (Over (Sp R₁)) ⟶ A₁)), Algebra.FiniteType ℤ R₁ ∧ R₁.subtype.comp β₁ = β ∧ IsAbelianScheme A₁ ∧ SmoothOfRelativeDimension g A₁.hom ∧ P₁.IsLB ∧ IsPullbackTriple c.A c.P (lvOf c) A₁ P₁ lv₁ (spMap R₁.subtype) := by
  first | exact @GlobalTheory.SiegFg.siegPre_data_descends_fg | exact GlobalTheory.SiegFg.siegPre_data_descends_fg | (intros; apply GlobalTheory.SiegFg.siegPre_data_descends_fg <;> assumption)
end
