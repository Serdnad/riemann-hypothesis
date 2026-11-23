module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle074
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle037
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle044
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle043
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle030
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier
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
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.FibreFunctionConstant

theorem exists_section_of_germs (Y : Scheme.{0}) (g : ∀ y : Y, Y.presheaf.stalk y)
    (hg : ∀ y : Y, ∃ (W : Y.Opens) (_ : y ∈ W) (t : Γ(Y, W)),
      ∀ z (hz : z ∈ W), Y.presheaf.germ W z hz t = g z) :
    ∃ a : Γ(Y, ⊤), ∀ y, Y.presheaf.germ ⊤ y trivial a = g y := by
  choose W hW t ht using hg
  have compat : TopCat.Presheaf.IsCompatible Y.sheaf.obj W t := by
    intro i j
    apply TopCat.Presheaf.section_ext Y.sheaf (W i ⊓ W j)
    rintro y ⟨hi, hj⟩
    exact (TopCat.Presheaf.germ_res_apply Y.presheaf
      (TopologicalSpace.Opens.infLELeft (W i) (W j)) y ⟨hi, hj⟩ (t i)).trans
      ((ht i y hi).trans ((ht j y hj).symm.trans
        (TopCat.Presheaf.germ_res_apply Y.presheaf
          (TopologicalSpace.Opens.infLERight (W i) (W j)) y ⟨hi, hj⟩ (t j)).symm))
  have hcov : (⊤ : Y.Opens) ≤ iSup W := fun y _ =>
    TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hW y⟩
  obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' W ⊤ (fun i => homOfLE le_top) hcov t compat
  refine ⟨a, fun q => ?_⟩
  have e := TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE (le_top : W q ≤ ⊤)) q (hW q) a
  have e2 : (Y.presheaf.map (homOfLE (le_top : W q ≤ ⊤)).op).hom a = t q := ha q
  exact e.symm.trans ((congrArg (fun z => (Y.presheaf.germ (W q) q (hW q)).hom z) e2).trans (ht q q (hW q)))

theorem unit_of_cover {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (hc : IsCptGen ξ)
    (π : Γ(X, ⊤)) (ϖ : Ω) (h0 : ϖ ≠ 0)
    (hπ : ∀ p : Cpt ξ, genMap ξ p (X.presheaf.germ ⊤ p.1 trivial π) = ϖ)
    (k : Type) [Field k] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of k)) [UniversallyClosed f]
    [ConnectedSpace Y] (ι : Y ⟶ X) (hι : ι.appTop π = 0) (hr : Set.range ι = zeroSet ξ ϖ)
    (h : Cpt ξ → Ω)
    (H : ∀ p : Cpt ξ, ¬ unitAt ξ p ϖ → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ¬ unitAt ξ q ϖ →
      h p ∈ regAt ξ q ∧ (h p - h q) / ϖ ∈ regAt ξ q)
    (hex : ∃ p, ¬ unitAt ξ p ϖ ∧ unitAt ξ p (h p)) : ∀ p, ¬ unitAt ξ p ϖ → unitAt ξ p (h p) := by
  have hy : ∀ y : Y, ι y ∈ zeroSet ξ ϖ := fun y => hr ▸ ⟨y, rfl⟩
  choose hs hn using hy
  have hreg : ∀ y : Y, ∃ c : X.presheaf.stalk (ι y), genMap ξ ⟨ι y, hs y⟩ c = h ⟨ι y, hs y⟩ := fun y => by
    obtain ⟨U, hU, HU⟩ := H ⟨ι y, hs y⟩ (hn y)
    exact (HU _ hU (hn y)).1
  choose c hcv using hreg
  have hzero : ∀ y : Y, (ι.stalkMap y).hom (X.presheaf.germ ⊤ (ι y) trivial π) = 0 := fun y => by
    have := Scheme.Hom.germ_stalkMap_apply ι ⊤ y trivial π
    rw [this]
    have e : (ι.app ⊤).hom π = 0 := hι
    erw [e]
    exact map_zero _
  obtain ⟨a, ha⟩ := exists_section_of_germs Y (fun y => (ι.stalkMap y).hom (c y)) (fun y => by
    obtain ⟨U, hU, HU⟩ := H ⟨ι y, hs y⟩ (hn y)
    obtain ⟨W, hW, t, ht⟩ := X.presheaf.exists_germ_eq (c y)
    refine ⟨ι ⁻¹ᵁ (W ⊓ U), ⟨hW, hU⟩, ι.app (W ⊓ U) (X.presheaf.map (homOfLE inf_le_left).op t), fun z hz => ?_⟩
    have hz' : ι z ∈ W ⊓ U := hz
    rw [← Scheme.Hom.germ_stalkMap_apply ι (W ⊓ U) z hz']
    have e1 := TopCat.Presheaf.germ_res_apply X.presheaf
      (homOfLE inf_le_left : W ⊓ U ⟶ W) (ι z) hz' t
    erw [e1]
    obtain ⟨d, hd⟩ := (HU ⟨ι z, hs z⟩ hz'.2 (hn z)).2
    have e2 : genMap ξ ⟨ι z, hs z⟩ (X.presheaf.germ W (ι z) hz'.1 t) = h ⟨ι y, hs y⟩ := by
      rw [← hcv y, ← ht]
      exact genMap_germ_eq_genMap_germ ξ W ⟨ι z, hs z⟩ ⟨ι y, hs y⟩ hz'.1 hW t
    have e3 : X.presheaf.germ W (ι z) hz'.1 t = c z + X.presheaf.germ ⊤ (ι z) trivial π * d := by
      apply hc.inj ⟨ι z, hs z⟩
      have e4 := hπ ⟨ι z, hs z⟩
      refine e2.trans ?_
      rw [map_add (f := _), map_mul]
      erw [hcv z, e4, hd]
      field_simp
      ring
    erw [e3]
    rw [map_add (f := _), map_mul, hzero, zero_mul, add_zero])
  have hiff : ∀ y : Y, y ∈ Y.basicOpen a ↔ unitAt ξ ⟨ι y, hs y⟩ (h ⟨ι y, hs y⟩) := fun y => by
    rw [Scheme.mem_basicOpen_top]
    erw [ha y]
    rw [isUnit_map_iff]
    refine Iff.trans ?_ (unitAt_iff_of_isCptGen ξ hc ⟨ι y, hs y⟩ _).symm
    constructor
    · intro hu
      exact ⟨c y, hu, hcv y⟩
    · rintro ⟨u, hu, e⟩
      rwa [← hc.inj ⟨ι y, hs y⟩ (e.trans (hcv y).symm)]
  have lift : ∀ p : Cpt ξ, ¬ unitAt ξ p ϖ → ∃ y : Y, p = ⟨ι y, hs y⟩ := fun p hp => by
    obtain ⟨y, hy⟩ : p.1 ∈ Set.range ι := hr ▸ (coe_mem_zeroSet p).2 hp
    exact ⟨y, Subtype.ext hy.symm⟩
  obtain ⟨p₀, hp₀, hu₀⟩ := hex
  obtain ⟨y₀, rfl⟩ := lift p₀ hp₀
  have hu := isUnit_of_basicOpen_nonempty_of_universallyClosed k Y f a ⟨y₀, (hiff y₀).2 hu₀⟩
  intro p hp
  obtain ⟨y, rfl⟩ := lift p hp
  refine (hiff y).1 ?_
  rw [Y.basicOpen_of_isUnit hu]
  trivial

end PositivityTheory.Xgn.FibreFunctionConstant

open PositivityTheory.Xgn.FibreFunctionConstant in
theorem PositivityTheory.Xgn.function_on_connected_fibre_unit : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) → ∀ h : Cpt ξ → Ω, (∀ p : Cpt ξ, ¬ unitAt ξ p (algebraMap O Ω ϖ) → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ¬ unitAt ξ q (algebraMap O Ω ϖ) → h p ∈ regAt ξ q ∧ (h p - h q) / algebraMap O Ω ϖ ∈ regAt ξ q) → (∃ p, ¬ unitAt ξ p (algebraMap O Ω ϖ) ∧ unitAt ξ p (h p)) → ∀ p, ¬ unitAt ξ p (algebraMap O Ω ϖ) → unitAt ξ p (h p) := by
  intro X Ω _ ξ O _ _ _ _ s _ ϖ hϖ hinj hs hc hconn h H hex
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  obtain ⟨U, hU, hUc, -⟩ := cpt_open_integral X Ω ξ hc
  haveI : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion _ (by simpa using hUc)
  let r : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶ Spec (CommRingCat.of O) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))
  haveI : IsClosedImmersion r :=
    IsClosedImmersion.spec_of_surjective _ (IsLocalRing.residue_surjective (R := O))
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hrr : ∀ x : Spec (CommRingCat.of O), x ∈ Set.range r ↔ ϖ ∈ x.asIdeal := fun x => by
    have e : Set.range r = PrimeSpectrum.zeroLocus (RingHom.ker (IsLocalRing.residue O) : Set O) :=
      range_comap_of_surjective _ _ (IsLocalRing.residue_surjective (R := O))
    rw [e, IsLocalRing.ker_residue, hmax, PrimeSpectrum.zeroLocus_span]
    exact Set.singleton_subset_iff
  let ι : pullback (U.ι ≫ s) r ⟶ X := pullback.fst _ _ ≫ U.ι
  have hr : Set.range ι = zeroSet ξ (algebraMap O Ω ϖ) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      have h1 : genPt ξ ⤳ ι y := (hU _).1 (pullback.fst (U.ι ≫ s) r y).2
      refine ⟨h1, ?_⟩
      rw [(ConstReg.regular_const X Ω ξ O s hs ⟨_, h1⟩ ϖ).2 hc, not_not, ← hrr]
      refine ⟨pullback.snd (U.ι ≫ s) r y, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← pullback.condition]
      simp [ι]
    · rintro ⟨h1, h2⟩
      rw [(ConstReg.regular_const X Ω ξ O s hs ⟨_, h1⟩ ϖ).2 hc, not_not, ← hrr] at h2
      have h3 : (⟨x, (hU x).2 h1⟩ : U.toScheme) ∈ Set.range (pullback.fst (U.ι ≫ s) r) := by
        rw [Scheme.Pullback.range_fst]
        exact h2
      obtain ⟨y, hy⟩ := h3
      refine ⟨y, ?_⟩
      simp [ι, hy]
  haveI : ConnectedSpace (pullback (U.ι ≫ s) r : Scheme.{0}) := by
    rw [← hr, ← Set.image_univ] at hconn
    rw [connectedSpace_iff_univ]
    exact ⟨hconn.1.of_image, ι.isEmbedding.isInducing.isPreconnected_image.1 hconn.2⟩
  refine unit_of_cover ξ hc (s.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ)) _
    ((map_ne_zero_iff _ hinj).2 hϖ.ne_zero) (fun p => ConstReg.genMap_germ_const ξ s hs p ϖ)
    (IsLocalRing.ResidueField O) _ (pullback.snd (U.ι ≫ s) r) ι ?_ hr h H hex
  have e : ι ≫ s = pullback.snd (U.ι ≫ s) r ≫ r := by
    rw [← pullback.condition]; simp [ι]
  have e1 : r.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ) = 0 := by
    have h3 := congrArg (fun q => q.hom ϖ)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (IsLocalRing.residue O)))
    have h3' : (Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField O))).inv.hom (IsLocalRing.residue O ϖ) =
      r.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ϖ) := h3
    rw [← h3', (IsLocalRing.residue_eq_zero_iff ϖ).2 (hmax ▸ Ideal.mem_span_singleton_self ϖ), map_zero]
  have e2 : (ι ≫ s).appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ) = 0 := by
    rw [e, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, e1, map_zero]
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at e2
  exact e2
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.ComponentDegreeAlt

section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {W : Type} [AddCommGroup W] [Module Ω W]

theorem wedge_ne_zero {r : ℕ} {b : Fin r → W} (hb : LinearIndependent Ω b) :
    exteriorPower.ιMulti Ω r b ≠ 0 := by
  have h := (exteriorPower.ιMulti_family_linearIndependent_field (n := r) hb).ne_zero
    (Set.powersetCard.ofFinEmbEquiv (OrderIso.refl (Fin r)).toOrderEmbedding)
  intro h0
  apply h
  simpa [exteriorPower.ιMulti_family] using h0

theorem unit_zpow {p : Cpt ξ} {u : Ω} (hu : unitAt ξ p u) (n : ℤ) : unitAt ξ p (u ^ n) := by
  cases n with
  | ofNat n => simpa using ZUnit.pow hu n
  | negSucc n => rw [zpow_negSucc]; exact ZUnit.inv (ZUnit.pow hu _)

theorem unit_prod {p : Cpt ξ} {I : Type} (s : Finset I) (u : I → Ω) (hu : ∀ i, unitAt ξ p (u i)) :
    unitAt ξ p (∏ i ∈ s, u i) :=
  Finset.prod_induction u (unitAt ξ p) (fun _ _ => ZUnit.mul) ZUnit.one (fun i _ => hu i)

theorem mul_mem_span {p : Cpt ξ} {u : Ω} (hu : u ∈ regAt ξ p) (t : Ω) :
    u * t ∈ Submodule.span (regAt ξ p) {t} :=
  Submodule.mem_span_singleton.2 ⟨⟨u, hu⟩, rfl⟩

theorem span_unit_mul {p : Cpt ξ} {u : Ω} (hu : unitAt ξ p u) (t : Ω) :
    Submodule.span (regAt ξ p) {u * t} = Submodule.span (regAt ξ p) {t} := by
  apply le_antisymm
  · exact (Submodule.span_singleton_le_iff_mem _ _).2 (mul_mem_span hu.2.1 t)
  · refine (Submodule.span_singleton_le_iff_mem _ _).2 ?_
    have := mul_mem_span hu.2.2 (u * t)
    rwa [inv_mul_cancel_left₀ hu.1] at this

theorem exists_gen_wedge {L : Lat ξ W} {r : ℕ} {b₀ : Fin r → W} (hb₀ : LinearIndependent Ω b₀)
    (hFl : L.IsFlagVBOn Set.univ b₀) (p : Cpt ξ) :
    ∃ t : Fin r → Ω, (∀ i, (L.gr b₀ i).IsGenAt p (t i)) ∧
      L.wedge r p = Submodule.span (regAt ξ p) {(∏ i, t i) • exteriorPower.ιMulti Ω r b₀} := by
  obtain ⟨U, hU, b, hbF, hbL⟩ := hFl p trivial
  have hfr : L.IsFrameAt b p := hbL p trivial hU
  choose c hc using FlagDet.exists_diag hbF
  refine ⟨c, fun i => FlagGrGen.gr_isGenAt X Ω ξ W L r b₀ b p i (c i) hb₀ hbF hfr (hc i), ?_⟩
  rw [Lat.wedge_eq_span_of_isFrameAt X Ω ξ W _ r _ p hfr,
    FlagDet.alt_triangular (exteriorPower.ιMulti Ω r (M := W)) b b₀ c hc]

theorem lineLat_eq {A B : Lat ξ W} {p q : ℕ} {a : ⋀[Ω]^p W} {b : ⋀[Ω]^q W} (ha : a ≠ 0) (hb : b ≠ 0)
    {x : Cpt ξ} {α β : Ω} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hA : A.wedge p x = Submodule.span (regAt ξ x) {α • a})
    (hB : B.wedge q x = Submodule.span (regAt ξ x) {β • b}) :
    lineLat A B p q a b x = Submodule.span (regAt ξ x) {α / β} := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨f, ⟨α', β', hα', hβ', hA', hB', hf⟩, rfl⟩
    obtain ⟨u, hu, eu⟩ := ZUnit.exists_of_span_eq (smul_ne_zero hα' ha) (hA'.symm.trans hA)
    obtain ⟨v, hv, ev⟩ := ZUnit.exists_of_span_eq (smul_ne_zero hβ' hb) (hB'.symm.trans hB)
    rw [smul_smul] at eu ev
    have e1 : α' = u * α := smul_left_injective Ω ha eu
    have e2 : β' = v * β := smul_left_injective Ω hb ev
    have e3 : f = β' / α' := by rw [← hf]; field_simp
    have e4 : f⁻¹ = (u * v⁻¹) * (α / β) := by
      have := hu.1
      have := hv.1
      rw [e3, e1, e2]; field_simp
    rw [e4]
    exact mul_mem_span (mul_mem hu.2.1 hv.2.2) _
  · refine (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.subset_span ?_)
    exact ⟨β / α, ⟨α, β, hα, hβ, hA, hB, div_mul_cancel₀ _ hα⟩, (inv_div _ _).symm⟩

theorem tens_unit_eq {Λ : Lat ξ Ω} {p : Cpt ξ} {t : Ω} (ht : Λ.IsGenAt p t) (n : ℤ) :
    Lat.tens (fun _ : Unit => Λ) (fun _ => n) p = Submodule.span (regAt ξ p) {t ^ n} := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨u, hu, eu⟩ := ZUnit.exists_of_span_eq (hs ()).1 ((hs ()).2.symm.trans ht.2)
    have e : ∏ i : Unit, s i ^ n = u ^ n * t ^ n := by
      rw [Fintype.prod_unique, ← mul_zpow]
      exact congrArg (· ^ n) eu
    rw [e]
    exact mul_mem_span (unit_zpow hu n).2.1 _
  · refine (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.subset_span ?_)
    exact ⟨fun _ => t, fun _ => ht, by rw [Fintype.prod_unique]⟩

theorem zpow_finsum {a : Ω} (ha : a ≠ 0) {I : Type} (s : Finset I) (n : I → ℤ) :
    a ^ (∑ i ∈ s, n i) = ∏ i ∈ s, a ^ n i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ ha, ih]

end General

theorem prod_root {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {Ω : Type} [Field Ω] (t : ∀ s, Fin (labelRk D s) → Ω) (τ : CMType H) :
    ∏ i : Fin (D.p + D.q), t (HodgeCpt.rootIdx D (τ, i)).1 (HodgeCpt.rootIdx D (τ, i)).2 ^
      HodgeCpt.rootSgn D (τ, i) = (∏ i, t (.inl τ) i) / ∏ j, t (.inr τ) j := by
  rw [Fin.prod_univ_add, div_eq_mul_inv]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    have h : ((Fin.castAdd D.q i : Fin (D.p + D.q)) : ℕ) < D.p := i.2
    have e : HodgeCpt.rootIdx D (τ, Fin.castAdd D.q i) = ⟨.inl τ, i⟩ := dif_pos h
    have e' : HodgeCpt.rootSgn D (τ, Fin.castAdd D.q i) = 1 := if_pos h
    rw [e, e', zpow_one]
  · rw [← Finset.prod_inv_distrib]
    refine Fintype.prod_equiv (Fin.revPerm (n := D.q)) _ _ fun j => ?_
    have h : ¬ ((Fin.natAdd D.p j : Fin (D.p + D.q)) : ℕ) < D.p := by simp
    have e : HodgeCpt.rootIdx D (τ, Fin.natAdd D.p j) = ⟨.inr τ, Fin.rev j⟩ := by
      refine (dif_neg h).trans ?_
      congr 1
      apply Fin.ext
      have hj : (j : ℕ) < D.q := j.2
      show D.p + D.q - 1 - (D.p + (j : ℕ)) = D.q - ((j : ℕ) + 1)
      omega
    have e' : HodgeCpt.rootSgn D (τ, Fin.natAdd D.p j) = -1 := if_neg h
    rw [e, e', zpow_neg_one]
    rfl

end PositivityTheory.Xgn.ComponentDegreeAlt

open PositivityTheory.Xgn.ComponentDegreeAlt in
theorem PositivityTheory.Xgn.hodge_component_flag_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω) (τ : CMType H), Fl.RootLines xdeg e → (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ)) (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))).IsDegOn Set.univ y (∑ i, xdeg (τ, i)) (∏ i, e (τ, i)) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 Fl xdeg e τ hR
  have hli : ∀ s, LinearIndependent Ω (Fl.b s) := by
    obtain ⟨_, _, -, -, -, h, -⟩ := Fl.generic
    exact h
  refine ⟨Finset.prod_ne_zero_iff.2 fun i _ => (hR (τ, i)).1, fun p _ cc hcc => ?_⟩
  choose t ht hw using fun s => exists_gen_wedge (hli s) (Fl.sub s) p
  have hy : ∀ k, y ⟨k, cc k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hcc.1 k (Finset.mem_univ k)
  rw [lineLat_eq (wedge_ne_zero (hli _)) (wedge_ne_zero (hli _))
    (Finset.prod_ne_zero_iff.2 fun i _ => (ht _ i).1) (Finset.prod_ne_zero_iff.2 fun i _ => (ht _ i).1)
    (hw (.inl τ)) (hw (.inr τ)), ← prod_root D t τ]
  have hu : ∀ i : Fin (D.p + D.q), ∃ u : Ω, unitAt 𝔐.ξ p u ∧
      t (HodgeCpt.rootIdx D (τ, i)).1 (HodgeCpt.rootIdx D (τ, i)).2 ^ HodgeCpt.rootSgn D (τ, i) =
        u • (∏ k, y ⟨k, cc k⟩ ^ xdeg (τ, i) k) • e (τ, i) := fun i =>
    ZUnit.exists_of_span_eq (zpow_ne_zero _ (ht _ _).1)
      ((tens_unit_eq (ht _ _) _).symm.trans ((hR (τ, i)).2 p trivial cc hcc))
  choose u hu eu using hu
  have key : ∏ i : Fin (D.p + D.q), t (HodgeCpt.rootIdx D (τ, i)).1 (HodgeCpt.rootIdx D (τ, i)).2 ^
      HodgeCpt.rootSgn D (τ, i) =
      (∏ i, u i) * ((∏ k, y ⟨k, cc k⟩ ^ (∑ i, xdeg (τ, i)) k) • ∏ i, e (τ, i)) := by
    simp only [eu, smul_eq_mul, Finset.prod_mul_distrib, Finset.sum_apply, zpow_finsum (hy _)]
    rw [Finset.prod_comm]
  rw [key]
  exact span_unit_mul (unit_prod _ u hu) _
end
