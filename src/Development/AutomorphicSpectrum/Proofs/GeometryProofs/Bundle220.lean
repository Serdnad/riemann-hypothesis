module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle218
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBaseDegreeSettingStrict
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.AbelianCmStokesIdentity
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductPullbackUnique
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle216
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle217
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle131
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle037
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
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle089
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ChangeGeo

theorem exists_factor_XF_of_genericPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ Y.X), GlobalTheory.CompanionTheory.Ar.genPt ξ ∈ genericPoints Y.X →
      ∃ y₀ : Sp Ω ⟶ Xo.XF c, ξ = y₀ ≫ Y.j := by
  intro E _ _ _ H D l Xo c Y Ω _ ξ hξ
  obtain ⟨K, _, _, n, x, y, ht, -, he⟩ := GlobalTheory.T.generic_point_normal_coords E H D l Xo c Y _ hξ
  obtain ⟨i, hi⟩ := GlobalTheory.CompanionTheory.Ar.TowerOfTest.factor (y ≫ Y.j) ht.gen ξ he.symm
  exact ⟨Spec.map (CommRingCat.ofHom i) ≫ y, by rw [hi, Category.assoc]⟩

end GlobalTheory.CompanionTheory.Ar.ChangeGeo
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.full_level_generic_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (K Ω : Type) [Field K] [Field Ω] [CharZero Ω] (i : K →+* Ω) (y : Sp K ⟶ Xo.XF c) (N : ℕ) (z : Ωˣ) (ev : D.La → (Over.mk (spMap i ≫ y ≫ Y.j) ⟶ Y.t.G)), 1 ≤ N → IsFullLevelAt D Y.t (spMap i ≫ y ≫ Y.j) N z ev → ∀ (X : Scheme.{0}) (ξ : Sp Ω ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ f : X ⟶ Y.X, ξ ≫ f = spMap i ≫ y ≫ Y.j → ∃ (t : SAB H X) (_ : SABMap t Y.t f) (ev' : D.La → (Over.mk ξ ⟶ t.G)), IsFullLevelAt D t ξ N z ev' ∧ FullTorsion t.G ξ N ∧ ∀ q : Cpt ξ, unitAt ξ q (z : Ω) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.XR.exists_full_level_over | exact GlobalTheory.CompanionTheory.Ar.XR.exists_full_level_over | (intros; apply GlobalTheory.CompanionTheory.Ar.XR.exists_full_level_over <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.PlaceOrd

variable {X X' : Scheme.{0}} {Ω : Type} [Field Ω]

def tr {A B : Subring Ω} (h : A = B) (N : Submodule B Ω) : Submodule A Ω where
  carrier := N
  add_mem' := N.add_mem
  zero_mem' := N.zero_mem
  smul_mem' := fun c _ hx => N.smul_mem ⟨c.1, h ▸ c.2⟩ hx

theorem tr_eq_span_iff {A B : Subring Ω} (h : A = B) (N : Submodule B Ω) (S : Set Ω) :
    tr h N = Submodule.span A S ↔ N = Submodule.span B S := by
  subst h
  have : tr rfl N = N := by ext; rfl
  rw [this]

theorem genMap_stalkMap₀ (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (g : X' ⟶ X) (q : Cpt ξ')
    (h : genPt (ξ' ≫ g) ⤳ g q.1) (s : X.presheaf.stalk (g q.1)) :
    genMap ξ' q ((g.stalkMap q.1).hom s) = genMap (ξ' ≫ g) ⟨g q.1, h⟩ s := by
  have e := Scheme.Hom.stalkSpecializes_stalkMap g _ _ q.2
  have e2 := congrArg (fun t => (t ≫ Scheme.stalkClosedPointTo ξ').hom s) e
  have e3 := Scheme.stalkClosedPointTo_comp ξ' g
  have e4 := congrArg (fun t => (X.presheaf.stalkSpecializes h ≫ t).hom s) e3
  exact e2.symm.trans e4.symm

def push (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (g : X' ⟶ X) (p : Cpt ξ') : Cpt (ξ' ≫ g) :=
  ⟨g p.1, p.2.map g.continuous⟩

variable {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} {g : X' ⟶ X}

def pullL (hr : ∀ p, regAt ξ' p = regAt (ξ' ≫ g) (push ξ' g p)) (L : Lat (ξ' ≫ g) Ω) : Lat ξ' Ω :=
  fun p => tr (hr p) (L (push ξ' g p))

section

variable (hr : ∀ p, regAt ξ' p = regAt (ξ' ≫ g) (push ξ' g p)) {L : Lat (ξ' ≫ g) Ω}
include hr

theorem unit_iff (p : Cpt ξ') (a : Ω) : unitAt ξ' p a ↔ unitAt (ξ' ≫ g) (push ξ' g p) a := by
  unfold unitAt
  rw [hr p]

theorem pull_span_iff (p : Cpt ξ') (S : Set Ω) :
    pullL hr L p = Submodule.span (regAt ξ' p) S ↔
      L (push ξ' g p) = Submodule.span (regAt (ξ' ≫ g) (push ξ' g p)) S :=
  tr_eq_span_iff _ _ _

theorem isVB_pull (hL : L.IsVB 1 ⊤) : (pullL hr L).IsVB 1 ⊤ := by
  intro p _
  obtain ⟨U, hU, b, hb, h⟩ := hL (push ξ' g p) trivial
  refine ⟨g ⁻¹ᵁ U, hU, b, hb, fun q _ hq => ?_⟩
  obtain ⟨h1, h2⟩ := h (push ξ' g q) trivial hq
  exact ⟨h1, (pull_span_iff hr q _).2 h2⟩

omit hr in
theorem isIntegral_congr {A B : Subring Ω} (h : A = B) {a : Ω} (ha : IsIntegral A a) : IsIntegral B a := by
  subst h
  exact ha

theorem normal_pull (hN : NormalCpt (ξ' ≫ g)) : NormalCpt ξ' := fun p a ha => by
  rw [hr p]
  exact hN _ a (isIntegral_congr (hr p) ha)

theorem isGenAt_pull {p : Cpt ξ'} {t : Ω} (h : L.IsGenAt (push ξ' g p) t) : (pullL hr L).IsGenAt p t :=
  ⟨h.1, (pull_span_iff hr p _).2 h.2⟩

theorem order_back {σ ϖ : Ω} {M : ℕ} {a : ℤ} {p : Cpt ξ'} (h : OrderAt (pullL hr L) σ ϖ M a p) :
    OrderAt L σ ϖ M a (push ξ' g p) := by
  obtain ⟨e, c, he, h1, h2, h3⟩ := h
  exact ⟨e, c, he, (pull_span_iff hr p _).1 h1, h2, (unit_iff hr p _).1 h3⟩

theorem trivMod_pull {ϖ l u : Ω} (e : l = ϖ * u) (hϖ : ∀ p, ϖ ∈ regAt ξ' p) (hu : ∀ p, u ∈ regAt ξ' p)
    (hT : TrivMod L l) : TrivMod (pullL hr L) ϖ := by
  obtain ⟨t, ht⟩ := hT
  have key : ∀ p, ¬ unitAt ξ' p ϖ → ¬ unitAt (ξ' ≫ g) (push ξ' g p) l := fun p hp hl =>
    hp (ZUnit.of_mul (hϖ p) (hu p) ((unit_iff hr p _).2 (e ▸ hl)))
  refine ⟨fun p => t (push ξ' g p), fun p hp => ?_⟩
  obtain ⟨U, hU, H⟩ := ht _ (key p hp)
  refine ⟨g ⁻¹ᵁ U, hU, fun q hq hq' => ?_⟩
  obtain ⟨h0, h1, y, hy, hty⟩ := H (push ξ' g q) hq (key q hq')
  refine ⟨h0, (pull_span_iff hr q _).2 h1, u • y, ?_, ?_⟩
  · exact (L (push ξ' g q)).smul_mem ⟨u, hr q ▸ hu q⟩ hy
  · change t (push ξ' g p) - t (push ξ' g q) = ϖ • u • y
    rw [hty, e, mul_smul]

end

theorem valAt_zero_down {R : Type} [CommRing R] [IsLocalRing R] (hc : IsCptGen ξ')
    (z : Spec (CommRingCat.of R) ⟶ X') {ϖ u l : Ω} (e : l = ϖ * u) (h : genPt ξ' ⤳ centre z)
    (hv : ValAt ξ' z ϖ 0) (hu : u ∈ regAt ξ' ⟨centre z, h⟩)
    (hl : l ∈ regAt (ξ' ≫ g) (push ξ' g ⟨centre z, h⟩)) : ValAt (ξ' ≫ g) (z ≫ g) l 0 := by
  obtain ⟨h', s, hs, h0⟩ := hv
  obtain ⟨t, ht⟩ : ∃ t : X'.presheaf.stalk (centre z), genMap ξ' ⟨centre z, h⟩ t = u := hu
  obtain ⟨w, hw⟩ := hl
  have e1 : (g.stalkMap (centre z)).hom w = s * t := by
    apply hc.inj ⟨centre z, h⟩
    rw [genMap_stalkMap₀ ξ' g ⟨centre z, h⟩ (push ξ' g ⟨centre z, h⟩).2 w, map_mul, ht]
    refine hw.trans ?_
    rw [e, ← hs]
  have e2 : (Scheme.stalkClosedPointTo (z ≫ g)).hom w =
      (Scheme.stalkClosedPointTo z).hom ((g.stalkMap (centre z)).hom w) :=
    congrArg (fun t => t.hom w) (Scheme.stalkClosedPointTo_comp z g)
  refine ⟨(push ξ' g ⟨centre z, h⟩).2, w, hw, e2.trans ?_⟩
  rw [e1]
  exact (map_mul (Scheme.stalkClosedPointTo z).hom s t).trans
    ((congrArg (fun x : R => x * (Scheme.stalkClosedPointTo z).hom t) h0).trans (zero_mul _))

theorem valAt_up {R : Type} [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X')
    (h : genPt ξ' ⤳ centre z) {a : Ω} {r : R} (hv : ValAt (ξ' ≫ g) (z ≫ g) a r) : ValAt ξ' z a r := by
  obtain ⟨h', s, hs, rfl⟩ := hv
  exact ⟨h, (g.stalkMap (centre z)).hom s, (genMap_stalkMap₀ ξ' g ⟨centre z, h⟩ h' s).trans hs,
    (congrArg (fun t => t.hom s) (Scheme.stalkClosedPointTo_comp z g)).symm⟩

def curvePush {ϖ l : Ω} (Γ : FibreCurve ξ' ϖ) (hz : ValAt (ξ' ≫ g) (Γ.η ≫ g) l 0) : FibreCurve (ξ' ≫ g) l where
  k := Γ.k
  κ := Γ.κ
  fg := Γ.fg
  trdeg := Γ.trdeg
  C := Γ.C
  w_pos := Γ.w_pos
  triv := Γ.triv
  all := Γ.all
  η := Γ.η ≫ g
  η_spec := hz.1
  η_zero := hz
  z := fun i => Γ.z i ≫ g
  z_gen := fun i => by rw [← Category.assoc, Γ.z_gen]

theorem hasDeg_back (hr : ∀ p, regAt ξ' p = regAt (ξ' ≫ g) (push ξ' g p)) {L : Lat (ξ' ≫ g) Ω} {ϖ l : Ω}
    (Γ : FibreCurve ξ' ϖ) (hz : ValAt (ξ' ≫ g) (Γ.η ≫ g) l 0) (h : (curvePush Γ hz).HasDeg L 0) :
    Γ.HasDeg (pullL hr L) 0 := by
  obtain ⟨e, f, r, he, hf, hv, hfin, hd⟩ := h
  refine ⟨e, f, r, isGenAt_pull hr he, fun i => ⟨Γ.z_spec i, ?_⟩, fun i => ⟨(hv i).1, ?_⟩, hfin, hd⟩
  · obtain ⟨_, h2⟩ := hf i
    exact isGenAt_pull hr h2
  · exact valAt_up _ Γ.η_spec (hv i).2

theorem numTrivMod_pull (hr : ∀ p, regAt ξ' p = regAt (ξ' ≫ g) (push ξ' g p)) (hc : IsCptGen ξ')
    {L : Lat (ξ' ≫ g) Ω} {ϖ l u : Ω} (e : l = ϖ * u) (hϖ : ∀ p, ϖ ∈ regAt ξ' p) (hu : ∀ p, u ∈ regAt ξ' p)
    (hT : NumTrivMod L l) : NumTrivMod (pullL hr L) ϖ := fun Γ => by
  let p : Cpt ξ' := ⟨centre Γ.η, Γ.η_spec⟩
  have hl : l ∈ regAt (ξ' ≫ g) (push ξ' g p) := by
    have h1 := mul_mem (hϖ p) (hu p)
    rwa [← e, hr p] at h1
  have hz := valAt_zero_down (g := g) hc Γ.η e Γ.η_spec Γ.η_zero (hu p) hl
  exact hasDeg_back hr Γ hz (hT (curvePush Γ hz))

theorem order_at_place : ∀ (X X' : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (g : X' ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X' ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O) (L : Lat ξ Ω) (σ : Ω) (ℓ : ℕ) (u : O), PropZ → Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ' ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → ξ' ≫ g = ξ → IsCptGen ξ → IsCptGen ξ' → (∀ q' : X', genPt ξ' ⤳ q') → NormalCpt ξ → ConstClosed O Ω → (∀ (p' : Cpt ξ') (p : Cpt ξ), p.1 = g p'.1 → ∀ a : Ω, a ∈ regAt ξ' p' ↔ a ∈ regAt ξ p) → L.IsVB 1 ⊤ → (∀ p ∈ genFibre ℤ ξ, L.IsGenAt p σ) → (ℓ : Ω) = algebraMap O Ω (ϖ * u) → (TrivMod L (ℓ : Ω) ∨ NumTrivMod L (ℓ : Ω)) → ∃ (M : ℕ) (a : ℤ), 0 < M ∧ ∀ p : Cpt ξ, (∃ p' : Cpt ξ', g p'.1 = p.1) → OrderAt L σ (algebraMap O Ω ϖ) M a p := by
  intro X X' Ω _ _ ξ ξ' g O _ _ _ _ s _ ϖ L σ ℓ u hZ hirr hinj hs hcomp hc hc' hall hN hcc hreg hVB hgen hℓ hT
  subst hcomp
  have hr : ∀ p, regAt ξ' p = regAt (ξ' ≫ g) (push ξ' g p) := fun p =>
    SetLike.ext (hreg p (push ξ' g p) rfl)
  have hconst : ∀ (o : O) (p : Cpt ξ'), algebraMap O Ω o ∈ regAt ξ' p := fun o p =>
    (ConstReg.regular_const X' Ω ξ' O s hs p o).1
  have hconn := GlobalTheory.T.isConnected_zeroSet_uniformizer X' Ω ξ' O s ϖ hirr hinj hs hc' hcc
  have hgen' : ∀ p ∈ genFibre O ξ', (pullL hr L).IsGenAt p σ := fun p hp => by
    refine isGenAt_pull hr (hgen _ fun o ho => ?_)
    have e : algebraMap ℤ Ω o = algebraMap O Ω (o : O) := by simp
    rw [e, ← unit_iff hr]
    refine hp _ fun h0 => ho ?_
    have := congrArg (algebraMap O Ω) h0
    simpa using this
  have e : (ℓ : Ω) = algebraMap O Ω ϖ * algebraMap O Ω u := by rw [hℓ, map_mul]
  have main : ∃ (M : ℕ) (a : ℤ), 0 < M ∧ ∀ p : Cpt ξ', OrderAt (pullL hr L) σ (algebraMap O Ω ϖ) M a p := by
    rcases hT with hT | hT
    · exact hZ X' Ω ξ' O s ϖ hirr hinj hs hc' (normal_pull hr hN) hconn (pullL hr L) σ (isVB_pull hr hVB)
        (trivMod_pull hr e (hconst ϖ) (hconst u) hT) hgen'
    · exact GlobalTheory.T.line_degree_special_fibre X' Ω ξ' O s ϖ hirr hinj hs hc' (normal_pull hr hN) hconn (pullL hr L) σ
        (isVB_pull hr hVB) (numTrivMod_pull hr hc' e (hconst ϖ) (hconst u) hT) hgen'
  obtain ⟨M, a, hM, H⟩ := main
  refine ⟨M, a, hM, ?_⟩
  rintro p ⟨p', hp⟩
  have : p = push ξ' g p' := Subtype.ext hp.symm
  rw [this]
  exact order_back hr (H p')

end GlobalTheory.CompanionTheory.Ar.Flat.PlaceOrd
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.orthogonal_metric_flag_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) [Fintype (CMType H)] (Fl : 𝔐.Flag) (h : LieMetric 𝔐.M y), h.Orth 𝔐.t.act → ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel 𝔐.t.G z B.carrier), IsFibre (fun z v w c => c = h.ip z v w) z B MB → ∃ (A : FlagPair B (CMType H) D.p D.q), A.IsOrthFull ∧ (∀ τ i, IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inl τ)) i.val) z MB ((A.W τ).F i)) ∧ ∀ τ i, IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inr τ)) i.val) z MB ((A.S τ).F i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagFib.flag_fibre | exact GlobalTheory.CompanionTheory.Ar.FlagFib.flag_fibre | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagFib.flag_fibre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.cp_ratio_unramified_odd_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime], p ∈ S → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ κ w : Ω, HT.IsCp p κ → HT.IsCp p w → HT.Sandwich 𝔐 p κ → ∀ q : Cpt 𝔐.ξ, InFibre 𝔐.ξ p q → w ∈ regAt 𝔐.ξ q → ∀ t : CMType H ⊕ CMType H, 𝔐.dR t q ≤ 𝔐.HT p t q ∧ ∀ e ∈ 𝔐.HT p t q, w • e ∈ 𝔐.dR t q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.SandPt.sandwich_at_point | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.SandPt.sandwich_at_point | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.SandPt.sandwich_at_point <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

theorem _root_.GlobalTheory.T.local_point_specializes_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (T : Type) [CommRing T] [IsLocalRing T] (y : Sp T ⟶ Xo.XF c) (c₀ : c.F →+* T), y ≫ pullback.snd _ _ = spMap c₀ → centre y ∈ U → ∃ (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (κ : c.F →+* Y.X.presheaf.stalk (centre (y ≫ Y.j))), (genMap (Z.ξ₀ ≫ Y.j) ⟨_, h⟩).comp κ = Z.inc ∧ (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp κ = c₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFn.Coef.exists_coef | exact GlobalTheory.CompanionTheory.Ar.LocFn.Coef.exists_coef | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFn.Coef.exists_coef <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.cm_integers_regular_at_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : E →+* Z.Ω), (∀ b : 𝓞 E, σ (b : E) = Z.inc (tauIn c τ b)) →
    ∀ (q : Cpt (Z.ξ₀ ≫ Y.j)) (a : 𝓞 E), σ (a : E) ∈ regAt (Z.ξ₀ ≫ Y.j) q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.integers_mem_regAt | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.integers_mem_regAt | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.integers_mem_regAt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem _root_.GlobalTheory.T.torsion_value_unique_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (n : ℕ) (s : Out.H0 D.t.PP.L n) (F : Type) [Field F] (b : Sp F ⟶ Sp (𝓞 L)) (y : Over.mk b ⟶ D.t.G) (N : ℕ), 1 ≤ N → y ^ N = 1 → (∃! T : F, TorsVal D.t.PP s y N T) ∧ ∀ (F' : Type) [Field F'] (f : F →+* F') (y' : Over.mk (spMap f ≫ b) ⟶ D.t.G) (T : F), y'.left = spMap f ≫ y.left → TorsVal D.t.PP s y N T → TorsVal D.t.PP s y' N (f T) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.TorsExist.torsVal_existsUnique | exact GlobalTheory.CompanionTheory.Ar.Sl.TorsExist.torsVal_existsUnique | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.TorsExist.torsVal_existsUnique <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

theorem _root_.GlobalTheory.CompanionTheory.Relay.intersection_final_estimate : PB.Inputs → Prov.An → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → Flat.GagaSections → GlobalTheory.Published.SemiAbelianHomExtension → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ) (U : ((Σ k, J k) → ℂ) → ℝ), IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ → Or.𝔐.IsCuspWeight Or.sm U → ∀ [DecidableEq (CMType H)] (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt), X.H = Hd → (∀ z ∈ Dc.Xo, X.Cd.cuspWeight z = U z) → CuspBundlePos X → ∀ B : ℕ, 4 * Dc.f + 2 ≤ B → ArLimExists X.H X.S B → Top.StokesAt X B := by
  first | exact @ModelDimension.abelian_cm_stokes_identity | exact ModelDimension.abelian_cm_stokes_identity
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_inner_product_pullback_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S' S : Scheme.{0}) (t' : SAB H S') (t : SAB H S) (f : S' ⟶ S) (m : SABMap t' t f) (z : Sp ℂ ⟶ S') (v' w' : epsAt z ⟶ t'.G) (v w : epsAt (z ≫ f) ⟶ t.G), v'.left ≫ m.φ = v.left → w'.left ≫ m.φ = w.left → (∀ c, HodgeIP t'.G t'.PP.L z v' w' c ↔ HodgeIP t.G t.PP.L (z ≫ f) v w c) ∧ ∀ c c', HodgeIP t.G t.PP.L (z ≫ f) v w c → HodgeIP t.G t.PP.L (z ≫ f) v w c' → c = c' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeUnique.main | exact GlobalTheory.CompanionTheory.Ar.HodgeUnique.main | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeUnique.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.cm_lie_model_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP), ∃ (M : LieModel Xo.univ.t.G (under X.y) (Fin g → X.K)) (ρ : 𝓞 E →+* Module.End X.K (Fin g → X.K)) (lam : ∀ b, PureType.lat hP (sgnRt H b) → Fin g → X.K), M.IsActOf Xo.univ.t.act.act ρ ∧ (∀ b a u, X.IsImage b a u ↔ u = M.pt (lam b a)) ∧ (∀ b (s : 𝓞 E) a, lam b (s • a) = ρ s (lam b a)) ∧ (∀ b a a', lam b (a + a') = lam b a + lam b a') ∧ (∀ b (s : X.K) a, (s : ℂ) = sgnRt H b → ρ H.rt (lam b a) = s • lam b a) ∧ ∀ b (τ : E →+* ℂ) a v, X.IsCMVec b τ a v ↔ v = M.pt (HT.eigProj ρ (X.β.comp (tauE c τ)) (lam b a)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.cm_lie_model_action | exact GlobalTheory.CompanionTheory.Relay.cm_lie_model_action | (intros; apply GlobalTheory.CompanionTheory.Relay.cm_lie_model_action <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.cm_pack_eigen_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (b : Bool) (τ : E →+* ℂ) (a : PureType.lat hP (sgnRt H b)) (v : epsAt (under X.y) ⟶ Xo.univ.t.G), X.IsCMVec b τ a v → IsDerivAt0 (fun s => (FU.ex i P s).left) ((Z b).z • tyPart ty τ (P a)) (spMap (dualMap (algebraMap X.K ℂ)) ≫ v.left) := by
  intro E _ _ _ H D l Xo c g ty FU i Z P hP X b τ a v hv
  exact GlobalTheory.CompanionTheory.Ar.Fl.CoordPart.isDerivAt0_of_isCMVec E H D l Xo c g ty FU i Z P hP X b τ a v hv
end
