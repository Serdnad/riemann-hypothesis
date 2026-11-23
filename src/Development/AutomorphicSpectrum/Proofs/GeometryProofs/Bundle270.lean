module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PolarizedDataFieldExtension
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle189
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle163
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle267
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle096
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsEigFrameOfFrPt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem _root_.GlobalTheory.T.polarized_data_field_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (L' : Type) [Field L'] [NumberField L'] [Algebra L L'], Nonempty (Σ D' : PPData H L', D.Ext D') ∧ ∀ (D' : PPData H L') (_ : D.Ext D'), D'.g = D.g ∧ D'.hp = D.hp ∧ ∃ io : D.B.carrier →ₛₗ[algebraMap (𝓞 L) (𝓞 L')] D'.B.carrier, Function.Injective io ∧ Submodule.span (𝓞 L') (Set.range io) = ⊤ ∧ ∀ (σ' : L' →+* ℂ) (x y : D.B.carrier), ((D'.B.metric.form σ').inner ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] io x) ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] io y) : ℂ) = ((D.B.metric.form (σ'.comp (algebraMap L L'))).inner ((1 : ComplexAt _) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt _) ⊗ₜ[𝓞 L] y) : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.ext_baseChange | exact GlobalTheory.CompanionTheory.Ar.Sl.ext_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.ext_baseChange <;> assumption)
end

section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem gramAt_posDef_of_isFrameAt_blocks : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (τ : CMType H) (b : Fin Dc.N → W τ) (h : genPt Or.𝔐.ξ ⤳ centre z), Or.𝔐.Interior z → (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsFrameAt b ⟨centre z, h⟩ → ∃ G : Matrix (Fin Dc.N) (Fin Dc.N) ℂ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (fun k => Or.i τ (b k)) G ∧ G.PosDef := by
  intro E _ _ _ H D l Xo c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or z τ b h hi hf
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hmem : ∀ w, Or.i τ w ∈ Or.𝔐.Vgen (Or.bg τ) ⊔ Or.𝔐.Vgen (Or.sm τ) := fun w => by
    rw [← Or.i_range τ]
    exact LinearMap.mem_range_self _ w
  let φ : W τ →ₗ[Ω] ↥(Or.𝔐.Vgen (Or.bg τ) ⊔ Or.𝔐.Vgen (Or.sm τ)) := (Or.i τ).codRestrict _ hmem
  have hφi : Function.Injective φ := fun x y hxy => Or.i_inj τ (congrArg Subtype.val hxy)
  have hφs : Function.Surjective φ := fun x => by
    have hx : (x : Or.𝔐.Li) ∈ LinearMap.range (Or.i τ) := by
      rw [Or.i_range τ]
      exact x.2
    obtain ⟨w, hw⟩ := hx
    exact ⟨w, Subtype.ext hw⟩
  have hpol := GlobalTheory.T.interior_point_polarised E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 z hi
  have hframe : (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p)
      (Or.𝔐.Vgen (Or.bg τ) ⊔ Or.𝔐.Vgen (Or.sm τ)).subtype).IsFrameAt (fun k => φ (b k)) ⟨centre z, h⟩ := by
    refine ⟨hf.1.map' φ (LinearMap.ker_eq_bot.2 hφi), ?_⟩
    have hs := hf.2
    ext x
    obtain ⟨w, rfl⟩ := hφs x
    have hrange : Set.range (fun k => φ (b k)) = φ '' Set.range b := by
      rw [← Set.range_comp]
      rfl
    have hspan : Submodule.span (regAt Or.𝔐.ξ ⟨centre z, h⟩) (Set.range (fun k => φ (b k))) =
        (Submodule.span (regAt Or.𝔐.ξ ⟨centre z, h⟩) (Set.range b)).map
          (φ.restrictScalars (regAt Or.𝔐.ξ ⟨centre z, h⟩)) := by
      rw [hrange, Submodule.map_span]
      rfl
    rw [hspan, ← hs]
    constructor
    · intro hx
      exact ⟨w, hx, rfl⟩
    · rintro ⟨w', hw', e⟩
      have : w' = w := hφi e
      subst this
      exact hw'
  obtain ⟨G, h1, h2⟩ := GlobalTheory.T.pair_sum_frame_at_point E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 (Or.bg τ) (Or.sm τ) Dc.N
    (fun k => φ (b k)) z h hpol hframe
  exact ⟨G, h1, h2⟩

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg

open GlobalTheory.CompanionTheory.Ar.HodgeCpt (rootIdx rootSgn)

theorem isHodgeLine_pull_tensor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (hv : IsBlockMap bk (blkV bk bx)) (r : CMType H × Fin (D.p + D.q)) (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀) (A₀ : HermLine J₀) (T : HermLine J), Function.Injective β → CharZero Ω → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → GenPull Fl₀ Fl i hd → NormPull Fl₀ Fl i h → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (a : Ω₀) (r : ℂ), ValAt 𝔐₀.ξ (z ≫ h) a r → ValAt 𝔐.ξ z (i a) r) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → CoordsAt 𝔐₀.ξ y₀ (z ≫ h) (fun p => w (blkV bk bx p))) → (∀ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, 𝔐.Interior z → 𝔐₀.Interior (z ≫ h)) → e ≠ 0 → A₀.a = a₀ → T.a = a - pullDeg bk a₀ → IsRatio 𝔐.ξ y y₀ bk bx i a a₀ e e₀ T.h → Fl₀.IsHodgeLine r e₀ A₀ → Fl.IsHodgeLine r e ((pullHerm hv A₀).tensor T) := by
  intro E _ _ _ H D l Xo c O _ β Y S₀ S Ω₀ Ω _ _ K₀ K _ _ J₀ J _ _ y₀ y 𝔐₀ 𝔐 i h hd Fl₀ Fl bk bx hv r a a₀ e e₀ A₀ T
    hβ hcz hy hGen hNorm hVal hCoord hInt he hA hT hR hH z w hw hI t ν hg
  haveI := hcz
  subst hA
  have hsp : genPt 𝔐₀.ξ ⤳ centre (z ≫ h) := 𝔐₀.all _
  have hw₀ := hCoord z w hw
  have hI₀ := hInt z hI

  obtain ⟨t₀, ht₀⟩ := Flag.gr_gen_of_isFlagVBOn (Fl₀.sub (rootIdx D r).1)
    (p := ⟨centre (z ≫ h), 𝔐₀.all _⟩) (Set.mem_univ _) (rootIdx D r).2
  obtain ⟨ν₀, -, hn₀⟩ := GlobalTheory.T.hodge_cpt_interior_flag E H D l Xo c O β Y S₀ Ω₀ K₀ J₀ y₀ 𝔐₀ Fl₀ hβ (z ≫ h) hI₀ _ _ t₀ ht₀
  have hgr₀ := (hn₀ t₀ ν₀).2 ⟨1, one_ne_zero, by rw [div_self ht₀.1]; exact CxVal.one hsp, by simp⟩

  have ecp : pushCpt hd ⟨centre z, 𝔐.all _⟩ = ⟨centre (z ≫ h), 𝔐₀.all _⟩ := Subtype.ext (by
    show h (z _) = (z ≫ h) _
    exact (Scheme.Hom.comp_apply z h _).symm)
  have hgen := hGen ⟨centre z, 𝔐.all _⟩ (fun p hp => not_inFibre 𝔐.ξ z (𝔐.all _) hp) _ _ t₀ (ecp ▸ ht₀)
  obtain ⟨ν₁, -, hn₁⟩ := GlobalTheory.T.hodge_cpt_interior_flag E H D l Xo c O β Y S Ω K J y 𝔐 Fl hβ z hI _ _ (i t₀) hgen
  have hit : i t₀ ≠ 0 := hgen.1
  obtain ⟨u', -, hu', e'⟩ := (hn₁ _ _).1 (hNorm z _ _ t₀ ν₀ hgr₀)
  have hu1 : u' = 1 := CxVal.unique hu' (by rw [div_self hit]; exact CxVal.one (𝔐.all _))
  obtain ⟨u₁, hu₁0, hu₁, eν⟩ := (hn₁ _ _).1 hg
  rw [hu1, norm_one, _root_.one_mul] at e'
  subst e'

  have hsec := hH (z ≫ h) _ hw₀ hI₀ t₀ ν₀ hgr₀
  choose c₀ hc₀ using hw₀.1
  choose c hc using hw.1
  have hc₀' : ∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0 := fun k => (hc₀ k).ne_zero
  have hc' : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  obtain ⟨u₀, hu₀, en₀⟩ := hsec.2.2 c₀ hc₀'
  obtain ⟨u, -, hu, eT⟩ := hR z w hw c c₀ hc' hc₀'
  have ha : ((pullHerm hv A₀).tensor T).a = a := by
    show pullDeg bk A₀.a + T.a = a
    rw [hT]
    abel
  have hM₀ : (∏ k, y₀ ⟨k, c₀ k⟩ ^ A₀.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hw₀.2 k (c₀ k) (hc₀ k)).1
  have hM : (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hw.2 k (c k) (hc k)).1
  have hm₀ : i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ A₀.a k) * e₀) ≠ 0 :=
    (map_ne_zero i).2 (mul_ne_zero hM₀ hsec.1)
  refine (secNorm_iff_chart he hw c hc').2 ⟨u₁ ^ rootSgn D r * u₀ * u, ?_, ?_⟩
  · rw [ha]
    convert CxVal.mul (CxVal.mul (CxVal.zpow hu₁ hu₁0 (rootSgn D r)) (hVal z _ _ hu₀)) hu using 1
    rw [map_div₀, map_zpow₀, div_zpow]
    generalize i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ A₀.a k) * e₀) = m at hm₀
    generalize (∏ k, y ⟨k, c k⟩ ^ a k) * e = n
    have hz : i t₀ ^ rootSgn D r ≠ 0 := zpow_ne_zero _ hit
    field_simp
  · rw [ha, eν]
    show (‖u₁‖ * ν₀) ^ rootSgn D r * (A₀.h (fun p => w (blkV bk bx p)) * T.h w) = _
    rw [mul_zpow, norm_mul, norm_mul, norm_zpow]
    linear_combination (‖u₁‖ ^ rootSgn D r * T.h w) * en₀ + (‖u₁‖ ^ rootSgn D r * ‖u₀‖) * eT

end GlobalTheory.CompanionTheory.Ar.Chg
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.RuleVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem ofAt_left (V : Type) [CommRing V] {G : Over (Sp V)} (f : epsOver V V ⟶ G) :
    (ofAt V ≫ f).left = f.left := Category.id_comp _

theorem toAt_left (V : Type) [CommRing V] {G : Over (Sp V)} (f : epsAt (𝟙 (Sp V)) ⟶ G) :
    (toAt V ≫ f).left = f.left := Category.id_comp _

theorem isIntFrame_of_basis (T : Formalism.L2.Pj.CDVR) (io : c.F →+* T.Fr) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr))
    {y' : Sp T.Fr ⟶ Xo.XF c} (m : SABMap t' Xo.univ.t (under y'))
    (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))) (τ' : E →+* ℂ) {N n : ℕ} (hn : N = n)
    (ub : Fin N → (epsOver T.V T.V ⟶ G.G)) (htan : ∀ i, IsTan (ub i))
    (heig : ∀ i, Formalism.L2.Pj.IsEigV c io G τ' (ub i))
    (hbas : ∀ w : epsOver T.V T.V ⟶ G.G, IsTan w → Formalism.L2.Pj.IsEigV c io G τ' w →
      ∃! a : Fin N → T.V, ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsComb ub a w)
    (v : Vecs y' n)
    (hv : ∀ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ t'.G.left, u' ≫ m.φ = (v i).left ∧
      u' ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ (ub (i.cast hn.symm)).left) :
    IsIntFrame m m2 (io.comp (tauIn c τ')) v := by
  subst hn
  obtain ⟨σV, hσ⟩ := exists_lift_int T (io.comp (tauIn c τ'))
  have hσa : ∀ a, algebraMap T.V T.Fr (σV a) = io (tauIn c τ' a) := fun a => RingHom.congr_fun hσ a
  have hinj := IsFractionRing.injective T.V T.Fr
  refine ⟨σV, fun i => ofAt T.V ≫ ub i, hσ, ⟨fun i => ⟨?_, fun a => ?_⟩, fun w hw => ?_⟩, fun a => ?_⟩
  · show _ ≫ (ofAt T.V ≫ ub i).left = _
    rw [ofAt_left, one_left_at]
    exact htan i
  · rw [Category.assoc, ofAt_left, ofAt_left]
    exact heig i a (σV a) (hσa a)
  · have htan' : IsTan (toAt T.V ≫ w) := by
      show _ ≫ (toAt T.V ≫ w).left = _
      rw [toAt_left, ← one_left_at]
      exact hw.1
    have heig' : Formalism.L2.Pj.IsEigV c io G τ' (toAt T.V ≫ w) := fun a z hz => by
      have hz' : z = σV a := hinj (hz.trans (hσa a).symm)
      subst hz'
      rw [Category.assoc, toAt_left, toAt_left]
      exact hw.2 a
    obtain ⟨a, ⟨u, hu1, hu2⟩, huniq⟩ := hbas _ htan' heig'
    refine ⟨a, ⟨fun i => ofAt T.V ≫ u i, fun i => ?_, ?_⟩, fun b hb => huniq b ?_⟩
    · rw [ofAt_left, ofAt_left]
      exact hu1 i
    · rw [← pre_prod, ← hu2, ← Category.assoc, ofAt_toAt, Category.id_comp]
    · obtain ⟨u', h1, h2⟩ := hb
      refine ⟨fun i => toAt T.V ≫ u' i, fun i => ?_, ?_⟩
      · rw [toAt_left, h1, ofAt_left]
        rfl
      · rw [← pre_prod, ← h2]
  · obtain ⟨u', h1, h2⟩ := hv a
    refine ⟨u', h1, ?_⟩
    rw [ofAt_left, h2]
    rfl

theorem exists_factor (f : Formalism.L2.Pj.Rul Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : Formalism.L2.Pj.FrPt Xo c S)
    (h : Formalism.L2.Pj.FromTest (K := c.F) (fun S _ _ => Formalism.L2.Pj.FrPt Xo c S)
      (fun φ y z => Formalism.L2.Pj.FrMap φ y z) y) :
    ∃ (p : Formalism.L2.Pj.TRing c.F) (ψ : p.R →ₐ[c.F] S) (z : Formalism.L2.Pj.FrPt Xo c p.R),
      Formalism.L2.Pj.FrMap ψ z y ∧ Formalism.L2.Pj.evR Xo c f y = ψ (f p z) :=
  ⟨_, _, _, h.choose_spec.choose_spec.choose_spec, by
    unfold Formalism.L2.Pj.evR Formalism.L2.Pj.evalAt
    rw [dite_eq_left h]⟩

theorem norm_le_one_iff_log_valuation (la : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F)) (a : c.F) (ha : a ≠ 0)
    {e : ℕ} (he : 0 < e) {ρ r : ℝ} (hρ : ρ < 0) (hr : 0 < r)
    (h : Real.log r = ((e : ℤ) * Formalism.L2.Pj.vLa la a : ℤ) * ρ) :
    la.valuation c.F a ≤ 1 ↔ r ≤ 1 := by
  have h0 : la.valuation c.F a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  have c1 : la.valuation c.F a ≤ 1 ↔ 0 ≤ Formalism.L2.Pj.vLa la a := by
    rw [← WithZero.log_le_log h0 one_ne_zero, WithZero.log_one, Formalism.L2.Pj.vLa]
    omega
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hc : 0 < (e : ℝ) * (-ρ) := mul_pos he' (neg_pos.2 hρ)
  have h' : Real.log r = ((e : ℝ) * (-ρ)) * (-(Formalism.L2.Pj.vLa la a : ℝ)) := by
    rw [h]; push_cast; ring
  rw [c1]
  constructor
  · intro hL
    have hL' : (0 : ℝ) ≤ Formalism.L2.Pj.vLa la a := by exact_mod_cast hL
    have : Real.log r ≤ 0 := by rw [h']; nlinarith [mul_nonneg hc.le hL']
    by_contra hgt
    have := Real.log_pos (not_le.1 hgt)
    linarith
  · intro hr1
    have hl : Real.log r ≤ 0 := Real.log_nonpos hr.le hr1
    by_contra hL
    have hL' : (Formalism.L2.Pj.vLa la a : ℝ) < 0 := by exact_mod_cast not_le.1 hL
    have := mul_pos hc (neg_pos.2 hL')
    linarith

end GlobalTheory.CompanionTheory.Ar.Flat.RuleVal

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

theorem GlobalTheory.CompanionTheory.Ar.Flat.nval_flat_rule : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (s : Formalism.L2.Pj.Rul Xo c) (t : ∀ p : Nat.Primes, (c.F →+* ℂ_[p]) → ℝ), τ (H.rt : E) = H.rt0 → IsLineFn U τ φ → (∀ (p : Formalism.L2.Pj.TRing c.F) (z : Formalism.L2.Pj.FrPt Xo c p.R) (F : Type) [Field F] (ψ : p.R →+* F) (y : Sp F ⟶ Xo.XF c), under y = spMap ψ ≫ z.x → y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F p.R)) → Set.range y ⊆ U → ∀ (v : Vecs y D.p) (w : Vecs y D.q) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q), (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm)) → (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) → ψ (s p z) = φ F y v w) → (∀ p κ, HasFinNorm U τ φ p κ (t p κ)) → ∀ (la : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F)) (T : Formalism.L2.Pj.CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : Formalism.L2.Pj.IntFr Xo c T io) (y' : Sp T.Fr ⟶ Xo.XF c), Formalism.L2.Pj.OverLa la T.V io e → y.IsAlg → under y' = (letI := io.toAlgebra; y.1.x) → y' ≫ pullback.snd _ _ = spMap io → Set.range y' ⊆ U → ∃ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), (∀ a : c.F, la.valuation c.F a ≤ 1 ↔ ‖κ a‖ ≤ 1) ∧ ∀ π : c.F, la.valuation c.F π = WithZero.exp (-1 : ℤ) → Formalism.L2.Pj.nval T.V e (Formalism.L2.Pj.evI y s) = ((t p κ / Real.log ‖κ π‖ : ℝ) : EReal) := by
  intro E _ _ _ H D l Xo c U τ φ s t hτ hφ hs hN la T io e y y' ho halg hy hyo hyU
  letI := io.toAlgebra
  obtain ⟨p, j, hj⟩ := RuleVal.exists_embed T halg
  obtain ⟨ρ, hρ, hlog⟩ := RuleVal.exists_log_norm T j hj
  have hI : Formalism.L2.Pj.Integral T io y.1 := y.2.2
  obtain ⟨G, t', m1, m2, ⟨ub, htan, heig, hbas, hlift⟩, -⟩ := hI
  obtain ⟨m, hm⟩ := RuleVal.exists_cast hy.symm m1
  have hp : D.mult τ = D.p := if_pos hτ
  have hq : D.mult (ComplexEmbedding.conjugate τ) = D.q := RuleVal.mult_conj τ hτ
  obtain ⟨v, hv⟩ := RuleVal.exists_vecs y.1 hy τ hp
  obtain ⟨w, hw⟩ := RuleVal.exists_vecs y.1 hy (ComplexEmbedding.conjugate τ) hq
  have hfr : IsFramed U τ io y' v w :=
    ⟨hyo, hyU, RuleVal.isEigFrame_of_frPt y.1 hy τ hp v hv, RuleVal.isEigFrame_of_frPt y.1 hy _ hq w hw⟩
  have hi1 : IsIntFrame m m2 (io.comp (tauIn c τ)) v :=
    RuleVal.isIntFrame_of_basis T io G t' m m2 τ hp (ub τ) (htan τ) (heig τ) (hbas τ) v fun i => by
      obtain ⟨u', h1, h2⟩ := hlift τ (i.cast hp.symm)
      exact ⟨u', by rw [hm, h1, hv], h2⟩
  have hi2 : IsIntFrame m m2 (io.comp (tauIn c (ComplexEmbedding.conjugate τ))) w :=
    RuleVal.isIntFrame_of_basis T io G t' m m2 _ hq (ub _) (htan _) (heig _) (hbas _) w fun i => by
      obtain ⟨u', h1, h2⟩ := hlift (ComplexEmbedding.conjugate τ) (i.cast hq.symm)
      exact ⟨u', by rw [hm, h1, hw], h2⟩
  have hval : Real.log ‖j (φ T.Fr y' v w)‖ = t p (j.comp io) :=
    hN p (j.comp io) T.V T.Fr j io y' v w G t' m m2 hj rfl hfr hi1 hi2
  have hev : Formalism.L2.Pj.evI y s = φ T.Fr y' v w := by
    obtain ⟨pz, ψ, z, hm', he⟩ := RuleVal.exists_factor s y.1 y.2.1
    have hcomp : ψ.toRingHom.comp (algebraMap c.F pz.R) = io := ψ.comp_algebraMap
    refine he.trans (hs pz z T.Fr ψ.toRingHom y' (hy.trans hm'.1) (by rw [hcomp]; exact hyo) hyU v w hp hq
      (fun i => (hv i).trans (hm'.2.1 τ _)) (fun i => (hw i).trans (hm'.2.1 _ _)))
  have hne : φ T.Fr y' v w ≠ 0 := hφ.ne T.Fr io y' v w hfr
  refine ⟨p, j.comp io, fun a => ?_, fun π hπ => ?_⟩
  · by_cases ha : a = 0
    · subst ha
      simp
    have hio : io a ≠ 0 := (map_ne_zero io).2 ha
    refine RuleVal.norm_le_one_iff_log_valuation la a ha ho.1 hρ (norm_pos_iff.2 ((map_ne_zero j).2 hio)) ?_
    rw [RingHom.comp_apply, hlog _ hio, ho.2 a]
  · have hπ0 : π ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hπ
      exact WithZero.exp_ne_zero hπ.symm
    have hio : io π ≠ 0 := (map_ne_zero io).2 hπ0
    have hvL : Formalism.L2.Pj.vLa la π = 1 := by
      rw [Formalism.L2.Pj.vLa, hπ, WithZero.log_exp]
      simp
    have he' : (e : ℝ) ≠ 0 := by exact_mod_cast ho.1.ne'
    have h1 : Real.log ‖(j.comp io) π‖ = (e : ℝ) * ρ := by
      rw [RingHom.comp_apply, hlog _ hio, ho.2 π, hvL]
      simp
    rw [hev, Formalism.L2.Pj.nval_of_ne hne, ← hval, h1, hlog _ hne]
    congr 1
    field_simp [hρ.ne]
end
end
