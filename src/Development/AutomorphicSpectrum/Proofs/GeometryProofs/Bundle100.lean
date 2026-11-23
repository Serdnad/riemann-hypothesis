module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle015
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle021
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Module.Connected
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

theorem isCptGen_comp_of_flat_preimmersion {A X : Scheme.{0}} (j : A ⟶ X) [IsPreimmersion j] [Flat j]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) (w : A) (hw : ∀ y : A, y ⤳ w → y = w) :
    IsCptGen (Ω := A.residueField w) (A.fromSpecResidueField w ≫ j) := by
  have e : genPt (Ω := A.residueField w) (A.fromSpecResidueField w ≫ j) = j w :=
    congrArg j (A.fromSpecResidueField_apply w _)
  refine isCptGen_of_maximal_of_surjective hX _ ?_ ?_
  · rw [e]
    intro y hy
    obtain ⟨a, ha, rfl⟩ := AlgebraicGeometry.Flat.generalizingMap j hy
    rw [hw a ha]
  · unfold Scheme.stalkClosedPointTo
    rw [CommRingCat.hom_comp, RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso _).hom).2.comp
      ((A.fromSpecResidueField w ≫ j).stalkMap_surjective _)

theorem eq_genericPoint_of_specializes {A : Type*} [TopologicalSpace A] [T0Space A] {U : Set A}
    (hU : U ∈ irreducibleComponents A) {w : A} (hw : IsGenericPoint w U) (y : A) (hy : y ⤳ w) : y = w := by
  have h1 : U ⊆ closure {y} := by
    rw [← hw.def]
    exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hy)) isClosed_closure
  have h2 : closure {y} ⊆ U := hU.2 isIrreducible_singleton.closure h1
  have h3 : w ⤳ y := hw.specializes (h2 (subset_closure rfl))
  exact (hy.antisymm h3).eq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem nonempty_cptOver_of_flat_preimmersion {O : Type} [CommRing O] {β : O →+* c.F} [IsPreimmersion (spMap β)]
    [Flat (spMap β)] (Y : Model Xo c β) (U : Set (Xo.XF c)) (hU : U ∈ irreducibleComponents (Xo.XF c)) :
    Nonempty (CptOver Y U) := by
  have := Y.jQ_open
  have : IsPreimmersion Y.j := by unfold Model.j; infer_instance
  have : Flat Y.j := by unfold Model.j; infer_instance
  obtain ⟨w, hw⟩ := QuasiSober.sober hU.1 (isClosed_of_mem_irreducibleComponents U hU)
  let Ω : Type := (Xo.XF c).residueField w
  let ξ₀ : Sp Ω ⟶ Xo.XF c := (Xo.XF c).fromSpecResidueField w
  have e : genPt ξ₀ = w := (Xo.XF c).fromSpecResidueField_apply w _
  obtain ⟨V, _, _, ⟨M⟩⟩ := lieModel_exists Y.X Y.t.G Ω (ξ₀ ≫ Y.j)
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act Y.X Y.t.G Ω (ξ₀ ≫ Y.j) V M (𝓞 E) Y.t.act.act
    Y.t.act.hom Y.t.act.one Y.t.act.mul Y.t.act.add
  exact ⟨{
    Ω := Ω
    ξ₀ := ξ₀
    inc := (Spec.preimage (ξ₀ ≫ pullback.snd _ _)).hom
    over_inc := (Spec.map_preimage _).symm
    gen := isCptGen_comp_of_flat_preimmersion Y.j (fun x => (Y.normal x).1) w
      (eq_genericPoint_of_specializes hU hw)
    closure := fun u => by rw [e]; exact hw.specializes_iff_mem.symm
    V := V
    M := M
    ρ := ρ
    act := hρ }⟩

theorem nonempty_cptOver_of_fraction {O : Type} [CommRing O] {β : O →+* c.F} (hβ : Function.Injective β)
    (hfr : ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) (Y : Model Xo c β) (U : Set (Xo.XF c))
    (hU : U ∈ irreducibleComponents (Xo.XF c)) : Nonempty (CptOver Y U) := by
  letI : Algebra O c.F := β.toAlgebra
  haveI : IsDomain O := hβ.isDomain β
  haveI : FaithfulSMul O c.F := (faithfulSMul_iff_algebraMap_injective O c.F).2 hβ
  haveI : IsFractionRing O c.F := IsFractionRing.of_field O c.F fun x => by
    obtain ⟨a, b, hb, h⟩ := hfr x
    exact ⟨a, b, (eq_div_iff hb).2 h⟩
  haveI : IsPreimmersion (spMap β) := IsPreimmersion.of_isLocalization (nonZeroDivisors O)
  haveI : Flat (spMap β) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact IsLocalization.flat c.F (nonZeroDivisors O)
  exact nonempty_cptOver_of_flat_preimmersion Y U hU

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FramesEig

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open LieTangent

section Germ

variable {X : Scheme.{0}} {O : Type} [CommRing O]

def germ (s : X ⟶ Sp O) (p : X) : O →+* X.presheaf.stalk p :=
  (Spec.preimage (X.fromSpecStalk p ≫ s)).hom

theorem spec_germ (s : X ⟶ Sp O) (p : X) :
    Spec.map (CommRingCat.ofHom (germ s p)) = X.fromSpecStalk p ≫ s := by
  simp only [germ, CommRingCat.ofHom_hom, Spec.map_preimage]

theorem map_germ (s : X ⟶ Sp O) (p : X) {K : Type} [CommRing K] (φ : X.presheaf.stalk p →+* K) (i : O →+* K)
    (h : Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk p ≫ s = spMap i) (n : O) :
    φ (germ s p n) = i n := by
  have h3 : Spec.map (CommRingCat.ofHom (φ.comp (germ s p))) = Spec.map (CommRingCat.ofHom i) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, spec_germ]
    exact h
  have h4 := Spec.map_injective h3
  exact congrArg (fun g => g.hom n) h4

end Germ

section Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {V : Type} [AddCommGroup V] [Module Ω V]

theorem valAt_comp (M : LieModel G ξ V) {R : Type} [CommRing R] [IsLocalRing R]
    {z : Spec (CommRingCat.of R) ⟶ X} (f : G ⟶ G) [IsMonHom f] {e e' : V} (he : M.pt e' = M.pt e ≫ f)
    {w : epsAt z ⟶ G} (h : M.ValAt z e w) : M.ValAt z e' (w ≫ f) := by
  obtain ⟨h1, v, hv, hw⟩ := h
  refine ⟨h1, v ≫ f, ⟨?_, ?_⟩, ?_⟩
  · have ht := (isTanAt_iff v).1 hv.1
    rw [isTanAt_iff, ← Category.assoc, ht, one_comp]
  · change (M.pt e').left = _
    rw [he]
    change (M.pt e).left ≫ f.left = _
    rw [hv.2, Category.assoc]
    rfl
  · change w.left ≫ f.left = _
    rw [hw, Category.assoc]
    rfl

end Val

theorem mem_eigSp_of_valAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (σ : c.F →+* ℂ) (y : Sp ℂ ⟶ Xo.XF c) (EC : Type) [AddCommGroup EC] [Module ℂ EC] (N : LieModel Y.t.G (y ≫ Y.j) EC) (ρ : 𝓞 E →+* Module.End ℂ EC) (t : 𝓞 E →+* c.F) (e : Z.V) (w : EC), (∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → y ≫ pullback.snd _ _ = spMap σ → N.IsActOf Y.t.act.act ρ → e ∈ eigSp Z.ρ (Z.inc.comp t) → Z.M.ValAt (y ≫ Y.j) e (N.pt w) → w ∈ eigSp ρ (σ.comp t) := by
  intro E _ _ _ H D l Xo c O _ β Y U Z σ y EC _ _ N ρ t e w hfr hy hN he hv
  have mem : ∀ {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (r : 𝓞 E →+* Module.End R V)
      (τ : 𝓞 E →+* R) (u : V), u ∈ eigSp r τ ↔ ∀ a, r a u = τ a • u := by
    intro R V _ _ _ r τ u
    simp [eigSp, Submodule.mem_iInf, sub_eq_zero]
  rw [mem] at he ⊢
  have h1 : Y.j ≫ Y.s = pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ spMap β := by
    show (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
  have hh := hv
  obtain ⟨h0, -⟩ := hh
  have hgen : ∀ n, genMap (Z.ξ₀ ≫ Y.j) ⟨centre (y ≫ Y.j), h0⟩ (germ Y.s (centre (y ≫ Y.j)) n) = Z.inc (β n) := by
    intro n
    refine map_germ Y.s _ _ (Z.inc.comp β) ?_ n
    rw [← Category.assoc, spec_genMap, Category.assoc, h1, ← Category.assoc, Z.over_inc]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hcl : ∀ n, (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom (germ Y.s (centre (y ≫ Y.j)) n) = σ (β n) := by
    intro n
    refine map_germ Y.s _ _ (σ.comp β) ?_ n
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Y.s) (spec_centre (y ≫ Y.j))).trans ?_)
    change (y ≫ Y.j) ≫ Y.s = _
    rw [Category.assoc, h1, ← Category.assoc, hy]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  intro a
  obtain ⟨n, d, hd, hnd⟩ := hfr (t a)
  have hva : Z.M.ValAt (y ≫ Y.j) (Z.ρ a e) (N.pt (ρ a w)) := by
    have := Y.t.act.hom a
    rw [hN a w]
    exact valAt_comp Z.M (Y.t.act.act a) (Z.act a e) hv
  have v1 := hva.smul h0 (germ Y.s (centre (y ≫ Y.j)) d)
  have v2 := hv.smul h0 (germ Y.s (centre (y ≫ Y.j)) n)
  rw [hgen, hcl, ← LieModel.pt_smul] at v1 v2
  have e1 : Z.inc (β d) • Z.ρ a e = Z.inc (β n) • e := by
    rw [he a, smul_smul, ← hnd]
    simp [mul_comm]
  rw [e1] at v1
  have e2 := N.inj (v1.unique Z.gen v2)
  rw [← hnd, map_mul, mul_comm, mul_smul] at e2
  have hσ : σ (β d) ≠ 0 := (map_ne_zero σ).2 hd
  exact smul_right_injective EC hσ e2

end GlobalTheory.CompanionTheory.Ar.FramesEig
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.PunctShape

def factor (a : ℕ) (ρ : ℝ) (n : ℕ) (i : Fin n) : Set ℂ := {w | ‖w‖ < ρ ∧ (i.val < a → w ≠ 0)}

theorem punct_eq_pi (n a : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    punct n a ρ = Set.pi Set.univ (factor a ρ n) := by
  ext z
  simp only [punct, factor, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies,
    mem_ball_zero_iff, pi_norm_lt_iff hρ]
  constructor
  · rintro ⟨h1, h2⟩ i
    exact ⟨h1 i, h2 i⟩
  · intro h
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩

theorem isOpen_factor (n a : ℕ) (ρ : ℝ) (i : Fin n) : IsOpen (factor a ρ n i) := by
  by_cases h : i.val < a
  · have he : factor a ρ n i = Metric.ball 0 ρ ∩ {0}ᶜ := by
      ext w
      simp [factor, h]
    rw [he]
    exact isOpen_ball.inter isOpen_compl_singleton
  · have he : factor a ρ n i = Metric.ball 0 ρ := by
      ext w
      simp [factor, h]
    rw [he]
    exact isOpen_ball

theorem isConnected_factor (n a : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (i : Fin n) :
    IsConnected (factor a ρ n i) := by
  by_cases h : i.val < a
  · have he : factor a ρ n i =
        (fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (p.2 * Complex.I)) '' (Set.Ioo 0 ρ ×ˢ Set.univ) := by
      ext w
      simp only [factor, h, true_implies, Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod,
        Set.mem_Ioo, Set.mem_univ, and_true, Prod.exists]
      constructor
      · rintro ⟨hw, hw0⟩
        exact ⟨‖w‖, Complex.arg w, ⟨norm_pos_iff.mpr hw0, hw⟩, Complex.norm_mul_exp_arg_mul_I w⟩
      · rintro ⟨r, θ, ⟨hr0, hrρ⟩, rfl⟩
        have hn : ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ = r := by
          rw [norm_mul, Complex.norm_exp_ofReal_mul_I, _root_.mul_one, Complex.norm_real,
            Real.norm_of_nonneg hr0.le]
        refine ⟨by rw [hn]; exact hrρ, ?_⟩
        exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hr0.ne') (Complex.exp_ne_zero _)
    rw [he]
    exact ((isConnected_Ioo hρ).prod isConnected_univ).image _ (by fun_prop)
  · have he : factor a ρ n i = Metric.ball 0 ρ := by
      ext w
      simp [factor, h]
    rw [he]
    exact isConnected_ball hρ

theorem punct_open_connected_nonempty : ∀ (n a : ℕ) (ρ : ℝ), 0 < ρ → IsOpen (punct n a ρ) ∧ IsPreconnected (punct n a ρ) ∧ (punct n a ρ).Nonempty := by
  intro n a ρ hρ
  rw [punct_eq_pi n a ρ hρ]
  exact ⟨isOpen_set_pi Set.finite_univ fun i _ => isOpen_factor n a ρ i,
    isPreconnected_univ_pi fun i => (isConnected_factor n a ρ hρ i).isPreconnected,
    Set.univ_pi_nonempty_iff.mpr fun i => (isConnected_factor n a ρ hρ i).nonempty⟩

end GlobalTheory.CompanionTheory.Ar.Flat.PunctShape
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def PolarisedAt {X : Scheme.{0}} (t : SAB H X) (z : Spec (CommRingCat.of ℂ) ⟶ X) : Prop :=
  ∃ (t' : SAB H (Sp ℂ)) (_ : SABMap t' t z), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
  [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}


open Classical in
def gramFn (𝔐 : HodgeCpt Y S y) {r : ℕ} (b : Fin r → 𝔐.Li) (w : (Σ k, J k) → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  if h : ∃ (Γ : Matrix (Fin r) (Fin r) ℂ) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X),
      CoordsAt 𝔐.ξ y z w ∧ 𝔐.Interior z ∧ 𝔐.M.GramAt 𝔐.t.PP.L z b Γ then h.choose else 0

def recentre {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (u : Fin n → ℂ) : Fin n → ℂ :=
  t₀ + (ρ : ℂ) • (u ∘ π)

def uncentre {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (t : Fin n → ℂ) : Fin n → ℂ :=
  fun i => (ρ : ℂ)⁻¹ * (t (π.symm i) - t₀ (π.symm i))

def periodGram {n a₀ g r : ℕ} {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a₀ g Λ)
    (U : Fin r → (Fin n → ℂ) → Fin g → ℂ) (u : Fin n → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i j => Real.pi * (U j u ⬝ᵥ L.H u *ᵥ star (U i u))

def IsFramePeriods (𝔐 : HodgeCpt Y S y) {r : ℕ} (b : Fin r → 𝔐.Li) {P : Ideal (MRing J)} {n : ℕ}
    {Bd : Set ((Σ k, J k) → ℂ)} (χ : SncChart P n Bd) (t₀ : Fin n → ℂ) (cc : (k : K) → J k) (f : Ω) {a₀ g : ℕ}
    {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a₀ g Λ) (π : Equiv.Perm (Fin n)) (ρ : ℝ)
    (U : Fin r → (Fin n → ℂ) → Fin g → ℂ) : Prop :=
  0 < ρ ∧ ρ ≤ 1 ∧ (∀ k, DifferentiableOn ℂ (U k) (Metric.ball 0 1)) ∧ LinearIndependent ℂ (fun k => U k 0) ∧
  (∀ i : Fin n, (i : ℕ) < a₀ → ((π.symm i : Fin n) : ℕ) < χ.a ∧ t₀ (π.symm i) = 0) ∧
  ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, recentre t₀ ρ π u ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧
    InFrameDomain y cc f (χ.γ (recentre t₀ ρ π u)) ∧ (χ.γ (recentre t₀ ρ π u) ∉ Bd ↔ u ∈ Flat.punct n a₀ 1) ∧
    (u ∈ Flat.punct n a₀ 1 → ∀ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (χ.γ (recentre t₀ ρ π u)) →
      𝔐.M.GramAt 𝔐.t.PP.L z b (periodGram L U u))

theorem recentre_uncentre {n : ℕ} (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n)) (t : Fin n → ℂ) :
    recentre t₀ ρ π (uncentre t₀ ρ π t) = t := by
  have h : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  funext i
  simp [recentre, uncentre, h]

theorem isOpen_punct (n a : ℕ) (ρ : ℝ) : IsOpen (Flat.punct n a ρ) := by
  have : Flat.punct n a ρ = Metric.ball 0 ρ ∩ ⋂ i : Fin n, {z : Fin n → ℂ | i.val < a → z i ≠ 0} := by
    ext z; simp [Flat.punct]
  rw [this]
  refine Metric.isOpen_ball.inter (isOpen_iInter_of_finite fun i => ?_)
  by_cases h : i.val < a
  · simpa [h] using isOpen_ne_fun (continuous_apply i) continuous_const
  · simp [h]

theorem contDiff_uncentre {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (uncentre t₀ ρ π) := by
  unfold uncentre
  exact contDiff_pi.2 fun i => contDiff_const.mul ((contDiff_apply ℝ (fun _ => ℂ) (π.symm i)).sub contDiff_const)

theorem uncentre_mem_ball {n : ℕ} {t₀ t : Fin n → ℂ} {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n))
    (h : ‖t - t₀‖ < ρ) : uncentre t₀ ρ π t ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
  rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
  intro i
  have h1 : ‖t (π.symm i) - t₀ (π.symm i)‖ ≤ ‖t - t₀‖ := norm_le_pi_norm (t - t₀) (π.symm i)
  simp only [uncentre, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hρ.le]
  rw [inv_mul_lt_iff₀ hρ]
  linarith

theorem uncentre_self {n : ℕ} (t : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) : uncentre t ρ π t = 0 := by
  funext i
  simp [uncentre]

theorem recentre_zero {n : ℕ} (t : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) : recentre t ρ π 0 = t := by
  funext i
  simp [recentre]

end GlobalTheory.CompanionTheory.Ar.HodgeMetric
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.Conj

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.Regular

section Polydisc

variable {n a : ℕ}

theorem norm_star_vec (z : Fin n → ℂ) : ‖star z‖ = ‖z‖ := by
  simp only [Pi.norm_def, Pi.star_apply]
  congr 1
  refine Finset.sup_congr rfl fun i _ => ?_
  simp [nnnorm_star]

theorem star_mem_ball {ρ : ℝ} {z : Fin n → ℂ} :
    star z ∈ Metric.ball (0 : Fin n → ℂ) ρ ↔ z ∈ Metric.ball (0 : Fin n → ℂ) ρ := by
  simp only [mem_ball_zero_iff, norm_star_vec]

theorem star_mem_punct {ρ : ℝ} {z : Fin n → ℂ} : star z ∈ punct n a ρ ↔ z ∈ punct n a ρ := by
  simp only [punct, Set.mem_setOf_eq, star_mem_ball, Pi.star_apply, ne_eq, star_eq_zero]

theorem star_mem_logCover (h : a ≤ n) {w : Fin n → ℂ} : star w ∈ logCover h ↔ w ∈ logCover h := by
  simp only [logCover, Set.mem_setOf_eq, Pi.star_apply, Complex.star_def, Complex.conj_re,
    RCLike.norm_conj, Complex.norm_conj]

theorem star_expCover (w : Fin n → ℂ) : star (expCover a w) = expCover a (star w) := by
  funext k
  simp only [expCover, Pi.star_apply]
  split_ifs
  · simp [Complex.exp_conj]
  · rfl

theorem star_real_smul (ρ : ℝ) (z : Fin n → ℂ) : star ((ρ : ℂ) • z) = (ρ : ℂ) • star z := by
  funext k
  simp

theorem differentiableOn_star_star {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [StarAddMonoid F]
    [StarModule ℂ F] [ContinuousStar F] {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [StarAddMonoid V]
    [StarModule ℂ V] [ContinuousStar V] {f : V → F} {B : Set V} (hB : IsOpen B) (hs : ∀ z, star z ∈ B ↔ z ∈ B)
    (hf : DifferentiableOn ℂ f B) : DifferentiableOn ℂ (fun z => star (f (star z))) B := by
  intro z hz
  have h1 : DifferentiableAt ℂ f (star z) := hf.differentiableAt (hB.mem_nhds ((hs z).2 hz))
  have h2 := h1.star_star
  rw [star_star] at h2
  exact h2.differentiableWithinAt

end Polydisc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

def conjPts {R : Type} [CommRing R] {n : ℕ} (ψ : (Fin n → ℂ) → (R →+* ℂ)) (z : Fin n → ℂ) : R →+* ℂ :=
  (starRingEnd ℂ).comp (ψ (star z))

theorem isHolPts_conjPts {R : Type} [CommRing R] {n : ℕ} {ψ : (Fin n → ℂ) → (R →+* ℂ)} {ρ : ℝ}
    (h : IsHolPts (Metric.ball 0 ρ) ψ) : IsHolPts (Metric.ball 0 ρ) (conjPts ψ) :=
  ⟨Metric.isOpen_ball, fun r => differentiableOn_star_star (f := fun b => ψ b r) Metric.isOpen_ball
    (fun _ => star_mem_ball) (h.2 r)⟩

def chart {Xo : Moduli D l} {σ : KA l →+* ℂ} {n a : ℕ} (C : BdryChart Xo σ n a) :
    BdryChart Xo ((starRingEnd ℂ).comp σ) n a where
  a_le := C.a_le
  R := C.R
  t := C.t
  g := C.g
  dim := C.dim
  M := C.M
  ψ := conjPts C.ψ
  hol := isHolPts_conjPts C.hol
  V := C.V
  j := C.j
  j_open := C.j_open
  k := C.k
  tV := C.tV
  m₁ := C.m₁
  m₂ := C.m₂
  pt z := spMap (starRingEnd ℂ) ≫ C.pt (star z)
  pt_eq z hz := by
    obtain ⟨h1, h2⟩ := C.pt_eq (star z) (star_mem_punct.2 hz)
    constructor
    · rw [Category.assoc, h1]
      exact (Spec.map_comp _ _).symm
    · rw [Category.assoc, h2]
      exact (Spec.map_comp _ _).symm

end GlobalTheory.CompanionTheory.Ar.Flat.Conj
end
end
