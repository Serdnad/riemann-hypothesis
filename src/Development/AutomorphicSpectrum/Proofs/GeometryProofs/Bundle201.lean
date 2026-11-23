module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle073
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle195
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle055
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle021
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle027
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle196
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle150
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdjointRelationGeneratorCorr
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NonemptyEquivOfCardHom
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDualToInvariantDifferentials
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFamilyExponentialLocally
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.QuotientUniformizationCharts
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.exists_family_exponential_locally : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)), Smooth G.hom → IsHolPts B ψ → ∀ b₀ ∈ B, ∃ ε : ℝ, 0 < ε ∧ ball b₀ ε ⊆ B ∧ Nonempty (FamExp G M (ball b₀ ε) ψ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_famExp_near | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_famExp_near | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_famExp_near <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

open GlobalTheory.CompanionTheory.Ar.LieTangent GlobalTheory.CompanionTheory.Ar.LieVB

section Frame

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {V : Type} [AddCommGroup V]
  [Module Ω V] {K : Type} [Field K]

theorem valAt_of_isDiffOf {M : LieModel G ξ V} {z : Sp K ⟶ X} (f : G ⟶ G) [IsMonHom f] (A : V →ₗ[Ω] V)
    (hf : M.IsDiffOf f A) {e : V} {w : epsAt z ⟶ G} (h : M.ValAt z e w) : M.ValAt z (A e) (w ≫ f) := by
  obtain ⟨hs, v, hv, hw⟩ := h
  refine ⟨hs, v ≫ f, ⟨?_, ?_⟩, ?_⟩
  · change _ ≫ (v ≫ f).left = _
    rw [Over.comp_left, ← Category.assoc, hv.1]
    exact congrArg Over.Hom.left (one_comp f)
  · change (M.pt (A e)).left = _
    rw [hf e, Over.comp_left, hv.2, Over.comp_left, Category.assoc]
  · change (w ≫ f).left = _
    rw [Over.comp_left, hw, Over.comp_left, Category.assoc]

theorem exists_model_of_frame [IsCommMonObj G] [Smooth G.hom] (hξ : IsCptGen ξ) (M : LieModel G ξ V) (z : Sp K ⟶ X)
    (h : genPt ξ ⤳ centre z) (ψ : regAt ξ ⟨_, h⟩ →+* K) (hψ : ∀ a : regAt ξ ⟨_, h⟩, ValAt ξ z (a : Ω) (ψ a)) {g : ℕ}
    (ℓ : Fin g → V) (hℓ : M.lat.IsFrameAt ℓ ⟨_, h⟩) :
    ∃ MY : LieModel G z (Fin g → K), ∀ x : Fin g → regAt ξ ⟨_, h⟩,
      M.ValAt z (comb ℓ x) (MY.pt fun i => ψ (x i)) := by
  obtain ⟨F, _, _, ⟨MF⟩⟩ := lieModel_exists X G K z
  obtain ⟨ev, hev, hsm, hsp⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X G Ω ξ V M K z h F MF hξ inferInstance
  have hmem : ∀ i, ℓ i ∈ M.lat ⟨_, h⟩ := fun i => by
    rw [hℓ.2]
    exact Submodule.subset_span ⟨i, rfl⟩
  let u : Fin g → F := fun i => ev ⟨ℓ i, hmem i⟩
  have hcomb : ∀ x : Fin g → regAt ξ ⟨_, h⟩, comb ℓ x ∈ M.lat ⟨_, h⟩ := fun x =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (x i) (hmem i)
  have hevc : ∀ x : Fin g → regAt ξ ⟨_, h⟩, ev ⟨comb ℓ x, hcomb x⟩ = ∑ i, ψ (x i) • u i := by
    intro x
    have e1 : (⟨comb ℓ x, hcomb x⟩ : M.lat ⟨_, h⟩) = ∑ i, x i • (⟨ℓ i, hmem i⟩ : M.lat ⟨_, h⟩) := by
      apply Subtype.ext
      simp [comb]
      rfl

    rw [e1, map_sum]
    exact Finset.sum_congr rfl fun i _ => hsm (x i) (ψ (x i)) _ (hψ (x i))
  have hle : ⊤ ≤ Submodule.span K (Set.range u) := by
    have hr : Set.range ev ⊆ (Submodule.span K (Set.range u) : Set F) := by
      rintro _ ⟨⟨e, he⟩, rfl⟩
      have he' := he
      rw [hℓ.2, Submodule.mem_span_range_iff_exists_fun] at he'
      obtain ⟨x, rfl⟩ := he'
      have e2 : (∑ i, x i • ℓ i) = comb ℓ x := rfl
      simp only [e2]
      rw [hevc x]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    rw [← hsp]
    exact Submodule.span_le.2 hr
  have hcard : Fintype.card (Fin g) = Module.finrank K F := by
    obtain ⟨_, hU, b', hb'sp, hb'⟩ := (lieLat_isVB_of_smooth X Ω ξ G V M hξ inferInstance).1 ⟨_, h⟩ trivial
    have hfr := hb' ⟨_, h⟩ trivial hU
    have htop : Submodule.span Ω (Set.range ℓ) = ⊤ := by
      rw [eq_top_iff, ← hb'sp, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have h3 : b' i ∈ M.lat ⟨_, h⟩ := by
        rw [hfr.2]
        exact Submodule.subset_span ⟨i, rfl⟩
      rw [hℓ.2, Submodule.mem_span_range_iff_exists_fun] at h3
      obtain ⟨x, hx⟩ := h3
      rw [← hx]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hg : Module.finrank Ω V = g := by
      rw [← finrank_top, ← htop, finrank_span_eq_card hℓ.1, Fintype.card_fin]
    obtain ⟨R', _, x, hx, F', _, _, MR, n, b, hp⟩ := exists_chart G (centre z)
    have hgen : genPt ξ ∈ x.opensRange := h.mem_open x.opensRange.isOpen hp
    obtain ⟨φ, hφ⟩ := exists_lift x ξ hgen
    obtain ⟨a, ha⟩ := exists_lift x z hp
    obtain ⟨β, B, -, -⟩ := basis_tr a x z ha MR MF b
    obtain ⟨c, hli, hsp', -⟩ := frame_of_basis x MR b ξ M φ hφ
    have hn : n = Module.finrank Ω V := by
      rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp'.ge), Fintype.card_fin]
    rw [Module.finrank_eq_card_basis B, Fintype.card_fin, Fintype.card_fin]
    omega
  let bb : Module.Basis (Fin g) K F := basisOfTopLeSpanOfCardEqFinrank u hle hcard
  refine ⟨lieModelOfEquiv MF bb.equivFun.symm, fun x => ?_⟩
  have e3 : bb.equivFun.symm (fun i => ψ (x i)) = ev ⟨comb ℓ x, hcomb x⟩ := by
    rw [hevc, Module.Basis.equivFun_symm_apply]
    exact Finset.sum_congr rfl fun i _ => by simp [bb]
  change M.ValAt z (comb ℓ x) (MF.pt (bb.equivFun.symm fun i => ψ (x i)))
  rw [e3]
  exact (hev _ _).2 ⟨hcomb x, rfl⟩

theorem isActOf_of_frame {E : Type} [Field E] [NumberField E] (hξ : IsCptGen ξ) {M : LieModel G ξ V} {z : Sp K ⟶ X}
    {h : genPt ξ ⤳ centre z} {ψ : regAt ξ ⟨_, h⟩ →+* K} {g : ℕ} {ℓ : Fin g → V}
    (hℓ : M.lat.IsFrameAt ℓ ⟨_, h⟩) (act : OAct (𝓞 E) G) {ρ : 𝓞 E →+* Module.End Ω V}
    (hact : M.IsActOf act.act ρ) {ρK : 𝓞 E →+* Module.End K (Fin g → K)} (hT : Tied ℓ ψ ρ ρK)
    {MY : LieModel G z (Fin g → K)}
    (hY : ∀ x : Fin g → regAt ξ ⟨_, h⟩, M.ValAt z (comb ℓ x) (MY.pt fun i => ψ (x i))) :
    MY.IsActOf act.act ρK := by
  obtain ⟨ρ', hρ', -⟩ := lieModel_exists_unique_act _ G K z _ MY (𝓞 E) act.act act.hom act.one act.mul act.add
  suffices hq : ρ' = ρK from hq ▸ hρ'
  refine RingHom.ext fun a => (Pi.basisFun K (Fin g)).ext fun i => ?_
  let x : Fin g → regAt ξ ⟨_, h⟩ := Pi.single i 1
  have hx : (fun j => ψ (x j)) = Pi.basisFun K (Fin g) i := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [x]
    · simp [x, hj]
  have hmem : ρ a (comb ℓ x) ∈ M.lat ⟨_, h⟩ := by
    refine GlobalTheory.T.lie_lattice_stable_under_action X Ω ξ G V M (𝓞 E) act ρ hact ⟨_, h⟩ a _ ?_
    rw [hℓ.2]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [hℓ.2, Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨x', hx'⟩ := hmem
  have hc : comb ℓ x' = ρ a (comb ℓ x) := hx'
  have := act.hom a
  have h1 : M.ValAt z (ρ a (comb ℓ x)) (MY.pt (fun j => ψ (x j)) ≫ act.act a) :=
    valAt_of_isDiffOf (act.act a) (ρ a) (hact a) (hY x)
  have h2 := hY x'
  rw [hc] at h2
  have h3 := h2.unique hξ h1
  rw [← hρ' a] at h3
  have h4 := MY.inj h3
  rw [← hx, ← h4]
  exact (hT a x x' hc.symm).symm

end Frame

theorem tangent_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (K : Type) [Field K] (y : Sp K ⟶ Xo.XF c) (h₁ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j))
    (ψ : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ →+* K) (g : ℕ) (ℓ : Fin g → Z.V) (ρK : 𝓞 E →+* Module.End K (Fin g → K)),
    (∀ a : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (a : Z.Ω) (ψ a)) → Z.M.lat.IsFrameAt ℓ ⟨_, h₁⟩ → Tied ℓ ψ Z.ρ ρK →
    ∃ (MU : LieModel Xo.univ.t.G (under y) (Fin g → K)) (MY : LieModel Y.t.G (y ≫ Y.j) (Fin g → K)),
      (∀ e, SameVec Y y (MU.pt e) (MY.pt e)) ∧
      (∀ x : Fin g → regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, Z.M.ValAt (y ≫ Y.j) (comb ℓ x) (MY.pt (fun i => ψ (x i)))) ∧
      MU.IsActOf Xo.univ.t.act.act ρK ∧ MY.IsActOf Y.t.act.act ρK := by
  intro E _ _ _ H D l Xo c O _ _ _ β Y U Z K _ y h₁ ψ g ℓ ρK hψ hℓ hT
  have : Smooth Y.t.G.hom := Y.t.semi.smooth
  obtain ⟨MY, hMY⟩ := exists_model_of_frame Z.gen Z.M (y ≫ Y.j) h₁ ψ hψ ℓ hℓ
  have hY : MY.IsActOf Y.t.act.act ρK := isActOf_of_frame Z.gen hℓ Y.t.act Z.act hT hMY
  have hp : IsGrpPullback Y.oF.t.G Xo.univ.t.G (pullback.fst _ _) Y.m0.toSABMap.φ := Y.m0.cart
  have hq : IsGrpPullback Y.oF.t.G Y.t.G Y.j Y.m.φ := Y.m.cart
  obtain ⟨Mo, hMo⟩ := (LiePull.lieModel_pullback _ _ Y.t.G Y.oF.t.G Y.j Y.m.φ hq K y (Fin g → K)).1 MY
  obtain ⟨MU, hMU⟩ := (LiePull.lieModel_pullback _ _ Xo.univ.t.G Y.oF.t.G (pullback.fst _ _) Y.m0.toSABMap.φ hp
    K y (Fin g → K)).2 Mo
  have hMoAct : ∀ (a : 𝓞 E) (e : Fin g → K), Mo.pt (ρK a e) = Mo.pt e ≫ Y.oF.t.act.act a := by
    intro a e
    apply Over.OverMorphism.ext
    apply hq.1.hom_ext
    · rw [hMo, hY a e, Over.comp_left, Over.comp_left, Category.assoc, Y.m.act, ← Category.assoc, hMo]
    · rw [Over.w, Over.comp_left, Category.assoc, Over.w, Over.w]
  refine ⟨MU, MY, fun e => ⟨(Mo.pt e).left, Over.w (Mo.pt e), hMU e, hMo e⟩, hMY, fun a e => ?_, hY⟩
  apply Over.OverMorphism.ext
  rw [← hMU, hMoAct a e, Over.comp_left, Over.comp_left, Category.assoc, Y.m0.act, ← Category.assoc, hMU]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
open MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GMove

section Ring

variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T]

theorem dualMap_algebraMap (f : R →+* S) :
    (dualMap f).comp (algebraMap R (DualNumber R)) = (algebraMap S (DualNumber S)).comp f := by
  ext x <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fstHom_dualMap (f : R →+* S) :
    (TrivSqZeroExt.fstHom S S S).toRingHom.comp (dualMap f) = f.comp (TrivSqZeroExt.fstHom R R R).toRingHom :=
  RingHom.ext fun x => by simp [dualMap]

theorem dualMap_comp (f : R →+* S) (g : S →+* T) : dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  ext x <;> simp [dualMap]

theorem specMap_comp (f : R →+* S) (g : S →+* T) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom (g.comp f)) := by
  rw [← Spec.map_comp]; rfl

end Ring

section Scheme

variable {X X' : Scheme.{0}} {Ω : Type} [Field Ω]

theorem specializes_of_iso (e : X' ≅ X) {a b : X'} (h : e.hom a ⤳ e.hom b) : a ⤳ b := by
  have := h.map e.inv.continuous
  simpa using this

theorem genMap_stalkMap_eq (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (g : X' ⟶ X) (q : Cpt ξ')
    (h : genPt (ξ' ≫ g) ⤳ g q.1) (s : X.presheaf.stalk (g q.1)) :
    genMap ξ' q ((g.stalkMap q.1).hom s) = genMap (ξ' ≫ g) ⟨g q.1, h⟩ s := by
  have e := Scheme.Hom.stalkSpecializes_stalkMap g _ _ q.2
  have e2 := congrArg (fun t => (t ≫ Scheme.stalkClosedPointTo ξ').hom s) e
  have e3 := Scheme.stalkClosedPointTo_comp ξ' g
  have e4 := congrArg (fun t => (X.presheaf.stalkSpecializes h ≫ t).hom s) e3
  exact e2.symm.trans e4.symm

theorem eta_comp {G : Over X} [GrpObj G] {G' : Over X'} [GrpObj G'] (f : X' ⟶ X) (φ : G'.left ⟶ G.left)
    (h : IsGrpPullback G' G f φ) : η[G'].left ≫ φ = f ≫ η[G].left := by
  have hw := h.1.w
  let x₀ : Over.mk ((Over.mk (𝟙 X')).hom ≫ f) ⟶ G :=
    Over.homMk ((1 : Over.mk (𝟙 X') ⟶ G').left ≫ φ) (by
      rw [Category.assoc, hw, ← Category.assoc, Over.w]; simp)
  have hm := h.2 (Over.mk (𝟙 X')) 1 1 x₀ x₀ rfl rfl
  have hx : x₀ * x₀ = x₀ := by
    ext1
    rw [hm, _root_.mul_one]
    rfl
  have h1 : x₀ = 1 := by simpa using hx
  have h2 := congrArg (fun u => u.left) h1
  simpa [x₀, Hom.one_def] using h2

end Scheme

section Move

variable {X X' : Scheme.{0}} {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V]

theorem valAt_up (e : X' ≅ X) {G : Over X} [GrpObj G] {G' : Over X'} [GrpObj G'] (φ : G'.left ≅ G.left)
    (hw : φ.hom ≫ G.hom = G'.hom ≫ e.hom) (hη : η[G'].left ≫ φ.hom = e.hom ≫ η[G].left)
    {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω ⟶ X'} (M : LieModel G ξ V) (M' : LieModel G' ξ' V) (hξ : ξ' ≫ e.hom = ξ)
    (hpt : ∀ v, (M'.pt v).left ≫ φ.hom = (M.pt v).left)
    {z : Sp ℂ ⟶ X'} {z₀ : Sp ℂ ⟶ X} (hz : z ≫ e.hom = z₀) {b : V} {w : epsAt z₀ ⟶ G} {w' : epsAt z ⟶ G'}
    (hww : w'.left ≫ φ.hom = w.left) : M.ValAt z₀ b w → M'.ValAt z b w' := by
  subst hξ hz
  rintro ⟨h, v, ⟨hvt, hve⟩, hvw⟩
  have h' : genPt ξ' ⤳ centre z := specializes_of_iso e h
  change e.hom (genPt ξ') ⤳ e.hom (centre z) at h
  change epsAt (R := X.presheaf.stalk (e.hom (centre z))) (X.fromSpecStalk (e.hom (centre z))) ⟶ G at v
  change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X.presheaf.stalk (e.hom (centre z)))
      (X.presheaf.stalk (e.hom (centre z))) (X.presheaf.stalk (e.hom (centre z)))).toRingHom) ≫ v.left =
      (1 : Over.mk (X.fromSpecStalk (e.hom (centre z))) ⟶ G).left at hvt
  change (M.pt b).left = Spec.map (CommRingCat.ofHom (dualMap (genMap (ξ' ≫ e.hom) ⟨e.hom (centre z), h⟩))) ≫
      v.left at hve
  change w.left = Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo (z ≫ e.hom)).hom)) ≫ v.left at hvw
  have hφ : φ.inv ≫ G'.hom = G.hom ≫ e.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, hw, Category.assoc, e.hom_inv_id, Category.comp_id]
  have hη' : e.hom ≫ η[G].left ≫ φ.inv = η[G'].left := by
    rw [← Category.assoc, ← hη, Category.assoc, φ.hom_inv_id, Category.comp_id]
  have hv : v.left ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (e.hom (centre z)))
      (DualNumber (X.presheaf.stalk (e.hom (centre z)))))) ≫ X.fromSpecStalk (e.hom (centre z)) := Over.w v
  have hσ : Spec.map (e.hom.stalkMap (centre z)) ≫ X.fromSpecStalk (e.hom (centre z)) =
      X'.fromSpecStalk (centre z) ≫ e.hom := Scheme.SpecMap_stalkMap_fromSpecStalk e.hom
  have k1 : Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (e.hom (centre z)))
        (DualNumber (X.presheaf.stalk (e.hom (centre z)))))) =
      Spec.map (CommRingCat.ofHom (algebraMap (X'.presheaf.stalk (centre z))
        (DualNumber (X'.presheaf.stalk (centre z))))) ≫ Spec.map (e.hom.stalkMap (centre z)) := by
    rw [specMap_comp, dualMap_algebraMap, ← specMap_comp]
    rfl
  let v' : epsAt (R := X'.presheaf.stalk (centre z)) (X'.fromSpecStalk (centre z)) ⟶ G' :=
    Over.homMk (Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) ≫ v.left ≫ φ.inv) (by
      show _ ≫ (v.left ≫ φ.inv) ≫ G'.hom = Spec.map (CommRingCat.ofHom (algebraMap (X'.presheaf.stalk (centre z))
        (DualNumber (X'.presheaf.stalk (centre z))))) ≫ X'.fromSpecStalk (centre z)
      rw [Category.assoc, hφ, reassoc_of% hv]
      show Spec.map _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (e.hom (centre z)))
        (DualNumber (X.presheaf.stalk (e.hom (centre z)))))) ≫ X.fromSpecStalk (e.hom (centre z))) ≫ e.inv = _
      rw [← Category.assoc, ← Category.assoc]
      erw [k1]
      erw [Category.assoc, Category.assoc, reassoc_of% hσ, e.hom_inv_id, Category.comp_id]
      rfl)
  have hv' : v'.left = Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) ≫ v.left ≫ φ.inv := rfl
  refine ⟨h', v', ⟨?_, ?_⟩, ?_⟩
  · have e1 : (1 : Over.mk (X'.fromSpecStalk (centre z)) ⟶ G').left = X'.fromSpecStalk (centre z) ≫ η[G'].left := by
      simp [Hom.one_def]
    have e2 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X.presheaf.stalk (e.hom (centre z)))
        (X.presheaf.stalk (e.hom (centre z))) (X.presheaf.stalk (e.hom (centre z)))).toRingHom) ≫ v.left =
        X.fromSpecStalk (e.hom (centre z)) ≫ η[G].left := by
      rw [hvt]
      simp [Hom.one_def]
    have k2 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X'.presheaf.stalk (centre z))
        (X'.presheaf.stalk (centre z)) (X'.presheaf.stalk (centre z))).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (e.hom.stalkMap (centre z)).hom)) =
        Spec.map (e.hom.stalkMap (centre z)) ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom
        (X.presheaf.stalk (e.hom (centre z))) (X.presheaf.stalk (e.hom (centre z)))
        (X.presheaf.stalk (e.hom (centre z)))).toRingHom) := by
      rw [specMap_comp, fstHom_dualMap, ← specMap_comp]
      rfl
    show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X'.presheaf.stalk (centre z))
        (X'.presheaf.stalk (centre z)) (X'.presheaf.stalk (centre z))).toRingHom) ≫ v'.left =
        (1 : Over.mk (X'.fromSpecStalk (centre z)) ⟶ G').left
    rw [hv', e1, ← hη', ← reassoc_of% hσ, ← reassoc_of% e2, reassoc_of% k2]
    rfl
  · have k3 : Spec.map (CommRingCat.ofHom (dualMap (genMap ξ' ⟨centre z, h'⟩))) ≫
        Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) =
        Spec.map (CommRingCat.ofHom (dualMap (genMap (ξ' ≫ e.hom) ⟨e.hom (centre z), h⟩))) := by
      have hg : (genMap ξ' ⟨centre z, h'⟩).comp (e.hom.stalkMap (centre z)).hom =
          genMap (ξ' ≫ e.hom) ⟨e.hom (centre z), h⟩ :=
        RingHom.ext (genMap_stalkMap_eq ξ' e.hom ⟨centre z, h'⟩ h)
      rw [specMap_comp, ← dualMap_comp, hg]
    show (M'.pt b).left = Spec.map (CommRingCat.ofHom (dualMap (genMap ξ' ⟨centre z, h'⟩))) ≫ v'.left
    rw [(Iso.eq_comp_inv φ).2 (hpt b), hve, hv', reassoc_of% k3]
    exact Category.assoc _ _ _
  · have k4 : Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo z).hom)) ≫
        Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) =
        Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo (z ≫ e.hom)).hom)) := by
      refine (specMap_comp (dualMap (e.hom.stalkMap (centre z)).hom) (dualMap (Scheme.stalkClosedPointTo z).hom)).trans ?_
      rw [Scheme.stalkClosedPointTo_comp]
      exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (dualMap_comp _ _).symm
    rw [(Iso.eq_comp_inv φ).2 hww, hvw, hv', ← k4]
    erw [Category.assoc, Category.assoc]

end Move


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem gramAt_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (e : X' ≅ X)
    (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (t : SAB H X) (t' : SAB H X') (k : SABMap t' t e.hom)
    (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V),
    ξ' ≫ e.hom = ξ → (∀ v, (M'.pt v).left ≫ k.φ = (M.pt v).left) →
    ∀ (z : Sp ℂ ⟶ X') (r : ℕ) (b : Fin r → V) (Γ : Matrix (Fin r) (Fin r) ℂ),
      M'.GramAt t'.PP.L z b Γ ↔ M.GramAt t.PP.L (z ≫ e.hom) b Γ := by
  intro E _ _ _ H X X' e Ω _ ξ ξ' t t' k V _ _ M M' hξ hpt z r b Γ
  haveI : IsIso k.φ := k.cart.1.isIso_fst_of_isIso
  let φ : t'.G.left ≅ t.G.left := asIso k.φ
  have hw : φ.hom ≫ t.G.hom = t'.G.hom ≫ e.hom := k.cart.1.w
  have hη : η[t'.G].left ≫ φ.hom = e.hom ≫ η[t.G].left := eta_comp e.hom k.φ k.cart
  have hw' : φ.symm.hom ≫ t'.G.hom = t.G.hom ≫ e.symm.hom := by
    show φ.inv ≫ _ = _ ≫ e.inv
    rw [Iso.inv_comp_eq, ← Category.assoc, hw, Category.assoc, e.hom_inv_id, Category.comp_id]
  have hη' : η[t.G].left ≫ φ.symm.hom = e.symm.hom ≫ η[t'.G].left := by
    show _ ≫ φ.inv = e.inv ≫ _
    rw [Iso.eq_inv_comp, ← reassoc_of% hη, φ.hom_inv_id, Category.comp_id]
  have hpt' : ∀ v, (M.pt v).left ≫ φ.symm.hom = (M'.pt v).left := fun v => by
    show _ ≫ φ.inv = _
    rw [← hpt v, Category.assoc]
    erw [φ.hom_inv_id]
    exact Category.comp_id _
  have hξ' : ξ ≫ e.symm.hom = ξ' := by rw [← hξ]; simp
  constructor
  · rintro ⟨v', hval, hip⟩
    let v : Fin r → (epsAt (z ≫ e.hom) ⟶ t.G) := fun i => Over.homMk ((v' i).left ≫ k.φ) (by
      have h1 := Over.w (v' i)
      rw [Category.assoc, k.cart.1.w, ← Category.assoc, h1]
      simp [epsAt])
    refine ⟨v, fun i => ?_, fun p q => ?_⟩
    · refine valAt_up e.symm φ.symm hw' hη' M' M hξ' hpt' (z := z ≫ e.hom) (z₀ := z) (by simp) ?_ (hval i)
      show ((v' i).left ≫ k.φ) ≫ φ.inv = _
      simp [φ]
    · exact (GlobalTheory.T.hodge_inner_product_pullback_iff E H X X' t t' e.hom k z (v' p) (v' q) (v p) (v q) (Γ p q) rfl rfl).1 (hip p q)
  · rintro ⟨v, hval, hip⟩
    let v' : Fin r → (epsAt z ⟶ t'.G) := fun i => Over.homMk ((v i).left ≫ φ.inv) (by
      have h1 := Over.w (v i)
      rw [Category.assoc, ← Iso.symm_hom, hw', ← Category.assoc, h1]
      simp [epsAt])
    have hv' : ∀ i, (v' i).left ≫ k.φ = (v i).left := fun i => by
      show ((v i).left ≫ φ.inv) ≫ φ.hom = _
      simp
    refine ⟨v', fun i => ?_, fun p q => ?_⟩
    · exact valAt_up e φ hw hη M M' hξ hpt (z := z) (z₀ := z ≫ e.hom) rfl (hv' i) (hval i)
    · exact (GlobalTheory.T.hodge_inner_product_pullback_iff E H X X' t t' e.hom k z (v' p) (v' q) (v p) (v q) (Γ p q) (hv' p) (hv' q)).2 (hip p q)

end GlobalTheory.CompanionTheory.Ar.GMove
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.adjoint_relation_generator_corr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (S : Type) [CommRing S] (x : Sp S ⟶ X) (d : ℕ) (g : GermAt t x d) (a : 𝓞 E) (wL : AdTy t a), wL.IsGen → AdRel t x d g.x g.B.A.act g.B.ad g.e a wL → ∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ wL (lift (1 : jOG x d m 1 ⟶ t.G) (g.x m)).left) (LB.oneGen t.PP.L) ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ wL (lift (g.x m) (1 : jOG x d m 1 ⟶ t.G)).left) (LB.oneGen t.PP.L) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.WAxis.adAxes | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.WAxis.adAxes | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.WAxis.adAxes <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.exists_dual_to_invariant_differentials : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L), ∃ θ : Module.Dual R L →ₗ[R] omega (Γ.btOrder ⊤), (Function.Surjective θ ∧ ∀ (f : augIdeal (Γ.btOrder ⊤)) (w : Module.Dual R L), θ w = (augIdeal (Γ.btOrder ⊤)).toCotangent f ↔ Γ.IsDerAtOne i M N (f.1.1 : T → R) w) ∧ (∀ w, θ w = 0 ↔ ∃ u, w = N • u) ∧ ∀ (χ : T →* Rˣ) (w : Module.Dual R L), Γ.IsHT i M N χ w → θ w = dlogChar (Γ.btOrder ⊤) χ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.omega_isDerAtOne | exact GlobalTheory.CompanionTheory.Ar.BT.omega_isDerAtOne | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.omega_isDerAtOne <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif.Charts

theorem exists_halfPolydisc_cover : Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), ∃ (n nc : ℕ) (w : Fin nc → (Fin n → ℂ) → (Σ k, J k) → ℂ) (a : Fin nc → ℕ), (∀ i, a i ≤ n) ∧ (∀ i, AnalyticOnNhd ℂ (w i) (ball 0 1)) ∧ (∀ i, ∀ t ∈ ball (0 : Fin n → ℂ) 1, w i t ∈ mcPts (mCoordIdeal y)) ∧ (∀ i, ∀ t ∈ ball (0 : Fin n → ℂ) 1, (∀ j : Fin n, (j : ℕ) < a i → t j ≠ 0) → ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w i t) → 𝔐.Interior z) ∧ ∀ x ∈ mcPts (mCoordIdeal y), ∃ (i : Fin nc) (t : Fin n → ℂ) (b : K → ℂ), ‖t‖ ≤ 1 / 2 ∧ (∀ k, b k ≠ 0) ∧ x = GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul b (w i t) :=
  PositivityTheory.Xgn.quotient_uniformization_charts

end GlobalTheory.CompanionTheory.Ar.QuotUnif.Charts
end
