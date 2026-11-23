module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle014
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle054
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle195
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle146
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle187
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle055
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle196
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle150
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGaugeTransform
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGaugeRelation
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FunctionFamilyChartFacts
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle197
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
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ValueSpan

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem mem_eigSp_iff {R E O : Type} [CommRing R] [AddCommGroup E] [Module R E] [CommRing O]
    {ρ : O →+* Module.End R E} {σ : O →+* R} {v : E} : v ∈ eigSp ρ σ ↔ ∀ a, ρ a v = σ a • v := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem valAt_act {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {V : Type}
    [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) {F : Type} [Field F] {z : Sp F ⟶ X} {W : Type}
    [AddCommGroup W] [Module F W] (Mz : LieModel G z W) {A : Type} [CommRing A] (act : OAct A G)
    {ρ : A →+* Module.End Ω V} {ρz : A →+* Module.End F W} (hρ : M.IsActOf act.act ρ)
    (hρz : Mz.IsActOf act.act ρz) (a : A) {e : V} {w : W} (h : M.ValAt z e (Mz.pt w)) :
    M.ValAt z (ρ a e) (Mz.pt (ρz a w)) := by
  haveI : IsMonHom (act.act a) := act.hom a
  obtain ⟨h', v, ⟨ht, he⟩, hw⟩ := h
  refine ⟨h', v ≫ act.act a, ⟨?_, ?_⟩, ?_⟩
  · show _ ≫ (v ≫ act.act a).left = (1 : Over.mk _ ⟶ G).left
    have h1 : (1 : Over.mk (X.fromSpecStalk (centre z)) ⟶ G) ≫ act.act a = 1 := MonObj.one_comp _
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (act.act a).left) ht).trans (congrArg CommaMorphism.left h1))
  · rw [hρ a e, Over.comp_left, he]
    exact Category.assoc _ _ _
  · rw [hρz a w, Over.comp_left, hw]
    exact Category.assoc _ _ _

theorem value_span : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (F : Type) [Field F] (z : Sp F ⟶ X) (h : genPt ξ ⤳ centre z) (W : Type) [AddCommGroup W] [Module F W] (Mz : LieModel G z W) (A : Type) [CommRing A] (act : OAct A G) (ρ : A →+* Module.End Ω V) (ρz : A →+* Module.End F W) (K : Type) [Field K] (inc : K →+* Ω) (βF : K →+* F) (σ : A →+* K) (n : ℕ) (e : Fin n → A) (cf : Fin n → K) (r : ℕ) (b : Fin r → V), IsCptGen ξ → Smooth G.hom → M.IsActOf act.act ρ → Mz.IsActOf act.act ρz → (∀ k : K, ValAt ξ z (inc k) (βF k)) → ∑ k, cf k * σ (e k) = 1 → (∀ (a : A) (w : V), ρ a (∑ k, inc (cf k) • ρ (e k) w) = inc (σ a) • ∑ k, inc (cf k) • ρ (e k) w) → (M.eigLat ρ (inc.comp σ)).IsFrameAt b ⟨centre z, h⟩ → ∃ u : Fin r → W, (∀ i, M.ValAt z (b i) (Mz.pt (u i))) ∧ Submodule.span F (Set.range u) = eigSp ρz (βF.comp σ) := by
  intro X G _ _ Ω _ ξ V _ _ M F _ z h W _ _ Mz A _ act ρ ρz K _ inc βF σ n e cf r b hgen hsm hρ hρz hinc hsum hπ hb
  obtain ⟨ev, hval, hsmul, hspan⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X G Ω ξ V M F z h W Mz hgen hsm
  have hreg : ∀ k : K, inc k ∈ regAt ξ ⟨centre z, h⟩ := by
    intro k
    obtain ⟨_, s, hs, _⟩ := hinc k
    exact ⟨s, hs⟩
  have hvalr : ∀ c : regAt ξ ⟨centre z, h⟩, ∃ t : F, ValAt ξ z (c : Ω) t := by
    rintro ⟨_, s, rfl⟩
    exact ⟨_, h, s, rfl, rfl⟩
  have hself : ∀ l : M.lat ⟨centre z, h⟩, M.ValAt z l (Mz.pt (ev l)) :=
    fun l => (hval _ _).2 ⟨l.2, rfl⟩
  have hact : ∀ (a : A) (l : M.lat ⟨centre z, h⟩), ∃ he : ρ a l ∈ M.lat ⟨centre z, h⟩,
      ev ⟨ρ a l, he⟩ = ρz a (ev l) :=
    fun a l => (hval _ _).1 (valAt_act M Mz act hρ hρz a (hself l))
  have hbm : ∀ i, b i ∈ (M.eigLat ρ (inc.comp σ)) ⟨centre z, h⟩ := fun i => by
    rw [hb.2]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hbl : ∀ i, b i ∈ M.lat ⟨centre z, h⟩ := fun i => (hbm i).1
  have hbe : ∀ i, b i ∈ eigSp ρ (inc.comp σ) := fun i => (hbm i).2
  refine ⟨fun i => ev ⟨b i, hbl i⟩, fun i => hself ⟨b i, hbl i⟩, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine mem_eigSp_iff.2 fun a => ?_
    obtain ⟨he, h2⟩ := hact a ⟨b i, hbl i⟩
    have h3 : ρ a (b i) = inc (σ a) • b i := mem_eigSp_iff.1 (hbe i) a
    have h4 : (⟨ρ a (b i), he⟩ : M.lat ⟨centre z, h⟩) =
        (⟨inc (σ a), hreg _⟩ : regAt ξ ⟨centre z, h⟩) • (⟨b i, hbl i⟩ : M.lat ⟨centre z, h⟩) := Subtype.ext h3
    have h5 : ρz a (ev ⟨b i, hbl i⟩) = βF (σ a) • ev ⟨b i, hbl i⟩ := by
      rw [← h2]
      refine (congrArg ev h4).trans ?_
      exact hsmul _ _ _ (hinc _)
    exact h5
  · intro w hw
    have hw' := mem_eigSp_iff.1 hw
    let πW : W →ₗ[F] W := ∑ k, βF (cf k) • ρz (e k)
    have hπw : πW w = w := by
      have h1 : ∀ k, βF (cf k) • ρz (e k) w = βF (cf k * σ (e k)) • w := fun k => by
        rw [hw' (e k), map_mul, mul_smul]
        rfl
      simp only [πW, LinearMap.sum_apply, LinearMap.smul_apply]

      rw [Finset.sum_congr rfl fun k _ => h1 k, ← Finset.sum_smul, ← map_sum, hsum, map_one, one_smul]
    have key : ∀ l : M.lat ⟨centre z, h⟩,
        πW (ev l) ∈ Submodule.span F (Set.range fun i => ev ⟨b i, hbl i⟩) := by
      intro l
      choose he hk using fun k => hact (e k) l
      let c : Fin n → regAt ξ ⟨centre z, h⟩ := fun k => ⟨inc (cf k), hreg _⟩
      let m : M.lat ⟨centre z, h⟩ := ∑ k, c k • (⟨ρ (e k) l, he k⟩ : M.lat ⟨centre z, h⟩)
      have hevm : ev m = πW (ev l) := by

        simp only [πW, LinearMap.sum_apply, LinearMap.smul_apply, m, map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hsmul _ _ _ (hinc (cf k)), hk k]
      have hmv : (m : V) = ∑ k, inc (cf k) • ρ (e k) l := by
        simp only [m, AddSubmonoidClass.coe_finsetSum]
        exact Finset.sum_congr rfl fun _ _ => rfl
      have hme : (m : V) ∈ eigSp ρ (inc.comp σ) := mem_eigSp_iff.2 fun a => by
        rw [hmv]
        exact hπ a l
      have hmL : (m : V) ∈ (M.eigLat ρ (inc.comp σ)) ⟨centre z, h⟩ := ⟨m.2, hme⟩
      rw [hb.2] at hmL
      obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hmL
      choose t ht using fun i => hvalr (d i)
      have hm : m = ∑ i, d i • (⟨b i, hbl i⟩ : M.lat ⟨centre z, h⟩) := by
        apply Subtype.ext
        rw [← hd, AddSubmonoidClass.coe_finsetSum]
        exact Finset.sum_congr rfl fun _ _ => rfl

      rw [← hevm, hm, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [hsmul _ _ _ (ht i)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hwt : w ∈ Submodule.span F (Set.range ev) := by
      rw [hspan]
      exact Submodule.mem_top
    rw [← hπw]
    refine Submodule.span_induction (p := fun y _ => πW y ∈
      Submodule.span F (Set.range fun i => ev ⟨b i, hbl i⟩)) ?_ ?_ ?_ ?_ hwt
    · rintro _ ⟨l, rfl⟩
      exact key l
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      rw [map_smul]
      exact Submodule.smul_mem _ c hx

end GlobalTheory.CompanionTheory.Ar.ValueSpan
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar Filter Topology Metric

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieFrameIndep

theorem linearIndependent_values {Ω C E EC : Type} [Field Ω] [Field C] [AddCommGroup E] [Module Ω E]
    [AddCommGroup EC] [Module C EC] (A : Subring Ω) (ρ : A →+* C) (P : Submodule A E) (ev : P →+ EC)
    (hsm : ∀ (a : A) (e : P), ev (a • e) = ρ a • ev e) (hspan : Submodule.span C (Set.range ev) = ⊤)
    {g n : ℕ} (b : Fin g → E) (hP : P = Submodule.span A (Set.range b))
    (hfin : Module.finrank C EC = g) (S : Finset (Fin g)) (c : Fin n → E) (hc : LinearIndependent Ω c)
    (hL : Submodule.span A (b '' S) = Submodule.span A (Set.range c))
    (w : Fin n → EC) (hw : ∀ i, ∃ he : c i ∈ P, ev ⟨c i, he⟩ = w i) : LinearIndependent C w := by
  subst hP
  have hbm : ∀ k, b k ∈ Submodule.span A (Set.range b) := fun k => Submodule.subset_span ⟨k, rfl⟩
  let v : Fin g → EC := fun k => ev ⟨b k, hbm k⟩
  have hcomb : ∀ {J : Type} [Fintype J] (f : J → Fin g) (t : J → A)
      (he : ∑ i, t i • b (f i) ∈ Submodule.span A (Set.range b)),
      ev ⟨∑ i, t i • b (f i), he⟩ = ∑ i, ρ (t i) • v (f i) := by
    intro J _ f t he
    have : (⟨∑ i, t i • b (f i), he⟩ : Submodule.span A (Set.range b)) =
        ∑ i, t i • (⟨b (f i), hbm _⟩ : Submodule.span A (Set.range b)) := by
      apply Subtype.ext
      simp

    rw [this, map_sum]
    exact Finset.sum_congr rfl fun i _ => hsm _ _
  have hvspan : ⊤ ≤ Submodule.span C (Set.range v) := by
    rw [← hspan]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨e, he⟩, rfl⟩
    obtain ⟨t, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 he
    have := hcomb (fun i => i) t he
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hv : LinearIndependent C v :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hvspan (by simp [hfin])
  have hvS : LinearIndependent C (fun k : S => v k) := hv.comp _ Subtype.val_injective
  have himg : b '' S = Set.range (fun k : S => b k) := by
    ext y
    simp
  rw [himg] at hL
  have hcm : ∀ i, c i ∈ Submodule.span A (Set.range fun k : S => b k) := fun i => by
    rw [hL]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hbS : ∀ k : S, b k ∈ Submodule.span A (Set.range c) := fun k => by
    rw [← hL]
    exact Submodule.subset_span ⟨k, rfl⟩
  choose a ha using fun i => (Submodule.mem_span_range_iff_exists_fun A).1 (hcm i)
  choose d hd using fun k => (Submodule.mem_span_range_iff_exists_fun A).1 (hbS k)
  have hdelta : ∀ i j, ∑ k, a i k * d k j = if i = j then 1 else 0 := by
    intro i j
    have hexp : ∑ j, (∑ k, a i k * d k j) • c j = c i := by
      conv_rhs => rw [← ha i]
      simp only [← hd, Finset.smul_sum, Finset.sum_smul, mul_smul]
      exact Finset.sum_comm
    have hz : ∑ j, (((∑ k, a i k * d k j : A) : Ω) - if i = j then 1 else 0) • c j = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [sub_eq_zero]
      exact hexp
    have := Fintype.linearIndependent_iff.1 hc _ hz j
    apply Subtype.ext
    rw [sub_eq_zero] at this
    rw [this]
    split_ifs <;> simp
  have hwexp : ∀ i, w i = ∑ k : S, ρ (a i k) • v k := by
    intro i
    obtain ⟨he, hev⟩ := hw i
    rw [← hev]
    have hmem : ∑ k : S, a i k • b k ∈ Submodule.span A (Set.range b) := by
      rw [ha i]
      exact he
    rw [← hcomb (fun k : S => (k : Fin g)) (a i) hmem]
    congr 2
    exact (ha i).symm
  rw [Fintype.linearIndependent_iff]
  intro l hl j
  have hk : ∀ k : S, ∑ i, l i * ρ (a i k) = 0 := by
    refine Fintype.linearIndependent_iff.1 hvS _ ?_
    rw [← hl]
    simp only [hwexp, Finset.smul_sum, Finset.sum_smul, mul_smul]
    exact Finset.sum_comm
  calc l j = ∑ i, l i * ρ (∑ k, a i k * d k j) := by
        simp only [hdelta]
        simp [apply_ite ρ]
    _ = ∑ k : S, (∑ i, l i * ρ (a i k)) * ρ (d k j) := by

        simp only [map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
        exact Finset.sum_comm
    _ = 0 := by simp [hk]


open GlobalTheory.CompanionTheory.Ar.LieVB in
theorem finrank_eq_of_isFrameAt {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {Ω : Type}
    [Field Ω] {ξ : Sp Ω ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) {C : Type} [Field C]
    {z : Sp C ⟶ X} (h : genPt ξ ⤳ centre z) {EC : Type} [AddCommGroup EC] [Module C EC] (N : LieModel G z EC)
    {g : ℕ} (b : Fin g → E) (hξ : IsCptGen ξ) (hb : M.lat.IsFrameAt b ⟨centre z, h⟩) :
    Module.finrank C EC = g := by
  obtain ⟨R, _, x, hx, F, _, _, MR, n', b', hp⟩ := exists_chart G (centre z)
  have hgen : genPt ξ ∈ x.opensRange := h.mem_open x.opensRange.isOpen hp
  obtain ⟨φ, hφ⟩ := exists_lift x ξ hgen
  obtain ⟨a, ha⟩ := exists_lift x z hp
  obtain ⟨_, B, -, -⟩ := basis_tr φ x ξ hφ MR M b'
  obtain ⟨_, BC, -, -⟩ := basis_tr a x z ha MR N b'
  have hC : Module.finrank C EC = n' := by
    rw [Module.finrank_eq_card_basis BC, Fintype.card_fin]
  have hΩ : Module.finrank Ω E = n' := by
    rw [Module.finrank_eq_card_basis B, Fintype.card_fin]
  haveI : Module.Finite Ω E := Module.Finite.of_basis B
  obtain ⟨U, hU, b₂, hsp, hfr⟩ := (lieLat_isVB_of_smooth X Ω ξ G E M hξ inferInstance).1 ⟨centre z, h⟩ (Set.mem_univ _)
  have h₂ := (hfr ⟨centre z, h⟩ (Set.mem_univ _) hU).2
  have hspan : ⊤ ≤ Submodule.span Ω (Set.range b) := by
    rw [← hsp]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    have hk : b₂ k ∈ Submodule.span (regAt ξ ⟨centre z, h⟩) (Set.range b) := by
      rw [← hb.2, h₂]
      exact Submodule.subset_span ⟨k, rfl⟩
    exact (Submodule.span_le_restrictScalars (regAt ξ ⟨centre z, h⟩) Ω (Set.range b)) hk
  have hg : Module.finrank Ω E = g := by
    rw [Module.finrank_eq_card_basis (Module.Basis.mk hb.1 hspan), Fintype.card_fin]
  rw [hC, ← hΩ, hg]

end GlobalTheory.CompanionTheory.Ar.LieFrameIndep

namespace GlobalTheory.CompanionTheory.Ar


open GlobalTheory.CompanionTheory.Ar.LieFrameIndep in
theorem values_frame_sublattice_linearIndependent : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (C : Type) [Field C] (z : Sp C ⟶ X) (h : genPt ξ ⤳ centre z) (EC : Type) [AddCommGroup EC] [Module C EC] (N : LieModel G z EC) (g n : ℕ) (b : Fin g → E) (S : Finset (Fin g)) (c : Fin n → E) (L : Lat ξ E) (w : Fin n → EC), IsCptGen ξ → M.lat.IsFrameAt b ⟨centre z, h⟩ → L ⟨centre z, h⟩ = Submodule.span (regAt ξ ⟨centre z, h⟩) (b '' S) → L.IsFrameAt c ⟨centre z, h⟩ → (∀ i, M.ValAt z (c i) (N.pt (w i))) → LinearIndependent C w := by
  intro X G _ _ _ Ω _ ξ E _ _ M C _ z h EC _ _ N g n b S c L w hξ hb hLb hLc hw
  obtain ⟨ev, h1, h2, h3⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X G Ω ξ E M C z h EC N hξ inferInstance
  let e : X.presheaf.stalk (centre z) ≃+* regAt ξ ⟨centre z, h⟩ :=
    RingEquiv.ofBijective (genMap ξ ⟨centre z, h⟩).rangeRestrict
      ⟨fun s t est => hξ.inj ⟨centre z, h⟩ (congrArg Subtype.val est), RingHom.rangeRestrict_surjective _⟩
  let ρ : regAt ξ ⟨centre z, h⟩ →+* C :=
    (Scheme.stalkClosedPointTo z).hom.comp (e.symm : regAt ξ ⟨centre z, h⟩ →+* X.presheaf.stalk (centre z))
  have hρ : ∀ a : regAt ξ ⟨centre z, h⟩, ValAt ξ z (a : Ω) (ρ a) := fun a =>
    ⟨h, e.symm a, congrArg Subtype.val (e.apply_symm_apply a), rfl⟩
  refine linearIndependent_values (regAt ξ ⟨centre z, h⟩) ρ (M.lat ⟨centre z, h⟩) ev
    (fun a x => h2 a _ x (hρ a)) h3 b hb.2 (finrank_eq_of_isFrameAt M h N b hξ hb) S c hLc.1 ?_ w
    fun i => (h1 _ _).1 (hw i)
  rw [← hLb, hLc.2]

end GlobalTheory.CompanionTheory.Ar
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.eigen_frame_field_extension : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) [Smooth G.hom] (P : Type) [CommRing P] (act : OAct P G) (σ : P →+* F) (F' : Type) [Field F'] (f : F →+* F') (x' : Sp F' ⟶ S), spMap f ≫ x = x' → ∀ (n : ℕ) (v : Fin n → (epsAt x ⟶ G)) (v' : Fin n → (epsAt x' ⟶ G)), (∀ i, (v' i).left = spMap (dualMap f) ≫ (v i).left) → IsEigFrame act x σ v → IsEigFrame act x' (f.comp σ) v' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.EigBase.isEigFrame_base | exact GlobalTheory.CompanionTheory.Ar.EigBase.isEigFrame_base | (intros; apply GlobalTheory.CompanionTheory.Ar.EigBase.isEigFrame_base <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.LocalFrames

theorem exists_affine_eigenframes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (p₀ : Cpt (Z.ξ₀ ≫ Y.j)), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → LinearIndependent Z.Ω b₁ → Submodule.span Z.Ω (Set.range b₁) = eigSp Z.ρ (Z.inc.comp (tauIn c τ)) → LinearIndependent Z.Ω b₂ → Submodule.span Z.Ω (Set.range b₂) = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) → p₀ ∈ Z.genFib → ∃ (A : Y.X.Opens) (hA : IsAffineOpen A) (EB : Type) (_ : AddCommGroup EB) (_ : Module Γ(Y.X, A) EB) (MB : LieModel Y.t.G hA.fromSpec EB) (e₁ : Fin D.p → EB) (e₂ : Fin D.q → EB) (v₁ : Fin D.p → Z.V) (v₂ : Fin D.q → Z.V), p₀.1 ∈ A ∧ (∀ q : Cpt (Z.ξ₀ ≫ Y.j), q.1 ∈ A → (Z.eig τ).IsFrameAt v₁ q ∧ (Z.eig (ComplexEmbedding.conjugate τ)).IsFrameAt v₂ q) ∧ (∀ (f : Γ(Y.X, A) →+* ℂ) (y : Sp ℂ ⟶ Y.X) (v : Fin D.p → (epsAt y ⟶ Y.t.G)) (w : Fin D.q → (epsAt y ⟶ Y.t.G)), y = spMap f ≫ hA.fromSpec → y ≫ Y.s = spMap (σ.comp β) → (∀ i, (v i).left = spMap (dualMap f) ≫ (MB.pt (e₁ i)).left) → (∀ j, (w j).left = spMap (dualMap f) ≫ (MB.pt (e₂ j)).left) → IsEigFrame Y.t.act y (σ.comp (tauIn c τ)) v ∧ IsEigFrame Y.t.act y (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) w) ∧ (∀ (f : Γ(Y.X, A) →+* ℂ) (y : Sp ℂ ⟶ Y.X) (v : Fin D.p → (epsAt y ⟶ Y.t.G)) (w : Fin D.q → (epsAt y ⟶ Y.t.G)), y = spMap f ≫ hA.fromSpec → genPt (Z.ξ₀ ≫ Y.j) ⤳ centre y → (∀ i, (v i).left = spMap (dualMap f) ≫ (MB.pt (e₁ i)).left) → (∀ j, (w j).left = spMap (dualMap f) ≫ (MB.pt (e₂ j)).left) → (∀ i, Z.M.ValAt y (v₁ i) (v i)) ∧ ∀ j, Z.M.ValAt y (v₂ j) (w j)) := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ σ b₁ b₂ p₀ hO hτ h1 h2 h3 h4 hp₀
  obtain ⟨hinj, hnoeth, hfr⟩ := hO
  haveI := hnoeth
  have := projProper _ _ _ Y.proj
  haveI : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  haveI : GlobalTheory.IsNormalScheme Y.X := GlobalTheory.IsNormalScheme.of_pred Y.normal
  haveI : Smooth Y.t.G.hom := Y.t.semi.smooth
  obtain ⟨-, -, h3c, -⟩ := GlobalTheory.T.eigen_lattice_vector_bundle E H D l Xo c O β Y U Z τ ⟨hinj, hnoeth, hfr⟩ hτ
  obtain ⟨g, b, hb, hS⟩ := h3c p₀ hp₀
  obtain ⟨S₁, hS₁⟩ := hS τ
  obtain ⟨S₂, hS₂⟩ := hS (ComplexEmbedding.conjugate τ)
  obtain ⟨hspan, N, hpN, hN⟩ := GlobalTheory.T.lattice_frame_open_condition Y.X Y.t.G Z.Ω _ Z.V Z.M p₀ g b hb
  have e₁ := GlobalTheory.T.lattice_intersection_frame_subspace Y.X Z.Ω _ Z.V Z.M.lat (eigSp Z.ρ (Z.inc.comp (tauIn c τ))) p₀ g b S₁ Z.gen hspan hb.2 hS₁
  have e₂ := GlobalTheory.T.lattice_intersection_frame_subspace Y.X Z.Ω _ Z.V Z.M.lat (eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ)))) p₀ g b S₂
    Z.gen hspan hb.2 hS₂
  have card : ∀ (S : Finset (Fin g)) (n : ℕ) (u : Fin n → Z.V), LinearIndependent Z.Ω u →
      Submodule.span Z.Ω (Set.range u) = Submodule.span Z.Ω (b '' S) → S.card = n := by
    intro S n u hu hsp
    have a₁ := finrank_span_eq_card hu
    have a₂ := finrank_span_eq_card (hb.1.comp (Subtype.val : S → Fin g) Subtype.val_injective)
    have a₃ : Set.range (b ∘ (Subtype.val : S → Fin g)) = b '' S := by
      rw [Set.range_comp, Subtype.range_coe]
    rw [a₃, ← hsp, a₁] at a₂
    simpa using a₂.symm
  have c₁ := card S₁ D.p b₁ h1 (h2.trans e₁)
  have c₂ := card S₂ D.q b₂ h3 (h4.trans e₂)
  let ι₁ := S₁.orderEmbOfFin c₁
  let ι₂ := S₂.orderEmbOfFin c₂
  have r₁ : Set.range (b ∘ ι₁) = b '' S₁ := by
    rw [Set.range_comp, Finset.range_orderEmbOfFin]
  have r₂ : Set.range (b ∘ ι₂) = b '' S₂ := by
    rw [Set.range_comp, Finset.range_orderEmbOfFin]
  obtain ⟨W, hW, hWd⟩ := GlobalTheory.ModelChart.exists_open_isDomain Y.X p₀.1
  have hmem : ∀ i, b i ∈ Z.M.lat p₀ := fun i => by
    rw [hb.2]
    exact Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨A, hA, EB, i₁, i₂, MB, e, hpA, hAN, hval⟩ := GlobalTheory.T.lattice_sections_affine_model Y.X Y.t.G Z.Ω _ Z.V Z.M p₀ (N ⊓ W) (Fin g) b ⟨hpN, hW⟩ hmem
  have hd : IsDomain Γ(Y.X, A) := hWd A hpA (hAN.trans inf_le_right)
  have hcl := GlobalTheory.T.affine_domain_generic_specializes Y.X Z.Ω _ A hA p₀ Z.gen hd hpA
  have hcA : ∀ (f : Γ(Y.X, A) →+* ℂ) (y : Sp ℂ ⟶ Y.X), y = spMap f ≫ hA.fromSpec → centre y ∈ A := by
    intro f y hy
    have h5 : centre y ∈ Set.range hA.fromSpec := by
      subst hy
      exact ⟨spMap f (IsLocalRing.closedPoint ℂ), (Scheme.Hom.comp_apply _ _ _).symm⟩
    rwa [hA.range_fromSpec] at h5
  refine ⟨A, hA, EB, i₁, i₂, MB, e ∘ ι₁, e ∘ ι₂, b ∘ ι₁, b ∘ ι₂, hpA, fun q hq => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact GlobalTheory.T.lattice_frame_sub_basis Y.X Z.Ω _ Z.V Z.M.lat _ q g D.p b ι₁ ι₁.injective hb.1 (hN q (hAN hq).1).2 (by rw [r₁]; exact e₁)
  · exact GlobalTheory.T.lattice_frame_sub_basis Y.X Z.Ω _ Z.V Z.M.lat _ q g D.q b ι₂ ι₂.injective hb.1 (hN q (hAN hq).1).2 (by rw [r₂]; exact e₂)
  · intro f y v w hy hs hv hw
    have hyA := hcA f y hy
    have h := hcl _ hyA
    have hq := (hN ⟨centre y, h⟩ (hAN hyA).1).2
    exact ⟨GlobalTheory.T.component_complex_point_tangents E H D l Xo c O β Y U Z τ σ D.p _ y h v hinj hfr hs
        (GlobalTheory.T.lattice_frame_sub_basis Y.X Z.Ω _ Z.V Z.M.lat _ _ g D.p b ι₁ ι₁.injective hb.1 hq (by rw [r₁]; exact e₁))
        (fun i => hval y f h hy (ι₁ i) (v i) (hv i)),
      GlobalTheory.T.component_complex_point_tangents E H D l Xo c O β Y U Z _ σ D.q _ y h w hinj hfr hs
        (GlobalTheory.T.lattice_frame_sub_basis Y.X Z.Ω _ Z.V Z.M.lat _ _ g D.q b ι₂ ι₂.injective hb.1 hq (by rw [r₂]; exact e₂))
        (fun j => hval y f h hy (ι₂ j) (w j) (hw j))⟩
  · intro f y v w hy h hv hw
    exact ⟨fun i => hval y f h hy (ι₁ i) (v i) (hv i), fun j => hval y f h hy (ι₂ j) (w j) (hw j)⟩

end GlobalTheory.CompanionTheory.Ar.Flat.LocalFrames
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelian_quotient_gauge_transform : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ (w : LB.Iso (t.PP.L.pull (pullback.fst t.G.hom x)) (Q.tB.PP.L.pull Q.q.left)), w.IsGen → ∀ Qs : Fin d' → PS k 1 d, (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) → (∀ m, fibPt t x (g.x m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ gB.x m) → ∃ lam : PS k 2 d, AxOne lam ∧ ∀ m, ∃ U : (Jet k (Fin 2 × Fin d) m)ˣ, (U : Jet k (Fin 2 × Fin d) m) = psJet m lam ∧ Tr w (cubeF t x ![jptG t x d g.x m (0 : Fin 2), jptG t x d g.x m (1 : Fin 2)]) (cφG t ![jptG t x d g.x m (0 : Fin 2), jptG t x d g.x m (1 : Fin 2)]) (fun I => (homAt (𝟙 (Sp k)) (sub2 Qs m)).left ≫ cφG Q.tB ![jptG Q.tB (𝟙 (Sp k)) d' gB.x m (0 : Fin 2), jptG Q.tB (𝟙 (Sp k)) d' gB.x m (1 : Fin 2)] I) (cε 2) (g.e m) (LB.pullGen Q.tB.PP.L (cφG Q.tB ![jptG Q.tB (𝟙 (Sp k)) d' gB.x m (0 : Fin 2), jptG Q.tB (𝟙 (Sp k)) d' gB.x m (1 : Fin 2)]) (cε 2) (gB.e m) (homAt (𝟙 (Sp k)) (sub2 Qs m)).left) (unitΓ U⁻¹) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.Lamex.exists_lam | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.Lamex.exists_lam | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.Lamex.exists_lam <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelian_quotient_gauge_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ (w : LB.Iso (t.PP.L.pull (pullback.fst t.G.hom x)) (Q.tB.PP.L.pull Q.q.left)), w.IsGen → ∀ Qs : Fin d' → PS k 1 d, (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) → (∀ m, fibPt t x (g.x m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ gB.x m) → ∀ lam : PS k 2 d, (∀ m, ∃ U : (Jet k (Fin 2 × Fin d) m)ˣ, (U : Jet k (Fin 2 × Fin d) m) = psJet m lam ∧ Tr w (cubeF t x ![jptG t x d g.x m (0 : Fin 2), jptG t x d g.x m (1 : Fin 2)]) (cφG t ![jptG t x d g.x m (0 : Fin 2), jptG t x d g.x m (1 : Fin 2)]) (fun I => (homAt (𝟙 (Sp k)) (sub2 Qs m)).left ≫ cφG Q.tB ![jptG Q.tB (𝟙 (Sp k)) d' gB.x m (0 : Fin 2), jptG Q.tB (𝟙 (Sp k)) d' gB.x m (1 : Fin 2)] I) (cε 2) (g.e m) (LB.pullGen Q.tB.PP.L (cφG Q.tB ![jptG Q.tB (𝟙 (Sp k)) d' gB.x m (0 : Fin 2), jptG Q.tB (𝟙 (Sp k)) d' gB.x m (1 : Fin 2)]) (cε 2) (gB.e m) (homAt (𝟙 (Sp k)) (sub2 Qs m)).left) (unitΓ U⁻¹)) → ∀ (a : 𝓞 E) (wL : AdTy t a) (wB : AdTy Q.tB a), wL.IsGen → wB.IsGen → AdRel t x d g.x g.B.A.act g.B.ad g.e a wL → AdRel Q.tB (𝟙 (Sp k)) d' gB.x gB.B.A.act gB.B.ad gB.e a wB → Tr w (adF t x a) (fun i => sqMap t x ≫ Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) i) (fun i => qq Q ≫ Sum.elim (cφG Q.tB ![fst Q.tB.G Q.tB.G, snd Q.tB.G Q.tB.G ≫ Q.tB.act.act (H.bar a)]) (cφG Q.tB ![fst Q.tB.G Q.tB.G ≫ Q.tB.act.act a, snd Q.tB.G Q.tB.G]) i) (Sum.elim (cε 2) fun I => -cε 2 I) (LB.pullGen t.PP.L _ _ wL (sqMap t x)) (LB.pullGen Q.tB.PP.L _ _ wB (qq Q)) 1 → subQ Qs (gB.B.ad a) * ev (n := 2) ![pt k d 0, comp1 (g.B.A.act (H.bar a)) (pt k d 1)] lam = ev (n := 2) ![comp1 (g.B.A.act a) (pt k d 0), pt k d 1] lam * g.B.ad a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdRelPf.adRel_series | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdRelPf.adRel_series | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdRelPf.adRel_series <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT


theorem _root_.GlobalTheory.CompanionTheory.Relay.arith_variety_prime_relay : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c' : ∀ k, J k), mseg y c' ≠ 0 → CharZero Ω ∧ IsNoetherianRing (CR O y c') ∧ IsIntegrallyClosed (CR O y c') ∧ IsFractionRing (CR O y c') Ω := by
  first | exact @PositivityTheory.Xgn.function_family_chart_facts | exact PositivityTheory.Xgn.function_family_chart_facts
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

theorem _root_.GlobalTheory.T.kronecker_character_period_formula : FlatDegree → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) [NumberField c.F] (N : LogNorms c.F) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → IsFlatGen U τ φ FU i → (∀ s, HasInfNorm U τ φ s (N.inf s)) → (∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), HasFinNorm U τ φ p κ (N.fin p κ)) → N.IsAdelic ∧ N.deg = ((D.p : ℝ) - D.q) / 2 * (GlobalTheory.CM.logOm E χ).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.TopLL.degree_frames | exact GlobalTheory.CompanionTheory.Ar.Fl.TopLL.degree_frames | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.TopLL.degree_frames <;> assumption)
end
