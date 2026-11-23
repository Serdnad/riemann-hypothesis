module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle020
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.SpreadingOut
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

section

noncomputable section

namespace PositivityTheory.HtPt.Htat

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

section
variable {S Y : Scheme.{0}} {G : Over S} [GrpObj G]

theorem mul_congr {a b : Y ⟶ S} (h : a = b) (g k : Over.mk a ⟶ G) (g' k' : Over.mk b ⟶ G) (e : g.left = g'.left)
    (e' : k.left = k'.left) : (g * k).left = (g' * k').left := by
  subst h
  rw [Over.OverMorphism.ext e, Over.OverMorphism.ext e']

theorem comp_pow_pt {A B : Over S} (ψ : A ⟶ B) (g : B ⟶ G) (n : ℕ) : ψ ≫ g ^ n = (ψ ≫ g) ^ n := by
  induction n with
  | zero => simp [MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] {Γ : QFGroup R T}
  {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left}

theorem tors_of_pt (h : Γ.IsTorsionAlong G x N i) (v : Y ⟶ Γ.G.left) {c : Y ⟶ S} (g : Over.mk c ⟶ G)
    (e : g.left = v ≫ i) : g ^ N = 1 := by
  have hc : c = (v ≫ Γ.G.hom) ≫ x := by
    rw [Category.assoc, ← h.isOver, ← Category.assoc, ← e]; exact (Over.w g).symm
  subst hc
  exact (h.kernel (Over.mk (v ≫ Γ.G.hom)) g).2 ⟨Over.homMk v rfl, e.symm⟩

theorem pt_of_tors (h : Γ.IsTorsionAlong G x N i) (b : Y ⟶ Spec (CommRingCat.of R)) {c : Y ⟶ S} (hc : c = b ≫ x)
    (g : Over.mk c ⟶ G) (hg : g ^ N = 1) : ∃ v : Y ⟶ Γ.G.left, v ≫ Γ.G.hom = b ∧ v ≫ i = g.left := by
  subst hc
  obtain ⟨y, hy⟩ := (h.kernel (Over.mk b) g).1 hg
  exact ⟨y.left, Over.w y, hy⟩

end

theorem torsion_bc : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → IsSeparated G.hom → ∀ (R' : Type) [CommRing R'] [IsDomain R'] (φ : R →+* R') (Γ' : QFGroup R' T) (i' : Γ'.G.left ⟶ G.left), Γ'.IsTorsionAlong G (Spec.map (CommRingCat.ofHom φ) ≫ x) N i' → ∀ (B : Type) [CommRing B] (b : R →+* B) (j : B →+* FractionRing R) (j' : B →+* FractionRing R') (σ : T → (Spec (CommRingCat.of B) ⟶ G.left)), Function.Injective j → j.comp b = algebraMap R _ → j'.comp b = (algebraMap R' _).comp φ → (∀ t, σ t ≫ G.hom = Spec.map (CommRingCat.ofHom b) ≫ x) → (∀ t, Spec.map (CommRingCat.ofHom j) ≫ σ t = (Γ.pt t).left ≫ i) → (∀ t, Spec.map (CommRingCat.ofHom j') ≫ σ t = (Γ'.pt t).left ≫ i') → ∃ F : Γ'.G.left ⟶ Γ.G.left, F ≫ i = i' ∧ Γ'.IsBaseChange Γ φ F := by
  intro R _ _ T _ _ Γ S G _ _ x N i h hsep R' _ _ φ Γ' i' h' B _ b j j' σ hj hjb hj'b hσ hσj hσj'
  let g : Over.mk (i' ≫ G.hom) ⟶ G := Over.homMk i' rfl
  obtain ⟨F, hF1, hF2⟩ := pt_of_tors h (Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom φ))
    (h'.isOver.trans (Category.assoc _ _ _).symm) g (tors_of_pt h' (𝟙 _) g (Category.id_comp _).symm)
  replace hF2 : F ≫ i = i' := hF2
  refine ⟨F, hF2, ?_, fun Y y z y₀ z₀ hy hz => ?_, ?_⟩
  · have hl : ∀ c : PullbackCone Γ.G.hom (Spec.map (CommRingCat.ofHom φ)), ∃ v : c.pt ⟶ Γ'.G.left,
        v ≫ F = c.fst ∧ v ≫ Γ'.G.hom = c.snd := fun c => by
      let k : Over.mk ((c.fst ≫ i) ≫ G.hom) ⟶ G := Over.homMk (c.fst ≫ i) rfl
      obtain ⟨v, h1, h2⟩ := pt_of_tors h' c.snd
        (by rw [Category.assoc, h.isOver, ← Category.assoc, c.condition, Category.assoc]) k (tors_of_pt h c.fst k rfl)
      exact ⟨v, tors_ext h (by rw [Category.assoc, hF1, ← Category.assoc, h1, c.condition])
        (by rw [Category.assoc, hF2, h2]; rfl), h1⟩
    choose l h1 h2 using hl
    exact ⟨⟨hF1⟩, ⟨PullbackCone.IsLimit.mk hF1 l h1 h2 fun c m a1 a2 => tors_ext h' (a2.trans (h2 c).symm) (by
      rw [← hF2, ← Category.assoc, ← Category.assoc, a1, h1])⟩⟩
  · have w : ∀ {y₀ : Over.mk (Y.hom ≫ Spec.map (CommRingCat.ofHom φ)) ⟶ Γ.G},
        (y₀.left ≫ i) ≫ G.hom = (Y.hom ≫ Spec.map (CommRingCat.ofHom φ)) ≫ x := fun {y₀} => by
      rw [Category.assoc, h.isOver, ← Category.assoc, Over.w y₀]; rfl
    have w' : ∀ {y : Y ⟶ Γ'.G}, (y.left ≫ i') ≫ G.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ x := fun {y} => by
      rw [Category.assoc, h'.isOver, ← Category.assoc, Over.w y]
    refine tors_ext h ?_ ?_
    · rw [Category.assoc, hF1, ← Category.assoc, Over.w (y * z)]
      exact Over.w (y₀ * z₀)
    · refine (h.mul _ y₀ z₀ (Over.homMk (y₀.left ≫ i) w) (Over.homMk (z₀.left ≫ i) w) rfl rfl).symm.trans ?_
      rw [Category.assoc, hF2]
      refine Eq.trans ?_ (h'.mul Y y z (Over.homMk (y.left ≫ i') w') (Over.homMk (z.left ≫ i') w') rfl rfl)
      refine mul_congr (Category.assoc _ _ _) _ _ _ _ ?_ ?_
      · show y₀.left ≫ i = y.left ≫ i'
        rw [hy, Category.assoc, hF2]
      · show z₀.left ≫ i = z.left ≫ i'
        rw [hz, Category.assoc, hF2]
  · have : IsDomain B := hj.isDomain j
    have : IsDominant (Spec.map (CommRingCat.ofHom j)) := ⟨by
      have := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical j).2 (by
        rw [(RingHom.injective_iff_ker_eq_bot j).1 hj]; exact bot_le)
      exact this⟩
    have hσ' : ∀ t, ∃ v : Spec (CommRingCat.of B) ⟶ Γ.G.left,
        v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom b) ∧ v ≫ i = σ t := fun t => by
      let k : Over.mk (σ t ≫ G.hom) ⟶ G := Over.homMk (σ t) rfl
      refine pt_of_tors h _ (hσ t) k ?_
      let ψ : Over.mk (Spec.map (CommRingCat.ofHom j) ≫ σ t ≫ G.hom) ⟶ Over.mk (σ t ≫ G.hom) :=
        Over.homMk (Spec.map (CommRingCat.ofHom j)) rfl
      have h1 : ψ ≫ k ^ N = ψ ≫ 1 := by
        rw [comp_pow_pt, MonObj.comp_one]
        exact tors_of_pt h (Γ.pt t).left _ (hσj t)
      exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Spec (CommRingCat.of B)) G.hom
        ((Over.w _).trans (Over.w _).symm) (Spec.map (CommRingCat.ofHom j)) (congrArg (·.left) h1))
    choose v h1 h2 using hσ'
    refine ⟨B, inferInstance, b, j, j', v, hj, hjb, hj'b, h1, fun t => tors_ext h ?_ ?_, fun t => tors_ext h ?_ ?_⟩
    · rw [Category.assoc, h1, Over.w, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjb]; rfl
    · rw [Category.assoc, h2, hσj]
    · rw [Category.assoc, Category.assoc, h1, hF1, ← Category.assoc, Over.w, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, hj'b, CommRingCat.ofHom_comp, Spec.map_comp]; rfl
    · rw [Category.assoc, Category.assoc, h2, hF2, hσj']

end PositivityTheory.HtPt.Htat
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace PositivityTheory.HtPt.Mk

theorem gen_stalk {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) :
    Spec.map (CommRingCat.ofHom (genMap ξ p)) ≫ X.fromSpecStalk p.1 = ξ := by
  obtain ⟨q, hq⟩ := p
  have a := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hq
  have b := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have c : Spec.map (CommRingCat.ofHom (genMap ξ ⟨q, hq⟩)) =
      Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (X.presheaf.stalkSpecializes hq) :=
    Spec.map_comp _ _
  rw [c, Category.assoc]
  exact (congrArg (fun m => Spec.map (Scheme.stalkClosedPointTo ξ) ≫ m) a).trans b

theorem stalk_normal₀ {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hξ : IsCptGen ξ)
    (hN : Flat.NormalCpt ξ) (q : Cpt ξ) : ∃ (_ : IsDomain (X.presheaf.stalk q.1)),
      IsIntegrallyClosed (X.presheaf.stalk q.1) ∧ ∃ κ : FractionRing (X.presheaf.stalk q.1) ≃+* Ω,
        κ.toRingHom.comp (algebraMap _ _) = genMap ξ q := by
  have hd : IsDomain (X.presheaf.stalk q.1) := (hξ.inj q).isDomain _
  letI : Algebra (X.presheaf.stalk q.1) Ω := (genMap ξ q).toAlgebra
  have : FaithfulSMul (X.presheaf.stalk q.1) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 (hξ.inj q)
  have hf : IsFractionRing (X.presheaf.stalk q.1) Ω := by
    refine IsFractionRing.of_field _ _ fun a => ?_
    obtain ⟨b, c, hc, e⟩ := GlobalTheory.T.exists_stalk_fraction_of_generic ξ hξ q a
    exact ⟨b, c, (eq_div_iff hc).2 e⟩
  refine ⟨hd, ?_, (FractionRing.algEquiv _ Ω).toRingEquiv, RingHom.ext (FractionRing.algEquiv _ Ω).commutes⟩
  rw [isIntegrallyClosed_iff Ω]
  intro a ha
  exact hN q a (IsIntegral.map_of_comp_eq (genMap ξ q).rangeRestrict (RingHom.id Ω) (RingHom.ext fun _ => rfl) ha)

theorem ht_lat_chart : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ q : Cpt ξ, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (x : Spec (CommRingCat.of R) ⟶ X) (κ : FractionRing R ≃+* Ω), IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsOpenImmersion x ∧ q.1 ∈ Set.range x ∧ (∀ y ∈ Set.range x, genPt ξ ⤳ y) ∧ spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x = ξ := by
  intro X _ Ω _ _ ξ hξ hN q
  obtain ⟨U, hqU, hU, hinj⟩ := X.exists_germ_injective q.1
  let k₀ : Γ(X, U) →+* Ω := (genMap ξ q).comp (X.presheaf.germ U q.1 hqU).hom
  have hk : Function.Injective k₀ := (hξ.inj q).comp hinj
  have hd : IsDomain Γ(X, U) := hk.isDomain _
  have hx : Spec.map (CommRingCat.ofHom k₀) ≫ hU.fromSpec = ξ := by
    refine Eq.trans ?_ (gen_stalk ξ q)
    rw [← hU.fromSpecStalk_eq_fromSpecStalk hqU, IsAffineOpen.fromSpecStalk, ← Category.assoc, ← Spec.map_comp]
    rfl
  have hall : ∀ p : Spec Γ(X, U), genPt ξ ⤳ hU.fromSpec p := by
    intro p
    have e : genPt ξ = hU.fromSpec (Spec.map (CommRingCat.ofHom k₀) (IsLocalRing.closedPoint Ω)) := by
      rw [← hx]; rfl
    rw [e]
    refine Specializes.map ?_ hU.fromSpec.continuous
    refine (PrimeSpectrum.le_iff_specializes _ _).1 fun a ha => ?_
    have h1 : k₀ a ∈ IsLocalRing.maximalIdeal Ω := ha
    rw [IsLocalRing.maximalIdeal_eq_bot] at h1
    rw [hk (h1.trans (map_zero k₀).symm)]
    exact Ideal.zero_mem _
  letI : Algebra Γ(X, U) Ω := k₀.toAlgebra
  have : FaithfulSMul Γ(X, U) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hk
  have hf : IsFractionRing Γ(X, U) Ω := by
    refine IsFractionRing.of_field _ _ fun a => ?_
    obtain ⟨b, c, hc, e⟩ := GlobalTheory.T.exists_stalk_fraction_of_generic ξ hξ q a
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨q.1, hqU⟩ : U)
    have hl := hU.isLocalization_stalk ⟨q.1, hqU⟩
    obtain ⟨⟨b₁, s⟩, hb⟩ := IsLocalization.surj (hU.primeIdealOf ⟨q.1, hqU⟩).asIdeal.primeCompl
      (S := X.presheaf.stalk q.1) b
    obtain ⟨⟨c₁, t⟩, hc'⟩ := IsLocalization.surj (hU.primeIdealOf ⟨q.1, hqU⟩).asIdeal.primeCompl
      (S := X.presheaf.stalk q.1) c
    have hb' : genMap ξ q b * k₀ s = k₀ b₁ := by
      have := congrArg (genMap ξ q) hb
      rwa [map_mul] at this
    have hc'' : genMap ξ q c * k₀ t = k₀ c₁ := by
      have := congrArg (genMap ξ q) hc'
      rwa [map_mul] at this
    have hne : ∀ s : (hU.primeIdealOf ⟨q.1, hqU⟩).asIdeal.primeCompl, k₀ s ≠ 0 := fun s h =>
      s.2 (by rw [hk (h.trans (map_zero k₀).symm)]; exact Ideal.zero_mem _)
    refine ⟨b₁ * t, c₁ * s, ?_⟩
    change a = k₀ (b₁ * t) / k₀ (c₁ * s)
    rw [map_mul, map_mul, ← hb', ← hc'', ← e, eq_div_iff (mul_ne_zero (mul_ne_zero hc (hne t)) (hne s))]
    ring
  refine ⟨Γ(X, U), inferInstance, hd, hU.fromSpec, (FractionRing.algEquiv _ Ω).toRingEquiv,
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩, ?_, inferInstance, ?_, ?_, ?_⟩
  · refine IsIntegrallyClosed.of_localization_maximal fun p _ hp => ?_
    let P : PrimeSpectrum Γ(X, U) := ⟨p, hp.isPrime⟩
    have hy : hU.fromSpec P ∈ U := by
      rw [← SetLike.mem_coe, ← hU.range_fromSpec]
      exact ⟨P, rfl⟩
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨_, hy⟩ : U)
    have hl : IsLocalization p.primeCompl (X.presheaf.stalk (hU.fromSpec P)) := hU.isLocalization_stalk' P hy
    obtain ⟨_, hic, -⟩ := stalk_normal₀ hξ hN ⟨_, hall P⟩
    exact IsIntegrallyClosed.of_equiv (R := X.presheaf.stalk (hU.fromSpec P))
      (IsLocalization.algEquiv p.primeCompl (X.presheaf.stalk (hU.fromSpec P)) (Localization.AtPrime p)).toRingEquiv
  · rw [hU.range_fromSpec]
    exact hqU
  · rintro _ ⟨p, rfl⟩
    exact hall p
  · have e : (FractionRing.algEquiv Γ(X, U) Ω).toRingEquiv.toRingHom.comp (algebraMap _ _) = k₀ :=
      RingHom.ext (FractionRing.algEquiv _ Ω).commutes
    rw [e]
    exact hx

end PositivityTheory.HtPt.Mk
end
end

section

noncomputable section

namespace PositivityTheory.HtPt.Flagb

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem unitAt_of_isUnit (q : Cpt ξ) (u : X.presheaf.stalk q.1) (hu : IsUnit u) : unitAt ξ q (genMap ξ q u) := by
  obtain ⟨u, rfl⟩ := hu
  refine ⟨(u.isUnit.map _).ne_zero, ⟨_, rfl⟩, ⟨(u⁻¹ : _ˣ), map_units_inv _ u⟩⟩

def secMap (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (hg : genPt ξ ∈ U) : Γ(X, U) →+* Ω :=
  (Scheme.stalkClosedPointTo ξ).hom.comp (X.presheaf.germ U (ξ (IsLocalRing.closedPoint Ω)) hg).hom

theorem genMap_germ (q : Cpt ξ) (U : X.Opens) (hq : q.1 ∈ U) (hg : genPt ξ ∈ U) (f : Γ(X, U)) :
    genMap ξ q ((X.presheaf.germ U q.1 hq).hom f) = secMap ξ U hg f := by
  obtain ⟨q, h⟩ := q
  have := X.presheaf.germ_stalkSpecializes_apply (x := ξ (IsLocalRing.closedPoint Ω)) hq h f
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom this

theorem exists_point {κ : Type} {x : κ → Ω} (tie : CoordTie ℤ ξ x) (c : κ) (hc : x c ≠ 0) {o : Type} [CommRing o]
    [Algebra o Ω] (A : Subalgebra o Ω) (hA : ∀ j, x j / x c ∈ A) (m : Ideal A) [hm : m.IsPrime] :
    ∃ q : Cpt ξ, InChart ξ x c q ∧ (∀ z ∈ regAt ξ q, ∃ s ∉ m, ∃ a : A, (s : Ω) * z = a) ∧
      ∀ n : ℕ, (n : A) ∉ m → unitAt ξ q (n : Ω) := by
  obtain ⟨U, hU, hUm⟩ := tie.affine c hc
  have hreg : ∀ a : Ω, a ∈ regAt ξ ⟨genPt ξ, specializes_rfl⟩ := by
    intro a
    obtain ⟨s, hs⟩ := tie.gen.bij.2 a
    refine ⟨s, ?_⟩
    unfold genMap
    have : X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) = 𝟙 _ :=
      X.presheaf.stalkSpecializes_refl _
    erw [this, Category.id_comp]
    exact hs
  have hg : genPt ξ ∈ U := (hUm _).2 ⟨specializes_rfl, hc, fun c' => hreg _⟩
  let ψ : Γ(X, U) →+* Ω := secMap ξ U hg
  have hψ : ∀ (q : Cpt ξ) (hq : q.1 ∈ U) (f : Γ(X, U)), genMap ξ q ((X.presheaf.germ U q.1 hq).hom f) = ψ f := by
    intro q hq f
    exact genMap_germ q U hq hg f
  have hψA : ∀ f, ψ f ∈ A := by
    intro f
    have h1 : ψ f ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) :=
      (tie.ring c hc _).2 fun q hq => ⟨_, hψ q ((hUm _).2 ⟨q.2, hq⟩) f⟩
    have h2 : Algebra.adjoin ℤ (Set.range fun j => x j / x c) ≤ subalgebraOfSubring A.toSubring :=
      Algebra.adjoin_le (by rintro _ ⟨j, rfl⟩; exact hA j)
    exact h2 h1
  let ψA : Γ(X, U) →+* A := ψ.codRestrict A hψA
  let 𝔭 : PrimeSpectrum Γ(X, U) := ⟨m.comap ψA, inferInstance⟩
  have hq : hU.fromSpec 𝔭 ∈ U := by
    have : hU.fromSpec 𝔭 ∈ Set.range hU.fromSpec := ⟨_, rfl⟩
    rwa [hU.range_fromSpec] at this
  obtain ⟨hs, hin⟩ := (hUm _).1 hq
  letI : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec 𝔭)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec 𝔭, hq⟩
  have hloc : IsLocalization 𝔭.asIdeal.primeCompl (X.presheaf.stalk (hU.fromSpec 𝔭)) :=
    hU.isLocalization_stalk' 𝔭 hq
  have hal : ∀ f, genMap ξ ⟨_, hs⟩ (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec 𝔭)) f) = ψ f :=
    fun f => hψ ⟨_, hs⟩ hq f
  refine ⟨⟨_, hs⟩, hin, ?_, fun n hn => ?_⟩
  · rintro _ ⟨z, rfl⟩
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (S := X.presheaf.stalk (hU.fromSpec 𝔭)) 𝔭.asIdeal.primeCompl z
    refine ⟨ψA s, s.2, ψA a, ?_⟩
    have := congrArg (genMap ξ ⟨_, hs⟩) h
    rw [map_mul, hal, hal] at this
    exact (mul_comm _ _).trans this
  · have hn' : (n : Γ(X, U)) ∈ 𝔭.asIdeal.primeCompl := by
      show ψA n ∉ m
      rwa [map_natCast]
    have := unitAt_of_isUnit ⟨_, hs⟩ _ (IsLocalization.map_units (X.presheaf.stalk (hU.fromSpec 𝔭)) ⟨_, hn'⟩)
    rwa [hal, map_natCast] at this

theorem unitAt_nat (q : Cpt ξ) (n : ℕ) (hn : n ≠ 0) (h : ∀ r : ℕ, r.Prime → r ∣ n → unitAt ξ q (r : Ω)) :
    unitAt ξ q (n : Ω) := by
  induction n using induction_on_primes with
  | zero => exact absurd rfl hn
  | one => exact ⟨by simp, by simpa using one_mem _, by simpa using one_mem _⟩
  | prime_mul p a hp ih =>
    have h1 := h p hp (dvd_mul_right _ _)
    have h2 := ih (right_ne_zero_of_mul hn) fun r hr hd => h r hr (hd.mul_left _)
    rw [Nat.cast_mul]
    exact ⟨mul_ne_zero h1.1 h2.1, mul_mem h1.2.1 h2.2.1, by rw [mul_inv]; exact mul_mem h1.2.2 h2.2.2⟩

theorem lat_stable {G : Over X} [GrpObj G] {L : Type} [AddCommGroup L] [Module Ω L] (M : LieModel G ξ L)
    (f : G ⟶ G) [IsMonHom f] (T : L →ₗ[Ω] L) (hT : M.IsDiffOf f T) (q : Cpt ξ) (e : L) (he : e ∈ M.lat q) :
    T e ∈ M.lat q := by
  induction he using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, h1, h2⟩ := hx
    refine Submodule.subset_span ⟨v ≫ f, ?_, ?_⟩
    · unfold IsTanAt at h1 ⊢
      rw [Over.comp_left, ← Category.assoc, h1, ← Over.comp_left, MonObj.one_comp]
    · rw [hT x, Over.comp_left, Over.comp_left, h2]
      exact Category.assoc _ _ _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    have : T (c • x) = c • T x := map_smul T (c : Ω) x
    rw [this]; exact Submodule.smul_mem _ c hx

end PositivityTheory.HtPt.Flagb
end
end

section

noncomputable section

namespace PositivityTheory.HtPt.Flagb

open AlgebraicGeometry CategoryTheory NumberField GlobalTheory.CompanionTheory.Ar

variable {Ω L : Type} [Field Ω] [AddCommGroup L] [Module Ω L]

theorem exists_lead {r : ℕ} (b₀ b : Fin r → L) (hF : ∀ i, flagStep Ω b i = flagStep Ω b₀ i) (i : Fin r) :
    ∃ τ : Ω, b i - τ • b₀ i ∈ flagStep Ω b₀ i := by
  have h1 : b i ∈ flagStep Ω b₀ (i + 1) := by
    rw [← hF]; exact Submodule.subset_span ⟨i, by simp, rfl⟩
  have h2 : b₀ '' {k | (k : ℕ) < i + 1} = insert (b₀ i) (b₀ '' {k | (k : ℕ) < i}) := by
    rw [← Set.image_insert_eq]
    congr 1
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Fin.ext_iff]
    omega
  unfold flagStep at h1
  rw [h2, Submodule.mem_span_insert] at h1
  obtain ⟨a, z, hz, h⟩ := h1
  exact ⟨a, by rw [h, add_sub_cancel_left]; exact hz⟩

theorem div_mem_of_span (R : Subring Ω) {a c : Ω} (h : a ∈ Submodule.span R {c}) : a / c ∈ R := by
  obtain ⟨u, rfl⟩ := Submodule.mem_span_singleton.1 h
  by_cases hc : c = 0
  · simp [hc]
  · show (u : Ω) * c / c ∈ R
    rw [mul_div_cancel_right₀ _ hc]; exact u.2

theorem tens_gen {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} (Λ : Lat ξ Ω) (q : Cpt ξ) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (τ c : Ω) (h : Λ.IsGenAt q τ)
    (hc : Lat.tens (fun _ : Unit => Λ) (fun _ => ε) q = Submodule.span (regAt ξ q) {c}) :
    τ ^ ε / c ∈ regAt ξ q ∧ c / τ ^ ε ∈ regAt ξ q := by
  constructor
  · refine div_mem_of_span _ ?_
    rw [← hc]
    exact Submodule.subset_span ⟨fun _ => τ, fun _ => h, by simp⟩
  · refine div_mem_of_span _ ?_
    have : Lat.tens (fun _ : Unit => Λ) (fun _ => ε) q ≤ Submodule.span (regAt ξ q) {τ ^ ε} := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨s, hs, rfl⟩
      replace hs : ∀ i, Λ.IsGenAt q (s i) := hs
      have h1 : s () / τ ∈ regAt ξ q := div_mem_of_span _ (by
        rw [← h.2, (hs ()).2]; exact Submodule.mem_span_singleton_self _)
      have h2 : τ / s () ∈ regAt ξ q := div_mem_of_span _ (by
        rw [← (hs ()).2, h.2]; exact Submodule.mem_span_singleton_self _)
      have h3 := h.1
      have h4 := (hs ()).1
      rcases hε with rfl | rfl
      · refine Submodule.mem_span_singleton.2 ⟨⟨_, h1⟩, ?_⟩
        show s () / τ * τ ^ (1 : ℤ) = _
        simp [h3]
      · refine Submodule.mem_span_singleton.2 ⟨⟨_, h2⟩, ?_⟩
        show τ / s () * τ ^ (-1 : ℤ) = _
        simp
        field_simp
    exact this (hc ▸ Submodule.mem_span_singleton_self _)

theorem mem_span_of_dual {V : Type} [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V] (R : Subring Ω) {r : ℕ}
    (f : Fin r → Module.Dual Ω V) (hf : LinearIndependent Ω f) (hs : Submodule.span Ω (Set.range f) = ⊤)
    (u : Module.Dual Ω V) (hu : ∀ e : V, (∀ j, f j e ∈ R) → u e ∈ R) : u ∈ Submodule.span R (Set.range f) := by
  classical
  let B : Module.Basis (Fin r) Ω (Module.Dual Ω V) := Module.Basis.mk hf hs.ge
  have hB : ∀ j, B j = f j := fun j => Module.Basis.mk_apply _ _ j
  have h1 : ∀ j, B.repr u j ∈ R := by
    intro j
    have h2 : ∀ w : Module.Dual Ω V, w ((Module.evalEquiv Ω V).symm (B.coord j)) = B.repr w j := fun w => by
      rw [Module.apply_evalEquiv_symm_apply]; rfl
    rw [← h2]
    refine hu _ fun i => ?_
    rw [h2, ← hB, B.repr_self, Finsupp.single_apply]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  rw [← B.sum_repr u]
  refine Submodule.sum_mem _ fun j _ => ?_
  exact Submodule.smul_mem (Submodule.span R (Set.range f)) (⟨_, h1 j⟩ : R) (Submodule.subset_span ⟨j, (hB j).symm⟩)

theorem apply_mem_of_span (R : Subring Ω) (w : Module.Dual Ω L) (s : Set L) (h : ∀ x ∈ s, w x ∈ R) (e : L)
    (he : e ∈ Submodule.span R s) : w e ∈ R := by
  induction he using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => rw [map_zero]; exact R.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    have : w (c • x) = (c : Ω) * w x := map_smul w (c : Ω) x
    rw [this]; exact mul_mem c.2 hx

theorem exists_nat_diff {E : Type} [Field E] [NumberField E] (x : E) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ δ ∈ differentIdeal ℤ (𝓞 E), (δ : E) = n * x := by
  obtain ⟨y, hy, hi⟩ := (show IsAlgebraic ℤ x from
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic x)).exists_integral_multiple
  obtain ⟨z, hz⟩ : ∃ z : 𝓞 E, algebraMap (𝓞 E) E z = y * x := ⟨⟨y • x, hi⟩, by rw [← zsmul_eq_mul]; rfl⟩
  have hN := Ideal.absNorm_mem (differentIdeal ℤ (𝓞 E))
  have hN0 : Ideal.absNorm (differentIdeal ℤ (𝓞 E)) ≠ 0 := fun h =>
    differentIdeal_ne_bot (A := ℤ) (B := 𝓞 E) (Ideal.absNorm_eq_zero_iff.1 h)
  refine ⟨Ideal.absNorm (differentIdeal ℤ (𝓞 E)) * y.natAbs ^ 2, mul_ne_zero hN0 (pow_ne_zero _ (by simpa using hy)),
    _, Ideal.mul_mem_right ((y : 𝓞 E) * z) _ hN, ?_⟩
  have : ((y.natAbs ^ 2 : ℕ) : E) = (y : E) * y := by
    rw [← Int.cast_natCast, Nat.cast_pow, Int.natAbs_sq, Int.cast_pow, sq]
  rw [Nat.cast_mul, this]
  simp only [map_mul, map_natCast, map_intCast]
  rw [hz]; ring

end PositivityTheory.HtPt.Flagb
end
end
