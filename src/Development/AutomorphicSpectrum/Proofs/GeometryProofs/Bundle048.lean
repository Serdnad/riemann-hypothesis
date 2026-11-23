module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle022
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtOfMulRight
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.TypeStar
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PatchIso

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem unitAt_congr {X' : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω) ⟶ X'}
    {p : Cpt ξ} {p' : Cpt ξ'} (h : regAt ξ' p' = regAt ξ p) (a : Ω) : unitAt ξ' p' a ↔ unitAt ξ p a := by
  unfold unitAt
  rw [h]

theorem char_zero_congr {X' : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω) ⟶ X'}
    {p : Cpt ξ} {p' : Cpt ξ'} (h : regAt ξ' p' = regAt ξ p) (hp : Char0 ξ p) : Char0 ξ' p' := fun r hr hf =>
  hp r hr fun hu => hf ((unitAt_congr h _).2 hu)

theorem mem_genFib_of_char0 [CharZero Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ} (hp : Char0 ξ p) :
    p ∈ genFib ξ := by
  have key : ∀ n : ℕ, 0 < n → ((n : Ω))⁻¹ ∈ regAt ξ p := by
    intro n
    induction n using induction_on_primes with
    | zero => exact fun h => absurd h (lt_irrefl 0)
    | one => intro _; simpa using (regAt ξ p).one_mem
    | prime_mul r a hr ih =>
      intro h
      have ha : 0 < a := Nat.pos_of_mul_pos_left h
      have hu : unitAt ξ p (r : Ω) := not_not.1 (hp r hr)
      rw [Nat.cast_mul, mul_inv]
      exact mul_mem hu.2.2 (ih ha)
  exact fun n hn => ⟨Nat.cast_ne_zero.2 hn.ne', natCast_mem _ n, key n hn⟩

theorem exists_below [CharZero Ω] {X₁ X₂ : Scheme.{0}} {ξ₁ : Spec (CommRingCat.of Ω) ⟶ X₁}
    {ξ₂ : Spec (CommRingCat.of Ω) ⟶ X₂} {g : X₂ ⟶ X₁} (hg : IsCptGen ξ₂)
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ₂ ξ₁ g (RingHom.id Ω))
    (hi : ∀ q ∈ genFib ξ₁, IsoAt ξ₂ g (RingHom.id Ω) q) (p : Cpt ξ₂) (hp : Char0 ξ₂ p) :
    ∃ p₁ : Cpt ξ₁, p₁.1 = g p.1 ∧ Char0 ξ₁ p₁ ∧ regAt ξ₂ p = regAt ξ₁ p₁ := by
  obtain ⟨h, -, hu⟩ := RegAtDom.regAt_dominates X₁ Ω ξ₁ X₂ Ω ξ₂ g (RingHom.id Ω) hd p
  have c : Char0 ξ₁ ⟨g p.1, h⟩ := fun r hr hf =>
    hf (hu hg (r : Ω) (natCast_mem _ r) (not_not.1 (hp r hr)))
  refine ⟨⟨g p.1, h⟩, rfl, c, ?_⟩
  rw [(hi _ (mem_genFib_of_char0 c)).regAt_eq p rfl, Subring.map_id]

theorem exists_above [CharZero Ω] {X₁ X₂ : Scheme.{0}} {ξ₁ : Spec (CommRingCat.of Ω) ⟶ X₁}
    {ξ₂ : Spec (CommRingCat.of Ω) ⟶ X₂} {g : X₂ ⟶ X₁}
    (hi : ∀ q ∈ genFib ξ₁, IsoAt ξ₂ g (RingHom.id Ω) q) (p₁ : Cpt ξ₁) (hp : Char0 ξ₁ p₁) :
    ∃ p : Cpt ξ₂, g p.1 = p₁.1 ∧ Char0 ξ₂ p ∧ regAt ξ₂ p = regAt ξ₁ p₁ := by
  have I := hi p₁ (mem_genFib_of_char0 hp)
  obtain ⟨p, hp', -⟩ := I.existsUnique
  have e : regAt ξ₂ p = regAt ξ₁ p₁ := by rw [I.regAt_eq p hp', Subring.map_id]
  exact ⟨p, hp', char_zero_congr e hp, e⟩

theorem sncPts_of_isoAt :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ₁ κ₂ : Type) (x₁ : κ₁ → Ω) (x₂ : κ₂ → Ω) (X₁ X₂ : Scheme.{0}) (ξ₁ : Sp Ω ⟶ X₁) (ξ₂ : Sp Ω ⟶ X₂) (g : X₂ ⟶ X₁) (e : ℕ) (Ab : Set X₁), (∀ q : X₁, genPt ξ₁ ⤳ q) → (∀ q : X₂, genPt ξ₂ ⤳ q) → CoordTie ℤ ξ₁ x₁ → CoordTie ℤ ξ₂ x₂ → GlobalTheory.CompanionTheory.Ar.Dominates ξ₂ ξ₁ g (RingHom.id Ω) → (∀ q ∈ genFib ξ₁, IsoAt ξ₂ g (RingHom.id Ω) q) → SncPts ξ₁ e {p | Char0 ξ₁ p ∧ p.1 ∉ Ab} → SncPts ξ₂ e {p | Char0 ξ₂ p ∧ g p.1 ∉ Ab} := by
  intro Ω _ _ κ₁ κ₂ x₁ x₂ X₁ X₂ ξ₁ ξ₂ g e Ab _ _ _ t₂ hd hi hs p hp
  have ePts : Pts ξ₂ = Pts ξ₁ := by
    ext R
    constructor
    · rintro ⟨p₂, c, rfl⟩
      obtain ⟨p₁, -, c₁, r⟩ := exists_below t₂.gen hd hi p₂ c
      exact ⟨p₁, c₁, r⟩
    · rintro ⟨p₁, c, rfl⟩
      obtain ⟨p₂, -, c₂, r⟩ := exists_above hi p₁ c
      exact ⟨p₂, c₂, r.symm⟩
  have eB : regAt ξ₂ '' {p | Char0 ξ₂ p ∧ g p.1 ∉ Ab} = regAt ξ₁ '' {p | Char0 ξ₁ p ∧ p.1 ∉ Ab} := by
    ext R
    constructor
    · rintro ⟨p₂, ⟨c, ha⟩, rfl⟩
      obtain ⟨p₁, e₁, c₁, r⟩ := exists_below t₂.gen hd hi p₂ c
      exact ⟨p₁, ⟨c₁, e₁ ▸ ha⟩, r.symm⟩
    · rintro ⟨p₁, ⟨c, ha⟩, rfl⟩
      obtain ⟨p₂, e₂, c₂, r⟩ := exists_above hi p₁ c
      exact ⟨p₂, ⟨c₂, by rwa [e₂]⟩, r⟩
  obtain ⟨p₁, -, c₁, r⟩ := exists_below t₂.gen hd hi p hp
  obtain ⟨A, z, n, q, hP, hq, hl⟩ := hs p₁ c₁
  refine ⟨A, z, n, q, ?_, hq, ?_⟩
  · rw [ePts, eB]
    exact hP
  · rw [r]
    exact hl

end GlobalTheory.CompanionTheory.Ar.PatchIso
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.char_zero_iff_nonzero_units : ∀ (F : Type) [Field F] [NumberField F] (Ω : Type) [Field Ω] [Algebra (𝓞 F) Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (κ : Type) (t : κ → Ω), CoordTie (𝓞 F) ξ t → ∀ p : Cpt ξ, Char0 ξ p ↔ ∀ d : 𝓞 F, d ≠ 0 → unitAt ξ p (algebraMap (𝓞 F) Ω d) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.CharTie.char_zero_iff_integers_units | exact GlobalTheory.CompanionTheory.Ar.SncBase.CharTie.char_zero_iff_integers_units | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.CharTie.char_zero_iff_integers_units <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

theorem regAt_generic_eq_top {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hg : IsCptGen ξ) (a : Ω) : a ∈ regAt ξ ⟨genPt ξ, specializes_rfl⟩ := by
  obtain ⟨s, hs⟩ := hg.bij.2 a
  refine (RingHom.mem_range).2 ⟨s, ?_⟩
  show (X.presheaf.stalkSpecializes (specializes_refl (genPt ξ)) ≫ Scheme.stalkClosedPointTo ξ).hom s = a
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact hs

theorem exists_leftInverse_flagForms (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (L : Lat ξ E) (r : ℕ)
    (V : Submodule Ω E) (m n : ℕ) (φ : Fin n → Module.Dual Ω E) (c : Fin r → E)
    (hT : CoordTie ℤ ξ x) (hV : L.IsVB r V) (hG : IsTwistGen ξ x L m φ)
    (hc : LinearIndependent Ω c) (hs : Submodule.span Ω (Set.range c) = V) :
    ∃ B : Matrix (Fin r) (Fin n) Ω, B * Matrix.of (fun j l => φ j (c l)) = 1 := by
  let p₀ : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩
  have hreg : ∀ a : Ω, a ∈ regAt ξ p₀ := fun a => regAt_generic_eq_top hT.gen a
  obtain ⟨k, hk⟩ := hT.cover p₀
  unfold Lat.IsVB Lat.IsVBOn at hV
  obtain ⟨U, hU, b, hbV, hbF⟩ := hV p₀ (Set.mem_univ _)
  obtain ⟨-, hLp⟩ := hbF p₀ (Set.mem_univ _) hU
  obtain ⟨-, hG2⟩ := hG
  have hw0 : ∀ i : Fin r, ∃ w : Module.Dual Ω E, ∀ l, w (c l) = if i = l then 1 else 0 := by
    intro i
    obtain ⟨w, hwf⟩ := LinearMap.exists_extend ((Module.Basis.span hc).coord i)
    refine ⟨w, fun l => ?_⟩
    have h1 : w (c l) = (Module.Basis.span hc).coord i (Module.Basis.span hc l) := by
      rw [← hwf]
      simp [Module.Basis.span_apply]
    rw [h1, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h : i = l
    · subst h
      simp
    · simp [h, Ne.symm h]
  choose w hw using hw0
  have hg0 : ∀ i, ∃ g : Fin n → Ω, (∀ j, g j ∈ regAt ξ p₀) ∧
      ∀ e ∈ L p₀, w i e = ∑ j, g j * (φ j e / x k ^ m) :=
    fun i => hG2 p₀ k hk (w i) (fun e _ => hreg _)
  choose g hgr hg using hg0
  have key : ∀ i, ∀ e ∈ V, w i e = ∑ j, g i j / x k ^ m * φ j e := by
    intro i
    obtain ⟨ψ, hψdef⟩ : ∃ ψ : E →ₗ[Ω] Ω, ψ = ∑ j, (g i j / x k ^ m) • φ j := ⟨_, rfl⟩
    have hψ : ∀ e, ψ e = ∑ j, g i j / x k ^ m * φ j e := by
      intro e
      rw [hψdef]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    have heq : Set.EqOn (w i) ψ (Set.range b) := by
      rintro _ ⟨t, rfl⟩
      have hbt : b t ∈ L p₀ := by
        rw [hLp]
        exact Submodule.subset_span ⟨t, rfl⟩
      rw [hg i (b t) hbt, hψ]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    intro e he
    rw [← hbV] at he
    rw [LinearMap.eqOn_span' heq he, hψ]
  refine ⟨Matrix.of fun i j => g i j / x k ^ m, ?_⟩
  ext i l
  have hcl : c l ∈ V := by
    rw [← hs]
    exact Submodule.subset_span ⟨l, rfl⟩
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [← key i (c l) hcl, hw i l]

end GlobalTheory.CompanionTheory.Ar.FlagBun
end
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.GenericColumns

theorem det_eq_one {K : Type*} [Field K] {n : ℕ} (u : Matrix (Fin n) (Fin n) K)
    (h1 : ∀ k, u k k = 1) (h0 : ∀ l k, l < k → u l k = 0) : u.det = 1 := by
  rw [Matrix.det_of_lowerTriangular u (fun i j hij => h0 _ _ hij)]
  simp [h1]

theorem linearIndependent_cols {K M : Type*} [Field K] [AddCommGroup M] [Module K M] {n : ℕ}
    (u : Matrix (Fin n) (Fin n) K) (h1 : ∀ k, u k k = 1) (h0 : ∀ l k, l < k → u l k = 0)
    (v : Fin n → M) (hv : LinearIndependent K v) :
    LinearIndependent K fun k => ∑ l, u l k • v l := by
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro g hg
  have hz : ∀ l, ∑ k, u l k * g k = 0 := by
    apply hv (fun l => ∑ k, u l k * g k)
    rw [← hg]
    simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by rw [mul_comm]
  have hm : u.mulVec g = 0 := funext hz
  have hg0 := Matrix.eq_zero_of_mulVec_eq_zero (by rw [det_eq_one u h1 h0]; exact one_ne_zero) hm
  intro i
  exact congrFun hg0 i

theorem span_cols {K M : Type*} [Field K] [AddCommGroup M] [Module K M] {n : ℕ}
    (u : Matrix (Fin n) (Fin n) K) (h1 : ∀ k, u k k = 1) (h0 : ∀ l k, l < k → u l k = 0)
    (v : Fin n → M) :
    Submodule.span K (Set.range fun k => ∑ l, u l k • v l) = Submodule.span K (Set.range v) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨m, rfl⟩
    have hu : u * u⁻¹ = 1 := Matrix.mul_nonsing_inv u (by rw [det_eq_one u h1 h0]; exact isUnit_one)
    have hvm : v m = ∑ k, u⁻¹ k m • ∑ l, u l k • v l := by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      have hl : ∀ l, ∑ k, (u⁻¹ k m * u l k) • v l = (if l = m then (1 : K) else 0) • v l := by
        intro l
        rw [← Finset.sum_smul]
        congr 1
        have := congrFun (congrFun hu l) m
        rw [Matrix.mul_apply, Matrix.one_apply] at this
        rw [← this]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      simp [hl]
    show v m ∈ _
    rw [hvm]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem genU_diag (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S) (k : Fin (r s)) :
    genU Ω r s k k = 1 := by
  simp [genU]

theorem genU_zero (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S) (l k : Fin (r s)) (h : l < k) :
    genU Ω r s l k = 0 := by
  have h1 : ¬ k < l := not_lt.2 h.le
  have h2 : l ≠ k := h.ne
  simp [genU, h1, h2]

theorem genU_gen (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (q : GenIx r) :
    genU Ω r q.1 q.2.1.1 q.2.1.2 =
      algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q) := by
  obtain ⟨s, ⟨⟨l, k⟩, h⟩⟩ := q
  exact dif_pos h

theorem algebraicIndependent_gen (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) :
    AlgebraicIndependent Ω (fun q : GenIx r =>
      algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q)) :=
  (MvPolynomial.algebraicIndependent_X (GenIx r) Ω).map'
    (f := IsScalarTower.toAlgHom Ω (MvPolynomial (GenIx r) Ω) (GenField Ω r))
    (IsFractionRing.injective _ _)

theorem algebraicIndependent_comp {Ω₀ Ω K I : Type} [Field Ω₀] [Field Ω] [Field K] [Algebra Ω K]
    (fn : Ω₀ →+* Ω) {x : I → K} (hx : AlgebraicIndependent Ω x) :
    letI := ((algebraMap Ω K).comp fn).toAlgebra;
    AlgebraicIndependent Ω₀ x := by
  letI a1 : Algebra Ω₀ Ω := fn.toAlgebra
  letI a2 : Algebra Ω₀ K := ((algebraMap Ω K).comp fn).toAlgebra
  haveI : IsScalarTower Ω₀ Ω K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact hx.restrictScalars (R := Ω₀) (K := Ω) fn.injective

theorem adjoin_entries {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] (fn : Ω₀ →+* Ω) {S : Type} (r : S → ℕ) :
    letI := ((algebraMap Ω (GenField Ω r)).comp fn).toAlgebra;
    IntermediateField.adjoin Ω₀
        (Set.range fun q : Σ s, Fin (r s) × Fin (r s) => genU Ω r q.1 q.2.1 q.2.2) =
      IntermediateField.adjoin Ω₀ (Set.range fun q : GenIx r =>
        algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q)) := by
  letI := ((algebraMap Ω (GenField Ω r)).comp fn).toAlgebra
  apply le_antisymm
  · refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨⟨s, l, k⟩, rfl⟩
    show genU Ω r s l k ∈ _
    by_cases h : k < l
    · have := genU_gen Ω r ⟨s, ⟨(l, k), h⟩⟩
      exact this ▸ IntermediateField.subset_adjoin _ _ ⟨_, rfl⟩
    · by_cases e : l = k
      · subst e
        rw [genU_diag]
        exact one_mem _
      · rw [genU_zero Ω r s l k (lt_of_le_of_ne (not_lt.1 h) e)]
        exact zero_mem _
  · refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨q, rfl⟩
    show algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q) ∈ _
    rw [← genU_gen]
    exact IntermediateField.subset_adjoin _ _ ⟨⟨q.1, q.2.1.1, q.2.1.2⟩, rfl⟩

theorem isGenericFlag_columns : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (fn : Ω₀ →+* Ω) (S : Type) (r : S → ℕ) (d : ℕ), 0 < d → (letI := ((algebraMap Ω (GenField Ω r)).comp fn).toAlgebra; Module.finrank (IntermediateField.adjoin Ω₀ (Set.range fun q : GenIx r => algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q))) (GenField Ω r) = d) → ∀ (E₀ E' : Type) [AddCommGroup E₀] [Module Ω₀ E₀] [AddCommGroup E'] [Module (GenField Ω r) E'] (j : E₀ →+ E') (V₀ : S → Submodule Ω₀ E₀) (c : ∀ s, Fin (r s) → E₀), (∀ s, LinearIndependent Ω₀ (c s) ∧ Submodule.span Ω₀ (Set.range (c s)) = V₀ s) → (∀ (a : Ω₀) e, j (a • e) = algebraMap Ω (GenField Ω r) (fn a) • j e) → (∀ s, LinearIndependent (GenField Ω r) fun k => j (c s k)) → (∀ s, Submodule.span (GenField Ω r) (Set.range fun k => ∑ l, genU Ω r s l k • j (c s l)) = Submodule.span (GenField Ω r) (Set.range fun k => j (c s k))) ∧ (letI := ((algebraMap Ω (GenField Ω r)).comp fn).toAlgebra; IsGenericFlag (Ω' := GenField Ω r) j V₀ (fun s k => ∑ l, genU Ω r s l k • j (c s l)) d) := by
  intro Ω₀ Ω _ _ fn S r d hd hdeg E₀ E' _ _ _ _ j V₀ c hc hj hli
  refine ⟨fun s => span_cols _ (genU_diag Ω r s) (genU_zero Ω r s) _, ?_⟩
  letI := ((algebraMap Ω (GenField Ω r)).comp fn).toAlgebra
  refine ⟨c, genU Ω r, hc, hj, hli,
    fun s => linearIndependent_cols _ (genU_diag Ω r s) (genU_zero Ω r s) _ (hli s),
    genU_diag Ω r, genU_zero Ω r, fun _ _ => rfl, ?_, hd, ?_⟩
  · have h := algebraicIndependent_comp fn (algebraicIndependent_gen Ω r)
    have he : (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} =>
        genU Ω r q.1 q.2.1.1 q.2.1.2) = fun q : GenIx r =>
        algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q) :=
      funext (genU_gen Ω r)
    rw [he]
    exact h
  · rw [adjoin_entries fn r]
    exact hdeg

end GlobalTheory.CompanionTheory.Ar.FlagBun.GenericColumns
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem inChart_flagCoord_ratios : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (S : Type) [Fintype S] (r n : S → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω r)) ⟶ X') (p' : Cpt ξ') (c₁ : κ) (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), InChart ξ' (flagCoord κ x φ c) ((c₁, J) : FlagIx κ n r) p' → algebraMap Ω (GenField Ω r) (x c₁) ≠ 0 ∧ InChart ξ' (fun k => algebraMap Ω (GenField Ω r) (x k)) c₁ p' ∧ ∀ q : Σ s, Fin (r s), ((flagMat φ c q.1).submatrix (J q) (Fin.castLE q.2.2)).det ≠ 0 ∧ ∀ l j, ((flagMat φ c q.1).submatrix (Function.update (J q) l j) (Fin.castLE q.2.2)).det / ((flagMat φ c q.1).submatrix (J q) (Fin.castLE q.2.2)).det ∈ regAt ξ' p' := by
  intro Ω _ E _ _ κ x S _ r n φ c X' ξ' p' c₁ J h
  classical
  simp only [InChart] at h ⊢
  obtain ⟨hne, hreg⟩ := h
  have hF : ∀ (k : κ) (J' : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)),
      flagCoord κ x φ c ((k, J') : FlagIx κ n r) = algebraMap Ω (GenField Ω r) (x k) *
        ∏ q : (Σ s, Fin (r s)), ((flagMat φ c q.1).submatrix (J' q) (Fin.castLE q.2.2)).det :=
    fun _ _ => rfl
  rw [hF] at hne
  have hx : algebraMap Ω (GenField Ω r) (x c₁) ≠ 0 := left_ne_zero_of_mul hne
  have hP : ∏ q : (Σ s, Fin (r s)), ((flagMat φ c q.1).submatrix (J q) (Fin.castLE q.2.2)).det ≠ 0 :=
    right_ne_zero_of_mul hne
  refine ⟨hx, ⟨hx, fun k => ?_⟩, fun q => ⟨?_, fun l j => ?_⟩⟩
  · have hq := hreg ((k, J) : FlagIx κ n r)
    rw [hF, hF] at hq
    rwa [mul_div_mul_right _ _ hP] at hq
  · exact (Finset.prod_ne_zero_iff.mp hP) q (Finset.mem_univ q)
  · have hsplit : ∀ J' : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1),
        ∏ q' : (Σ s, Fin (r s)), ((flagMat φ c q'.1).submatrix (J' q') (Fin.castLE q'.2.2)).det =
        ((flagMat φ c q.1).submatrix (J' q) (Fin.castLE q.2.2)).det *
          ∏ q' ∈ Finset.univ.erase q, ((flagMat φ c q'.1).submatrix (J' q') (Fin.castLE q'.2.2)).det := by
      intro J'
      rw [← Finset.mul_prod_erase Finset.univ
        (fun q' : (Σ s, Fin (r s)) => ((flagMat φ c q'.1).submatrix (J' q') (Fin.castLE q'.2.2)).det)
        (Finset.mem_univ q)]
    have hrest : ∏ q' ∈ Finset.univ.erase q,
          ((flagMat φ c q'.1).submatrix (Function.update J q (Function.update (J q) l j) q')
            (Fin.castLE q'.2.2)).det =
        ∏ q' ∈ Finset.univ.erase q, ((flagMat φ c q'.1).submatrix (J q') (Fin.castLE q'.2.2)).det :=
      Finset.prod_congr rfl fun q' hq' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hq')]
    have hR : ∏ q' ∈ Finset.univ.erase q,
        ((flagMat φ c q'.1).submatrix (J q') (Fin.castLE q'.2.2)).det ≠ 0 := by
      intro h0
      apply hP
      rw [hsplit J, h0, mul_zero]
    have hq := hreg ((c₁, Function.update J q (Function.update (J q) l j)) : FlagIx κ n r)
    rw [hF, hF, hsplit (Function.update J q (Function.update (J q) l j)), hsplit J, hrest,
      Function.update_self] at hq
    rwa [mul_div_mul_left _ _ hx, mul_div_mul_right _ _ hR] at hq

end GlobalTheory.CompanionTheory.Ar.FlagBun
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

theorem unitAt_finsetProd {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {p : Cpt ξ}
    {I : Type} (s : Finset I) (f : I → Ω) (hf : ∀ i ∈ s, unitAt ξ p (f i)) :
    unitAt ξ p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using unitAt_one ξ p
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact unitAt_mul (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem unitAt_of_finsetProd {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {p : Cpt ξ}
    {I : Type} (s : Finset I) (f : I → Ω) (hf : ∀ i ∈ s, f i ∈ regAt ξ p)
    (hu : unitAt ξ p (∏ i ∈ s, f i)) {i : I} (hi : i ∈ s) : unitAt ξ p (f i) := by
  classical
  rw [← Finset.mul_prod_erase s f hi] at hu
  exact unitAt_of_mul_left hu (hf i hi)
    (prod_mem fun j hj => hf j (Finset.mem_of_mem_erase hj))

theorem exists_chartQ_unit_sep (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X)
    (κ : Type) (x : κ → Ω) (c : κ) (B : Set (Cpt ξ)) (h : Ω) (e n : ℕ)
    (z : Fin e → Mdl.invAdj (Mdl.chartQ x c) h) (p : Cpt ξ) (_hξ : IsCptGen ξ)
    (hB : ∀ q ∈ B, Char0 ξ q) (hh : h ∈ Mdl.chartQ x c) (h0 : h ≠ 0)
    (hcl : ∀ q : Cpt ξ, Char0 ξ q → InChart ξ x c q → unitAt ξ q h →
      (q ∈ B ↔ ∃ i : Fin e, (i : ℕ) < n ∧ ¬ unitAt ξ q (z i : Ω)))
    (hp : Char0 ξ p) (hpc : InChart ξ x c p) (hph : unitAt ξ p h) (hpB : p ∉ B) :
    ∃ a ∈ Mdl.chartQ x c, unitAt ξ p a ∧ ∀ q ∈ B, InChart ξ x c q → ¬ unitAt ξ q a := by
  classical
  set S : Finset (Fin e) := Finset.univ.filter fun i => (i : ℕ) < n with hS
  set f : Fin e → Ω := fun i => (z i : Ω) with hf
  set ζ : Ω := ∏ i ∈ S, f i with hζ
  have hζm : ζ ∈ Mdl.invAdj (Mdl.chartQ x c) h :=
    Subalgebra.prod_mem _ fun i _ => (z i).2
  obtain ⟨m, hm⟩ := exists_mul_pow_mem hh h0 hζm
  refine ⟨ζ * h ^ m * h, (Mdl.chartQ x c).mul_mem hm hh, ?_, ?_⟩
  · have hz : ∀ i ∈ S, unitAt ξ p (f i) := by
      intro i hi
      by_contra hni
      exact hpB ((hcl p hp hpc hph).2 ⟨i, (Finset.mem_filter.1 hi).2, hni⟩)
    exact unitAt_mul (unitAt_mul (unitAt_finsetProd S f hz) (unitAt_pow hph m)) hph
  · intro q hq hqc hua
    have hq0 := hB q hq
    have hA : ∀ s ∈ Mdl.chartQ x c, s ∈ regAt ξ q := fun s hs => chartQ_le hq0 hqc hs
    by_cases hqh : unitAt ξ q h
    · obtain ⟨i, hin, hni⟩ := (hcl q hq0 hqc hqh).1 hq
      have hreg : ∀ j ∈ S, f j ∈ regAt ξ q := fun j _ => invAdj_le hq0 hA hqh (z j).2
      have hζr : ζ ∈ regAt ξ q := prod_mem hreg
      have hhm : h ^ m * h ∈ regAt ξ q := (regAt ξ q).mul_mem (pow_mem (hA h hh) m) (hA h hh)
      have hua' : unitAt ξ q (ζ * (h ^ m * h)) := by rwa [← _root_.mul_assoc]
      have hζu : unitAt ξ q ζ := unitAt_of_mul_left hua' hζr hhm
      exact hni (unitAt_of_finsetProd S f hreg hζu (Finset.mem_filter.2 ⟨Finset.mem_univ i, hin⟩))
    · exact hqh (unitAt_of_mul_right hua (hA _ hm) (hA h hh))

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl
end
end

section

open Formalism.L2.Pj


theorem _root_.GlobalTheory.T.algebraic_approximation_complete_dvr : ∀ (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R] [IsDomain R] [Algebra F R] [Algebra.Smooth F R] (T : CDVR), T.FinRes → ∀ (io : F →+* T.Fr) (ψ : R →+* T.Fr), ψ.comp (algebraMap F R) = io → ∀ (S : Finset R) (n : ℕ) (g : R), g ≠ 0 → ∃ ψ' : R →+* T.Fr, ψ'.comp (algebraMap F R) = io ∧ (∀ x, IsAlgebraic ℤ (ψ' x)) ∧ (∀ s ∈ S, ψ' s = ψ s ∨ (n : ℤ) ≤ vV T.V (ψ' s - ψ s)) ∧ ψ' g ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.algebraic_approximation_complete_dvr | exact GlobalTheory.CompanionTheory.Relay.algebraic_approximation_complete_dvr | (intros; apply GlobalTheory.CompanionTheory.Relay.algebraic_approximation_complete_dvr <;> assumption)
end
