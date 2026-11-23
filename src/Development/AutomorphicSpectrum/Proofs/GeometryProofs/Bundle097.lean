module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle087
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle089
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle088
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle090
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle013
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric.ConjPoint

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (φ : R →+* R') (ψ : R' →+* R'') :
    dualMap (ψ.comp φ) = (dualMap ψ).comp (dualMap φ) :=
  RingHom.ext fun a => TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

theorem dualMap_algebraMap {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (a : R) :
    dualMap φ (algebraMap R (DualNumber R) a) = algebraMap R' (DualNumber R') (φ a) := by
  change dualMap φ (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl (φ a)
  exact TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

theorem centre_conj (z : Spec (CommRingCat.of ℂ) ⟶ X) : centre (spMap (starRingEnd ℂ) ≫ z) = centre z := by
  have h : (spMap (starRingEnd ℂ)) (IsLocalRing.closedPoint ℂ) = IsLocalRing.closedPoint ℂ :=
    Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact congrArg (fun p => z p) h

theorem extends_conj (M : LieModel G ξ E) {x x' : X} (hx : x = x') (h : genPt ξ ⤳ x) (h' : genPt ξ ⤳ x') (e : E)
    (v : epsAt (X.fromSpecStalk x) ⟶ G) (hv : M.Extends ⟨x, h⟩ e v)
    (φ : X.presheaf.stalk x ⟶ CommRingCat.of ℂ) (φ' : X.presheaf.stalk x' ⟶ CommRingCat.of ℂ)
    (H : Spec.map φ' ≫ X.fromSpecStalk x' = spMap (starRingEnd ℂ) ≫ Spec.map φ ≫ X.fromSpecStalk x) :
    ∃ v' : epsAt (X.fromSpecStalk x') ⟶ G, M.Extends ⟨x', h'⟩ e v' ∧
      Spec.map (CommRingCat.ofHom (dualMap φ'.hom)) ≫ v'.left =
        spMap (dualMap (starRingEnd ℂ)) ≫ Spec.map (CommRingCat.ofHom (dualMap φ.hom)) ≫ v.left := by
  subst hx
  refine ⟨v, hv, ?_⟩
  have h1 : Spec.map φ' = Spec.map (φ ≫ CommRingCat.ofHom (starRingEnd ℂ)) := by
    rw [← cancel_mono (X.fromSpecStalk x), H, Spec.map_comp, Category.assoc]
  have h2 : φ' = φ ≫ CommRingCat.ofHom (starRingEnd ℂ) := Spec.map_injective h1
  subst h2
  have h3 : dualMap (φ ≫ CommRingCat.ofHom (starRingEnd ℂ)).hom =
      (dualMap (starRingEnd ℂ)).comp (dualMap φ.hom) := dualMap_comp _ _
  rw [h3, CommRingCat.ofHom_comp, Spec.map_comp]
  exact Category.assoc _ _ _

def conjVec (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : epsAt z ⟶ G) : epsAt (spMap (starRingEnd ℂ) ≫ z) ⟶ G :=
  Over.homMk (spMap (dualMap (starRingEnd ℂ)) ≫ w.left) (by
    have h1 : w.left ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))) ≫ z := Over.w w
    have h2 : CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) ≫ CommRingCat.ofHom (dualMap (starRingEnd ℂ)) =
        CommRingCat.ofHom (starRingEnd ℂ) ≫ CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) :=
      CommRingCat.hom_ext (RingHom.ext fun a => dualMap_algebraMap (starRingEnd ℂ) a)
    have h3 := congrArg Spec.map h2
    simp only [Spec.map_comp] at h3
    simp only [Over.mk_hom, Category.assoc, h1]
    rw [← Category.assoc, h3, Category.assoc])

theorem valAt_conj (M : LieModel G ξ E) (z : Spec (CommRingCat.of ℂ) ⟶ X) (e : E) (w : epsAt z ⟶ G)
    (hw : M.ValAt z e w) : M.ValAt (spMap (starRingEnd ℂ) ≫ z) e (conjVec z w) := by
  obtain ⟨h, v, hv, hl⟩ := hw
  have hc := centre_conj z
  have h' : genPt ξ ⤳ centre (spMap (starRingEnd ℂ) ≫ z) := hc ▸ h
  obtain ⟨v', hv', hl'⟩ := extends_conj M hc.symm h h' e v hv (Scheme.stalkClosedPointTo z)
    (Scheme.stalkClosedPointTo (spMap (starRingEnd ℂ) ≫ z)) (by
      refine (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (spMap (starRingEnd ℂ) ≫ z)).trans ?_
      exact congrArg (spMap (starRingEnd ℂ) ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z).symm)
  refine ⟨h', v', hv', ?_⟩
  have : (conjVec z w).left = spMap (dualMap (starRingEnd ℂ)) ≫ w.left := rfl
  rw [this, hl]
  exact hl'.symm

theorem gramAt_conj_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐.Li) (Γ : Matrix (Fin r) (Fin r) ℂ), 𝔐.M.GramAt 𝔐.t.PP.L z b Γ → 𝔐.M.GramAt 𝔐.t.PP.L (spMap (starRingEnd ℂ) ≫ z) b (Γ.map (starRingEnd ℂ)) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 z r b Γ ⟨v, hv, hG⟩
  refine ⟨fun i => conjVec z (v i), fun i => valAt_conj 𝔐.M z (b i) (v i) (hv i), fun p q => ?_⟩
  exact GlobalTheory.T.hodge_inner_product_conjugate E H 𝔐.X 𝔐.t z (v p) (v q) (conjVec z (v p)) (conjVec z (v q)) (Γ p q) rfl rfl (hG p q)

end GlobalTheory.CompanionTheory.Ar.HodgeMetric.ConjPoint
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_cpt_interior_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (z : Sp ℂ ⟶ A.X), Mono (spMap β) → Mono Y.j ∧ (A.Interior z ↔ ∃ u : Spec (A.X.presheaf.stalk (centre z)) ⟶ Xo.XF c, u ≫ Y.j = A.X.fromSpecStalk (centre z) ≫ A.f) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.IntOpen.interior_iff_factor | exact GlobalTheory.CompanionTheory.Ar.IntOpen.interior_iff_factor | (intros; apply GlobalTheory.CompanionTheory.Ar.IntOpen.interior_iff_factor <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

theorem _root_.GlobalTheory.T.root_lines_flag_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω) (r : CMType H × Fin (D.p + D.q)) (q : Cpt 𝔐.ξ) (cc : (k : K) → J k) (b : Fin (labelRk D (HodgeCpt.rootIdx D r).1) → 𝔐.Li) (t : Ω), Fl.RootLines xdeg e → InChart 𝔐.ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) cc q → (∀ j, flagStep Ω b j = flagStep Ω (Fl.b (HodgeCpt.rootIdx D r).1) j) → (𝔐.V (HodgeCpt.rootIdx D r).1).IsFrameAt b q → b (HodgeCpt.rootIdx D r).2 - t • Fl.b (HodgeCpt.rootIdx D r).1 (HodgeCpt.rootIdx D r).2 ∈ flagStep Ω (Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2 → unitAt 𝔐.ξ q ((∏ k, y ⟨k, cc k⟩ ^ xdeg r k) * e r / t ^ HodgeCpt.rootSgn D r) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrVert.rootLine_unitAt | exact GlobalTheory.CompanionTheory.Ar.OrVert.rootLine_unitAt | (intros; apply GlobalTheory.CompanionTheory.Ar.OrVert.rootLine_unitAt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.constants_in_coord_ratio_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (cc : (k : K) → J k), (∀ k, y ⟨k, cc k⟩ ≠ 0) → ∀ r : c.F, 𝔐.cst r ∈ Algebra.adjoin ℚ (Set.range fun p : Σ k, J k => y p / y ⟨p.1, cc p.1⟩) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CstChart.cst_mem_chart | exact GlobalTheory.CompanionTheory.Ar.CstChart.cst_mem_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.CstChart.cst_mem_chart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.frame_borel_change_vectors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ : E →+* ℂ) (S : Type) [CommRing S] [Algebra c.F S] (t : Formalism.L2.Pj.Ix D → Sˣ) (z z' : Formalism.L2.Pj.FrPt Xo c S), Formalism.L2.Pj.FrBor t z z' → ∀ (F : Type) [Field F] (ψ : S →+* F) (y : Sp F ⟶ Xo.XF c) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q) (v v' : Vecs y D.p) (w w' : Vecs y D.q), under y = spMap ψ ≫ z.x → (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm)) → (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) → (∀ i, (v' i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z'.u τ (i.cast hp.symm)) → (∀ j, (w' j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z'.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) → ∃ (A : Matrix (Fin D.p) (Fin D.p) F) (B : Matrix (Fin D.q) (Fin D.q) F), (∀ i, Fl.IsComb (A i) v (v' i)) ∧ (∀ j, Fl.IsComb (B j) w (w' j)) ∧ A.det = ∏ i : Fin D.p, ψ (t (some ⟨τ, i.cast hp.symm⟩) : Sˣ) ∧ B.det = ∏ j : Fin D.q, ψ (t (some ⟨ComplexEmbedding.conjugate τ, j.cast hq.symm⟩) : Sˣ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrameTri.exists_triangular_at_field | exact GlobalTheory.CompanionTheory.Ar.Flat.FrameTri.exists_triangular_at_field | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrameTri.exists_triangular_at_field <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ClearConstants

private theorem prod_one_sub_lemma {Ω : Type} [Field Ω] (W : ValuationSubring Ω) (π : Ω)
    (s : Finset Ω) (h : ∀ μ ∈ s, ∃ u ∈ W, 1 - μ = π * u) :
    ∃ w ∈ W, ∏ μ ∈ s, (1 - μ) = w * π ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, W.one_mem, by simp⟩
  | insert a s ha ih =>
    obtain ⟨w, hw, hs⟩ := ih (fun μ hμ => h μ (Finset.mem_insert_of_mem hμ))
    obtain ⟨u, hu, hau⟩ := h a (Finset.mem_insert_self a s)
    refine ⟨u * w, mul_mem hu hw, ?_⟩
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, hs, hau]
    ring

theorem prime_eq_mul_pow {Ω : Type} [Field Ω] (W : ValuationSubring Ω) {p : ℕ} (hp : p.Prime) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ p) : ∃ w ∈ W, (p : Ω) = w * (ζ - 1) ^ (p - 1) := by
  haveI := Fact.mk hp
  have hpow : ζ ^ p = 1 := hζ.pow_eq_one
  have hζW : ζ ∈ W := by
    rcases W.mem_or_inv_mem ζ with h | h
    · exact h
    · have hne : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
      have h1 : (ζ⁻¹) ^ (p - 1) * ζ⁻¹ = 1 := by
        rw [← pow_succ, Nat.sub_add_cancel hp.one_le, inv_pow, hpow, inv_one]
      have key : (ζ⁻¹) ^ (p - 1) = ζ := by
        calc (ζ⁻¹) ^ (p - 1) = (ζ⁻¹) ^ (p - 1) * ζ⁻¹ * ζ := by
              rw [mul_assoc, inv_mul_cancel₀ hne, mul_one]
          _ = ζ := by rw [h1, one_mul]
      rw [← key]
      exact pow_mem h _
  have hprod : (p : Ω) = ∏ μ ∈ primitiveRoots p Ω, (1 - μ) := by
    have h0 := Polynomial.eval_one_cyclotomic_prime (R := Ω) (p := p)
    rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at h0
    simpa using h0.symm
  have hcard : (primitiveRoots p Ω).card = p - 1 := by
    rw [hζ.card_primitiveRoots, Nat.totient_prime hp]
  have hall : ∀ μ ∈ primitiveRoots p Ω, ∃ u ∈ W, 1 - μ = (ζ - 1) * u := by
    intro μ hμ
    have hμp : IsPrimitiveRoot μ p := (mem_primitiveRoots hp.pos).mp hμ
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hμp.pow_eq_one
    refine ⟨-(∑ j ∈ Finset.range i, ζ ^ j), neg_mem (sum_mem fun j _ => pow_mem hζW j), ?_⟩
    rw [← hi]
    linear_combination geom_sum_mul ζ i
  obtain ⟨w, hw, hw'⟩ := prod_one_sub_lemma W (ζ - 1) _ hall
  rw [hcard] at hw'
  exact ⟨w, hw, hprod.trans hw'⟩

def expo (q p : ℕ) : ℕ := if p = 2 then 2 * q else q / (p - 1)

theorem expo_cast {q p : ℕ} (hp : p.Prime) (hd : p - 1 ∣ q) :
    (expo q p : ℝ) = q * (if p = 2 then 2 else 1 / ((p : ℝ) - 1)) := by
  unfold expo
  by_cases h : p = 2
  · subst h
    simp only [if_true]
    push_cast
    ring
  · rw [if_neg h, if_neg h]
    have hne : ((p - 1 : ℕ) : ℝ) ≠ 0 := by
      have h2 : 2 ≤ p := hp.two_le
      have h3 : p - 1 ≠ 0 := by omega
      exact_mod_cast h3
    rw [Nat.cast_div hd hne, Nat.cast_sub hp.one_le]
    push_cast
    ring

theorem pow_expo_eq {Ω : Type} [Field Ω] (W : ValuationSubring Ω) {p q : ℕ} (hp : p.Prime) (hd : p - 1 ∣ q)
    {κ : Ω} (hκ : HT.IsCp p κ) : ∃ w ∈ W, ((p ^ expo q p : ℕ) : Ω) = w * κ ^ q := by
  unfold HT.IsCp at hκ
  by_cases h2 : p = 2
  · subst h2
    rw [if_pos rfl] at hκ
    refine ⟨1, W.one_mem, ?_⟩
    have he : expo q 2 = 2 * q := by simp [expo]
    rw [hκ, one_mul, he, pow_mul]
    norm_num
  · rw [if_neg h2] at hκ
    obtain ⟨ζ, hζ, rfl⟩ := hκ
    obtain ⟨r, rfl⟩ := hd
    obtain ⟨w₀, hw₀, hpw⟩ := prime_eq_mul_pow W hp hζ
    have hpos : 0 < p - 1 := by have := hp.two_le; omega
    refine ⟨w₀ ^ r, pow_mem hw₀ r, ?_⟩
    have he : expo ((p - 1) * r) p = r := by
      simp only [expo, if_neg h2]
      exact Nat.mul_div_cancel_left r hpos
    rw [he, Nat.cast_pow, hpw, mul_pow, ← pow_mul]

theorem clear_constants : ∀ (S : Finset ℕ) (m₀ : ℕ), (∀ p ∈ S, p.Prime) → 0 < m₀ → ∃ q m : ℕ, 0 < q ∧ 0 < m ∧
    Real.log m ≤ q * (Real.log m₀ + ∑ p ∈ S, (if p = 2 then 2 else 1 / ((p : ℝ) - 1)) * Real.log p) ∧
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] (W : ValuationSubring Ω) (κ : Ω), (κ = 1 ∨ ∃ p ∈ S, HT.IsCp p κ) →
      ∀ t : Ω, ((m₀ : Ω) * κ) * t ∈ W → (m : Ω) * t ^ q ∈ W := by
  intro S m₀ hS hm₀
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = ∏ p ∈ S, (p - 1) := ⟨_, rfl⟩
  have hqpos : 0 < q := by
    rw [hq]
    exact Finset.prod_pos fun p hp => by have := (hS p hp).two_le; omega
  have hdvd : ∀ p ∈ S, p - 1 ∣ q := fun p hp => by
    rw [hq]
    exact Finset.dvd_prod_of_mem (fun p => p - 1) hp
  refine ⟨q, m₀ ^ q * ∏ p ∈ S, p ^ expo q p, hqpos,
    Nat.mul_pos (pow_pos hm₀ q) (Finset.prod_pos fun p hp => pow_pos (hS p hp).pos _), ?_, ?_⟩
  · apply le_of_eq
    push_cast
    have hm0 : ((m₀ : ℝ) ^ q) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hm₀.ne')
    have hprod : (∏ p ∈ S, (p : ℝ) ^ expo q p) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (by exact_mod_cast (hS p hp).ne_zero)
    rw [Real.log_mul hm0 hprod, Real.log_pow,
      Real.log_prod fun p hp => pow_ne_zero _ (by exact_mod_cast (hS p hp).ne_zero),
      mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Real.log_pow, expo_cast (hS p hp) (hdvd p hp)]
    ring
  · intro Ω _ _ W κ hκ t ht
    have hrest : ∀ T : Finset ℕ, (∏ x ∈ T, ((x : Ω) ^ expo q x)) ∈ W :=
      fun T => prod_mem fun x _ => pow_mem (natCast_mem W x) _
    push_cast
    rcases hκ with rfl | ⟨p, hpS, hp⟩
    · rw [mul_one] at ht
      have e : (m₀ : Ω) ^ q * (∏ x ∈ S, (x : Ω) ^ expo q x) * t ^ q
          = ((m₀ : Ω) * t) ^ q * ∏ x ∈ S, (x : Ω) ^ expo q x := by ring
      rw [e]
      exact mul_mem (pow_mem ht q) (hrest S)
    · obtain ⟨w, hw, hpw⟩ := pow_expo_eq W (hS p hpS) (hdvd p hpS) hp
      push_cast at hpw
      have hsplit : ∏ x ∈ S, (x : Ω) ^ expo q x = w * κ ^ q * ∏ x ∈ S.erase p, (x : Ω) ^ expo q x := by
        rw [← Finset.mul_prod_erase S (fun x => (x : Ω) ^ expo q x) hpS, hpw]
      rw [hsplit]
      have e : (m₀ : Ω) ^ q * (w * κ ^ q * ∏ x ∈ S.erase p, (x : Ω) ^ expo q x) * t ^ q
          = w * ((m₀ : Ω) * κ * t) ^ q * ∏ x ∈ S.erase p, (x : Ω) ^ expo q x := by ring
      rw [e]
      exact mul_mem (mul_mem hw (pow_mem ht q)) (hrest _)

end GlobalTheory.CompanionTheory.Ar.ClearConstants
end

section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT.KappaDvd

theorem kappa_dvd_sq : ∀ (A Ω : Type) [CommRing A] [IsDomain A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω]
    [IsIntegrallyClosed A] [CharZero Ω] (p : ℕ) [Fact p.Prime] (κ : A),
    IsCp p (algebraMap A Ω κ) → κ ∣ (p : A) ^ 2 := by
  intro A Ω _ _ _ _ _ _ _ p hp κ h
  have hinj : Function.Injective (algebraMap A Ω) := IsFractionRing.injective A Ω
  unfold IsCp at h
  split_ifs at h with h2
  · subst h2
    have : κ = 4 := hinj (by rw [h]; exact (map_ofNat _ 4).symm)
    subst this
    exact ⟨1, by norm_num⟩
  · obtain ⟨ζ, hζ, hκ⟩ := h
    have hp1 : 1 < p := hp.out.one_lt
    have hint : IsIntegral A ζ := by
      refine ⟨Polynomial.X ^ p - 1, Polynomial.monic_X_pow_sub_C 1 hp.out.ne_zero, ?_⟩
      simp [hζ.pow_eq_one]
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    have hz' : IsPrimitiveRoot z p := by
      rw [← hz] at hζ
      exact hζ.of_map_of_injective hinj
    have hκz : κ = z - 1 := hinj (by rw [hκ, map_sub, map_one, hz])
    have hsum : ∑ i ∈ Finset.range p, z ^ i = 0 := hz'.geom_sum_eq_zero hp1
    have hp_eq : (p : A) = ∑ i ∈ Finset.range p, (1 - z ^ i) := by
      rw [Finset.sum_sub_distrib, hsum]; simp
    have hdvd : κ ∣ (p : A) := by
      rw [hp_eq, hκz]
      refine Finset.dvd_sum fun i _ => ?_
      have := sub_dvd_pow_sub_pow z 1 i
      rw [one_pow] at this
      rw [show (1 : A) - z ^ i = -(z ^ i - 1) by ring]
      exact dvd_neg.mpr this
    exact hdvd.trans (dvd_pow_self _ two_ne_zero)

end GlobalTheory.CompanionTheory.Ar.HT.KappaDvd
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num

section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {V : Type} [AddCommGroup V]
  [Module Ω V]

theorem patch_eq_of_subset {S₀ S : Finset ℕ} (h : S₀ ⊆ S) (L₀ : Lat ξ V) (Lp : ℕ → Lat ξ V) {q : Cpt ξ}
    (hq : ∀ p ∈ S, p ∉ S₀ → ¬ InFibre ξ p q) : Lat.patch S₀ L₀ Lp q = Lat.patch S L₀ Lp q := by
  have hmem : ∀ p, (p ∈ S₀ ∧ InFibre ξ p q) ↔ (p ∈ S ∧ InFibre ξ p q) := fun p =>
    ⟨fun ⟨a, b⟩ => ⟨h a, b⟩, fun ⟨a, b⟩ => ⟨by_contra fun c => hq p a c b, b⟩⟩
  have hex : (∃ p ∈ S₀, InFibre ξ p q) ↔ ∃ p ∈ S, InFibre ξ p q := exists_congr hmem
  simp only [Lat.patch]
  by_cases hc : ∃ p ∈ S, InFibre ξ p q
  · rw [if_pos hc, if_pos (hex.2 hc)]
    refine le_antisymm (le_iInf₂ fun p hp => le_iInf fun hf => ?_) (le_iInf₂ fun p hp => le_iInf fun hf => ?_)
    · exact iInf₂_le_of_le p ((hmem p).2 ⟨hp, hf⟩).1 (iInf_le _ hf)
    · exact iInf₂_le_of_le p (h hp) (iInf_le _ hf)
  · rw [if_neg hc, if_neg (fun c => hc (hex.1 c))]

theorem gr_congr_at {L L' : Lat ξ V} {r : ℕ} (b : Fin r → V) (i : Fin r) {q : Cpt ξ} (hq : L q = L' q) :
    L.gr b i q = L'.gr b i q := by
  simp only [Lat.gr, hq]

theorem tens_congr_at {I : Type} [Fintype I] {Λ Λ' : I → Lat ξ Ω} (a : I → ℤ) {q : Cpt ξ}
    (hq : ∀ i, Λ i q = Λ' i q) : Lat.tens Λ a q = Lat.tens Λ' a q := by
  simp only [Lat.tens, Lat.IsGenAt, hq]

end General

theorem rootLat_shrink_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (Fl : 𝔐.Flag) (S₀ : Finset ℕ) (h : S₀ ⊆ S) (hvb : ∀ s, (𝔐.VAt S₀ s).IsVB (labelRk D s) (𝔐.Vgen s)) (hsub : ∀ s, (𝔐.VAt S₀ s).IsFlagVBOn Set.univ (Fl.b s)) (q : Cpt 𝔐.ξ), (∀ p ∈ S, p ∉ S₀ → ¬ InFibre 𝔐.ξ p q) → ∀ r, (Fl.shrink S₀ h hvb hsub).rootLat r q = Fl.rootLat r q := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d _ Fl S₀ h hvb hsub q hq r
  refine tens_congr_at (Λ := fun _ : Unit => (𝔐.VAt S₀ (HodgeCpt.rootIdx D r).1).gr (Fl.b (HodgeCpt.rootIdx D r).1)
    (HodgeCpt.rootIdx D r).2) (Λ' := fun _ : Unit => (𝔐.V (HodgeCpt.rootIdx D r).1).gr (Fl.b (HodgeCpt.rootIdx D r).1)
    (HodgeCpt.rootIdx D r).2) _ fun _ => gr_congr_at _ _ ?_
  exact patch_eq_of_subset h _ _ hq

end GlobalTheory.CompanionTheory.Ar.Num

end
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.OrArch

section Lines

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem log_h_torus (A : HermLine ι) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) {w : (Σ k, ι k) → ℂ}
    (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) :
    Real.log (A.h fun p => c p.1 * w p) = ∑ k, (A.a k : ℝ) * Real.log ‖c k‖ + Real.log (A.h w) := by
  have h0 : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
  rw [A.smul c w hc, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (h0 k))
    (A.pos w hw).ne', Real.log_prod (fun k _ => zpow_ne_zero _ (h0 k))]
  simp only [Real.log_zpow]

theorem log_sub_of_sameOrbit {A B : HermLine ι} (hAB : A.a = B.a) {z w : (Σ k, ι k) → ℂ}
    (h : SameOrbit z w) (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) :
    Real.log (A.h z) - Real.log (B.h z) = Real.log (A.h w) - Real.log (B.h w) := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [log_h_torus A hc hw, log_h_torus B hc hw, hAB]
  ring

theorem log_add_sum_of_sameOrbit {α : Type} (T : Finset α) {A : HermLine ι} (B : α → HermLine ι)
    (hA : A.a = -∑ j ∈ T, (B j).a) {z w : (Σ k, ι k) → ℂ} (h : SameOrbit z w)
    (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) :
    Real.log (A.h z) + ∑ j ∈ T, Real.log ((B j).h z) =
      Real.log (A.h w) + ∑ j ∈ T, Real.log ((B j).h w) := by
  obtain ⟨c, hc, rfl⟩ := h
  simp only [log_h_torus _ hc hw, Finset.sum_add_distrib]
  have h1 : ∑ k, (A.a k : ℝ) * Real.log ‖c k‖ =
      -∑ j ∈ T, ∑ k, ((B j).a k : ℝ) * Real.log ‖c k‖ := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hA, Pi.neg_apply, Finset.sum_apply, Int.cast_neg, Int.cast_sum, neg_mul, Finset.sum_mul]
  rw [h1]
  ring

end Lines

theorem defect_eq_regWeight_add_bracket :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (M R : Top.RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (o : RootOrigin Y S M Fx) (o₀ : RootOrigin Y S₀ R Fx) (x : o.Re.R.X) (x' : o₀.Re.R.X) (w₁ : (Σ k, M.ι k) → ℂ) (w₂ : (Σ k, R.ι k) → ℂ) (v : RootIx D → ℝ) (t : ℝ), 0 < t → t ≤ Sys.t₀ → w₁ ∈ mcPts M.P → w₂ ∈ mcPts R.P → ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (o.Re.R.lift x x) w₁ → ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (o₀.Re.R.lift x' x') w₂ → o.Re.π x = o₀.Re.π x' → o.Re.π x ∈ Sys.open' → (∀ r, 0 < v r ∧ v r * (o₀.sing r).h w₂ = (o.sing r).h w₁) → ∀ (τ : CMType H) (p : Fin (D.p + D.q)), -∑ k ∈ Finset.Iic p, (Real.log ((M.x t (τ, k)).h w₁) - Real.log ((R.x 1 (τ, k)).h w₂) - Real.log (v (τ, k))) = Sys.phT (some (τ, p)) t (o.Re.π x) + (Real.log ((o₀.Re.ref (some (τ, p))).h w₂) + ∑ k ∈ Finset.Iic p, Real.log ((R.x 1 (τ, k)).h w₂)) := by
  intro E _ _ _ H D l Xo c Y S S₀ M R Sys Fx o o₀ x x' w₁ w₂ v t ht0 htle hw₁ hw₂ hx hx' hπ hop hv τ p
  have hop₀ : o₀.Re.π x' ∈ Sys.open' := hπ ▸ hop

  have hreg := o.fund_reg τ p t ht0 htle w₁ hw₁
  have hline := o.Re.line_eq (some (τ, p)) t ht0 htle x
  have hsc := log_sub_of_sameOrbit (o.Re.line_deg (some (τ, p)) t) hx hw₁.1

  have hs := o.fund_sing τ p x hop
  have hs₀ := o₀.fund_sing τ p x' hop₀
  have hdeg : ∀ (N : Top.RootModel (CMType H) (D.p + D.q)) (S' : Finset ℕ) (Fx' : FixedData Y Sys)
      (q : RootOrigin Y S' N Fx'),
      (q.Re.ref (some (τ, p))).a = -∑ k ∈ Finset.Iic p, (q.sing (τ, k)).a := by
    intro N S' Fx' q
    rw [q.fund_deg τ p]
    simp only [q.sing_deg]
  have hb := log_add_sum_of_sameOrbit (Finset.Iic p) (fun k => o.sing (τ, k)) (hdeg _ _ _ o) hx hw₁.1
  have hb₀ := log_add_sum_of_sameOrbit (Finset.Iic p) (fun k => o₀.sing (τ, k)) (hdeg _ _ _ o₀) hx' hw₂.1

  have hsum : ∑ k ∈ Finset.Iic p, Real.log ((o.sing (τ, k)).h w₁) =
      ∑ k ∈ Finset.Iic p, Real.log (v (τ, k)) + ∑ k ∈ Finset.Iic p, Real.log ((o₀.sing (τ, k)).h w₂) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    obtain ⟨h0, h1⟩ := hv (τ, k)
    rw [← h1, Real.log_mul h0.ne' ((o₀.sing (τ, k)).pos w₂ hw₂.1).ne']
  rw [hπ] at hs hline
  simp only [Finset.sum_sub_distrib]
  rw [hπ]
  linarith

end GlobalTheory.CompanionTheory.Ar.OrArch
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_comp_comparison_right : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] (K₁ : Type) [Fintype K₁] (J₁ : K₁ → Type) [∀ k, Fintype (J₁ k)] (y₁ : (Σ k, J₁ k) → Ω₁) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S₀ y₁) (Fl : A.Flag) (B : HodgeCpt Y S y) (i : Ω₁ →+* Ω) (h : B.X ⟶ A.X) (jA : A.Li →+ B.Li), GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ h i → B.f = h ≫ A.f → B.cst = i.comp A.cst → IsExtOver i jA → (∀ e, (B.M.pt (jA e)).left ≫ B.m.φ = spMap (dualMap i) ≫ (A.M.pt e).left ≫ A.m.φ) → (∀ a e, jA (A.ρ a e) = B.ρ a (jA e)) → B.M.lat = A.M.lat.pull B.ξ h jA → ∀ q ∈ genFib B.ξ, ∀ s, (B.V s).IsFlagVBOn {q} (fun a => jA (Fl.b s a)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.VbGen.isFlagVBOn_genFib | exact GlobalTheory.CompanionTheory.Ar.VbGen.isFlagVBOn_genFib | (intros; apply GlobalTheory.CompanionTheory.Ar.VbGen.isFlagVBOn_genFib <;> assumption)
end
