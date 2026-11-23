module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle061
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle039
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle021
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfMul
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace PositivityTheory.HtPt.Htat.QuotientDualMap

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

theorem valAt_top {B : Type} [CommRing B] {X : Scheme.{0}} (v : Spec (CommRingCat.of B) ⟶ X) (s : Γ(X, ⊤)) :
    valAt v ⊤ le_top s = (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (v.appTop.hom s) := by
  rfl

theorem valAt_spec_comp {B C : Type} [CommRing B] [CommRing C] {X : Scheme.{0}} (φ : B →+* C)
    (v : Spec (CommRingCat.of B) ⟶ X) (s : Γ(X, ⊤)) :
    valAt (Spec.map (CommRingCat.ofHom φ) ≫ v) ⊤ le_top s = φ (valAt v ⊤ le_top s) := by
  rw [valAt_top, valAt_top, Scheme.Hom.comp_appTop]
  exact congrArg (fun f => f.hom (v.appTop.hom s)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))

theorem valAt_mul [Finite T] (Γ : QFGroup R T) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤))
    (hs : Γ.HasValues s (fun t => ((χ t : Rˣ) : R))) {B : Type} [CommRing B]
    (q : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) (y z : Over.mk q ⟶ Γ.G) :
    valAt (B := B) (y * z).left ⊤ le_top s =
      valAt (B := B) y.left ⊤ le_top s * valAt (B := B) z.left ⊤ le_top s := by
  have h := (PositivityTheory.HtPt.Htat.ht_char_mul R T Γ χ s hs (Over.mk q)).1 y z
  rw [valAt_top, valAt_top, valAt_top, ← map_mul]
  exact congrArg _ h

theorem valAt_one [Finite T] (Γ : QFGroup R T) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤))
    (hs : Γ.HasValues s (fun t => ((χ t : Rˣ) : R))) {B : Type} [CommRing B]
    (q : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) :
    valAt (B := B) (1 : Over.mk q ⟶ Γ.G).left ⊤ le_top s = 1 := by
  have h := (PositivityTheory.HtPt.Htat.ht_char_mul R T Γ χ s hs (Over.mk q)).2
  rw [valAt_top]
  refine (congrArg _ h).trans ?_
  exact map_one _

theorem tors_one {Γ : QFGroup R T} {S : Scheme.{0}} {G : Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left} (h : Γ.IsTorsionAlong G x N i)
    (Y : Over (Spec (CommRingCat.of R))) :
    (1 : Y ⟶ Γ.G).left ≫ i = (1 : Over.mk (Y.hom ≫ x) ⟶ G).left := by
  let y₀ : Over.mk (Y.hom ≫ x) ⟶ G := Over.homMk ((1 : Y ⟶ Γ.G).left ≫ i) (by
    show ((1 : Y ⟶ Γ.G).left ≫ i) ≫ G.hom = Y.hom ≫ x
    rw [Category.assoc, h.isOver, ← Category.assoc, Over.w])
  have h1 := h.mul Y 1 1 y₀ y₀ rfl rfl
  rw [_root_.mul_one] at h1
  have h2 : y₀ * y₀ = y₀ * 1 := by
    rw [_root_.mul_one]
    exact Over.OverMorphism.ext h1
  have h3 : y₀ = 1 := mul_left_cancel h2
  exact congrArg (fun f => f.left) h3

section Tangent

variable {A : Type} [CommRing A] (π : R →+* A)

abbrev qMap : Spec (CommRingCat.of (DualNumber A)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom ((algebraMap A (DualNumber A)).comp π))

abbrev dMap : Spec (CommRingCat.of (DualNumber A)) ⟶ Spec (CommRingCat.of (DualNumber R)) :=
  Spec.map (CommRingCat.ofHom (dualMap π))

theorem dMap_over : dMap π ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) = qMap π := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_epsMul (c : R) :
    (epsMul (π c)).comp (dualMap π) = (dualMap π).comp (epsMul c) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_comm]

theorem epsMul_algebraMap (c : A) : (epsMul c).comp (algebraMap A (DualNumber A)) = algebraMap A (DualNumber A) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_dualMap : ((TrivSqZeroExt.fstHom A A A).toRingHom).comp (dualMap π) =
    π.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => ?_
  simp [dualMap]

theorem fst_q : ((TrivSqZeroExt.fstHom A A A).toRingHom).comp ((algebraMap A (DualNumber A)).comp π) = π := by
  refine RingHom.ext fun a => ?_
  simp [TrivSqZeroExt.algebraMap_eq_inl]

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S}
  {L : Type} [AddCommGroup L] [Module R L]

def IsTan (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left) (M : LieModel G x L) (e : L)
    (v : Spec (CommRingCat.of (DualNumber A)) ⟶ Γ.G.left) : Prop :=
  v ≫ Γ.G.hom = qMap π ∧ v ≫ i = dMap π ≫ (M.pt e).left

variable {π} {N : ℕ} {Γ : QFGroup R T} {i : Γ.G.left ⟶ G.left} {M : LieModel G x L}

theorem fst_valAt [Finite T] (h : Γ.IsTorsionAlong G x N i) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤))
    (hs : Γ.HasValues s (fun t => ((χ t : Rˣ) : R))) {e : L}
    {v : Spec (CommRingCat.of (DualNumber A)) ⟶ Γ.G.left} (hv : IsTan π Γ i M e v) :
    (valAt v ⊤ le_top s).fst = 1 := by
  let r : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom π)
  let p : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (DualNumber A)) :=
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom)
  have hpq : p ≫ qMap π = r := by
    simp only [p, r, qMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, fst_q]
  let y : Over.mk r ⟶ Γ.G := Over.homMk (p ≫ v) (by
    show (p ≫ v) ≫ Γ.G.hom = r
    rw [Category.assoc, hv.1, hpq])
  have hy : y = 1 := by
    apply h.inj (Over.mk r)
    rw [tors_one h]
    have hp : p ≫ dMap π = r ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
      simp only [p, r, dMap]
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, fst_dualMap]
    let w : Over.mk (r ≫ x) ⟶ Over.mk x := Over.homMk r rfl
    have h1 : (w ≫ (1 : Over.mk x ⟶ G)).left = r ≫ (1 : Over.mk x ⟶ G).left := rfl
    rw [comp_one] at h1
    show (p ≫ v) ≫ i = (1 : Over.mk (r ≫ x) ⟶ G).left
    rw [h1, Category.assoc, hv.2, ← Category.assoc, hp, Category.assoc]
    exact congrArg (r ≫ ·) (M.tan e)
  have h2 : valAt (p ≫ v) ⊤ le_top s = 1 := by
    have h3 := valAt_one Γ χ s hs r
    rw [← hy] at h3
    exact h3
  have h4 := valAt_spec_comp (TrivSqZeroExt.fstHom A A A).toRingHom v s
  exact h4.symm.trans h2

theorem isTan_add [Finite T] (h : Γ.IsTorsionAlong G x N i) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤))
    (hs : Γ.HasValues s (fun t => ((χ t : Rˣ) : R))) {e e' : L}
    {v v' : Spec (CommRingCat.of (DualNumber A)) ⟶ Γ.G.left} (hv : IsTan π Γ i M e v)
    (hv' : IsTan π Γ i M e' v') :
    ∃ w, IsTan π Γ i M (e + e') w ∧ valAt w ⊤ le_top s = valAt v ⊤ le_top s * valAt v' ⊤ le_top s := by
  let y : Over.mk (qMap π) ⟶ Γ.G := Over.homMk v hv.1
  let z : Over.mk (qMap π) ⟶ Γ.G := Over.homMk v' hv'.1
  let ρ : Over.mk (qMap π ≫ x) ⟶ epsAt x := Over.homMk (dMap π) (by
    show dMap π ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x = qMap π ≫ x
    rw [← Category.assoc, dMap_over])
  have hm := h.mul (Over.mk (qMap π)) y z (ρ ≫ M.pt e) (ρ ≫ M.pt e') hv.2.symm hv'.2.symm
  rw [← comp_mul, ← M.add] at hm
  exact ⟨(y * z).left, ⟨Over.w (y * z), hm.symm⟩, valAt_mul Γ χ s hs (qMap π) y z⟩

theorem isTan_smul (c : R) {e : L} {v : Spec (CommRingCat.of (DualNumber A)) ⟶ Γ.G.left}
    (hv : IsTan π Γ i M e v) :
    IsTan π Γ i M (c • e) (Spec.map (CommRingCat.ofHom (epsMul (π c))) ≫ v) := by
  constructor
  · rw [Category.assoc, hv.1, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, epsMul_algebraMap]
  · rw [Category.assoc, hv.2, M.smul, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, dualMap_epsMul]

end Tangent

theorem snd_epsMul {A : Type} [CommRing A] (c : A) (a : DualNumber A) :
    (epsMul c a).snd = c * a.snd := by
  simp [epsMul]

theorem char_on_tangent_linear : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤)), Γ.HasValues s (fun t => ((χ t : Rˣ) : R)) → ∃ l : L →ₗ[R] (R ⧸ Ideal.span {(N : R)}), ∀ (e : L) (v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left), v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) ∧ v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left → valAt v ⊤ le_top s = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (l e) := by
  intro R _ _ T _ _ Γ S G _ _ x N i h L _ _ M χ s hs
  have hex : ∀ e : L, ∃ v, IsTan (Ideal.Quotient.mk (Ideal.span {(N : R)})) Γ i M e v ∧
      ∀ w, IsTan (Ideal.Quotient.mk (Ideal.span {(N : R)})) Γ i M e w → w = v :=
    fun e => GlobalTheory.T.existsUnique_tangent_dual_number R T Γ S G x N i h L M e
  choose v hv hu using hex
  have hfst : ∀ e, (valAt (v e) ⊤ le_top s).fst = 1 := fun e => fst_valAt h χ s hs (hv e)
  refine ⟨{ toFun := fun e => (valAt (v e) ⊤ le_top s).snd, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro e e'
    obtain ⟨w, hw, hval⟩ := isTan_add h χ s hs (hv e) (hv e')
    rw [← hu _ w hw, hval, TrivSqZeroExt.snd_mul, hfst, hfst]
    simp [add_comm]
  · intro c e
    have h1 := hu _ _ (isTan_smul c (hv e))
    rw [← h1, valAt_spec_comp, snd_epsMul]
    simp [Algebra.smul_def]
  · intro e w hw
    rw [hu e w hw]
    ext
    · simp [hfst]
    · simp

end PositivityTheory.HtPt.Htat.QuotientDualMap

theorem PositivityTheory.HtPt.Htat.ht_linear : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤)), Γ.HasValues s (fun t => ((χ t : Rˣ) : R)) → ∃ l : L →ₗ[R] (R ⧸ Ideal.span {(N : R)}), ∀ (e : L) (v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left), v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) ∧ v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left → valAt v ⊤ le_top s = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (l e) :=
  @PositivityTheory.HtPt.Htat.QuotientDualMap.char_on_tangent_linear
end
end

section

noncomputable section

namespace PositivityTheory.HtPt.Hcptgen

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.ChartFin ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem isUnit_iff_unitAt {q : Cpt ξ} (hi : Function.Injective (genMap ξ q)) (s : X.presheaf.stalk q.1) :
    IsUnit s ↔ unitAt ξ q (genMap ξ q s) := by
  constructor
  · rintro ⟨u, rfl⟩
    have h : genMap ξ q (u : X.presheaf.stalk q.1) * genMap ξ q (↑u⁻¹ : X.presheaf.stalk q.1) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    exact ⟨left_ne_zero_of_mul_eq_one h, ⟨_, rfl⟩, ⟨_, eq_inv_of_mul_eq_one_right h⟩⟩
  · rintro ⟨h0, -, t, ht⟩
    refine IsUnit.of_mul_eq_one t (hi ?_)
    rw [map_mul, ht, mul_inv_cancel₀ h0, map_one]

theorem overZp_iff {p : ℕ} (hp : p.Prime) (q : Cpt ξ) :
    (∀ r : ℕ, r.Prime → InFibre ξ r q → r = p) ↔ ∀ b : ℕ, ¬ p ∣ b → unitAt ξ q (b : Ω) := by
  constructor
  · intro hq b hb
    induction b using Nat.recOnMul with
    | zero => exact absurd (dvd_zero p) hb
    | one =>
      rw [Nat.cast_one]
      exact ⟨one_ne_zero, one_mem _, by rw [inv_one]; exact one_mem _⟩
    | prime r hr =>
      by_contra h
      exact hb (by rw [hq r hr h])
    | mul a b iha ihb =>
      have ha := iha fun h => hb (h.mul_right b)
      have hb' := ihb fun h => hb (h.mul_left a)
      rw [Nat.cast_mul]
      exact ⟨mul_ne_zero ha.1 hb'.1, mul_mem ha.2.1 hb'.2.1, by
        rw [mul_inv]; exact mul_mem ha.2.2 hb'.2.2⟩
  · intro h r hr hf
    by_contra hne
    exact hf (h r fun hd => hne ((Nat.prime_dvd_prime_iff_eq hp hr).1 hd).symm)

theorem mem_adjoin_loc [CharZero Ω] {p : ℕ} (hp : p.Prime) {o : Type} [CommRing o] [Algebra o Ω]
    (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω))
    (T : Set Ω) {a : Ω} (ha : a ∈ Algebra.adjoin o T) :
    ∃ b : ℕ, ¬ p ∣ b ∧ a * b ∈ Algebra.adjoin ℤ T := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, hp.not_dvd_one, by simpa using Algebra.subset_adjoin hx⟩
  | algebraMap r =>
    obtain ⟨m, b, hb, e⟩ := (ho _).1 ⟨r, rfl⟩
    have hb0 : (b : Ω) ≠ 0 := Nat.cast_ne_zero.2 fun h => hb (h ▸ dvd_zero p)
    exact ⟨b, hb, by rw [e, div_mul_cancel₀ _ hb0]; exact intCast_mem _ m⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb, hx⟩ := hx
    obtain ⟨b', hb', hy⟩ := hy
    refine ⟨b * b', hp.not_dvd_mul hb hb', ?_⟩
    have : (x + y) * ((b * b' : ℕ) : Ω) = x * b * b' + y * b' * b := by push_cast; ring
    rw [this]
    exact add_mem (mul_mem hx (natCast_mem _ _)) (mul_mem hy (natCast_mem _ _))
  | mul x y _ _ hx hy =>
    obtain ⟨b, hb, hx⟩ := hx
    obtain ⟨b', hb', hy⟩ := hy
    refine ⟨b * b', hp.not_dvd_mul hb hb', ?_⟩
    have : (x * y) * ((b * b' : ℕ) : Ω) = x * b * (y * b') := by push_cast; ring
    rw [this]
    exact mul_mem hx hy

theorem chart_int {κ : Type} {x : κ → Ω} (T : CoordTie ℤ ξ x) (hn : IsNormalScheme X) {c : κ} (hc : x c ≠ 0) :
    IsFractionRing (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) Ω ∧
      IsIntegrallyClosed (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) := by
  have hf : IsFractionRing (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) Ω := by
    refine IsFractionRing.of_field _ _ fun a => ?_
    obtain ⟨g, hg, h, hh, -, e⟩ := FlagBun.FracChart.exists_eq_div_adjoin X Ω ξ κ x c T hc a
    exact ⟨⟨g, hg⟩, ⟨h, hh⟩, e⟩
  refine ⟨hf, (isIntegrallyClosed_iff Ω).2 fun {a} ha => ?_⟩
  refine ⟨⟨a, (T.ring c hc a).2 fun q hq => ?_⟩, rfl⟩
  obtain ⟨h1, -, h3⟩ := GlobalTheory.T.regAt_fraction_noetherian_closed X Ω ξ T.gen q
  have h4 := h3 (hn q.1).2
  let φ : Algebra.adjoin ℤ (Set.range fun j => x j / x c) →+* regAt ξ q :=
    (algebraMap (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) Ω).codRestrict _
      fun r => (T.ring c hc r).1 r.2 q hq
  have h5 : IsIntegral (regAt ξ q) a := ha.map_of_comp_eq φ (RingHom.id Ω) rfl
  obtain ⟨r, rfl⟩ := (isIntegrallyClosed_iff Ω).1 h4 h5
  exact r.2

theorem chart_loc [CharZero Ω] {κ : Type} [Finite κ] {x : κ → Ω} (hall : ∀ q : X, genPt ξ ⤳ q)
    (T : CoordTie ℤ ξ x) (hn : IsNormalScheme X) {p : ℕ} (hp : p.Prime) {o : Type} [CommRing o] [Algebra o Ω]
    (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω))
    {c : κ} (hc : x c ≠ 0) (B : Subalgebra o Ω) (hB : B = Algebra.adjoin o (Set.range fun j => x j / x c)) :
    IsNoetherianRing B ∧ IsIntegrallyClosed B ∧ IsFractionRing B Ω ∧
      ∃ z : Sp B ⟶ X, spMap (algebraMap B Ω) ≫ z = ξ ∧
        ∀ q : Cpt ξ, q.1 ∈ Set.range z ↔ (InChart ξ x c q ∧ ∀ r : ℕ, r.Prime → InFibre ξ r q → r = p) := by
  obtain ⟨U, hUa, hUm⟩ := T.affine c hc
  have hg : genPt ξ ∈ U := (hUm _).2 ⟨specializes_rfl, inChart_genPt T.gen hc⟩
  obtain ⟨E, hE⟩ := ChartSmooth.exists_secEquiv hall T hc hUm hg
  obtain ⟨hAf, hAi⟩ := chart_int T hn hc
  have hAB : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), a ∈ B := by
    intro a ha
    have : Algebra.adjoin ℤ (Set.range fun j => x j / x c) ≤ subalgebraOfSubring B.toSubring :=
      Algebra.adjoin_le (by rw [hB]; exact Algebra.subset_adjoin)
    exact this ha
  have hinj := secVal_injective hall T.gen.inj U hg
  let ψ : Γ(X, U) →+* B := (secVal ξ U hg).codRestrict _ fun s => hAB _ (hE s ▸ (E s).2)
  have hψ : ∀ s, (ψ s : Ω) = secVal ξ U hg s := fun _ => rfl
  letI : Algebra Γ(X, U) B := ψ.toAlgebra
  let M : Submonoid Γ(X, U) :=
    { carrier := {r | ∃ b : ℕ, ¬ p ∣ b ∧ r = b}
      one_mem' := ⟨1, hp.not_dvd_one, Nat.cast_one.symm⟩
      mul_mem' := by
        rintro _ _ ⟨b, hb, rfl⟩ ⟨b', hb', rfl⟩
        exact ⟨b * b', hp.not_dvd_mul hb hb', (Nat.cast_mul _ _).symm⟩ }
  have hb0 : ∀ b : ℕ, ¬ p ∣ b → (b : Ω) ≠ 0 := fun b hb => Nat.cast_ne_zero.2 fun h => hb (h ▸ dvd_zero p)
  haveI hloc : IsLocalization M B := by
    refine ⟨?_, fun a => ?_, fun {r s} h => ⟨1, ?_⟩⟩
    · rintro ⟨_, b, hb, rfl⟩
      obtain ⟨r, hr⟩ := (ho ((1 : ℤ) / (b : Ω))).2 ⟨1, b, hb, rfl⟩
      refine IsUnit.of_mul_eq_one (algebraMap o B r) (Subtype.ext ?_)
      have h1 : ((algebraMap o B r : B) : Ω) = algebraMap o Ω r := rfl
      simp only [map_natCast, MulMemClass.coe_mul, SubringClass.coe_natCast, h1, hr, OneMemClass.coe_one]
      rw [Int.cast_one, mul_one_div_cancel (hb0 b hb)]
    · obtain ⟨b, hb, hab⟩ := mem_adjoin_loc hp ho _ (hB.le a.2)
      refine ⟨⟨E.symm ⟨_, hab⟩, ⟨b, b, hb, rfl⟩⟩, Subtype.ext ?_⟩
      show (a : Ω) * secVal ξ U hg (b : Γ(X, U)) = secVal ξ U hg _
      rw [← hE (E.symm _), E.apply_symm_apply, map_natCast]
    · have h' : secVal ξ U hg r = secVal ξ U hg s := (hψ r).symm.trans ((congrArg Subtype.val h).trans (hψ s))
      rw [hinj h']
  haveI : Algebra.FiniteType ℤ (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) := by
    refine (Subalgebra.fg_iff_finiteType _).1 ⟨(Set.finite_range fun j => x j / x c).toFinset, ?_⟩
    rw [Set.Finite.coe_toFinset]
  haveI : IsNoetherianRing (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) :=
    Algebra.FiniteType.isNoetherianRing ℤ _
  have hRN : IsNoetherianRing Γ(X, U) := isNoetherianRing_of_ringEquiv _ E.symm
  haveI : IsDomain Γ(X, U) := hinj.isDomain _
  haveI : IsIntegrallyClosed Γ(X, U) := IsIntegrallyClosed.of_equiv E.symm
  have hM : M ≤ nonZeroDivisors Γ(X, U) := by
    rintro _ ⟨b, hb, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h => hb0 b hb ?_
    rw [← map_natCast (secVal ξ U hg), h, map_zero]
  refine ⟨IsLocalization.isNoetherianRing M B hRN, isIntegrallyClosed_of_isLocalization B M hM, ?_,
    Spec.map (CommRingCat.ofHom ψ) ≫ hUa.fromSpec, ?_, fun q => ?_⟩
  · refine IsFractionRing.of_field _ _ fun a => ?_
    obtain ⟨g, hg, h, hh, -, e⟩ := FlagBun.FracChart.exists_eq_div_adjoin X Ω ξ κ x c T hc a
    exact ⟨⟨g, hAB g hg⟩, ⟨h, hAB h hh⟩, e⟩
  · have e0 : Spec.map (Scheme.stalkClosedPointTo ξ) ≫ X.fromSpecStalk (genPt ξ) = ξ :=
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
    have e1 : X.fromSpecStalk (genPt ξ) = Spec.map (X.presheaf.germ U _ hg) ≫ hUa.fromSpec :=
      (hUa.fromSpecStalk_eq_fromSpecStalk hg).symm
    have e2 : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap B Ω) =
        X.presheaf.germ U _ hg ≫ Scheme.stalkClosedPointTo ξ := rfl
    refine Eq.trans ?_ e0
    rw [e1, ← Spec.map_comp_assoc]
    exact (congrArg (fun m => Spec.map m ≫ hUa.fromSpec) e2).trans (Spec.map_comp_assoc _ _ _)
  · have hunit : ∀ (P : PrimeSpectrum Γ(X, U)) (hP : hUa.fromSpec P = q.1) (b : ℕ),
        (b : Γ(X, U)) ∉ P.asIdeal ↔ unitAt ξ q (b : Ω) := by
      intro P hP b
      have hq : q.1 ∈ U := by
        rw [← hP, ← SetLike.mem_coe, ← hUa.range_fromSpec]
        exact ⟨P, rfl⟩
      have h1 : P ∈ hUa.fromSpec ⁻¹ᵁ X.basicOpen (b : Γ(X, U)) ↔ q.1 ∈ X.basicOpen (b : Γ(X, U)) := by
        rw [← hP]; rfl
      rw [hUa.fromSpec_preimage_basicOpen, X.mem_basicOpen _ _ hq, isUnit_iff_unitAt (T.gen.inj q), map_natCast,
        map_natCast] at h1
      exact h1
    have hrange := PrimeSpectrum.localization_comap_range B M
    rw [overZp_iff hp]
    constructor
    · rintro ⟨P, hP⟩
      have hP' : hUa.fromSpec (PrimeSpectrum.comap (algebraMap Γ(X, U) B) P) = q.1 := hP
      have hq : q.1 ∈ U := by
        rw [← hP', ← SetLike.mem_coe, ← hUa.range_fromSpec]
        exact ⟨_, rfl⟩
      refine ⟨((hUm _).1 hq).2, fun b hb => (hunit _ hP' b).1 fun hm => ?_⟩
      have hd := hrange.subset ⟨P, rfl⟩
      exact Set.disjoint_left.1 hd ⟨b, hb, rfl⟩ hm
    · rintro ⟨hq, hu⟩
      have hqU : q.1 ∈ (U : Set X) := (hUm _).2 ⟨q.2, hq⟩
      rw [← hUa.range_fromSpec] at hqU
      obtain ⟨P, hP⟩ := hqU
      have hd : (P : PrimeSpectrum Γ(X, U)) ∈ Set.range (PrimeSpectrum.comap (algebraMap Γ(X, U) B)) := by
        rw [hrange]
        refine Set.disjoint_left.2 ?_
        rintro _ ⟨b, hb, rfl⟩
        exact (hunit P hP b).2 (hu b hb)
      obtain ⟨Q, rfl⟩ := hd
      exact ⟨Q, hP⟩

end PositivityTheory.HtPt.Hcptgen
end
end
