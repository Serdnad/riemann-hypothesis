module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem herm_pos_toV_mulVec_of_pos {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ)
    (y : LKCx.grp G β) (z : Fin G.n → ℂ) (hz : 0 < (star z ⬝ᵥ LKCx.herm G v β *ᵥ z).re) :
    0 < (star (↑(LKCx.toV G v β y) *ᵥ z) ⬝ᵥ LKCx.herm G v β *ᵥ (↑(LKCx.toV G v β y) *ᵥ z)).re := by
  have hM : (↑(LKCx.toV G v β y) : Matrix (Fin G.n) (Fin G.n) ℂ) = G.psi v ↑(↑y : G.Cˣ × ℚˣ).1 := rfl
  have hs := GlobalTheory.ArchBound.herm_sim G β y v
  have hpos : (0 : ℝ) < ((↑(↑y : G.Cˣ × ℚˣ).2 : ℚ) : ℝ) := by exact_mod_cast y.2.2
  rw [hM, Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hs, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
  exact mul_pos hpos hz

private theorem actY_actY_inv {p : ℕ} [Fact p.Prime] {D : UPel.HT.Datum p} {G : HTGroup p} (L : Link D G)
    {β : G.Cˣ} (a : LKCx.grp G β) (w : VQ D) : actY L a (actY L a⁻¹ w) = w := by
  show L.rep _ (L.rep _ w) = w
  rw [← Module.End.mul_apply, ← map_mul]
  have h1 : ((↑(↑a : G.Cˣ × ℚˣ).1 : G.C) * ↑(↑a⁻¹ : G.Cˣ × ℚˣ).1) = 1 := by
    rw [← Units.val_mul, ← Prod.fst_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Prod.fst_one,
      Units.val_one]
  rw [h1, map_one, Module.End.one_apply]

theorem UpperTheory.Gal.W2.fixLine_of :
    UpperTheory.Gal.W2.ActY → UpperTheory.Gal.W2.FixLine := by
  intro hA
  unfold ActY at hA
  unfold FixLine
  intro p _ D G L v t₀ ρ β RD Q z hQ hrel y
  have hz0 : z.1 ≠ 0 := by
    intro h0
    have h1 := z.2
    rw [h0] at h1
    simp at h1
  have hinvmul : ∀ (y' : LKCx.grp G β) (x : Fin G.n → ℂ),
      (LKCx.toV G v β y'⁻¹).val *ᵥ ((LKCx.toV G v β y').val *ᵥ x) = x := by
    intro y' x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.one_mulVec]
  have hne : ∀ (y' : LKCx.grp G β) (c : ℂ), (LKCx.toV G v β y').val *ᵥ z.1 = c • z.1 → c ≠ 0 := by
    rintro y' c hc rfl
    rw [zero_smul] at hc
    apply hz0
    rw [← hinvmul y' z.1, hc, Matrix.mulVec_zero]
  have inv : ∀ y' : LKCx.grp G β, LKCx.FixL G v β y' z.1 → LKCx.FixL G v β y'⁻¹ z.1 := by
    rintro y' ⟨c, hc⟩
    have hc0 := hne y' c hc
    have h1 : z.1 = c • ((LKCx.toV G v β y'⁻¹).val *ᵥ z.1) := by
      rw [← Matrix.mulVec_smul, ← hc, hinvmul]
    refine ⟨c⁻¹, ?_⟩
    calc (LKCx.toV G v β y'⁻¹).val *ᵥ z.1
        = c⁻¹ • (c • ((LKCx.toV G v β y'⁻¹).val *ᵥ z.1)) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • z.1 := by rw [← h1]
  let zi : LKCx.PosV G v β := ⟨(LKCx.toV G v β y⁻¹).val *ᵥ z.1, herm_pos_toV_mulVec_of_pos G v β y⁻¹ z.1 z.2⟩
  let Q₂ : VQ D →+ Fin D.g → ℂ := Q.comp (actY L y).toAddMonoidHom
  have hQ₂ : ∀ w, Q₂ w = Q (actY L y w) := fun w => rfl
  have hback : ∀ w, Q₂ (actY L y⁻¹ w) = Q w := by
    intro w
    rw [hQ₂, actY_actY_inv]
  have hper : IsPerQ L β ρ Q₂ := (hA p D G L β y⁻¹).2.2.1 ρ Q Q₂ hQ hback
  have hrel₂ : RD.rel Q₂ zi.1 := RD.equiv y⁻¹ Q Q₂ z.1 hback hrel
  have key := RD.uniq Q Q₂ z zi hQ hper hrel hrel₂
  refine ⟨⟨fun hF => ?_, fun ⟨H, hH⟩ => ?_⟩, inv y⟩
  · obtain ⟨c, hc⟩ := inv y hF
    obtain ⟨h, hh⟩ := key.mpr ⟨c, hne _ c hc, hc⟩
    refine ⟨LinearMap.toMatrix' (h : (Fin D.g → ℂ) →ₗ[ℂ] Fin D.g → ℂ), fun w => ?_⟩
    rw [LinearMap.toMatrix'_mulVec, ← hQ₂, hh w]
    rfl
  · have hsurj : Function.Surjective (Matrix.toLin' H) := by
      rw [← LinearMap.range_eq_top]
      have hle : Submodule.span ℝ (Set.range ⇑Q) ≤ (LinearMap.range (Matrix.toLin' H)).restrictScalars ℝ := by
        rw [Submodule.span_le]
        rintro _ ⟨w, rfl⟩
        refine ⟨Q (actY L y⁻¹ w), ?_⟩
        rw [Matrix.toLin'_apply, ← hH, actY_actY_inv]
      rw [hQ.2.1] at hle
      exact eq_top_iff.mpr (fun x _ => hle (Submodule.mem_top : x ∈ (⊤ : Submodule ℝ (Fin D.g → ℂ))))
    have hinj := LinearMap.injective_iff_surjective.mpr hsurj
    obtain ⟨c, hc0, hc⟩ := key.mp ⟨LinearEquiv.ofBijective (Matrix.toLin' H) ⟨hinj, hsurj⟩, fun w => by
      show Q₂ w = Matrix.toLin' H (Q w)
      rw [Matrix.toLin'_apply, hQ₂, hH]⟩
    have h2 := inv y⁻¹ ⟨c, hc⟩
    rwa [inv_inv] at h2
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2

private theorem actY_inv_left {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {β : G.Cˣ}
    (y : GlobalTheory.LKCx.grp G β) (w : VQ D) : actY L y⁻¹ (actY L y w) = w := by
  show L.rep ((y⁻¹ : GlobalTheory.LKCx.grp G β) : G.Cˣ × ℚˣ).1 (L.rep ((y : G.Cˣ × ℚˣ).1 : G.C) w) = w
  rw [← Module.End.mul_apply, ← map_mul]
  simp

private theorem perMove (hA : ActY) {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)
    {v : InfinitePlace G.F} {t₀ : D.F →+* ℂ} {ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ} {β : G.Cˣ}
    (RD : RDic L v β ρ t₀) (hs : sh G β = β) (y : GlobalTheory.LKCx.grp G β) {Q'' : VQ D →+ (Fin D.g → ℂ)}
    (hQ : IsPerQ L β ρ Q'') (z : GlobalTheory.LKCx.PosV G v β) (hr : RD.rel Q'' z.1) :
    ∃ (Q₁ : VQ D →+ (Fin D.g → ℂ)) (z₁ : GlobalTheory.LKCx.PosV G v β), IsPerQ L β ρ Q₁ ∧
      (∀ w, Q₁ (actY L y w) = Q'' w) ∧ RD.rel Q₁ z₁.1 ∧
      z₁.1 = (GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1 := by
  obtain ⟨-, -, h3, h4⟩ := hA p D G L β y
  let Q₁ : VQ D →+ (Fin D.g → ℂ) := Q''.comp (actY L y⁻¹).toAddMonoidHom
  have e : ∀ w, Q₁ (actY L y w) = Q'' w := fun w => by
    show Q'' (actY L y⁻¹ (actY L y w)) = _
    rw [actY_inv_left]
  obtain ⟨z₁, hz₁⟩ := h4 v z hs
  refine ⟨Q₁, z₁, h3 ρ Q'' Q₁ hQ e, e, ?_, hz₁⟩
  rw [hz₁]
  exact RD.equiv y Q'' Q₁ z.1 e hr

private theorem same_mk {p : ℕ} [Fact p.Prime] {G : HTGroup p} {v : InfinitePlace G.F} (B : GlobalTheory.LKCx.Form G)
    (K : Subgroup G.GAf) (K' : Subgroup (Gr G 1)) (a b : GlobalTheory.LKCx.Dat G v B.β) (y : GlobalTheory.LKCx.grp G B.β) (c : ℂ)
    (hc : c ≠ 0) (h1 : b.1.1⁻¹ * B.toAf y * a.1.1 ∈ K) (h2 : b.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * a.1.2 ∈ K')
    (hz : b.2.1 = c • ((GlobalTheory.LKCx.toV G v B.β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a.2.1)) :
    GlobalTheory.LKCx.Same G v B.β B.trivAf.choose B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec K K' a b := by
  refine ⟨y, ((b.1.1⁻¹ * B.toAf y * a.1.1)⁻¹, (b.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * a.1.2)⁻¹), c,
    inv_mem h1, inv_mem h2, hc, ?_, hz⟩
  change b.1 = (B.toAf y, GlobalTheory.LKCx.toP1 G B.β y) * a.1 * _
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_mul]
    group
  · simp only [Prod.snd_mul]
    group

private theorem same_of_eq {p : ℕ} [Fact p.Prime] {G : HTGroup p} {v : InfinitePlace G.F} (B : GlobalTheory.LKCx.Form G)
    (K : Subgroup G.GAf) (K' : Subgroup (Gr G 1)) (a b : GlobalTheory.LKCx.Dat G v B.β)
    (h : (Quot.mk _ a : GlobalTheory.LKCx.Form.Pts v B K K') = Quot.mk _ b) :
    GlobalTheory.LKCx.Same G v B.β B.trivAf.choose B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec K K' b a := by
  have key : ∀ a b : GlobalTheory.LKCx.Dat G v B.β,
      Relation.EqvGen (GlobalTheory.LKCx.Same G v B.β B.trivAf.choose B.trivAf.choose_spec.choose
        B.trivAf.choose_spec.choose_spec K K') a b →
      (∃ y : GlobalTheory.LKCx.grp G B.β, y • GlobalTheory.CxUnfold.OrbitSumGen.pairOfDat G v B.β B.trivAf.choose
          B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec K K' a =
        GlobalTheory.CxUnfold.OrbitSumGen.pairOfDat G v B.β B.trivAf.choose
          B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec K K' b) ∧
      (∃ y : GlobalTheory.LKCx.grp G B.β, y • GlobalTheory.CxUnfold.OrbitSumGen.pairOfDat G v B.β B.trivAf.choose
          B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec K K' b =
        GlobalTheory.CxUnfold.OrbitSumGen.pairOfDat G v B.β B.trivAf.choose
          B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec K K' a) := by
    intro a b hab
    induction hab with
    | rel x y hxy =>
      obtain ⟨g, hg⟩ := (GlobalTheory.CxUnfold.OrbitSumGen.same_iff_smul _ _ _ _ _ _ _ _ x y).1 hxy
      exact ⟨⟨g, hg⟩, ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩⟩
    | refl x => exact ⟨⟨1, one_smul _ _⟩, ⟨1, one_smul _ _⟩⟩
    | symm x y _ ih => exact ⟨ih.2, ih.1⟩
    | trans x y z _ _ ih1 ih2 =>
      obtain ⟨⟨g1, hg1⟩, ⟨h1, hh1⟩⟩ := ih1
      obtain ⟨⟨g2, hg2⟩, ⟨h2, hh2⟩⟩ := ih2
      exact ⟨⟨g2 * g1, by rw [mul_smul, hg1, hg2]⟩, ⟨h1 * h2, by rw [mul_smul, hh2, hh1]⟩⟩
  exact (GlobalTheory.CxUnfold.OrbitSumGen.same_iff_smul _ _ _ _ _ _ _ _ b a).2 (key a b (Quot.eqvGen_exact h)).2

end UpperTheory.Gal.W2

private theorem ext_lemma {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {β : G.Cˣ}
    {D' : PLat D.O D.inv} {j : D'.La →+ VQ D} (hj : IsPlace L β D' j) (Q Q₁ : VQ D →+ (Fin D.g → ℂ))
    (h : (Fin D.g → ℂ) ≃ₗ[ℂ] (Fin D.g → ℂ)) (hQ : ∀ u, Q (j u) = h (Q₁ (j u))) :
    ∀ w, Q w = h (Q₁ w) := by
  intro w
  obtain ⟨m, u, hm, hmu⟩ := hj.2.2.1 w
  have key : m • Q w = m • h (Q₁ w) := by
    rw [← map_nsmul Q, hmu, hQ, ← hmu, map_nsmul Q₁, map_nsmul h]
  exact smul_right_injective _ hm key

theorem UpperTheory.Gal.W2.coordIso_of :
    UpperTheory.Gal.W2.LatForm → UpperTheory.Gal.W2.LatIso → UpperTheory.Gal.W2.ActY → UpperTheory.Gal.W2.CoordIso := by
  intro hF hI hA p _ D G L v t₀ ρ PD RD N hN hNp D' t P D'' t'' P'' hc hc'' q q'' a a'' j j'' ha ha''
  obtain ⟨hpl, hca, hlp, Q, hQ, hQj, hr⟩ := ha
  obtain ⟨hpl'', hca'', hlp'', Q'', hQ'', hQj'', hr''⟩ := ha''
  constructor
  · rintro ⟨w, h, hw, hPh⟩
    obtain ⟨y, s, hs, hy, hjw⟩ := hF p D G L _ _ D' D'' j j'' hpl hpl'' w.toLinearMap 1 one_pos
      (by intro u u'; rw [_root_.one_mul]; exact hw.1 u u')
    have hjw' : ∀ u, j (w u) = L.rep (y : G.C) (j'' u) := hjw
    have hrel : GlobalTheory.LKCx.Form.Rel (Quot.out q'') (Quot.out q) := by
      refine ⟨y, (s : ℚ)⁻¹, inv_pos.mpr hs, ?_⟩
      rw [hy, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ (ne_of_gt hs), map_one, _root_.one_mul]
    have hq : q'' = q :=
      (Quot.out_eq (q'' : Quot GlobalTheory.LKCx.Form.Rel)).symm.trans
        ((Quot.sound hrel).trans (Quot.out_eq (q : Quot GlobalTheory.LKCx.Form.Rel)))
    subst hq
    let yy : GlobalTheory.LKCx.grp G (Quot.out q'').β := ⟨(y, s), hy, hs⟩
    obtain ⟨Q₁, z₁, hQ₁, hQ₁y, hr₁, hz₁⟩ := perMove hA L (RD _) (Quot.out q'').sym yy hQ'' a''.2 hr''
    have hext : ∃ h' : (Fin D.g → ℂ) ≃ₗ[ℂ] (Fin D.g → ℂ), ∀ w0, Q w0 = h' (Q₁ w0) := by
      refine ⟨h, ext_lemma hpl Q Q₁ h ?_⟩
      intro u
      obtain ⟨u'', rfl⟩ := w.surjective u
      rw [hQj, hPh, ← hQj'', ← hQ₁y, hjw']
      rfl
    obtain ⟨c, hc0, hac⟩ := ((RD _).uniq Q₁ Q z₁ a.2 hQ₁ hQ hr₁ hr).1 hext
    have hmem := (hI p D G L (Quot.out q'') (PD _) N hN hNp D' t D'' t'' j j'' a.1 a''.1 N N t t''
      hc hc'' hpl hpl'' hca hca'' hlp hlp'' yy).2 ⟨w, hw, hjw'⟩
    exact congrArg (Sigma.mk _)
      (Quot.sound (same_mk _ _ _ a'' a yy c hc0 hmem.1 hmem.2 (by rw [hac, hz₁]))).symm
  · intro heq
    obtain ⟨hq, hh⟩ := Sigma.mk.inj heq
    subst hq
    obtain ⟨y, k, c, hk1, hk2, hc0, hk, hz⟩ := same_of_eq _ _ _ a a'' (eq_of_heq hh)
    have hmem1 : a.1.1⁻¹ * (Quot.out q).toAf y * a''.1.1 ∈ L.KN N := by
      have e : a.1.1 = (Quot.out q).toAf y * a''.1.1 * k.1 := congrArg Prod.fst hk
      have e2 : ((Quot.out q).toAf y * a''.1.1 * k.1)⁻¹ * (Quot.out q).toAf y * a''.1.1 = k.1⁻¹ := by
        group
      rw [e, e2]
      exact inv_mem hk1
    have hmem2 : a.1.2⁻¹ * GlobalTheory.LKCx.toP1 G (Quot.out q).β y * a''.1.2 ∈ KHT p G.m G.n 1 G.Fw := by
      have e : a.1.2 = GlobalTheory.LKCx.toP1 G (Quot.out q).β y * a''.1.2 * k.2 := congrArg Prod.snd hk
      have e2 : (GlobalTheory.LKCx.toP1 G (Quot.out q).β y * a''.1.2 * k.2)⁻¹ * GlobalTheory.LKCx.toP1 G (Quot.out q).β y *
          a''.1.2 = k.2⁻¹ := by
        group
      rw [e, e2]
      exact inv_mem hk2
    obtain ⟨w, hw, hjw⟩ := (hI p D G L (Quot.out q) (PD _) N hN hNp D' t D'' t'' j j'' a.1 a''.1 N N t t''
      hc hc'' hpl hpl'' hca hca'' hlp hlp'' y).1 ⟨hmem1, hmem2⟩
    obtain ⟨Q₁, z₁, hQ₁, hQ₁y, hr₁, hz₁⟩ := perMove hA L (RD _) (Quot.out q).sym y hQ'' a''.2 hr''
    obtain ⟨h, hh'⟩ := ((RD _).uniq Q₁ Q z₁ a.2 hQ₁ hQ hr₁ hr).2 ⟨c, hc0, by rw [hz, hz₁]⟩
    refine ⟨w, h, hw, fun u => ?_⟩
    rw [← hQj, hjw, hh', hQ₁y, hQj'']
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem herm_add_right {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (x a b : Fin g → ℂ) :
    hermForm M x (a + b) = hermForm M x a + hermForm M x b := by
  simp [hermForm, Matrix.mulVec_add, dotProduct_add]

private theorem herm_add_left {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (a b y : Fin g → ℂ) :
    hermForm M (a + b) y = hermForm M a y + hermForm M b y := by
  simp [hermForm, add_dotProduct]

private theorem herm_smul_right {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (x a : Fin g → ℂ) :
    hermForm M x (c • a) = star c * hermForm M x a := by
  simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private theorem herm_smul_left {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (a y : Fin g → ℂ) :
    hermForm M (c • a) y = c * hermForm M a y := by
  simp only [hermForm, smul_dotProduct, smul_eq_mul]

private theorem herm_sub_smul {g : ℕ} (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ) (t : ℂ) (x y : Fin g → ℂ) :
    hermForm (H₁ - t • H₂) x y = hermForm H₁ x y - t * hermForm H₂ x y := by
  simp [hermForm, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul]

private theorem real_smul_eq {g : ℕ} (c : ℝ) (a : Fin g → ℂ) : c • a = (c : ℂ) • a := by
  ext i; simp

private theorem herm_im_zero {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (s : Set (Fin g → ℂ))
    (hs : Submodule.span ℝ s = ⊤) (h : ∀ x ∈ s, ∀ y ∈ s, (hermForm M x y).im = 0) (z w : Fin g → ℂ) :
    (hermForm M z w).im = 0 := by
  have key : ∀ w ∈ s, ∀ z, (hermForm M z w).im = 0 := by
    intro w hw z
    have hz : z ∈ Submodule.span ℝ s := by rw [hs]; trivial
    induction hz using Submodule.span_induction with
    | mem x hx => exact h x hx w hw
    | zero => simp [hermForm]
    | add a b _ _ ha hb => rw [herm_add_left]; simp [ha, hb]
    | smul c a _ ha => rw [real_smul_eq, herm_smul_left]; simp [ha]
  have hw : w ∈ Submodule.span ℝ s := by rw [hs]; trivial
  induction hw using Submodule.span_induction with
  | mem y hy => exact key y hy z
  | zero => simp [hermForm]
  | add a b _ _ ha hb => rw [herm_add_right]; simp [ha, hb]
  | smul c a _ ha => rw [real_smul_eq, herm_smul_right]; simp [ha]

private theorem bil_dvd {M : Type} [AddCommGroup M] (Bf : LinearMap.BilinForm ℤ M) (n : ℕ) (x y e e' : M) :
    (n : ℤ) ∣ Bf (x + n • e) (y + n • e') - Bf x y := by
  refine ⟨Bf x e' + Bf e y + n * Bf e e', ?_⟩
  simp [map_add (f := _), map_nsmul, LinearMap.add_apply, nsmul_eq_mul]
  ring

private theorem form_step {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (h : G.GAf) (n : ℕ)
    {a a' b b' : D.La} {w w' : AfP p ⊗[ℚ] VQ D} (hw : w ∈ LaHat D) (hw' : w' ∈ LaHat D)
    (e : L.actG h (inAf D a) = inAf D b + n • w) (e' : L.actG h (inAf D a') = inAf D b' + n • w') :
    ∃ i : AfP p, IsIntAf i ∧ ((D.EF b b' : ℤ) : AfP p) =
      ((uSimR (AfP p) h : (AfP p)ˣ) : AfP p) * ((D.EF a a' : ℤ) : AfP p) + (n : AfP p) * i := by
  have h1 := MultScale.EFA_actG L h (inAf D a) (inAf D a')
  rw [e, e', MultScale.EFA_inAf] at h1
  simp only [map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul,
    MultScale.EFA_inAf] at h1
  have hn : IsIntAf (n : AfP p) := by
    have := MultScale.isIntAf_intCast (p := p) (n : ℤ)
    simpa using this
  refine ⟨-(MultScale.EFA D (inAf D b) w' + MultScale.EFA D w (inAf D b') +
    (n : AfP p) * MultScale.EFA D w w'), ?_, ?_⟩
  · exact MultScale.isIntAf_neg (MultScale.isIntAf_add (MultScale.isIntAf_add
      (MultScale.isIntAf_EFA D (MultScale.inAf_mem D b) hw')
      (MultScale.isIntAf_EFA D hw (MultScale.inAf_mem D b')))
      (MultScale.isIntAf_mul hn (MultScale.isIntAf_EFA D hw hw')))
  · linear_combination h1

private theorem cross_dvd {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (h : G.GAf)
    {D' D'' : PLat D.O D.inv} (inc : D'.La →ₗ[D.O] D''.La) {f : ℕ → D.La →+ D'.La} {nu : ℕ → ℤ}
    {f'' : ℕ → D.La →+ D''.La} {nu'' : ℕ → ℤ} (hf : IsWit D' f nu) (hf'' : IsWit D'' f'' nu'')
    (hyp : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ a b : D.La,
      (∃ u, inc (f n a) = f'' n b + n • u) ↔ ∃ w ∈ LaHat D, L.actG h (inAf D a) = inAf D b + n • w)
    (u₁ u₂ u₃ u₄ : D'.La) (n : ℕ) (hn : 0 < n) (hc : n.Coprime p) :
    (n : ℤ) ∣ D''.EF (inc u₁) (inc u₂) * D'.EF u₃ u₄ - D''.EF (inc u₃) (inc u₄) * D'.EF u₁ u₂ := by
  unfold IsWit at hf hf''
  have hX : ∀ x x' : D'.La, ∃ b b' a a' : D.La,
      (D''.EF (inc x) (inc x') ≡ nu'' n * (2 * D.EF b b') [ZMOD n]) ∧
      (D'.EF x x' ≡ nu n * (2 * D.EF a a') [ZMOD n]) ∧
      ∃ i : AfP p, IsIntAf i ∧ ((D.EF b b' : ℤ) : AfP p) =
        ((uSimR (AfP p) h : (AfP p)ˣ) : AfP p) * ((D.EF a a' : ℤ) : AfP p) + (n : AfP p) * i := by
    intro x x'
    obtain ⟨a, e, rfl⟩ := (hf.2 n hn hc).2.2.2.1 x
    obtain ⟨a', e', rfl⟩ := (hf.2 n hn hc).2.2.2.1 x'
    obtain ⟨b, E, hb⟩ := (hf''.2 n hn hc).2.2.2.1 (inc (f n a))
    obtain ⟨b', E', hb'⟩ := (hf''.2 n hn hc).2.2.2.1 (inc (f n a'))
    obtain ⟨w, hw, hwe⟩ := (hyp n hn hc a b).1 ⟨E, hb⟩
    obtain ⟨w', hw', hwe'⟩ := (hyp n hn hc a' b').1 ⟨E', hb'⟩
    refine ⟨b, b', a, a', ?_, ?_, form_step L h n hw hw' hwe hwe'⟩
    · have h1 : inc (f n a + n • e) = f'' n b + n • (E + inc e) := by
        rw [map_add (f := _), map_nsmul, hb, smul_add, add_assoc]
      have h2 : inc (f n a' + n • e') = f'' n b' + n • (E' + inc e') := by
        rw [map_add (f := _), map_nsmul, hb', smul_add, add_assoc]
      rw [h1, h2]
      exact (Int.modEq_iff_dvd.mpr (bil_dvd D''.EF n _ _ _ _)).symm.trans
        (Int.modEq_iff_dvd.mpr ((hf''.2 n hn hc).2.2.2.2 b b')).symm
    · exact (Int.modEq_iff_dvd.mpr (bil_dvd D'.EF n _ _ _ _)).symm.trans
        (Int.modEq_iff_dvd.mpr ((hf.2 n hn hc).2.2.2.2 a a')).symm
  obtain ⟨b1, b2, a1, a2, hX1, hY1, i12, hi12, he12⟩ := hX u₁ u₂
  obtain ⟨b3, b4, a3, a4, hX3, hY3, i34, hi34, he34⟩ := hX u₃ u₄
  have hZ : (n : ℤ) ∣ D.EF b1 b2 * D.EF a3 a4 - D.EF b3 b4 * D.EF a1 a2 := by
    apply IntDvd.int_dvd_of_eq_mul_isIntAf p n hn hc _
      (i12 * ((D.EF a3 a4 : ℤ) : AfP p) - i34 * ((D.EF a1 a2 : ℤ) : AfP p))
    · rw [sub_eq_add_neg]
      exact MultScale.isIntAf_add (MultScale.isIntAf_mul hi12 (MultScale.isIntAf_intCast _))
        (MultScale.isIntAf_neg (MultScale.isIntAf_mul hi34 (MultScale.isIntAf_intCast _)))
    · rw [map_intCast]
      push_cast
      linear_combination ((D.EF a3 a4 : ℤ) : AfP p) * he12 - ((D.EF a1 a2 : ℤ) : AfP p) * he34
  have h0 : nu'' n * (2 * D.EF b1 b2) * (nu n * (2 * D.EF a3 a4)) -
      nu'' n * (2 * D.EF b3 b4) * (nu n * (2 * D.EF a1 a2)) ≡ 0 [ZMOD n] := by
    apply Int.modEq_zero_iff_dvd.mpr
    obtain ⟨k, hk⟩ := hZ
    exact ⟨4 * nu'' n * nu n * k, by linear_combination (4 * nu'' n * nu n) * hk⟩
  exact Int.modEq_zero_iff_dvd.mp (((hX1.mul hY3).sub (hX3.mul hY1)).trans h0)

private theorem cross {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (h : G.GAf)
    {D' D'' : PLat D.O D.inv} (inc : D'.La →ₗ[D.O] D''.La) {f : ℕ → D.La →+ D'.La} {nu : ℕ → ℤ}
    {f'' : ℕ → D.La →+ D''.La} {nu'' : ℕ → ℤ} (hf : IsWit D' f nu) (hf'' : IsWit D'' f'' nu'')
    (hyp : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ a b : D.La,
      (∃ u, inc (f n a) = f'' n b + n • u) ↔ ∃ w ∈ LaHat D, L.actG h (inAf D a) = inAf D b + n • w)
    (u₁ u₂ u₃ u₄ : D'.La) :
    D''.EF (inc u₁) (inc u₂) * D'.EF u₃ u₄ = D''.EF (inc u₃) (inc u₄) * D'.EF u₁ u₂ := by
  set d := D''.EF (inc u₁) (inc u₂) * D'.EF u₃ u₄ - D''.EF (inc u₃) (inc u₄) * D'.EF u₁ u₂ with hd
  suffices hz : d = 0 by exact sub_eq_zero.mp hz
  have hn : 0 < p * d.natAbs + 1 := Nat.succ_pos _
  have hc : (p * d.natAbs + 1).Coprime p :=
    ((Nat.coprime_mul_left_add_right p 1 d.natAbs).mpr (Nat.coprime_one_right p)).symm
  have hdvd := cross_dvd L h inc hf hf'' hyp u₁ u₂ u₃ u₄ _ hn hc
  apply Int.eq_zero_of_abs_lt_dvd hdvd
  have hp : (2 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  rw [Int.abs_eq_natAbs]
  push_cast
  nlinarith [Int.natCast_nonneg d.natAbs]

theorem UpperTheory.Gal.W2.isogForm_of :
    UpperTheory.Gal.W2.RdForm → UpperTheory.Gal.W2.IsogForm := by
  intro _ p _ D G L h ρ D' D'' P P'' inc hP hP'' hPinc f nu f'' nu'' hf hf'' hyp
  by_cases hall : ∀ u u' : D'.La, D'.EF u u' = 0
  · refine ⟨1, one_pos, fun u u' => ?_⟩
    have h0 : ∀ x : D'.La, x = 0 := fun x => D'.nondeg x (hall x)
    rw [h0 u]
    simp
  push_neg at hall
  obtain ⟨u₃, u₄, hne⟩ := hall
  have hrel : ∀ u u' : D'.La, ((D''.EF (inc u) (inc u') : ℤ) : ℚ) =
      ((D''.EF (inc u₃) (inc u₄) : ℚ) / (D'.EF u₃ u₄ : ℚ)) * (D'.EF u u' : ℚ) := by
    intro u u'
    have hcq : ((D'.EF u₃ u₄ : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hne
    rw [div_mul_eq_mul_div, eq_div_iff hcq]
    exact_mod_cast cross L h inc hf hf'' hyp u u' u₃ u₄
  refine ⟨(D''.EF (inc u₃) (inc u₄) : ℚ) / (D'.EF u₃ u₄ : ℚ), ?_, hrel⟩
  unfold PELU.IsPeriod at hP hP''
  obtain ⟨-, hPinj, -, hspan, H1, -, hpos1, him1⟩ := hP
  obtain ⟨-, -, -, -, H2, -, hpos2, him2⟩ := hP''
  set q : ℚ := (D''.EF (inc u₃) (inc u₄) : ℚ) / (D'.EF u₃ u₄ : ℚ) with hq
  have hzero : ∀ z w, (hermForm (H2 - ((q : ℝ) : ℂ) • H1) z w).im = 0 := by
    apply herm_im_zero _ (Set.range P) hspan
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [herm_sub_smul, Complex.sub_im, Complex.im_ofReal_mul, him1, ← hPinc x, ← hPinc y, him2]
    have hr : ((D''.EF (inc x) (inc y) : ℤ) : ℝ) = (q : ℝ) * ((D'.EF x y : ℤ) : ℝ) := by
      have := congrArg (fun t : ℚ => (t : ℝ)) (hrel x y)
      simpa [hq] using this
    rw [hr]
    ring
  have hM : ∀ z w, hermForm (H2 - ((q : ℝ) : ℂ) • H1) z w = 0 := by
    intro z w
    apply Complex.ext
    · have := hzero (Complex.I • z) w
      rw [herm_smul_left] at this
      simpa using this
    · simpa using hzero z w
  have hu3 : P u₃ ≠ 0 := by
    intro h0
    have hu : u₃ = 0 := hPinj (by rw [h0, map_zero])
    apply hne
    rw [hu]
    simp
  have e := hM (P u₃) (P u₃)
  rw [herm_sub_smul, sub_eq_zero] at e
  have p1 := hpos1 _ hu3
  have p2 := hpos2 _ hu3
  rw [e, Complex.re_ofReal_mul] at p2
  have hpos : (0 : ℝ) < (q : ℝ) := lt_of_not_ge (fun hle => by nlinarith)
  exact Rat.cast_pos.mp hpos
end
