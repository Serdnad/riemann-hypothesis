module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem u_eq_of_marked {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ}
    {Λ : Type} {F : Fam ℂ O Λ g} {N : ℕ} {Cl : ∀ D' : PLat O bar, (Λ → D'.La) → Prop}
    (U : Unif F (RingHom.id ℂ) ρ N Cl) (i i' : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ))
    (P' : (U.Di i').La →+ (Fin g → ℂ)) (hP : IsPeriod (U.Di i) ρ P) (hP' : IsPeriod (U.Di i') ρ P')
    (w : (U.Di i').La ≃ₗ[O] (U.Di i).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hw : IsMarkedIsom N (U.Di i') (U.Di i) (U.t i') (U.t i) w) (hh : ∀ u, P (w u) = h (P' u)) :
    U.u i' P' = U.u i P := by
  obtain rfl := U.distinct i' i w hw
  exact (U.fibre i' P' P hP' hP).2 ⟨w, h, hw, hh⟩

private theorem marked_of_u_eq {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ}
    {Λ : Type} {F : Fam ℂ O Λ g} {N : ℕ} {Cl : ∀ D' : PLat O bar, (Λ → D'.La) → Prop}
    (U : Unif F (RingHom.id ℂ) ρ N Cl) (i i' : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ))
    (P' : (U.Di i').La →+ (Fin g → ℂ)) (hP : IsPeriod (U.Di i) ρ P) (hP' : IsPeriod (U.Di i') ρ P')
    (e : U.u i' P' = U.u i P) :
    ∃ (w : (U.Di i').La ≃ₗ[O] (U.Di i).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      IsMarkedIsom N (U.Di i') (U.Di i) (U.t i') (U.t i) w ∧ ∀ u, P (w u) = h (P' u) := by
  obtain rfl := U.disj i' i P' P hP' hP e
  exact (U.fibre i' P' P hP' hP).1 e

private theorem isPeriod_comp {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ}
    {D' D'' : PLat O bar} {P : D'.La →+ (Fin g → ℂ)} (hP : IsPeriod D' ρ P) (w : D''.La ≃ₗ[O] D'.La)
    (hw : IsIsom D'' D' w) : IsPeriod D'' ρ (P.comp w.toLinearMap.toAddMonoidHom) := by
  obtain ⟨h1, h2, h3, h4, Hm, hH, hpos, hEF⟩ := hP
  have hs : Set.range (P.comp w.toLinearMap.toAddMonoidHom) = Set.range P := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨w x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨w.symm x, by simp⟩
  have hr : (P.comp w.toLinearMap.toAddMonoidHom).range = P.range := by
    ext z
    exact Set.ext_iff.1 hs z
  refine ⟨fun a x => ?_, h2.comp w.injective, ?_, ?_, Hm, hH, hpos, fun x y => ?_⟩
  · show P (w (a • x)) = _
    rw [map_smul, h1]
    rfl
  · rw [hr]
    exact h3
  · rw [hs]
    exact h4
  · show (hermForm Hm (P (w x)) (P (w y))).im = _
    rw [hEF, hw x y]

private theorem marked_symm {O : Type} [Ring O] {bar : O → O} {Λ : Type} {N : ℕ} {D₁ D₂ : PLat O bar}
    {t₁ : Λ → D₁.La} {t₂ : Λ → D₂.La} {w : D₁.La ≃ₗ[O] D₂.La} (h : IsMarkedIsom N D₁ D₂ t₁ t₂ w) :
    IsMarkedIsom N D₂ D₁ t₂ t₁ w.symm := by
  refine ⟨fun x y => ?_, fun a => ?_⟩
  · have := h.1 (w.symm x) (w.symm y)
    simpa using this.symm
  · obtain ⟨e, he⟩ := h.2 a
    refine ⟨-(w.symm e), ?_⟩
    have h2 := congrArg w.symm he
    rw [LinearEquiv.symm_apply_apply, map_add (f := _), map_nsmul] at h2
    rw [h2, smul_neg]
    abel

theorem UpperTheory.Gal.W2.unifG_of :
    UpperTheory.Gal.W2.CoordEx → UpperTheory.Gal.W2.CoordOcc → UpperTheory.Gal.W2.CoordIso → UpperTheory.Gal.W2.CoordMove → UpperTheory.Gal.W2.UnifG := by
  intro hEx hOcc hIso hMove p _ D G L hDa hDm v hv t₀ ht₀ ρ hρ PD RD N hN hNp F U
  have hch : ∀ x : CxPts F.s (RingHom.id ℂ), ∃ (i : Fin U.n) (P : (U.Di i).La →+ (Fin D.g → ℂ))
      (q : GlobalTheory.LKCx.FCls G) (a : GlobalTheory.LKCx.Dat G v (Quot.out q).β) (j : (U.Di i).La →+ VQ D),
      IsPeriod (U.Di i) ρ P ∧ x.1 = U.u i P ∧ IsCoord L (Quot.out q) (PD _) (RD _) N (U.Di i) (U.t i) P j a := by
    intro x
    obtain ⟨i, P, hP, hu⟩ := U.onto x.1 x.2
    obtain ⟨q, a, j, hc⟩ := hEx p D G L hDa hDm v hv t₀ ht₀ ρ hρ PD RD N hN hNp (U.Di i) (U.t i) P (U.mem i) hP
    exact ⟨i, P, q, a, j, hP, hu.symm, hc⟩
  choose i P q a j hP hu hc using hch
  let Φ₀ : CxPts F.s (RingHom.id ℂ) → GlobalTheory.LKCx.AllPts G v (L.KN N) (KHT p G.m G.n 1 G.Fw) :=
    fun x => ⟨q x, Quot.mk _ (a x)⟩
  have hinj : Function.Injective Φ₀ := by
    intro x x' e
    obtain ⟨w, h, hw, hh⟩ := (hIso p D G L v t₀ ρ PD RD N hN hNp (U.Di (i x)) (U.t (i x)) (P x)
      (U.Di (i x')) (U.t (i x')) (P x') (U.mem _) (U.mem _) (q x) (q x') (a x) (a x') (j x) (j x')
      (hc x) (hc x')).2 e
    apply Subtype.ext
    rw [hu x, hu x']
    exact (u_eq_of_marked U _ _ _ _ (hP x) (hP x') w h hw hh).symm
  have hsurj : Function.Surjective Φ₀ := by
    rintro ⟨q₀, c⟩
    obtain ⟨a₀, rfl⟩ := Quot.exists_rep c
    obtain ⟨D', t, Pd, jd, hCl, hPd, hcd⟩ :=
      hOcc p D G L hDa hDm v hv t₀ ht₀ ρ hρ PD RD N hN hNp (Quot.out q₀) a₀
    obtain ⟨i₀, w, hw⟩ := U.all D' t hCl ⟨Pd, hPd⟩
    have hws := marked_symm hw
    let P₀ := Pd.comp w.symm.toLinearMap.toAddMonoidHom
    have hP₀ : IsPeriod (U.Di i₀) ρ P₀ := isPeriod_comp hPd w.symm hws.1
    let j₀ := jd.comp w.symm.toLinearMap.toAddMonoidHom
    have hc₀ : IsCoord L (Quot.out q₀) (PD _) (RD _) N (U.Di i₀) (U.t i₀) P₀ j₀ a₀ :=
      hMove p D G L v t₀ ρ (Quot.out q₀) (PD _) (RD _) N D' t Pd (U.Di i₀) (U.t i₀) P₀ w.symm hws
        (fun _ => rfl) jd j₀ (fun _ => rfl) a₀ hcd
    let x : CxPts F.s (RingHom.id ℂ) := ⟨U.u i₀ P₀, (U.unif i₀ P₀ hP₀).1⟩
    refine ⟨x, ?_⟩
    obtain ⟨w', h', hw', hh'⟩ := marked_of_u_eq U i₀ (i x) P₀ (P x) hP₀ (hP x) (hu x).symm
    exact ((hIso p D G L v t₀ ρ PD RD N hN hNp (U.Di i₀) (U.t i₀) P₀ (U.Di (i x)) (U.t (i x)) (P x)
      (U.mem _) (U.mem _) q₀ (q x) a₀ (a x) j₀ (j x) hc₀ (hc x)).1 ⟨w', h', hw', hh'⟩).symm
  exact ⟨Equiv.ofBijective Φ₀ ⟨hinj, hsurj⟩, fun x => ⟨q x, a x, i x, P x, j x, rfl, hP x, hu x, hc x⟩⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2.PActY

variable {p : ℕ} [Fact p.Prime]

private theorem sh_sh' (G : HTGroup p) (a : G.C) : sh G (sh G a) = a := G.star_star a

private theorem key (G : HTGroup p) (β y : G.Cˣ) (s : ℚ)
    (h : (y : G.C) * β * sh G y = algebraMap ℚ G.C s * β) :
    sh G y * ((β⁻¹ : G.Cˣ) : G.C) * y = algebraMap ℚ G.C s * ((β⁻¹ : G.Cˣ) : G.C) := by
  calc sh G y * ((β⁻¹ : G.Cˣ) : G.C) * y
      = ((β⁻¹ : G.Cˣ) : G.C) * ((y⁻¹ : G.Cˣ) : G.C) * ((y : G.C) * β * sh G y) * ((β⁻¹ : G.Cˣ) : G.C) * y := by
        simp only [_root_.mul_assoc, Units.inv_mul_cancel_left]
    _ = ((β⁻¹ : G.Cˣ) : G.C) * ((y⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C s * β) * ((β⁻¹ : G.Cˣ) : G.C) * y := by
        rw [h]
    _ = algebraMap ℚ G.C s * ((β⁻¹ : G.Cˣ) : G.C) := by
        simp only [_root_.mul_assoc, Units.mul_inv_cancel_left]
        rw [Algebra.commutes s (y : G.C), Units.inv_mul_cancel_left]
        exact (Algebra.commutes s _).symm

private theorem form_act {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ) (y : GlobalTheory.LKCx.grp G β)
    (u w : VQ D) : formB L β (actY L y u) (actY L y w) = (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) * formB L β u w := by
  have hk := key G β (y : G.Cˣ × ℚˣ).1 (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) y.2.1
  have h1 := L.adj (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))
    (L.rep ((β⁻¹ : G.Cˣ) : G.C) (L.rep (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) u)) w
  rw [sh_sh'] at h1
  have h2 : L.rep (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))
      (L.rep ((β⁻¹ : G.Cˣ) : G.C) (L.rep (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) u)) =
      (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) • L.rep ((β⁻¹ : G.Cˣ) : G.C) u := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hk, map_mul,
      AlgHom.commutes, Module.End.mul_apply, Module.algebraMap_end_apply]
  simp only [formB, actY]
  rw [← h1, h2, map_smul, LinearMap.smul_apply, smul_eq_mul]

private theorem act_comm {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ) (y : GlobalTheory.LKCx.grp G β)
    (c : D.O) (w : VQ D) : actY L y (actQ D c w) = actQ D c (actY L y w) := by
  have h := (L.rep_range (actY L y)).1 ⟨_, rfl⟩ c
  exact LinearMap.congr_fun h w

private theorem act_inv {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ) (y : GlobalTheory.LKCx.grp G β)
    (w : VQ D) : actY L y (L.rep (((((y : G.Cˣ × ℚˣ).1 : G.Cˣ))⁻¹ : G.Cˣ) : G.C) w) = w := by
  simp only [actY]
  rw [← Module.End.mul_apply, ← map_mul, Units.mul_inv, map_one, Module.End.one_apply]

private theorem per_act {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ) (y : GlobalTheory.LKCx.grp G β)
    (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (Q Q' : VQ D →+ (Fin D.g → ℂ)) (hP : IsPerQ L β ρ Q)
    (hQ : ∀ w, Q' (actY L y w) = Q w) : IsPerQ L β ρ Q' := by
  obtain ⟨h1, h2, Hm, hH, hpos, him⟩ := hP
  have hsc : ∀ (c : ℂ) (z z' : Fin D.g → ℂ), hermForm (c • Hm) z z' = c * hermForm Hm z z' := by
    intro c z z'
    simp only [hermForm, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hr : (0 : ℝ) < ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by
    exact_mod_cast y.prop.2
  have hQ' : ∀ u, Q' u = Q (L.rep ((((y : G.Cˣ × ℚˣ).1 : G.Cˣ)⁻¹ : G.Cˣ) : G.C) u) := by
    intro u
    rw [← hQ, act_inv]
  refine ⟨fun c w => ?_, ?_, (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) : ℂ) • Hm, ?_, fun z hz => ?_, fun u w => ?_⟩
  · rw [hQ', hQ', ← h1]
    congr 1
    exact LinearMap.congr_fun ((L.rep_range _).1 ⟨_, rfl⟩ c) w
  · rw [eq_top_iff, ← h2]
    apply Submodule.span_mono
    rintro _ ⟨w, rfl⟩
    exact ⟨_, hQ w⟩
  · simp [Matrix.IsHermitian, Matrix.conjTranspose_smul, hH.eq, Complex.star_def, Complex.conj_ofReal]
  · rw [hsc, Complex.re_ofReal_mul]
    exact mul_pos hr (hpos z hz)
  · rw [← act_inv L β y u, ← act_inv L β y w, hQ, hQ, hsc, form_act, Complex.im_ofReal_mul, him]
    push_cast
    ring

private theorem psi_rat (G : HTGroup p) (v : InfinitePlace G.F) (s : ℚ) :
    G.psi v (algebraMap ℚ G.C s) = ((s : ℝ) : ℂ) • (1 : Matrix (Fin G.n) (Fin G.n) ℂ) := by
  have he : v.embedding (algebraMap ℚ G.F s) = (s : ℂ) := map_ratCast (v.embedding.comp (algebraMap ℚ G.F)) s
  rw [IsScalarTower.algebraMap_apply ℚ G.F G.C, G.psi_F, he]
  ext i j
  simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]

private theorem pos_act (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (y : GlobalTheory.LKCx.grp G β)
    (z : GlobalTheory.LKCx.PosV G v β) :
    0 < (star ((GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1) ⬝ᵥ
      (GlobalTheory.LKCx.herm G v β *ᵥ ((GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1))).re := by
  have hk := key G β (y : G.Cˣ × ℚˣ).1 (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) y.prop.1
  have hr : (0 : ℝ) < ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by
    exact_mod_cast y.prop.2
  have hV : ((GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ)) =
      G.psi v (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) := rfl
  have hg : (G.psi v (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))ᴴ * G.gram v =
      G.gram v * G.psi v (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) := by
    rw [show sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
      MulOpposite.unop (G.star (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) from rfl, G.psi_star,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (G.gram_det v)), Matrix.one_mul]
  have hpsi : G.psi v (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) * G.psi v ((β⁻¹ : G.Cˣ) : G.C) *
      G.psi v (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
      (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) : ℂ) • G.psi v ((β⁻¹ : G.Cˣ) : G.C) := by
    rw [← map_mul, ← map_mul, hk, map_mul, psi_rat, smul_one_mul]
  have hM : (G.psi v (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))ᴴ * GlobalTheory.LKCx.herm G v β *
      G.psi v (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
      (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) : ℂ) • GlobalTheory.LKCx.herm G v β := by
    simp only [GlobalTheory.LKCx.herm]
    rw [← Matrix.mul_assoc, hg, ← Matrix.mul_smul, ← hpsi]
    simp only [Matrix.mul_assoc]
  rw [hV, Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hM, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
  exact mul_pos hr z.2

end UpperTheory.Gal.W2.PActY

open UpperTheory.Gal.W2.PActY in
theorem UpperTheory.Gal.W2.actY_of :
    UpperTheory.Gal.W2.ActY := by
  intro p _ D G L β y
  exact ⟨form_act L β y, act_comm L β y, fun ρ Q Q' hP hQ => per_act L β y ρ Q Q' hP hQ,
    fun v z _ => ⟨⟨_, pos_act G v β y z⟩, rfl⟩⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem rd_add' {p : ℕ} [Fact (Nat.Prime p)] {D : UPel.HT.Datum p} {G : HTGroup p}
    (L : Link D G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (h : G.GAf) (a b : VQ D) :
    rd L x h (a + b) = rd L x h a + rd L x h b := by
  simp only [rd, TensorProduct.tmul_add, map_add (f := _)]

private theorem rd_nsmul' {p : ℕ} [Fact (Nat.Prime p)] {D : UPel.HT.Datum p} {G : HTGroup p}
    (L : Link D G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (h : G.GAf) (N : ℕ) (a : VQ D) :
    rd L x h (N • a) = N • rd L x h a := by
  induction N with
  | zero => simp only [zero_smul, rd, TensorProduct.tmul_zero, map_zero]
  | succ n ih => rw [succ_nsmul, rd_add', ih, succ_nsmul]

theorem UpperTheory.Gal.W2.coordMove_of :
    UpperTheory.Gal.W2.CoordMove := by
  intro p _ D G L v t₀ ρ B PD RD N D' t P D'' t'' P'' w hw hP j j'' hj a ha
  obtain ⟨hiso, hmark⟩ := hw
  obtain ⟨⟨hinj, hact, hsurj, s, hs, hform⟩, ⟨hA1, hA2⟩, hloc, Q, hQ, hQj, hrel⟩ := ha
  have key : ∀ w0 : VQ D, (∃ u : D'.La, w0 = j u) ↔ ∃ u : D''.La, w0 = j'' u := by
    intro w0
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨w.symm u, by rw [hj, LinearEquiv.apply_symm_apply]⟩
    · rintro ⟨u, rfl⟩
      exact ⟨w u, hj u⟩
  refine ⟨⟨?_, ?_, ?_, s, hs, ?_⟩, ⟨?_, ?_⟩, ?_, Q, hQ, ?_, hrel⟩
  · intro u u' huu
    rw [hj, hj] at huu
    exact w.injective (hinj huu)
  · intro c u
    rw [hj, hj, map_smul, hact]
  · intro w0
    obtain ⟨m, u, hm, hmu⟩ := hsurj w0
    exact ⟨m, w.symm u, hm, by rw [hj, LinearEquiv.apply_symm_apply, hmu]⟩
  · intro u u'
    rw [hj, hj, ← hform, hiso]
  · intro w0
    rw [← hA1 w0]
    constructor
    · rintro ⟨r, u, hu⟩
      exact ⟨r, w u, by rw [hu, hj]⟩
    · rintro ⟨r, u, hu⟩
      exact ⟨r, w.symm u, by rw [hu, hj, LinearEquiv.apply_symm_apply]⟩
  · intro a0
    obtain ⟨e, he⟩ := hmark a0
    obtain ⟨w1, hw1, hw1e⟩ := hA2 a0
    have he' : rd L (trivX B) a.1.1 (j e) ∈ LaHat D := (hA1 (j e)).1 ⟨0, e, by simp⟩
    refine ⟨w1 + rd L (trivX B) a.1.1 (j e), add_mem hw1 he', ?_⟩
    rw [hj, he, map_add (f := _), map_nsmul, rd_add', rd_nsmul', hw1e, smul_add, add_assoc]
  · intro w0
    rw [← hloc w0]
    constructor
    · rintro ⟨m, u, hm, hu⟩
      exact ⟨m, w u, hm, by rw [hu, hj]⟩
    · rintro ⟨m, u, hm, hu⟩
      exact ⟨m, w.symm u, hm, by rw [hu, hj, LinearEquiv.apply_symm_apply]⟩
  · intro u
    rw [hj, hQj, hP]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.minBridge_of :
    UpperTheory.Gal.W2.MinBridge := by
  intro p _ D G L β D' j hP ga c hga
  obtain ⟨hinj, hsmul, hspan, -⟩ := hP
  set f : 𝓞 D.F →+* G.F := (L.e : D.F →+* G.F).comp (algebraMap (𝓞 D.F) D.F) with hf
  have hpow : ∀ (n : ℕ) (u : D'.La), j ((ga ^ n) u) = (L.rep c ^ n) (j u) := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ n ih =>
      intro u
      rw [pow_succ, Module.End.mul_apply, ih, hga, pow_succ, Module.End.mul_apply]
  have key : ∀ (q : (𝓞 D.F)[X]) (u : D'.La),
      j (q.sum fun i b => algebraMap (𝓞 D.F) D.O b • (ga ^ i) u) =
        L.rep (aeval c (q.map f)) (j u) := by
    intro q u

    rw [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.eval₂_eq_sum, Polynomial.sum_def,
    Polynomial.sum_def, map_sum, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsmul, hpow, map_mul, map_pow, Module.End.mul_apply, ← L.rep_F]
    rfl
  have hK : ∀ q : (𝓞 D.F)[X], Kills (algebraMap (𝓞 D.F) D.O) ga q ↔ aeval c (q.map f) = 0 := by
    intro q
    constructor
    · intro h
      apply L.rep_inj
      rw [map_zero]
      refine LinearMap.ext fun w => ?_
      obtain ⟨m, u, hm, hmu⟩ := hspan w
      have h1 : L.rep (aeval c (q.map f)) (j u) = 0 := by rw [← key, h u, map_zero]
      have h2 : m • L.rep (aeval c (q.map f)) w = 0 := by
        rw [← LinearMap.map_smul_of_tower, hmu, h1]
      rw [← Nat.cast_smul_eq_nsmul ℚ] at h2
      rw [LinearMap.zero_apply]
      exact (smul_eq_zero.mp h2).resolve_left (Nat.cast_ne_zero.mpr hm)
    · intro h x
      apply hinj
      rw [key, h, map_zero, LinearMap.zero_apply, map_zero]
  refine ⟨(minpoly.monic (Algebra.IsIntegral.isIntegral c)).map _, fun q => ?_⟩
  have hcomp : (L.e.symm : G.F →+* D.F).comp f = algebraMap (𝓞 D.F) D.F := by
    ext b
    simp [hf]
  rw [hK, ← minpoly.dvd_iff, ← map_dvd_iff (Polynomial.mapEquiv L.e.symm),
    Polynomial.mapEquiv_apply, Polynomial.mapEquiv_apply, Polynomial.map_map, hcomp]
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

private theorem actOn_inC {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (c : G.C) (w : VQ D) :
    actOn L.rep (AfP p) (inC G (AfP p) c) ((1 : AfP p) ⊗ₜ w) = (1 : AfP p) ⊗ₜ (L.rep c w) := by
  simp only [actOn, inC, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
  erw [Algebra.TensorProduct.lift_tmul]
  simp only [map_one, one_mul, Module.End.baseChangeHom, AlgHom.comp_apply]
  exact LinearMap.baseChange_tmul _ _ _

private theorem actG_toAf {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (B : GlobalTheory.LKCx.Form G)
    (y : GlobalTheory.LKCx.grp G B.β) (w : VQ D) :
    L.actG (B.toAf y) (actOn L.rep (AfP p) (trivX B : AfP p ⊗[ℚ] G.C) ((1 : AfP p) ⊗ₜ w)) =
      actOn L.rep (AfP p) (trivX B : AfP p ⊗[ℚ] G.C) ((1 : AfP p) ⊗ₜ (L.rep (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) w)) := by
  have hval : (L.actG (B.toAf y) : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D))
      = actOn L.rep (AfP p) ((trivX B : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)
          * (((trivX B)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) := rfl
  rw [hval, ← Module.End.mul_apply, ← map_mul,
    show (trivX B : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)
          * (((trivX B)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * (trivX B : AfP p ⊗[ℚ] G.C)
        = (trivX B : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) by
      simp [mul_assoc],
    map_mul, Module.End.mul_apply, actOn_inC]

theorem rdAct_of : RdAct := by
  intro p _ D G L B y h₁ h₂ w
  simp only [rd, actY]
  conv_rhs =>
    rw [← Module.End.mul_apply, ← map_mul, _root_.mul_assoc, _root_.mul_assoc, _root_.mul_inv_cancel, _root_.mul_one, map_mul,
      Module.End.mul_apply, actG_toAf]

end UpperTheory.Gal.W2
end
end

section

private theorem UpperTheory.Gal.W2.mul_inv_star_of_triv {S A : Type*} [Ring S] [CommRing A] [Algebra A S]
    (σ : S →+* Sᵐᵒᵖ) (b : S) (x x' : Sˣ) (t t' : Aˣ)
    (hx : (x : S) * b * (σ x).unop = algebraMap A S t)
    (hx' : (x' : S) * b * (σ x').unop = algebraMap A S t') :
    ((x * x'⁻¹ : Sˣ) : S) * (σ ((x * x'⁻¹ : Sˣ) : S)).unop = algebraMap A S ((t * t'⁻¹ : Aˣ) : A) := by
  have key : ∀ u : Sˣ, (σ (u : S)).unop * (σ ((u⁻¹ : Sˣ) : S)).unop = 1 := by
    intro u
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have hb : b = ((x'⁻¹ : Sˣ) : S) * (algebraMap A S t' * (σ ((x'⁻¹ : Sˣ) : S)).unop) := by
    rw [← hx']
    calc b = (((x'⁻¹ : Sˣ) : S) * x') * b * ((σ (x' : S)).unop * (σ ((x'⁻¹ : Sˣ) : S)).unop) := by
          rw [Units.inv_mul, key, one_mul, mul_one]
      _ = _ := by simp only [mul_assoc]
  rw [hb] at hx
  simp only [mul_assoc, Algebra.left_comm] at hx
  simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
  calc _ = algebraMap A S ((t'⁻¹ * t' : Aˣ) : A) * ((x : S) * (((x'⁻¹ : Sˣ) : S) *
        ((σ ((x'⁻¹ : Sˣ) : S)).unop * (σ (x : S)).unop))) := by simp
    _ = algebraMap A S ((t'⁻¹ : Aˣ) : A) * algebraMap A S t := by
        rw [Units.val_mul, map_mul, mul_assoc, hx]
    _ = _ := Algebra.commutes _ _

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.adOfWit_of :
    UpperTheory.Gal.W2.AdCore → UpperTheory.Gal.W2.AdOfWit := by
  intro hcore
  unfold AdCore at hcore
  unfold AdOfWit
  intro p _ D G L B D' j hpl f nu hw
  obtain ⟨x, c, hxc, hread⟩ := hcore p D G L B.β D' j hpl f nu hw
  obtain ⟨t0, ht0⟩ := B.trivAf.choose_spec
  have hmem : ((trivX B * x⁻¹, t0 * c⁻¹) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) ∈ UPts G.star (AfP p) := by
    rw [UPts, mem_uGroup]
    exact mul_inv_star_of_triv _ _ _ _ _ _ ht0 hxc
  let h : G.GAf := ⟨(trivX B * x⁻¹, t0 * c⁻¹), hmem⟩
  refine ⟨h, ?_⟩
  have hrd : ∀ w, rd L (trivX B) h w = rd L x 1 w := by
    intro w
    have hy : (((trivX B * x⁻¹)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * (trivX B : AfP p ⊗[ℚ] G.C) = x := by
      rw [← Units.val_mul]
      congr 1
      group
    simp only [rd, inv_one, map_one, one_apply_eq_self]
    rw [← hy, map_mul, mul_apply_eq_comp]
    rfl
  intro n hn hcop
  obtain ⟨h1, h2⟩ := hread n hn hcop
  exact ⟨fun w => by rw [hrd]; exact h1 w, fun a => by rw [hrd]; exact h2 a⟩
end
