import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdLB
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy

open AlgebraicGeometry CategoryTheory Limits MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt)

section Alg

variable {S : Type} [CommRing S] (d : ℕ)

abbrev swJ (m : ℕ) : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 2 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d =>
    (![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S)
      p.1 p.2

private theorem jetSubstP_apply_mk {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S)
    (p : MvPolynomial κ S) :
    jetSubstP m φ (Ideal.Quotient.mk (orig S κ ^ (m + 1)) p) =
      Ideal.Quotient.mk _ (aeval (fun i => φ i - C (MvPolynomial.constantCoeff (φ i))) p) := by
  rfl

theorem swJ_X (m : ℕ) (p : Fin 2 × Fin d) :
    swJ (S := S) d m (Ideal.Quotient.mk _ (X p)) = Ideal.Quotient.mk _ (X (Equiv.swap (0 : Fin 2) 1 p.1, p.2)) := by
  obtain ⟨i, j⟩ := p
  rw [jetSubstP_apply_mk, aeval_X]
  fin_cases i <;> simp

theorem swJ_swJ (m : ℕ) : (swJ (S := S) d m).comp (swJ d m) = AlgHom.id S _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro p
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, swJ_X, AlgHom.id_apply,
    Equiv.swap_apply_self]

theorem mk_psTrunc_X {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ) (q : τ) :
    (Ideal.Quotient.mk (orig S τ ^ (m + 1)) (psTrunc m (MvPowerSeries.X q))) = Ideal.Quotient.mk _ (X q) := by
  rw [FBIdJet.psTrunc_eq, ← MvPolynomial.coe_X]
  exact FBIdJet.mk_trunc_coe m (X q)

-- Retain the arithmetic lemma exported by the original truncation proof.
theorem mk_psTrunc_X._proof_1_1 {τ : Type} (m : ℕ) (q : τ) (h : ¬ 1 ≤ m) :
    (¬ m = 0) → False :=
  fun hn => hn (Nat.eq_zero_of_not_pos h)

theorem psJet_ev_swap (m : ℕ) (f : PS S 2 d) :
    psJet m (ev (n := 2) ![pt S d 1, pt S d 0] f) = swJ d m (psJet m f) := by
  have ha : ∀ p : Fin 2 × Fin d, MvPowerSeries.constantCoeff
      ((fun p : Fin 2 × Fin d => (![pt S d 1, pt S d 0] : Fin 2 → Pt S 2 d) p.1 p.2) p) = 0 := by
    rintro ⟨i, j⟩
    fin_cases i <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev
  rw [psJet_subst m _ ha f]
  refine DFunLike.congr_fun ?_ (psJet m f)
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [swJ_X, GermD.jetMap_mk, aeval_X]
  fin_cases i <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt, mk_psTrunc_X]

end Alg

section Axes

variable {S : Type} [CommRing S] (d : ℕ)

abbrev axJ (m : ℕ) (b : Bool) : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 1 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d =>
    (if b then ![fun _ => 0, fun j => X ((0 : Fin 1), j)] else ![fun j => X ((0 : Fin 1), j), fun _ => 0] :
      Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S) p.1 p.2

def axV (b : Bool) (k : Fin 2) (j : Fin d) : MvPolynomial (Fin 1 × Fin d) S :=
  if (k = 1) = b then X ((0 : Fin 1), j) else 0

theorem axJ_X (m : ℕ) (b : Bool) (k : Fin 2) (j : Fin d) :
    axJ (S := S) d m b (Ideal.Quotient.mk _ (X (k, j))) = Ideal.Quotient.mk _ (axV d b k j) := by
  rw [jetSubstP_apply_mk, aeval_X]
  cases b <;> fin_cases k <;> simp [axV]

theorem axJ_swJ (m : ℕ) (b : Bool) : (axJ (S := S) d m b).comp (swJ d m) = axJ d m (!b) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨k, j⟩
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, swJ_X, axJ_X]
  cases b <;> fin_cases k <;> simp [axV]

theorem psTrunc_zero {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ) :
    psTrunc m (0 : MvPowerSeries τ S) = 0 := by
  simp [psTrunc]

theorem psJet_ev_ax (m : ℕ) (f : PS S 2 d) (b : Bool) :
    psJet m (ev (n := 1) (if b then ![0, pt S d 0] else ![pt S d 0, 0]) f) = axJ d m b (psJet m f) := by
  have ha : ∀ p : Fin 2 × Fin d, MvPowerSeries.constantCoeff
      ((fun p : Fin 2 × Fin d => ((if b then ![0, pt S d 0] else ![pt S d 0, 0]) : Fin 2 → Pt S 1 d) p.1 p.2) p) = 0 := by
    rintro ⟨i, j⟩
    cases b <;> fin_cases i <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev
  rw [psJet_subst m _ ha f]
  refine DFunLike.congr_fun ?_ (psJet m f)
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨k, j⟩
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [axJ_X, GermD.jetMap_mk, aeval_X]
  cases b <;> fin_cases k <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt, mk_psTrunc_X, axV, psTrunc_zero]

end Axes

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

theorem scaleGenG_scaleGenG {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ)
    (v w : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb t.PP.L φ ε)) :
    scaleGenG t φ ε v (scaleGenG t φ ε w g) = scaleGenG t φ ε (v * w) g := by
  simp only [scaleGenG, Units.val_mul, map_mul, mul_assoc]

theorem unitΓ_mul {A : Type} [CommRing A] (a b : Aˣ) : unitΓ (a * b) = unitΓ a * unitΓ b := by
  exact map_mul (Units.map (toΓ A).toMonoidHom) a b

theorem unitΓ_one {A : Type} [CommRing A] : unitΓ (1 : Aˣ) = 1 := by
  exact map_one (Units.map (toΓ A).toMonoidHom)

theorem unit_eq_one_of_corr (hL : t.PP.L.IsLB) {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ t.G.left)}
    {ε : K → ℤ} {g : LB.Gen (LB.LinComb t.PP.L φ ε)} (hg : g.IsGen) {v : Γ(Y, ⊤)ˣ}
    (h : LB.Gen.Corr t.PP.L φ ε φ ε g (scaleGenG t φ ε v g)) : v = 1 := by
  have h1 := FBIdLB.scale_eq_of_corr t hL (DVR.corr_refl _ hg) (v := 1) (v' := v)
    (by rw [FBIdLB.scaleGenG_one]; exact h)
  exact h1.symm

theorem sy_unit (hL : t.PP.L.IsLB) {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S}
    {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S} {ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S}
    {sy : MvPowerSeries (Fin 2 × Fin d) S} {ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S}
    {e : ∀ m, FrTyG t x0 d x m} (hfr : IsFrameG t x0 d x F act ph1 ph2 sy ad e) (m : ℕ) :
    psJet m sy * swJ d m (psJet m sy) = 1 := by
  obtain ⟨u, hu, hc⟩ := hfr.sy m
  have hge := hfr.gen m
  have hhh : (homAt x0 (swJ (S := S) d m)).left ≫ (homAt x0 (swJ d m)).left = 𝟙 _ := by
    rw [← Over.comp_left, homAt_comp, swJ_swJ, homAt_id]
    rfl
  have h1 := DVR.corr_pullGen hc (homAt x0 (swJ (S := S) d m)).left
  rw [FBIdLB.pullGen_scaleGenG] at h1
  have h2 := DVR.corr_trans hL (DVR.corr_pullGen_comp (e m) (homAt x0 (swJ (S := S) d m)).left
    (homAt x0 (swJ (S := S) d m)).left)
    (DVR.corr_trans hL (DVR.corr_pullGen_of_eq (e m) hge _ _ hhh) (DVR.corr_pullGen_id (e m)))
  have h3 := DVR.corr_trans hL h1 (FBIdLB.corr_scaleGenG t h2 _)
  have h4 := DVR.corr_trans hL hc (FBIdLB.corr_scaleGenG t h3 (unitΓ u⁻¹))
  erw [scaleGenG_scaleGenG] at h4
  have h5 := unit_eq_one_of_corr t hL hge h4
  rw [FBIdLB.unitΓ_homAt, ← unitΓ_mul, ← unitΓ_one] at h5
  have h6 := FBIdLB.unitΓ_injective h5
  have h7 : (u : Jet S (Fin 2 × Fin d) m) * swJ d m u = 1 := by
    have h8 := congrArg (fun w : (Jet S (Fin 2 × Fin d) m)ˣ => (w⁻¹ : (Jet S (Fin 2 × Fin d) m)ˣ)) h6
    simp only [inv_one, mul_inv_rev, inv_inv, map_inv] at h8
    have h9 := congrArg Units.val h8
    simp only [Units.val_one, Units.val_mul, Units.coe_map] at h9
    rw [mul_comm]
    exact h9
  rw [← hu]
  exact h7

theorem sy_inv_of (hL : t.PP.L.IsLB) {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S}
    {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S} {ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S}
    {sy : MvPowerSeries (Fin 2 × Fin d) S} {ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S}
    {e : ∀ m, FrTyG t x0 d x m} (hfr : IsFrameG t x0 d x F act ph1 ph2 sy ad e) :
    sy * ev (n := 2) ![pt S d 1, pt S d 0] sy = 1 := by
  refine GermFun.psJet_inj fun m => ?_
  rw [FBIdJet.psJet_mul, psJet_ev_swap, sy_unit t x0 d x hL hfr m, FBIdJet.psJet_one]

theorem sy_ax_of (hL : t.PP.L.IsLB) {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S}
    {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S} {ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S}
    {sy : MvPowerSeries (Fin 2 × Fin d) S} {ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S}
    {e : ∀ m, FrTyG t x0 d x m} (hfr : IsFrameG t x0 d x F act ph1 ph2 sy ad e)
    (hax : FrAxes t x0 d x e) (b : Bool) :
    ev (n := 1) (if b then ![0, pt S d 0] else ![pt S d 0, 0]) sy = 1 := by
  refine psJet_inj fun m => ?_
  rw [psJet_ev_ax, psJet_one]
  obtain ⟨u, hu, hc⟩ := hfr.sy m
  have hA : ∀ b' : Bool, LB.Gen.Corr t.PP.L _ _ _ _
      (LB.pullGen t.PP.L (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m)
        (homAt x0 (axJ (S := S) d m b')).left) (LB.oneGen t.PP.L) := by
    intro b'
    cases b'
    · exact (hax m).2
    · exact (hax m).1
  have hcomp : (homAt x0 (axJ (S := S) d m b)).left ≫ (homAt x0 (swJ (S := S) d m)).left =
      (homAt x0 (axJ (S := S) d m (!b))).left := by
    rw [← Over.comp_left, homAt_comp, axJ_swJ]
  have h1 := DVR.corr_pullGen hc (homAt x0 (axJ (S := S) d m b)).left
  rw [FBIdLB.pullGen_scaleGenG] at h1
  have h2 := DVR.corr_trans hL (DVR.corr_pullGen_comp (e m) (homAt x0 (swJ (S := S) d m)).left
    (homAt x0 (axJ (S := S) d m b)).left) (DVR.corr_pullGen_of_eq (e m) (hfr.gen m) _ _ hcomp)
  have h3 := DVR.corr_trans hL h1 (FBIdLB.corr_scaleGenG t h2 _)
  have hAB := DVR.corr_trans hL (hA b) (DVR.corr_symm (hA (!b)))
  have h4 := FBIdLB.scale_eq_of_corr t hL hAB (v := 1)
    (by rw [FBIdLB.scaleGenG_one]; exact h3)
  rw [FBIdLB.unitΓ_homAt, ← unitΓ_one] at h4
  have h5 := FBIdLB.unitΓ_injective h4
  have h6 := congrArg (fun w : (Jet S (Fin 1 × Fin d) m)ˣ => ((w⁻¹ : (Jet S (Fin 1 × Fin d) m)ˣ) :
    Jet S (Fin 1 × Fin d) m)) h5
  simp only [inv_one, Units.val_one, map_inv, inv_inv, Units.coe_map] at h6
  rw [← hu]
  exact h6.symm

end Frame

end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy
