import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTieGerm
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBCNab
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTiePf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open MvPowerSeries

attribute [local instance] Over.cartesianMonoidalCategory

theorem psJet_pow {R κ : Type} [CommRing R] [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ R) (k : ℕ) :
    psJet m (f ^ k) = psJet m f ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, FBIdJet.psJet_one]
  | succ k ih => rw [pow_succ, pow_succ, FBIdJet.psJet_mul, ih]

theorem jetSubstPS_psJet {S : Type} [CommRing S] {d N : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin N) S)
    (h0 : ∀ j, constantCoeff (φ j) = 0) (m : ℕ) (f : MvPowerSeries (Fin 1 × Fin d) S) :
    (jetSubstPS (m := m) (fun p : Fin 1 × Fin d => φ p.2)) (psJet m f) =
      psJet m (subst (fun p : Fin 1 × Fin d => φ p.2) f) := by
  have h : ∀ p : Fin 1 × Fin d, constantCoeff (φ p.2) = 0 := fun p => h0 p.2
  have hmap : jetSubstPS (m := m) (fun p : Fin 1 × Fin d => φ p.2) =
      jetMap (fun p : Fin 1 × Fin d => psTrunc m (φ p.2))
        (fun p => FBIdJet.psTrunc_mem_orig m (φ p.2) (h p)) := by
    unfold jetSubstPS
    congr 1
    funext p
    have hc : MvPolynomial.constantCoeff (psTrunc m (φ p.2)) = 0 := by
      change MvPolynomial.coeff 0 (psTrunc m (φ p.2)) = 0
      rw [GermFun.coeff_psTrunc m (φ p.2) 0 (by simp), coeff_zero_eq_constantCoeff_apply, h0]
    rw [hc, map_zero, sub_zero]
  rw [hmap, FBIdJet.psJet_subst m _ h]

-- Retain the arithmetic lemma exported by the original substitution proof.
theorem jetSubstPS_psJet._proof_1_4 {d N : ℕ} (m : ℕ)
    (e : Fin 1 × Fin N →₀ ℕ) (he : (e.sum fun _ j => j) ≤ m)
    (u : Fin 1 × Fin d →₀ ℕ) (hu : ¬ (u.sum fun _ j => j) ≤ m) :
    (¬ (e.sum fun _ j => j) < u.sum fun _ j => j) → False :=
  fun h => h (lt_of_le_of_lt he (lt_of_not_ge hu))

theorem exp_pow_inv {S : Type} [CommRing S] [Algebra ℚ S] {σ : Type} (b : MvPowerSeries σ S)
    (hb : constantCoeff b = 0) (k : ℕ) :
    PowerSeries.subst ((k : S) • b) (PowerSeries.exp S) * (PowerSeries.subst (-b) (PowerSeries.exp S)) ^ k = 1 := by
  have hs : PowerSeries.HasSubst b := PowerSeries.HasSubst.of_constantCoeff_zero hb
  have key : ∀ r : S, PowerSeries.subst (r • b) (PowerSeries.exp S) =
      PowerSeries.subst b (PowerSeries.rescale r (PowerSeries.exp S)) := by
    intro r
    rw [PowerSeries.rescale_eq_subst, PowerSeries.subst_comp_subst_apply
      (PowerSeries.HasSubst.of_constantCoeff_zero
        (by exact (congrArg (r * ·) PowerSeries.constantCoeff_X).trans (mul_zero r))) hs]
    congr 1
    rw [PowerSeries.subst_smul hs, PowerSeries.subst_X hs]
  have hneg : -b = (-1 : S) • b := by simp
  rw [hneg, key, key, ← PowerSeries.subst_pow hs, ← PowerSeries.subst_mul hs]
  rw [← PowerSeries.exp_pow_eq_rescale_exp, ← mul_pow]
  have h1 : PowerSeries.exp S * PowerSeries.rescale (-1 : S) (PowerSeries.exp S) = 1 := by
    have h2 := PowerSeries.exp_mul_exp_eq_exp_add (A := S) 1 (-1)
    rw [add_neg_cancel, PowerSeries.rescale_one, RingHom.id_apply] at h2
    rw [h2, PowerSeries.rescale_zero, RingHom.comp_apply, PowerSeries.constantCoeff_exp, map_one]
  rw [h1, one_pow]
  first
    | exact PowerSeries.subst_one hs
    | exact (PowerSeries.substAlgHom hs).map_one
    | simp [← PowerSeries.coe_substAlgHom hs]

theorem isValueAt_of_eq {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left) (a : ℤ) {T : Over S0}
    {s : LB.Sec (LPow A L a T)} {z : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))} {v v' : Γ(T.left, ⊤)}
    (h : IsValueAt A L a s z τ v) (e : v = v') : IsValueAt A L a s z τ v' := e ▸ h

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem homAt_jφ_jBase {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] [StarRing (𝓞 E)]
    (y : FrPt Xo c S) (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (m : ℕ) :
    Formalism.L2.Pj.homAt y.x (jφ φ m) ≫ jBase y C.d m 1 = jBase y (dL Dw) m 1 := by
  apply Over.OverMorphism.ext
  exact spMap_comp_alg (jφ φ m)

theorem appTop_toΓ {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X) {A B : Type} [CommRing A] [Algebra S A] [CommRing B]
    [Algebra S B] (f : A →ₐ[S] B) (a : A) :
    ((Formalism.L2.Pj.homAt x0 f).left.appTop).hom (toΓ A a) = toΓ B (f a) := by
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (f : A →+* B))
  exact (congrArg (fun g => g.hom a) h).symm

end Main

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTiePf

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open MvPowerSeries ExpTieAlg ExpTieGerm ExpTiePf

attribute [local instance] Over.cartesianMonoidalCategory

theorem tie_holds : TieSt := by
  intro E _ _ _ H Dw l Xo c _ _ S _ _ _ y C φ hφ e he k F f hf
  have hL := Xo.univ.t.PP.isLB
  have hs0 : HasSubst (famL φ) := hasSubst0 fun p => hφ.const p.2
  have hhL : constantCoeff (C.B.hL S C.h H.w0) = 0 := CIndBCNab.const_hL C.B C.h C.gauge H.w0
  refine ⟨compL φ (f * Germ.FB.expS S ((k : S) • C.B.hL S C.h H.w0)), fun m => ?_, fun α => ?_⟩
  · obtain ⟨F₁, τ₁, hP₁, hC₁, hV₁⟩ := hf m
    obtain ⟨u, hu, hCe⟩ := he m
    obtain ⟨F₂, hP₂⟩ := GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ)
      (Formalism.L2.Pj.homAt y.x (jφ φ m) ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F₁
    let τ₂ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (xExp y C φ m).left) fun _ => (k : ℤ)) :=
      ⟨fun j => (e m).s j ^ k⟩
    have hG : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ τ₂
        (scaleGen _ _ (unitΓ u ^ k) (LB.pullGen Xo.univ.t.PP.L _ _
          (genPow _ _ (eL y C.d C.x C.B.A.act C.e C.wP m) k) (Formalism.L2.Pj.homAt y.x (jφ φ m)).left)) := by
      have := corr_genPow hCe k
      rw [genPow_scale_pull] at this
      exact this
    have h1 : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (scaleGen _ _ (unitΓ u ^ k) (LB.pullGen Xo.univ.t.PP.L _ _ τ₁ (Formalism.L2.Pj.homAt y.x (jφ φ m)).left))
        (scaleGen _ _ (unitΓ u ^ k) (LB.pullGen Xo.univ.t.PP.L _ _
          (genPow _ _ (eL y C.d C.x C.B.A.act C.e C.wP m) k) (Formalism.L2.Pj.homAt y.x (jφ φ m)).left)) :=
      corr_scale (corr_pullGen _ hC₁ _) _
    have heq := GermFun.gen_eq_of_corr _ hL _ _ _ _ _ τ₂ _ h1 hG
    refine ⟨F₂, τ₂, isPullSec_congr _ _ _ (homAt_jφ_jBase y C φ m) (isPullSec_comp _ _ _ _ _ hP₁ hP₂), ?_, ?_⟩
    · intro j j' _ _ c3
      have : j = j' := funext fun i => c3 i i rfl
      subst this
      rfl
    · rw [← heq]
      have hval := isValueAt_pullScale hL (k : ℤ) (Formalism.L2.Pj.homAt y.x (jφ φ m)) hP₂ hV₁ (unitΓ u ^ k)
      have hb : constantCoeff (compL φ (C.B.hL S C.h H.w0)) = 0 := by
        unfold compL
        rw [const_subst0 (a := famL φ) (fun p => hφ.const p.2)]
        exact hhL
      have hsub : subst (famL φ) (Germ.FB.expS S ((k : S) • C.B.hL S C.h H.w0)) =
          PowerSeries.subst ((k : S) • compL φ (C.B.hL S C.h H.w0)) (PowerSeries.exp S) := by
        unfold Germ.FB.expS
        rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.subst_exp (famL φ) (fun p => hφ.const p.2)
          (by rw [smul_eq_C_mul, map_mul, hhL, mul_zero]), subst_smul hs0]
        rfl
      have hprod : psJet m (subst (famL φ) (Germ.FB.expS S ((k : S) • C.B.hL S C.h H.w0))) * ↑(u ^ k) = 1 := by
        rw [Units.val_pow_eq_pow_val, hu, ← psJet_pow, ← FBIdJet.psJet_mul, hsub]
        unfold Germ.FB.expS
        rw [exp_pow_inv _ hb k]
        exact FBIdJet.psJet_one m
      have hinv : psJet m (subst (famL φ) (Germ.FB.expS S ((k : S) • C.B.hL S C.h H.w0))) = ↑((u ^ k)⁻¹) := by
        set X := psJet m (subst (famL φ) (Germ.FB.expS S ((k : S) • C.B.hL S C.h H.w0))) with hX
        calc X = X * ((↑(u ^ k) : Jet S (Fin 1 × Fin (dL Dw)) m) * ↑((u ^ k)⁻¹)) := by
              rw [Units.mul_inv, _root_.mul_one]
          _ = (X * ↑(u ^ k)) * ↑((u ^ k)⁻¹) := (_root_.mul_assoc _ _ _).symm
          _ = ↑((u ^ k)⁻¹) := by rw [hprod, _root_.one_mul]
      have hu' : ((unitΓ u ^ k)⁻¹ : Γ(Sp (Jet S (Fin 1 × Fin (dL Dw)) m), ⊤)ˣ) = unitΓ ((u ^ k)⁻¹) := by
        simp [unitΓ, map_pow, map_inv]
      refine isValueAt_of_eq _ _ _ hval ?_
      rw [appTop_toΓ, hu']
      show toΓ (Jet S (Fin 1 × Fin (dL Dw)) m) _ * toΓ (Jet S (Fin 1 × Fin (dL Dw)) m) _ =
        toΓ (Jet S (Fin 1 × Fin (dL Dw)) m) _
      rw [← map_mul]
      congr 1
      symm
      unfold compL jφ
      rw [jetSubstPS_psJet φ hφ.const m f, subst_mul hs0, FBIdJet.psJet_mul]
      congr 1
  · rw [nabVal_eq_const, tie_alg C.B.G.F C.uvec φ hφ α]

end Formalism.MainNotions.ModuliIntegralCharts.H1
