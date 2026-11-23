module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle579
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle918
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
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

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.exists_integral_coboundary_divisible_of_quasiLog_defect : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E) (s : MvPowerSeries (Fin d) O) (y : G.A 1), QL c.μ ⊤ f → map (algebraMap O E) s = defect c.μ p f → c.ev 1 s = (p : O) • y → ∃ t : MvPowerSeries (Fin d) O, constantCoeff t = 0 ∧ In (Ideal.span {(p : O)}) (cob1 (up E c.μ) (f - map (algebraMap O E) t)) := by
  first | exact @GlobalTheory.QLog.exists_int_cob_dvd_of_defect_ev | exact GlobalTheory.QLog.exists_int_cob_dvd_of_defect_ev | (intros; apply GlobalTheory.QLog.exists_int_cob_dvd_of_defect_ev <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem lie_surj_mod_p : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E],
    IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d),
    ∀ l : G.dual.Lie, ∃ (f : MvPowerSeries (Fin d) E) (l' l'' : G.dual.Lie),
      QL c.μ ⊤ f ∧ c.IsLie f l' ∧ l = l' + (p : O) • l'' := by
  intro p _ O E _ _ _ hF G d c l
  obtain ⟨b, z, hbz, hl⟩ := GlobalTheory.T.dual_lie_exists_additive_eval_mod_prime_pow p O G l 1
  rw [pow_one] at hbz
  obtain ⟨f, s, y, hf, hs, hy⟩ := GlobalTheory.T.additive_mod_prime_eq_quasiLogarithm_defect p O E hF G d c b z hbz
  obtain ⟨l', hl', -⟩ := GlobalTheory.T.existsUnique_isLie_of_isFrame_of_QL p O E hF G d c f hf
  have hdiv : ∀ w : G.dual.omega, (p : O) ∣ (l - l') w := by
    intro w
    obtain ⟨φ, hφ⟩ := AugCot.d_surjective _ (w.1 1)
    have h1 := hl w φ hφ
    have h2 := hl'.2 1 w φ s hφ (by rw [pow_one]; exact hs)
    rw [pow_one] at h1 h2
    rw [hy, map_add (f := _), map_smul, smul_eq_mul] at h2
    have h3 : (p : O) ∣ l' w - φ b := by
      have := dvd_add h2 (dvd_mul_right (p : O) (φ y))
      rwa [show l' w - (φ b + (p : O) * φ y) + (p : O) * φ y = l' w - φ b by ring] at this
    have := dvd_sub h1 h3
    rwa [show l w - φ b - (l' w - φ b) = (l - l') w by simp] at this
  obtain ⟨l'', hl''⟩ := GlobalTheory.T.dual_eq_smul_of_forall_dvd' O G.dual.omega (p : O) (fun x hx => hF.sat x hx) (l - l') hdiv
  exact ⟨f, l', l'', hf, hl', by rw [← hl'']; abel⟩

end GlobalTheory.QLog
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

section Basic

variable {X : Over (Sp R)} (f f' : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (r : R)

theorem fv_add_apply (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (x : Pt X D) : fv (f + f') D D' φ x = fv f D D' φ x + fv f' D D' φ x := rfl

theorem fv_smul_apply (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (x : Pt X D) : fv (r • f) D D' φ x = r • fv f D D' φ x := rfl

theorem cotVal_add_apply {D : Type} [CommRing D] [Bialgebra R D] (y : Pt X D) :
    cotVal (f + f') y = cotVal f y + cotVal f' y := by
  unfold cotVal
  simp only [fv_add_apply, map_add (f := _), map_sub]
  abel

theorem cotVal_smul_apply {D : Type} [CommRing D] [Bialgebra R D] (y : Pt X D) :
    cotVal (r • f) y = r • cotVal f y := by
  unfold cotVal
  simp only [fv_smul_apply, map_smul, map_sub, smul_sub]

end Basic

variable {A : Over (Sp R)} [GrpObj A] {p : ℕ} {G : PDivGroup p R} {t : G.TorsionTower A} {c c' : primDR A}

def Dat.sum (d : Dat t c) (d' : Dat t c') : Dat t (c + c') where
  f := d.f + d'.f
  cl := by rw [map_add (f := _), d.cl, d'.cl]; rfl
  g := fun D _ _ x y ↦ d.g D x y + d'.g D x y
  add := fun D _ _ D' _ _ φ x y ↦ by
    have h := d.add D D' φ x y
    have h' := d'.add D D' φ x y
    simp only [fv_add_apply, map_add (f := _)]
    linear_combination h + h'
  h := fun n ↦ d.h n + d'.h n
  res := fun n ↦ by
    have h := d.res n
    have h' := d'.res n
    simp only [fv_add_apply, map_add (f := _)]
    linear_combination h + h'

def Dat.scale (r : R) (d : Dat t c) : Dat t (r • c) where
  f := r • d.f
  cl := by rw [map_smul, d.cl]; rfl
  g := fun D _ _ x y ↦ r • d.g D x y
  add := fun D _ _ D' _ _ φ x y ↦ by
    have h := d.add D D' φ x y
    simp only [fv_smul_apply, map_smul]
    rw [← smul_sub, h, smul_sub, smul_sub]
  h := fun n ↦ r • d.h n
  res := fun n ↦ by
    have h := d.res n
    simp only [fv_smul_apply, map_smul]
    rw [← smul_sub, h]

theorem Dat.coc_sum (d : Dat t c) (d' : Dat t c') (n : ℕ) : (d.sum d').coc n = d.coc n + d'.coc n := by
  simp only [Dat.coc, Dat.sum, fv_add_apply, map_add (f := _)]
  abel

theorem Dat.om_sum (d : Dat t c) (d' : Dat t c') (n : ℕ) : (d.sum d').om n = d.om n + d'.om n := by
  simp only [Dat.om, Dat.sum, cotVal_add_apply, map_add (f := _)]
  abel

theorem Dat.coc_scale (r : R) (d : Dat t c) (n : ℕ) : (d.scale r).coc n = r • d.coc n := by
  simp only [Dat.coc, Dat.scale, fv_smul_apply, map_smul, smul_sub]

theorem Dat.om_scale (r : R) (d : Dat t c) (n : ℕ) : (d.scale r).om n = r • d.om n := by
  simp only [Dat.om, Dat.scale, cotVal_smul_apply, map_smul, smul_sub]

theorem isCan_add_smul (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) :
    (∀ (c c' : primDR A) (x x' : G.RigExt),
      IsCan t c x → IsCan t c' x' → IsCan t (c + c') (x + x')) ∧
    (∀ (r : R) (c : primDR A) (x : G.RigExt), IsCan t c x → IsCan t (r • c) (r • x)) := by
  constructor
  · rintro c c' _ _ ⟨d, z, w, hz, hw, rfl⟩ ⟨d', z', w', hz', hw', rfl⟩
    refine ⟨d.sum d', z + z', w + w', fun n ↦ ?_, fun n ↦ ?_, (map_add G.rigMk _ _).symm⟩
    · rw [Dat.coc_sum, ← hz, ← hz']; rfl
    · rw [Dat.om_sum, ← hw, ← hw']; rfl
  · rintro r c _ ⟨d, z, w, hz, hw, rfl⟩
    refine ⟨d.scale r, r • z, r • w, fun n ↦ ?_, fun n ↦ ?_, (map_smul G.rigMk r (z, w)).symm⟩
    · rw [Dat.coc_scale, ← hz]; rfl
    · rw [Dat.om_scale, ← hw]; rfl

end GlobalTheory.PtExt
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt.Lift

variable {R : Type} [CommRing R] {X : Over (Sp R)}

def trivEquiv (T : Thick (dp0 R) (X.hom ≫ 𝟙 _)) (hT : T.J = ⊥) : T.B ≃+* T.B₀ :=
  RingEquiv.ofBijective T.π ⟨(injective_iff_map_eq_zero T.π).2 fun b hb ↦ by
      have h := (T.ker b).1 hb
      rw [hT] at h
      exact Ideal.mem_bot.1 h, T.surj⟩

theorem trivEquiv_symm_π (T : Thick (dp0 R) (X.hom ≫ 𝟙 _)) (hT : T.J = ⊥) (b : T.B) :
    (trivEquiv T hT).symm (T.π b) = b :=
  (trivEquiv T hT).symm_apply_apply b

def trivPt (T : Thick (dp0 R) (X.hom ≫ 𝟙 _)) (hT : T.J = ⊥) : Pt X T.B :=
  Over.homMk (U := SpAlg R T.B) (spMap ((trivEquiv T hT).symm.toRingHom) ≫ T.x) (by
    have h : T.x ≫ X.hom = spMap (T.π.comp (algebraMap R T.B)) :=
      ((Category.comp_id _).symm.trans (Category.assoc _ _ _)).trans T.w
    change (spMap _ ≫ T.x) ≫ X.hom = spMap (algebraMap R T.B)
    rw [Category.assoc, h, ← Cris.spMap_comp]
    congr 1
    ext r
    exact trivEquiv_symm_π T hT _)

theorem spOver_trivPt {T T' : Thick (dp0 R) (X.hom ≫ 𝟙 _)} (hT : T.J = ⊥) (hT' : T'.J = ⊥) (φ : T ⟶ T') :
    spOver φ.φ ≫ trivPt T hT = trivPt T' hT' := by
  apply Over.OverMorphism.ext
  change spMap (φ.φ : T.B →+* T'.B) ≫ spMap ((trivEquiv T hT).symm.toRingHom) ≫ T.x =
    spMap ((trivEquiv T' hT').symm.toRingHom) ≫ T'.x
  rw [← φ.pt, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp]
  congr 2
  ext b
  obtain ⟨b, rfl⟩ := T.surj b
  change φ.φ ((trivEquiv T hT).symm (T.π b)) = (trivEquiv T' hT').symm (φ.φ₀ (T.π b))
  rw [φ.comm, trivEquiv_symm_π, trivEquiv_symm_π]

theorem trivPt_trivAt {D : Type} [CommRing D] [Algebra R D] (x : Pt X D) : trivPt (trivAt x) rfl = x := by
  apply Over.OverMorphism.ext
  change spMap ((trivEquiv (trivAt x) rfl).symm.toRingHom) ≫ x.left = x.left
  have : (trivEquiv (trivAt x) rfl).symm.toRingHom = RingHom.id D :=
    RingHom.ext fun b ↦ trivEquiv_symm_π (trivAt x) rfl b
  rw [this, Cris.spMap_id, Category.id_comp]

def trivCoc (u : Fn1 X) (hu : IsCoc (whole X) u) :
    Z1 ((IsTriv (X.hom ≫ 𝟙 _)).ι ⋙ O (dp0 R) (X.hom ≫ 𝟙 _)) :=
  ⟨fun T T' φ ↦ u T.obj.B T'.obj.B φ.hom.φ (trivPt T.obj T.property), fun T T' T'' φ ψ ↦ by
    change u _ _ (ψ.hom.φ.comp φ.hom.φ) _ = ψ.hom.φ (u _ _ φ.hom.φ _) + u _ _ ψ.hom.φ _
    rw [hu _ _ _ φ.hom.φ ψ.hom.φ _ (sm_whole _), spOver_trivPt T.property T'.property φ.hom]⟩

end GlobalTheory.PtExt.Lift


open GlobalTheory.PtExt.Lift in
theorem GlobalTheory.PtExt.cohom_fv_of_toH1O_surjective : ∀ (R : Type) [CommRing R] (X : Over (Sp R)),
    Function.Surjective (toH1O (X.hom ≫ 𝟙 _)) → ∀ u : Fn1 X, IsCoc (whole X) u →
      ∃ f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _)), Cohom (whole X) u (fv f) := by
  intro R _ X hs u hu
  obtain ⟨c, hc⟩ := hs (H1.mk _ (trivCoc u hu))
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  have hc' : H1.mk _ ((CoefMap.restrict (O (dp0 R) (X.hom ≫ 𝟙 _)) (IsTriv (X.hom ≫ 𝟙 _)).ι).pullbackOneCocycle f) =
      H1.mk _ (trivCoc u hu) := hc
  obtain ⟨g, hg⟩ := H1.mk_eq_mk.1 hc'
  refine ⟨f, fun D _ _ x ↦ -g ⟨trivAt x, rfl⟩, ?_⟩
  intro D _ _ D' _ _ φ x _
  let T : (IsTriv (X.hom ≫ 𝟙 _)).FullSubcategory := ⟨trivAt x, rfl⟩
  let T' : (IsTriv (X.hom ≫ 𝟙 _)).FullSubcategory := ⟨trivAt (spOver φ ≫ x), rfl⟩
  let a : T ⟶ T' := ObjectProperty.homMk (trivMap φ x)
  let b : D := g T
  let b' : D' := g T'
  have h := congrFun (congrFun (congrFun hg T) T') a
  change b' - φ b = ev f (trivMap φ x) - u D D' φ (trivPt (trivAt x) rfl) at h
  rw [trivPt_trivAt] at h
  change u D D' φ x + -ev f (trivMap φ x) = -b' - φ (-b)
  rw [map_neg]
  linear_combination h
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem val_sub_pull {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {Y Y' : Scheme.{0}}
    {t : Y ⟶ Sp R} {t' : Y' ⟶ Sp R'} {φ : Y' ⟶ Y} (m : IsMor (dp0 R) t (dp0 R') t' σ φ)
    (E : SqExt R) (E' : SqExt R') (ρ : E.C →+* E'.C) (ρ₀ : E.B →+* E'.B)
    (hρ : ∀ r, ρ (algebraMap R E.C r) = algebraMap R' E'.C (σ r))
    (hρ₀ : ∀ r, ρ₀ (algebraMap R E.B r) = algebraMap R' E'.B (σ r))
    (hπ : ∀ c, ρ₀ (E.π c) = E'.π (ρ c)) (hi : ∀ b, ρ (E.i b) = E'.i (ρ₀ b))
    {T₀ : Thick (dp0 R) t} {T₀' : Thick (dp0 R') t'} (a : T₀ ⟶ m.obj T₀')
    (z : Sp E.C ⟶ Y) (hz : z ≫ t = spMap (algebraMap R E.C))
    (z' : Sp E'.C ⟶ Y') (hz' : z' ≫ t' = spMap (algebraMap R' E'.C))
    (τ : T₀ ⟶ Thick.triv E.C z hz) (τ' : T₀' ⟶ Thick.triv E'.C z' hz')
    (h : ∀ c, ρ (τ.φ c) = τ'.φ (a.φ c)) (f : Z1 (O (dp0 R) t)) :
    ∃ b : E'.B, E'.val z' hz' (m.coef.pullbackOneCocycle f) - ev (m.coef.pullbackOneCocycle f) τ' =
      ρ (E.val z hz f - ev f τ) + τ'.φ (ev f a) - E'.i b := by
  have e : spMap ρ ≫ z = z' ≫ φ := by
    let u : T₀.B₀ →+* E.C := τ.φ₀
    let u' : T₀'.B₀ →+* E'.C := τ'.φ₀
    let a₀ : T₀.B₀ →+* T₀'.B₀ := a.φ₀
    have h1 : spMap u ≫ T₀.x = z := τ.pt
    have h2 : spMap u' ≫ T₀'.x = z' := τ'.pt
    have h3 : spMap a₀ ≫ T₀.x = T₀'.x ≫ φ := a.pt
    rw [← h1, ← h2, Category.assoc, ← h3, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 2
    refine RingHom.ext fun c ↦ ?_
    obtain ⟨c, rfl⟩ := T₀.surj c
    exact (congrArg ρ (τ.comm c)).trans ((h c).trans
      ((τ'.comm (a.φ c)).symm.trans (congrArg τ'.φ₀ (a.comm c).symm)))
  have e₀ : spMap ρ₀ ≫ spMap (E.π : E.C →+* E.B) ≫ z = (spMap (E'.π : E'.C →+* E'.B) ≫ z') ≫ φ := by
    rw [Category.assoc, ← e, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 2
    exact RingHom.ext hπ
  let Φ : E.thick _ (E.red_w hz) ⟶ m.obj (E'.thick _ (E'.red_w hz')) :=
    { φ := { ρ with commutes' := hρ }
      φ₀ := ρ₀
      comm := hπ
      dp := isDPMorphism_sqDP E.sq E'.sq _ fun c hc ↦ by
        have hc' : E.π c = 0 := hc
        change E'.π (ρ c) = 0
        rw [← hπ, hc', map_zero]
      pt := e₀ }
  let b : Thick.triv E.B _ (E.red_w hz) ⟶ m.obj (Thick.triv E'.B _ (E'.red_w hz')) :=
    Thick.trivHom { ρ₀ with commutes' := hρ₀ } e₀
  have k1 := ev_sq f b (m.functor.map (E'.secHom (E'.red_w hz') E'.i E'.π_i))
    (E.secHom (E.red_w hz) E.i E.π_i) Φ fun c ↦ (hi c).symm
  have k2 := ev_sq f a (m.functor.map (τ' ≫ E'.idHom hz')) (τ ≫ E.idHom hz) Φ fun c ↦ (h c).symm
  have k3 := ev_comp f τ (E.idHom hz)
  have k4 := ev_comp (m.coef.pullbackOneCocycle f) τ' (E'.idHom hz')
  have key : ∀ (A B C : E.C) (x y u v w k l : E'.C) (N : E.C), x + y = ρ A + w → l + k = ρ N + w → N = C + B →
      k = v + u → y - u - v = ρ (A - B - C) + l - x := fun A B C x y u v w k l N h1 h2 h3 h4 ↦ by
    subst h3 h4
    rw [map_add (f := _)] at h2
    rw [map_sub, map_sub]
    linear_combination h1 - h2
  exact ⟨ev f b, key _ _ _ _ _ _ _ _ _ _ _ k1 k2 k3 k4⟩

attribute [local instance] cotOp cotCentral cotTower

def cotRingHom {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {D D' : Type} [CommRing D] [Bialgebra R D]
    [CommRing D'] [Bialgebra R' D'] (s : SemiBialgHom σ D D') :
    TrivSqZeroExt R (Cot R D) →+* TrivSqZeroExt R' (Cot R' D') where
  toFun c := TrivSqZeroExt.inl (σ c.fst) + TrivSqZeroExt.inr ((SemiBialgHom.cot s) c.snd)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp [map_smulₛₗ]

set_option backward.isDefEq.respectTransparency false in
theorem cotVal_pull (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R')
    (X : Over (Sp R)) (X' : Over (Sp R')) (φ : X'.left ⟶ X.left)
    (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R') (X'.hom ≫ 𝟙 _) σ φ)
    (D D' : Type) [CommRing D] [Bialgebra R D] [CommRing D'] [Bialgebra R' D']
    (s : SemiBialgHom σ D D') (y : Pt X D) (y' : Pt X' D')
    (a : trivAt y ⟶ m.obj (trivAt y')) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _)))
    (ha : ∀ r : D, (a.φ r : D') = s r) :
    cotVal (m.coef.pullbackOneCocycle f) y' =
      (SemiBialgHom.cot s) (cotVal f y) + dUnit (R := R') (A := D') (ev f a) := by
  have hf : ∀ c, (cotRingHom s c).fst = σ c.fst := fun c ↦ add_zero _
  have hs : ∀ c, (cotRingHom s c).snd = (SemiBialgHom.cot s) c.snd := fun c ↦ zero_add _
  have pf : ∀ c : D, TrivSqZeroExt.fst (cotPt R D c) = Coalgebra.counit c := fun c ↦ add_zero _
  have ps : ∀ c : D, TrivSqZeroExt.snd (cotPt R D c) = dUnit (R := R) c := fun c ↦ zero_add _
  have pf' : ∀ c : D', TrivSqZeroExt.fst (cotPt R' D' c) = Coalgebra.counit c := fun c ↦ add_zero _
  have ps' : ∀ c : D', TrivSqZeroExt.snd (cotPt R' D' c) = dUnit (R := R') c := fun c ↦ zero_add _
  obtain ⟨b, hb⟩ := val_sub_pull m (cotExt R D) (cotExt R' D') (cotRingHom s) σ
    (fun r ↦ TrivSqZeroExt.ext (hf _) ((hs _).trans (map_zero _))) (fun _ ↦ rfl) (fun c ↦ (hf c).symm)
    (fun r ↦ TrivSqZeroExt.ext (hf _) ((hs _).trans (map_zero _))) a
    (spOver (cotPt R D) ≫ y).left (Pt.w _) (spOver (cotPt R' D') ≫ y').left (Pt.w _)
    (trivMap (cotPt R D) y) (trivMap (cotPt R' D') y') (fun c ↦ by
      change cotRingHom s (cotPt R D c) = cotPt R' D' (a.φ c : D')
      have h := congrArg (fun u : D' ↦ cotPt R' D' u) (ha (show D from c))
      refine Eq.trans ?_ h.symm
      ext
      · rw [hf, pf, pf', s.counit_map]
      · rw [hs, ps, ps', s.cot_d]) f
  refine (congrArg (cotSnd R' D') hb).trans ?_
  rw [map_sub, map_add (f := _)]
  refine (sub_zero _).trans ?_
  exact congrArg₂ (· + ·) (hs _) (ps' _)

end GlobalTheory.PtExt
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

attribute [local instance] cotOp cotCentral cotTower

theorem cotSnd_cotPt_eq_dUnit (R : Type) [CommRing R] (D : Type) [CommRing D] [Bialgebra R D] (z : D) :
    cotSnd R D (cotPt R D z) = dUnit (R := R) z := by
  change TrivSqZeroExt.snd (algebraMap R (TrivSqZeroExt R (Cot R D)) (Coalgebra.counit z) +
    TrivSqZeroExt.inr (AugCot.d (Bialgebra.counitAlgHom R D) z)) = _
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]

theorem crystallineCocycleCotangentValue_sub_of_coboundary (R : Type) [CommRing R]
    (X : Over (Sp R)) (D : Type) [CommRing D] [Bialgebra R D] (y : Pt X D)
    (f f' : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (k : C0 (O (dp0 R) (X.hom ≫ 𝟙 _)))
    (h : d0 _ k = f.1 - f'.1) :
    cotVal f y - cotVal f' y = dUnit (R := R) (A := D) (k (trivAt y)) := by
  have hf : f - f' = ⟨d0 _ k, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ k⟩ := Subtype.ext h.symm
  let E := cotExt R D
  let p : D →ₐ[R] E.C := cotPt R D
  let y' : Pt X E.C := spOver p ≫ y
  let k₀ : E.B := k (Thick.triv E.B _ (E.red_w y'.w))
  let i : E.C := E.i k₀
  have h1 : E.val y'.left y'.w f - E.val y'.left y'.w f' = k (trivAt y') - i := by
    rw [← map_sub, hf]
    exact E.tangentValue_coboundary y'.left y'.w k
  have h2 : fv f D E.C p y - fv f' D E.C p y = k (trivAt y') - p (k (trivAt y)) := by
    let τ : trivAt y ⟶ trivAt y' := trivMap p y
    have e := congrArg (fun g : C1 (O (dp0 R) (X.hom ≫ 𝟙 _)) ↦ g _ _ τ) h
    change d0 _ k _ _ τ = _ at e
    rw [amitsur_d0_apply, mp_O] at e
    exact e.symm
  have hi : cotSnd R D i = 0 := by
    exact TrivSqZeroExt.snd_inl (M := Cot R D) k₀
  change cotSnd R D (E.val y'.left y'.w f - fv f D E.C p y) -
    cotSnd R D (E.val y'.left y'.w f' - fv f' D E.C p y) = _
  rw [← map_sub, sub_sub_sub_comm, h1, h2, sub_sub_sub_cancel_left, map_sub]
  rw [show p (k (trivAt y)) = cotPt R D (k (trivAt y)) from rfl,
    cotSnd_cotPt_eq_dUnit, hi, sub_zero]

end GlobalTheory.PtExt
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem ev_eq_fv_of_triv {R : Type} [CommRing R] {X : Over (Sp R)} (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _)))
    (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (x : Pt X D) (x' : Pt X D')
    (φ : D →ₐ[R] D') (a : trivAt x ⟶ trivAt x') (h : ∀ r : D, a.φ r = φ r) :
    spOver φ ≫ x = x' ∧ ev f a = fv f D D' φ x := by
  have e : spOver φ ≫ x = x' := by
    have h0 : a.φ₀ = (φ : D →+* D') := RingHom.ext fun r ↦ (a.comm r).trans (h r)
    have hp := a.pt
    rw [h0] at hp
    exact Over.OverMorphism.ext hp
  subst x'
  refine ⟨rfl, ?_⟩
  have ha : a = trivMap φ x := Thick.Hom.ext' (AlgHom.ext h)
  exact congrArg (ev f) ha

theorem fv_isCoc_and_ev_eq :
    ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))),
      IsCoc (whole X) (fv f) ∧
        ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
          (x : Pt X D) (x' : Pt X D') (φ : D →ₐ[R] D') (a : trivAt x ⟶ trivAt x'),
          (∀ r : D, a.φ r = φ r) → spOver φ ≫ x = x' ∧ ev f a = fv f D D' φ x := by
  intro R _ X f
  refine ⟨?_, fun D _ _ D' _ _ x x' φ a h ↦ ev_eq_fv_of_triv f D D' x x' φ a h⟩
  intro D _ _ D' _ _ D'' _ _ φ ψ x _
  let y : Pt X D' := spOver φ ≫ x
  let z : Pt X D'' := spOver ψ ≫ y
  have h := (ev_eq_fv_of_triv f D D'' x z (ψ.comp φ)
    (trivMap φ x ≫ trivMap ψ y) (fun _ ↦ rfl)).2
  exact h.symm.trans (ev_comp f (trivMap φ x) (trivMap ψ y))

end GlobalTheory.PtExt
end
end
