module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle032
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle034
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.exists_fibreSection_pow_mul_baseChange_away : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (g : S) (s' : LB.Sec (PPx (spMap (algebraMap S (Localization.Away g)) ≫ x))), ∃ (N : ℕ) (s : LB.Sec (PPx x)) (s₁ : LB.Sec (PPx (spMap (algebraMap S (Localization.Away g)) ≫ x))), SecBC (algebraMap S (Localization.Away g)) 1 x _ s s₁ ∧ ∀ i, s₁.f i = scal _ ((algebraMap S (Localization.Away g)) g ^ N) i * s'.f i := by
  first | exact @GlobalTheory.Frames.SecLoc.exists_secBC_pow_mul | exact GlobalTheory.Frames.SecLoc.exists_secBC_pow_mul | (intros; apply GlobalTheory.Frames.SecLoc.exists_secBC_pow_mul <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PeriodBalance

variable {R : Type} [CommRing R] [IsDomain R]

def cst (ξ : Spec (CommRingCat.of (FractionRing R))) :
    R →+* (Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ :=
  (((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom).comp (algebraMap R (FractionRing R))

theorem cst_injective (ξ : Spec (CommRingCat.of (FractionRing R))) : Function.Injective (cst ξ) :=
  (RingHom.injective (((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom)).comp
    (IsFractionRing.injective R (FractionRing R))

theorem cst_eq (ξ : Spec (CommRingCat.of (FractionRing R))) (r : R) :
    cst ξ r = ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom
      (((jK R).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
  have hnat := congrArg (fun f => (CommRingCat.Hom.hom f) r)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat
  exact congrArg ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom hnat

variable [IsLocalRing R]

theorem unit_gm (ξ : Spec (CommRingCat.of (FractionRing R))) (U : (Spec (CommRingCat.of R)).Opens)
    (hU : (closedPoint R : Spec (CommRingCat.of R)) ∈ U) (a : Γ(Spec (CommRingCat.of R), U)ˣ) :
    ∃ u : Rˣ, (gm (jK R) ξ U a).val = cst ξ u := by
  obtain rfl := DVR.eq_top_of_closedPoint_mem U hU
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom a, ?_⟩
  rw [gm_val _ ξ ⊤ trivial, cst_eq]
  refine congrArg ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom
    (congrArg ((jK R).app ⊤).hom ?_)
  exact (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of R)) a.val).symm

theorem unit_gm' (ξ : Spec (CommRingCat.of (FractionRing R))) {X : Scheme.{0}} (p : Spec (CommRingCat.of R) ⟶ X)
    (U : X.Opens) (hU : p (closedPoint R) ∈ U) (a : Γ(X, U)ˣ) :
    ∃ u : Rˣ, (gm (jK R ≫ p) ξ U a).val = cst ξ u := by
  have h : p (jK R ξ) ∈ U := by
    have := DVR.eq_top_of_closedPoint_mem (p ⁻¹ᵁ U) hU
    have h2 : jK R ξ ∈ p ⁻¹ᵁ U := by rw [this]; trivial
    exact h2
  rw [← gm_pull (jK R) p ξ U h]
  exact unit_gm ξ _ hU _

theorem exists_good_integral (ξ : Spec (CommRingCat.of (FractionRing R))) {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (s : X ⟶ Spec (CommRingCat.of R)) [IsSeparated s] :
    ∃ J, Good L ξ J ∧ ∀ p : Spec (CommRingCat.of R) ⟶ X, p ≫ s = 𝟙 _ →
      p (closedPoint R) ∈ L.U (J (jK R ≫ p)) := by
  haveI : IsDominant (jK R) := DVR.isDominant_jK
  choose pick hpk using fun p : Spec (CommRingCat.of R) ⟶ X => exists_chart hL (p (closedPoint R))
  obtain ⟨J, hJ, e⟩ := exists_good L hL ξ (K := {p : Spec (CommRingCat.of R) ⟶ X // p ≫ s = 𝟙 _})
    (fun p => jK R ≫ p.1) (fun p => pick p.1)
    (fun a b h => congrArg pick (ext_of_isDominant_of_isSeparated s (a.2.trans b.2.symm) (jK R) h))
    (fun p => by
      have := DVR.eq_top_of_closedPoint_mem (p.1 ⁻¹ᵁ L.U (pick p.1)) (hpk p.1)
      have h2 : jK R ξ ∈ p.1 ⁻¹ᵁ L.U (pick p.1) := by rw [this]; trivial
      exact h2)
  exact ⟨J, hJ, fun p hp => (e ⟨p, hp⟩).symm ▸ hpk p⟩

theorem val_psi (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) (χ : D.X) (r : R) (hr : PsiCoord D χ r) :
    ∃ u : Rˣ, (val (D.psi χ) (𝟙 _) ξ J).val = cst ξ (u * r) := by
  obtain ⟨j, hj, h, e⟩ := hr
  have hx : D.xK χ = jK R ≫ (D.c χ).left := DVR.QForm.ptK_eq D χ
  have hm : (𝟙 (Spec (CommRingCat.of (FractionRing R))) : _ ⟶ _) ξ ∈ LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j :=
    h (show ξ ∈ jK R ⁻¹ᵁ ⊤ from trivial)
  have t := gen_trans (D.psi_gen χ) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ
    (hJ.mem (fun _ : PUnit => D.xK χ) (𝟙 _)) hm
  have h1 : (gm (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ
      (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j) ((D.psi χ).s j)).val = cst ξ r := by
    refine (gm_val _ ξ _ hm _).trans (Eq.trans ?_ (cst_eq ξ r).symm)
    have e' : ((jK R).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = _ := Eq.trans ?_ e
    · rw [e']
      exact (TopCat.Presheaf.germ_res_apply (Spec (CommRingCat.of (FractionRing R))).presheaf (homOfLE h) ξ trivial _).symm
    · congr 1
  obtain ⟨u, hu⟩ := unit_gm' ξ (D.c χ).left (D.P.L.U (J (jK R ≫ (D.c χ).left)) ⊓ D.P.L.U (j PUnit.unit))
    ⟨hJc _ (Over.w _), hj trivial⟩ (D.P.L.g (J (jK R ≫ (D.c χ).left)) (j PUnit.unit))
  have h2 : trF (L := D.P.L) (fun _ : PUnit => D.xK χ) (fun _ => -1) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ
      (fun _ => J (𝟙 _ ≫ D.xK χ)) j = (gm (jK R ≫ (D.c χ).left) ξ _ (D.P.L.g (J (jK R ≫ (D.c χ).left)) (j PUnit.unit)))⁻¹ := by
    rw [trF, Fintype.prod_unique, zpow_neg_one, Category.id_comp, hx]
  refine ⟨u⁻¹, (congrArg Units.val t).trans ?_⟩
  refine (Units.val_mul _ _).trans ?_
  rw [map_mul]
  refine congrArg₂ (· * ·) ?_ h1
  refine (congrArg Units.val h2).trans ?_
  rw [Units.inv_eq_of_mul_eq_one_left]
  rw [hu, ← map_mul, Units.inv_mul, map_one]

omit [IsLocalRing R] in
theorem val_tau (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J) (a b : D.X) :
    val (D.tau a b) (𝟙 _) ξ J = val (D.psi (a + b)) (𝟙 _) ξ J * (val (D.psi a) (𝟙 _) ξ J)⁻¹ *
      (val (D.psi b) (𝟙 _) ξ J)⁻¹ * (val D.rigK (𝟙 _) ξ J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem coord_balance {O : Type} [Ring O] [StarRing O] (D : DegPre R) [Module O D.X] (ρ : D.OAct O) (x : O)
    (a b : D.X) {r₁ r₂ r₃ s₁ s₂ s₃ : R} (h₁ : PsiCoord D (x • a + b) r₁) (h₂ : PsiCoord D (x • a) r₂)
    (h₃ : PsiCoord D b r₃) (k₁ : PsiCoord D (a + star x • b) s₁) (k₂ : PsiCoord D a s₂)
    (k₃ : PsiCoord D (star x • b) s₃) : ∃ u : Rˣ, u * (r₁ * s₂ * s₃) = s₁ * r₂ * r₃ := by
  haveI := ρ.onB.hom x
  haveI := ρ.onB.hom (star x)
  haveI : IsProper D.P.A.hom := D.P.isAb.proper
  obtain ⟨w, hw, h₀⟩ := exists_ros GlobalTheory.globalFns_holds D.P.isAb D.P.isLB _ _ (ρ.onB.rosati x)
  have hc := ρ.tau_bal x w hw h₀ a b
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J, hJ, hJc⟩ := exists_good_integral ξ D.P.isLB D.P.A.hom
  have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ hc (𝟙 _))
  have e1 := val_tau D ξ hJ (x • a) b
  have e2 := val_tau D ξ hJ a (star x • b)
  have e3 := val_pull hJ w (D.pt2 a b) (𝟙 _)
  have hp : 𝟙 _ ≫ D.pt2 a b = jK R ≫ (lift (D.c a) (D.c b)).left := by
    simp [DegPre.pt2, ← CartesianMonoidalCategory.comp_lift]
  obtain ⟨v, hv⟩ : ∃ v : Rˣ, (val w (jK R ≫ (lift (D.c a) (D.c b)).left) ξ J).val = cst ξ v := by
    refine unit_gm' ξ _ _ (Set.mem_iInter.2 fun k => ?_) _
    obtain ⟨q, hq⟩ : ∃ q : D.P.A ⊗ D.P.A ⟶ D.P.A, rosatiφ D.P.A (ρ.onB.act x) (ρ.onB.act (star x)) k = q.left := by
      fin_cases k <;> exact ⟨_, rfl⟩
    have := hJc ((lift (D.c a) (D.c b)).left ≫ rosatiφ D.P.A (ρ.onB.act x) (ρ.onB.act (star x)) k) (by
      rw [hq, Category.assoc, Over.w q, Over.w]; rfl)
    exact this
  have e3' := e3.trans (congrArg (fun q => val w q ξ J) hp)
  have e4 := (congrArg₂ (@HMul.hMul _ _ ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ instHMul)
    e1 e3').symm.trans (e.trans e2)
  obtain ⟨u₁, g₁⟩ := val_psi D ξ hJ hJc _ _ h₁
  obtain ⟨u₂, g₂⟩ := val_psi D ξ hJ hJc _ _ h₂
  obtain ⟨u₃, g₃⟩ := val_psi D ξ hJ hJc _ _ h₃
  obtain ⟨v₁, f₁⟩ := val_psi D ξ hJ hJc _ _ k₁
  obtain ⟨v₂, f₂⟩ := val_psi D ξ hJ hJc _ _ k₂
  obtain ⟨v₃, f₃⟩ := val_psi D ξ hJ hJc _ _ k₃
  have key : ∀ {G : Type} [CommGroup G] (A₁ A₂ A₃ B₁ B₂ B₃ Z W : G),
      A₁ * A₂⁻¹ * A₃⁻¹ * Z⁻¹ * W = B₁ * B₂⁻¹ * B₃⁻¹ * Z⁻¹ → W * A₁ * B₂ * B₃ = B₁ * A₂ * A₃ := by
    intro G _ A₁ A₂ A₃ B₁ B₂ B₃ Z W h
    have h' := congrArg Additive.ofMul h
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv] at h' ⊢
    rw [← sub_eq_zero] at h' ⊢
    refine Eq.trans ?_ h'
    abel
  have e5 := congrArg Units.val (key _ _ _ _ _ _ _ _ e4)
  have e6 : cst ξ (v * (u₁ * r₁) * (v₂ * s₂) * (v₃ * s₃)) = cst ξ ((v₁ * s₁) * (u₂ * r₂) * (u₃ * r₃)) := by
    rw [map_mul, map_mul, map_mul, map_mul (cst ξ) (_ * _) (_ * r₃), map_mul (cst ξ) (_ * s₁), ← hv, ← g₁, ← g₂,
      ← g₃, ← f₁, ← f₂, ← f₃]
    exact e5
  have e7 := cst_injective ξ e6
  refine ⟨(v₁ * u₂ * u₃)⁻¹ * (v * u₁ * v₂ * v₃), ?_⟩
  rw [Units.val_mul, mul_assoc, Units.inv_mul_eq_iff_eq_mul]
  push_cast
  linear_combination e7

theorem norm_unit {R C : Type} [CommRing R] [NormedField C] (f : R →+* C) (hf : ∀ a, ‖f a‖ ≤ 1) (u : Rˣ) :
    ‖f u‖ = 1 := by
  have h : ‖f u‖ * ‖f (u⁻¹ : Rˣ)‖ = 1 := by rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  have h1 := hf u
  have h2 := hf (u⁻¹ : Rˣ)
  have h3 := norm_nonneg (f u)
  nlinarith

theorem betaAt_balanced : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (t : SAB H (Sp R)) (U : PELUnif (maximalIdeal R) t) (C : Type) [NormedField C] [IsUltrametricDist C] (f : R →+* C) (p : ℕ), IsIntegrallyClosed R → (∀ a, ‖f a‖ ≤ 1) → (∀ χ r, PsiCoord U.D.toPre χ r → f r ≠ 0) → ∀ (x : 𝓞 E) a b, betaAt U.D.toPre f p (x • a) b = betaAt U.D.toPre f p a (H.bar x • b) := by
  intro E _ _ _ H R _ _ _ _ t U C _ _ f p hR hf hne x a b
  letI := H.starRing
  have hex : ∀ χ, ∃ r, PsiCoord U.D.toPre χ r := fun χ =>
    ((GlobalTheory.PsiCoordLocal.main R U.D hR χ).1).imp fun _ h => h.1
  have hv : ∀ χ, vPsiAt U.D.toPre f p χ = -Real.logb p ‖f (hex χ).choose‖ := fun χ => dif_pos (hex χ)
  have hn : ∀ χ, ‖f (hex χ).choose‖ ≠ 0 := fun χ => norm_ne_zero_iff.2 (hne χ _ (hex χ).choose_spec)
  obtain ⟨u, hu⟩ := coord_balance U.D.toPre U.oD x a b (hex (x • a + b)).choose_spec (hex (x • a)).choose_spec
    (hex b).choose_spec (hex (a + H.bar x • b)).choose_spec (hex a).choose_spec (hex (H.bar x • b)).choose_spec
  have h := congrArg (fun r => Real.logb p ‖f r‖) hu
  simp only [map_mul, norm_mul, norm_unit f hf u, one_mul] at h
  rw [Real.logb_mul (mul_ne_zero (hn _) (hn _)) (hn _), Real.logb_mul (mul_ne_zero (hn _) (hn _)) (hn _),
    Real.logb_mul (hn _) (hn _), Real.logb_mul (hn _) (hn _)] at h
  simp only [betaAt, hv]
  linarith

end GlobalTheory.PeriodBalance
end
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShortConnIndep

theorem starRing_eq {R : Type} [CommRing R] (s t : StarRing R)
    (h : ∀ a : R, @star R s.toStarMul.toInvolutiveStar.toStar a = @star R t.toStarMul.toInvolutiveStar.toStar a) :
    s = t := by
  cases s with | @mk s1 _ =>
  cases t with | @mk t1 _ =>
  cases s1 with | @mk s2 _ =>
  cases t1 with | @mk t2 _ =>
  cases s2 with | @mk s3 _ =>
  cases t2 with | @mk t3 _ =>
  have : s3 = t3 := by
    cases s3; cases t3; congr; exact funext h
  subst this
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem sum_eq (hC : ChartIndepSt2) [StarRing (𝓞 E)] (nab nab' : NabV Xo c) (h : IsNab Xo c nab)
    (h' : IsNab Xo c nab') {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n : ℕ}
    (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) (N : ℕ)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) :
    ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b) =
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab' y ((N : ℤ) ^ 2) (F b) (colOf m b) := by
  letI : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
  have hU := thExprUniq_of_chartIndep2 hC
  obtain ⟨M, hM, hMP, hsupp⟩ := GlobalTheory.exists_natCast_smul_mem_harmA E H Dw l c a n P hP
  have key0 : ∀ (K : ℤ) (k : ℕ), K = (k : ℤ) →
      ∀ G : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L K (ptO Xo y.x)),
      ∑ m ∈ ((M : c.F) • P).support, algebraMap c.F S (((M : c.F) • P).coeff m) *
          ∏ b, nab y K (G b) (colOf m b) =
        ∑ m ∈ ((M : c.F) • P).support, algebraMap c.F S (((M : c.F) • P).coeff m) *
          ∏ b, nab' y K (G b) (colOf m b) := by
    rintro K k rfl G
    exact hU E H Dw l Xo c nab nab' h h' S y k n G a _ hMP
  have key := key0 _ (N ^ 2) (Nat.cast_pow N 2).symm F
  rw [hsupp] at key
  simp only [MvPolynomial.coeff_smul, smul_eq_mul, map_mul (algebraMap c.F S),
    _root_.mul_assoc, ← Finset.mul_sum] at key
  have hu : IsUnit (algebraMap c.F S (M : c.F)) :=
    (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hM.ne')).map _
  exact hu.mul_left_cancel key

theorem shortValAt_of (hC : ChartIndepSt2) [StarRing (𝓞 E)] (nab nab' : NabV Xo c) (h : IsNab Xo c nab)
    (h' : IsNab Xo c nab') {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F) (N : ℕ)
    (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)))
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S)
    (hv : ShortValAt Xo c nab w Λ β N P y v) : ShortValAt Xo c nab' w Λ β N P y v := by
  obtain ⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  refine ⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7.trans ?_⟩
  congr 1
  refine finsum_congr fun q => ?_
  congr 1
  exact Finset.sum_congr rfl fun i _ => sum_eq hC nab nab' h h' y' a P hP N (F q i)

end GlobalTheory.ShortConnIndep

namespace GlobalTheory

theorem shortGen_indep_connection : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (nab : NabV Xo c) (bad nV : ℕ), (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → ∀ (_ : StarRing (𝓞 E)) (nab' : NabV d.Xo₂ d.c₂), IsNab d.Xo₂ d.c₂ nab' → ∀ a, shortGen Xo c nab bad nV a n { d with nab₂ := nab' } = shortGen Xo c nab bad nV a n d := by
  intro hC E _ _ _ H Dw l Xo c n d nab bad nV ⟨s, hs⟩ t nab' ht a
  have hst : s = t := ShortConnIndep.starRing_eq s t fun x => (hs.1 x).trans (ht.1 x).symm
  subst hst
  have hmap : ∀ P : MvPolynomial (LtN Dw n) c.F,
      P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) →
      MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P ∈
        HHa Dw.mult n d.c₂.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) := by
    intro P hP
    have hs : Function.Surjective (d.eF : c.F →+* d.c₂.F) :=
      fun y => ⟨d.eF.symm y, d.eF.apply_symm_apply y⟩
    generalize (d.eF : c.F →+* d.c₂.F) = f at hs ⊢
    obtain ⟨h1, h2, h3⟩ := hP
    refine ⟨?_, ?_, ?_⟩
    · simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at h1 ⊢
      intro τ hτ b b'
      have hlap : lap Dw.mult n d.c₂.F 1 τ _ b b' (MvPolynomial.map f P) =
          MvPolynomial.map f (lap Dw.mult n c.F 1 τ _ b b' P) := by
        simp only [lap, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum,
          Derivation.coeFn_coe, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C,
          MvPolynomial.pderiv_map]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        congr 2
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      rw [hlap, h1 τ hτ b b', map_zero]
    · intro σ i i' hi t
      obtain ⟨s, rfl⟩ := hs t
      have hshift : rowShift Dw.mult n d.c₂.F σ i i' (f s) (MvPolynomial.map f P) =
          MvPolynomial.map f (rowShift Dw.mult n c.F σ i i' s P) := by
        clear h1 h2 h3
        induction P using MvPolynomial.induction_on with
        | C x => simp [rowShift]
        | add p q hp hq =>
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_add (f := _), hp, hq]
        | mul_X p x hp =>
          simp only [map_mul, hp, MvPolynomial.map_X]
          congr 1
          simp only [rowShift, MvPolynomial.aeval_X]
          set_option synthInstance.maxHeartbeats 100000 in
            split_ifs <;> simp
      rw [hshift, h2 σ i i' hi s]
    · intro m hm
      exact h3 m (MvPolynomial.support_map_subset f P hm)
  refine Set.ext fun f => ⟨?_, ?_⟩
  · rintro ⟨hf, Λ, N, x0, P, h1, h2, h3, h4, h5, hP, hr⟩
    refine ⟨hf, Λ, N, x0, P, h1, h2, h3, h4, h5, hP, ?_⟩
    intro k i1 i2 i3 i4 hk y y₂ hy
    obtain ⟨v, hv, he⟩ := @hr k i1 i2 i3 i4 hk y y₂ hy
    exact ⟨v, ShortConnIndep.shortValAt_of hC nab' d.nab₂ ht hs _ Λ _ N a _ (hmap P hP.1) y₂ v hv, he⟩
  · rintro ⟨hf, Λ, N, x0, P, h1, h2, h3, h4, h5, hP, hr⟩
    refine ⟨hf, Λ, N, x0, P, h1, h2, h3, h4, h5, hP, ?_⟩
    intro k i1 i2 i3 i4 hk y y₂ hy
    obtain ⟨v, hv, he⟩ := @hr k i1 i2 i3 i4 hk y y₂ hy
    exact ⟨v, ShortConnIndep.shortValAt_of hC d.nab₂ nab' hs ht _ Λ _ N a _ (hmap P hP.1) y₂ v hv, he⟩

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_inverse_unit_tower (ν : ℕ → ℤ) (h1 : ∀ n : ℕ, 0 < n → IsCoprime (ν n) (n : ℤ))
    (h2 : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n) :
    ∃ κ : ℕ → ℤ, (∀ n : ℕ, 0 < n → (n : ℤ) ∣ κ n * ν n - 1) ∧ (∀ n : ℕ, 0 < n → IsCoprime (κ n) (n : ℤ)) ∧
      ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ κ (n * m) - κ n := by
  have h : ∀ n : ℕ, ∃ x : ℤ, 0 < n → (n : ℤ) ∣ x * ν n - 1 := by
    intro n
    by_cases hn : 0 < n
    · obtain ⟨x, y, hxy⟩ := h1 n hn
      exact ⟨x, fun _ => ⟨-y, by linear_combination hxy⟩⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose κ hκ using h
  refine ⟨κ, hκ, fun n hn => ?_, fun n m hn hm => ?_⟩
  · obtain ⟨c, hc⟩ := hκ n hn
    exact ⟨ν n, -c, by linear_combination hc⟩
  · obtain ⟨c, hc⟩ := hκ n hn
    obtain ⟨c', hc'⟩ := hκ (n * m) (Nat.mul_pos hn hm)
    obtain ⟨d, hd⟩ := h2 n m hn hm
    push_cast at hc'
    refine ⟨κ n * m * c' - κ (n * m) * c - κ (n * m) * κ n * d, ?_⟩
    linear_combination κ n * hc' - κ (n * m) * hc - κ (n * m) * κ n * hd

theorem level_smul_mem_half {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H)
    {V : Type} [AddCommGroup V] [Module (𝓞 E) V] {s : 𝓞 E} (hs : s ∈ l.Mb) {a : V}
    (ha : a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) V)) : ∃ e, s • a = l.M • e := by
  have h : s • a ∈ Ideal.span {(l.M : 𝓞 E)} • (⊤ : Submodule (𝓞 E) V) := by
    rw [← l.prod, mul_smul]
    exact Submodule.smul_mem_smul hs ha
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h
  obtain ⟨e, -, he⟩ := h
  exact ⟨e, by rw [← he, Nat.cast_smul_eq_nsmul]⟩

theorem familyUnif_lattice_genus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)), IsPeriod (U.Di i) ty P → ∃ f : ℕ → D.La →ₗ[𝓞 E] (U.Di i).La, (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ (U.Di i).EF (f n a) (f n a') - D.EF a a') ∧ ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, f l.M a = U.t i a + l.M • e := by
  intro E _ _ _ H D l Xo σ g ty U i P hP
  obtain ⟨f, ν, h1, h2, h3, h4, h5, h6, -⟩ := familyUnif_lattice_similar E H D l Xo σ g ty U i P hP
  obtain ⟨κ, hκ1, hκ2, hκ3⟩ := exists_inverse_unit_tower ν h3 h4
  obtain ⟨s, hs1, hs2, hs3⟩ := GlobalTheory.T.exists_compatible_norm_tower_profinite E H l κ hκ2 hκ3
  have hinv : ∀ n : ℕ, 0 < n → ∃ r c : 𝓞 E, r * s n = 1 + n * c := by
    intro n hn
    obtain ⟨c, hc⟩ := hs1 n hn
    obtain ⟨d, hd⟩ := hκ1 n hn
    have hd' : (κ n : 𝓞 E) * (ν n : 𝓞 E) - 1 = (n : 𝓞 E) * (d : 𝓞 E) := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hd
    exact ⟨(ν n : 𝓞 E) * H.bar (s n), (ν n : 𝓞 E) * c + d, by linear_combination (ν n : 𝓞 E) * hc + hd'⟩
  refine ⟨fun n => s n • f n, fun n m hn hm a => ?_, fun n hn => ⟨fun a => ⟨?_, ?_⟩, fun a' => ?_⟩,
    fun n hn a a' => ?_, fun a ha => ?_⟩
  · obtain ⟨e, he⟩ := h1 n m hn hm a
    obtain ⟨c, hc⟩ := hs2 n m hn hm
    have hc' : s (n * m) = s n + n * c := by linear_combination hc
    refine ⟨c • f n a + s (n * m) • e, ?_⟩
    simp only [LinearMap.smul_apply]
    rw [he, hc', ← Nat.cast_smul_eq_nsmul (𝓞 E), ← Nat.cast_smul_eq_nsmul (𝓞 E)]
    module
  · rintro ⟨e, he⟩
    obtain ⟨r, c, hrc⟩ := hinv n hn
    rw [← (h2 n hn).1 a]
    refine ⟨r • e - c • f n a, ?_⟩
    rw [LinearMap.smul_apply, ← Nat.cast_smul_eq_nsmul (𝓞 E)] at he
    have h : (r * s n) • f n a = r • (n : 𝓞 E) • e := by rw [mul_smul, he]
    rw [hrc] at h
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    linear_combination (norm := module) h
  · rintro ⟨e, rfl⟩
    exact ⟨(s n • f n) e, by rw [map_nsmul]⟩
  · obtain ⟨a, e, he⟩ := (h2 n hn).2 a'
    obtain ⟨r, c, hrc⟩ := hinv n hn
    refine ⟨r • a, e - c • f n a, ?_⟩
    rw [LinearMap.smul_apply, map_smul, smul_smul, mul_comm, hrc, he, ← Nat.cast_smul_eq_nsmul (𝓞 E),
      ← Nat.cast_smul_eq_nsmul (𝓞 E)]
    module
  · obtain ⟨c, hc⟩ := hs1 n hn
    obtain ⟨d, hd⟩ := hκ1 n hn
    obtain ⟨k, hk⟩ := h5 n hn (s n • a) (s n • a')
    have hc' : H.bar (s n) * s n = (κ n : 𝓞 E) + (n : 𝓞 E) * c := by linear_combination hc
    have e1 : D.EF (s n • a) (s n • a') = κ n * D.EF a a' + n * D.EF a (c • a') := by
      rw [D.adj, smul_smul, hc', add_smul, mul_smul, Nat.cast_smul_eq_nsmul, Int.cast_smul_eq_zsmul, map_add (f := _),
        map_nsmul, map_zsmul, smul_eq_mul, nsmul_eq_mul]
    simp only [LinearMap.smul_apply, ← map_smul]
    rw [e1] at hk
    refine ⟨k + d * D.EF a a' + ν n * D.EF a (c • a'), ?_⟩
    linear_combination hk + D.EF a a' * hd
  · obtain ⟨e, he⟩ := h6 a ha
    obtain ⟨e', he'⟩ := level_smul_mem_half l hs3 ha
    refine ⟨e + f l.M e', ?_⟩
    have h : s l.M • a = a + l.M • e' := by rw [← he', sub_smul, one_smul, add_sub_cancel]
    rw [LinearMap.smul_apply, ← map_smul, h, map_add (f := _), map_nsmul, he, smul_add, add_assoc]

end GlobalTheory
end
