module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3109
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedIsoPulledBackPeriodRelation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackPeriodConstantsMultiplicative
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMultiplicationPullbackIntegralFamilyOdd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3127
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiMemMaximalIdealTendstoZero
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3136
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle070
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle080
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PeriodPos

theorem gm_spMap_unitOn {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) (z : Sp B) (u : Aˣ) :
    gm (spMap g) z ⊤ (unitOn u) = gm (𝟙 _) z ⊤ (unitOn (Units.map g.toMonoidHom u)) := by
  refine (congrArg (fun f => gm f z ⊤ (unitOn u)) (Category.id_comp (spMap g)).symm).trans ?_
  refine (gm_pull (𝟙 _) (spMap g) z ⊤ trivial _).symm.trans ?_
  show gm (𝟙 _) z ⊤ (Units.map (spMap g).appTop.hom (unitOn u)) = _
  congr 1
  apply Units.ext
  have e := congrArg (fun φ => φ.hom (u : A)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  exact e.symm

theorem gm_unitOn_injective (R : Type) [CommRing R] [IsDomain R] (z : (TK R).left) (a b : (FractionRing R)ˣ)
    (h : gm (𝟙 _) z ⊤ (unitOn a) = gm (𝟙 _) z ⊤ (unitOn b)) : a = b := by
  have e := congrArg Units.val h
  rw [gm_val _ z ⊤ trivial, gm_val _ z ⊤ trivial] at e
  let φ : FractionRing R →+* (TK R).left.presheaf.stalk z :=
    ((TK R).left.presheaf.germ (𝟙 (TK R).left ⁻¹ᵁ ⊤) z trivial).hom.comp
      ((Scheme.Hom.app (𝟙 (TK R).left) ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom)
  exact Units.ext (φ.injective e)

theorem gm_generic_of_closed {X : Scheme.{0}} (U : X.Opens) (a : Γ(X, U)ˣ) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] (h : Sp R ⟶ X) (z : (TK R).left) (hc : h (closedPoint R) ∈ U) :
    ∃ v : Rˣ, gm (jK R ≫ h) z U a =
      gm (𝟙 _) z ⊤ (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom v)) := by
  have htop : h ⁻¹ᵁ U = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem h hc
  have hz : h (jK R z) ∈ U := by
    show jK R z ∈ h ⁻¹ᵁ U
    rw [htop]; trivial
  let b : Γ(Sp R, ⊤)ˣ := res htop.ge (pullU h U a)
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom b, ?_⟩
  rw [← gm_pull (jK R) h z U hz a, ← gm_res (jK R) z htop.ge trivial (pullU h U a)]
  have hb : b = unitOn (Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom b) := by
    apply Units.ext
    exact ((Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply _).symm
  change gm (jK R) z ⊤ b = _
  exact (congrArg (gm (jK R) z ⊤) hb).trans (gm_spMap_unitOn (algebraMap R (FractionRing R)) z _)

theorem exists_good_closed {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] {K : Type} (h : K → (Sp R ⟶ X)) (z : (TK R).left)
    (hinj : ∀ a b, jK R ≫ h a = jK R ≫ h b → h a = h b) :
    ∃ J, Good L z J ∧ ∀ k, h k (closedPoint R) ∈ L.U (J (jK R ≫ h k)) := by
  choose ch hch using fun g : Sp R ⟶ X => exists_chart hL (g (closedPoint R))
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (fun k => jK R ≫ h k) (fun k => ch (h k))
    (fun a b hab => by rw [hinj a b hab]) (fun k => by
      rw [Scheme.Hom.comp_apply]
      show jK R z ∈ h k ⁻¹ᵁ L.U (ch (h k))
      rw [Scheme.preimage_eq_top_of_closedPoint_mem (h k) (hch (h k))]; trivial)
  exact ⟨J, hJ, fun k => by rw [e k]; exact hch (h k)⟩

theorem ext_generic {X : Scheme.{0}} {W : Type} [CommRing W] (s : X ⟶ Sp W) [IsSeparated s] (R : Type) [CommRing R]
    [IsDomain R] (f g : Sp R ⟶ X) (h : jK R ≫ f = jK R ≫ g) : f = g := by
  have hs : f ≫ s = g ≫ s := by
    have e : jK R ≫ (f ≫ s) = jK R ≫ (g ≫ s) := by rw [← Category.assoc, h, Category.assoc]
    rw [← Spec.map_preimage (f ≫ s), ← Spec.map_preimage (g ≫ s)] at e ⊢
    rw [← Spec.map_comp, ← Spec.map_comp] at e
    congr 1
    have e' := Spec.map_injective e
    ext x
    exact IsFractionRing.injective R (FractionRing R) (congrArg (fun φ => φ.hom x) e')
  have : IsDominant (jK R) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨p⟩ : Nonempty (TK R).left := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
    let y : PrimeSpectrum R := (jK R).base p
    have hy : y.asIdeal = ⊥ := by
      ext r
      refine ⟨fun hr => ?_, fun hr => by rw [Ideal.mem_bot.1 hr]; exact zero_mem _⟩
      have h1 : algebraMap R (FractionRing R) r ∈ p.asIdeal := hr
      have hp : p.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ _ p.isPrime
      rw [hp, Ideal.mem_bot] at h1
      exact Ideal.mem_bot.2 ((IsFractionRing.injective R (FractionRing R)).eq_iff.1 (h1.trans (map_zero _).symm))
    have hcl : closure ({y} : Set (PrimeSpectrum R)) = Set.univ := by
      rw [PrimeSpectrum.closure_singleton, hy]; exact PrimeSpectrum.zeroLocus_bot
    have key : (x : PrimeSpectrum R) ∈ closure ({y} : Set (PrimeSpectrum R)) := hcl ▸ Set.mem_univ _
    have sub : ({y} : Set (PrimeSpectrum R)) ⊆ Set.range (jK R).base := Set.singleton_subset_iff.2 ⟨p, rfl⟩
    exact closure_mono sub key
  exact ext_of_isDominant_of_isSeparated s hs (jK R) h

theorem exists_fracMap (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (f₁ : V →+* V₁)
    (hf : Function.Injective f₁) : ∃ κK : (TK V₁).left ⟶ (TK V).left, κK ≫ jK V = jK V₁ ≫ spMap f₁ ∧
      ∀ (z : (TK V₁).left) (r : V) (k : (FractionRing V)ˣ), (k : FractionRing V) = algebraMap V _ r →
        ∃ k' : (FractionRing V₁)ˣ, (k' : FractionRing V₁) = algebraMap V₁ _ (f₁ r) ∧
          gm κK z ⊤ (unitOn k) = gm (𝟙 _) z ⊤ (unitOn k') := by
  let fK : FractionRing V →+* FractionRing V₁ := IsLocalization.map (FractionRing V₁) f₁
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f₁ hf)
  have hfK : ∀ x, fK (algebraMap V _ x) = algebraMap V₁ _ (f₁ x) := fun x => IsLocalization.map_eq _ _
  refine ⟨spMap fK, ?_, fun z r k hk => ⟨Units.map fK.toMonoidHom k, ?_, gm_spMap_unitOn fK z k⟩⟩
  · rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact hfK x
  · rw [Units.coe_map, ← hfK, ← hk]; rfl

theorem periods_pos_diag : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → ∀ (x : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')), (∀ a, (x a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ (x a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∀ (w₁ : LB.Iso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂')) (q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ), w₁.IsGen → PeriodRel D.toPre L.T f₁ κ₁ w₁ (e.trans e₀) x n q → ∀ a, a ≠ 0 → ∃ w ∈ maximalIdeal V₁, w ≠ 0 ∧ (q a a : FractionRing V₁) = algebraMap V₁ _ w := by
  intro n V _ _ _ D r e₀ L V₁ _ _ _ f₁ κ₁ e B' _ β' β'' β₂ β₂' _ _ _ _ hf₁ _ hloc _ _ _ _ _ x _ w₁ q _ hP a ha
  classical
  set c := e.trans e₀ with hc
  have hy : c a ≠ 0 := (AddEquiv.map_ne_zero_iff c).2 ha
  obtain ⟨r₀, hr₀, k, hk, u, hu⟩ := GlobalTheory.T.degenerationData_period_diagonal_mem_maxIdeal_mul_generator V D (c a) hy
  obtain ⟨κK, hκ, hfr⟩ := exists_fracMap V V₁ f₁ hf₁
  obtain ⟨z⟩ : Nonempty (TK V₁).left := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  let P : Sp V₁ ⟶ (G2 B').left := (lift (x a) (x a)).left
  have : IsProper L.T.B.hom := L.T.isAb.proper
  have : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  obtain ⟨J, hJ, hJc⟩ := exists_good_closed L.T.M.L L.T.M.isLB V₁
    (Sum.elim (fun I : ULift (Finset (Fin 2)) => P ≫ β₂' ≫ (psum L.T.B (x2 L.T.B) I.down).left)
      (fun k : Fin 4 => spMap κ₁ ≫ lamPts (L.T.c₀ ((n : ℤ) • a)) (L.T.c₀ ((n : ℤ) • a)) k)) z
    (fun _ _ h => ext_generic L.T.B.hom V₁ _ _ h)
  obtain ⟨J', hJ', hJc'⟩ := exists_good_closed D.toPre.P.L D.toPre.P.isLB V₁
    (Sum.elim (fun I : ULift (Finset (Fin 2)) => P ≫ β₂ ≫ (psum D.toPre.P.A (x2 D.toPre.P.A) I.down).left)
      (fun k : Fin 4 => spMap f₁ ≫ lamPts (D.toPre.c (c a)) (D.toPre.c (c a)) k)) z
    (fun _ _ h => ext_generic D.toPre.P.A.hom V₁ _ _ h)
  have key := hP κK hκ a a z J J' hJ hJ'
  rw [hu _ κK z J' hJ'] at key
  obtain ⟨v₁, hv₁⟩ : ∃ v : V₁ˣ, val u (κK ≫ jK V) z J' =
      gm (𝟙 _) z ⊤ (unitOn (Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom v)) := by
    rw [hκ]
    unfold val
    refine gm_generic_of_closed _ _ V₁ (spMap f₁) z (Set.mem_iInter.2 fun k => ?_)
    have := hJc' (Sum.inr k)
    simp only [Sum.elim_inr, Scheme.Hom.comp_apply] at this; exact this
  obtain ⟨v₂, hv₂⟩ : ∃ v : V₁ˣ, isoVal w₁ (lift (toUnit (TK V₁) ≫ x a) (toUnit (TK V₁) ≫ x a)).left z J J' =
      gm (𝟙 _) z ⊤ (unitOn (Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom v)) := by
    have hp : (lift (toUnit (TK V₁) ≫ x a) (toUnit (TK V₁) ≫ x a)).left = jK V₁ ≫ P := by
      rw [← comp_lift]; rfl
    unfold isoVal
    rw [hp]
    refine gm_generic_of_closed _ _ V₁ P z ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun I => ?_,
      Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun I => ?_⟩
    · have := hJc (Sum.inl I)
      simp only [Sum.elim_inl, Scheme.Hom.comp_apply] at this; exact this
    · have := hJc' (Sum.inl I)
      simp only [Sum.elim_inl, Scheme.Hom.comp_apply] at this; exact this
  obtain ⟨v₃, hv₃⟩ : ∃ v : V₁ˣ, val (L.T.τ₀ ((n : ℤ) • a) ((n : ℤ) • a)) ((TK V₁).hom ≫ spMap κ₁) z J =
      gm (𝟙 _) z ⊤ (unitOn (Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom v)) := by
    unfold val
    refine gm_generic_of_closed _ _ V₁ (spMap κ₁) z (Set.mem_iInter.2 fun k => ?_)
    have := hJc (Sum.inr k)
    simp only [Sum.elim_inr, Scheme.Hom.comp_apply] at this; exact this
  obtain ⟨k', hk', hkk⟩ := hfr z r₀ k hk
  rw [hkk, hv₁, hv₂, hv₃] at key
  have hmul : ∀ s t : (FractionRing V₁)ˣ,
      gm (𝟙 _) z ⊤ (unitOn (s * t)) = gm (𝟙 _) z ⊤ (unitOn s) * gm (𝟙 _) z ⊤ (unitOn t) := fun s t => by
    rw [← map_mul]; congr 1; exact map_mul _ _ _
  rw [← hmul, ← hmul, ← hmul] at key
  have e' := gm_unitOn_injective V₁ z _ _ key

  have hq : q a a = k' * Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom (v₁ * (v₂ * v₃)⁻¹) := by
    rw [map_mul, map_inv, map_mul]
    exact (eq_mul_inv_of_mul_eq e'.symm).trans (_root_.mul_assoc _ _ _)
  have hv : ((q a a : (FractionRing V₁)ˣ) : FractionRing V₁) = algebraMap V₁ _ (f₁ r₀ * ↑(v₁ * (v₂ * v₃)⁻¹)) := by
    rw [hq, Units.val_mul, hk', Units.coe_map, map_mul]
    rfl
  refine ⟨f₁ r₀ * ↑(v₁ * (v₂ * v₃)⁻¹), Ideal.mul_mem_right _ _ (map_nonunit f₁ r₀ hr₀), ?_, hv⟩
  intro hw
  apply (q a a).ne_zero
  rw [hv, hw, map_zero]

end GlobalTheory.PeriodPos
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_normalised_iso_pulledBack_period_relation : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → LBIso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂') → ∀ (x : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')), (∀ a, (x a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ (x a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∃ (w₁ : LB.Iso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂')) (q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ), w₁.IsGen ∧ IsNormIso w₁ ∧ PeriodRel D.toPre L.T f₁ κ₁ w₁ (e.trans e₀) x n q := by
  first | exact @GlobalTheory.TChart.Ratio.exists_normIso_periodRel | exact GlobalTheory.TChart.Ratio.exists_normIso_periodRel | (intros; apply GlobalTheory.TChart.Ratio.exists_normIso_periodRel <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.pulledBack_period_constants_multiplicative : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → ∀ (x : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')), (∀ a, (x a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ (x a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∀ (w₁ : LB.Iso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂')) (q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ), w₁.IsGen → PeriodRel D.toPre L.T f₁ κ₁ w₁ (e.trans e₀) x n q → IsNormIso w₁ → ∀ a a' b, q (a + a') b = q a b * q a' b := by
  first | exact @GlobalTheory.TChart.PeriodAdd.period_add | exact GlobalTheory.TChart.PeriodAdd.period_add | (intros; apply GlobalTheory.TChart.PeriodAdd.period_add <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_multiplicationPullback_genericSection_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ θ₀ : SecK C.P.L.L C.α 1, ∃ S : SecK C.P.L.L C.α (m ^ 2), MulSecK C m θ₀ S := by
  first | exact @GlobalTheory.Mum.exists_mulSecK | exact GlobalTheory.Mum.exists_mulSecK | (intros; apply GlobalTheory.Mum.exists_mulSecK <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.multiplicationPullback_family_ne_zero_odd : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (m : ℕ), Odd m → ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (G : IntFam (maximalIdeal R) D.toPre (m ^ 2)), MulFam m F₁ G → (∃ α j, (F₁.f α).f j ≠ 0) → ∃ α j, (G.f α).f j ≠ 0 := by
  first | exact @GlobalTheory.Mum.mulFam_exists_ne_zero | exact GlobalTheory.Mum.mulFam_exists_ne_zero | (intros; apply GlobalTheory.Mum.mulFam_exists_ne_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.expansion_multiplicationPullback_trait_degreeOne : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (m : ℕ), Odd m →
    ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (G : IntFam (maximalIdeal R) D.toPre (m ^ 2)), MulFam m F₁ G →
    ∀ (σ' : H0 T.U.LG.L 1) (f' : ∀ x, T.D'.toPre.SecB 1 x), (∀ x, PullB T.hD x (F₁.f (T.hD.xe x)) (f' x)) →
    (∀ e, T.U.ExpandsAt e 1 σ' f') →
    ∀ (f'' : ∀ x, T.D'.toPre.SecB (m ^ 2) x), (∀ x, PullB T.hD x (G.f (T.hD.xe x)) (f'' x)) →
    ∃ (uG : LB.Gen (LB.LinComb T.U.LG.L (K := Fin 2) ![𝟙 T.G.left, (mulA T.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]))
      (σ'' : H0 T.U.LG.L (m ^ 2)), uG.IsGen ∧
      (∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) (J : (Z ⟶ T.G.left) → T.U.LG.L.ι), Good T.U.LG.L z J →
        sval σ'' r z J = (val uG (r ≫ 𝟙 _) z J).val * sval σ' (r ≫ (mulA T.G m).left) z J) ∧
      ∀ e, T.U.ExpandsAt e (m ^ 2) σ'' f'' := by
  first | exact @GlobalTheory.Mum.MulExpand.expand | exact GlobalTheory.Mum.MulExpand.expand | (intros; apply GlobalTheory.Mum.MulExpand.expand <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_multiplicationPullback_integralFamily_odd : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (m : ℕ), Odd m → ∀ F₁ : IntFam (maximalIdeal R) D.toPre 1, ∃ G : IntFam (maximalIdeal R) D.toPre (m ^ 2), MulFam m F₁ G := by
  first | exact @GlobalTheory.Mum.exists_intFam_mul | exact GlobalTheory.Mum.exists_intFam_mul | (intros; apply GlobalTheory.Mum.exists_intFam_mul <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_mumfordMultiplier_exponent_nonzero_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∃ N : ℕ, 1 ≤ N ∧ GlobalTheory.MumMult.PosN D a h h' N ∧ ∃ (σ₀ : LB.Sec (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1])) (x : D.toPre.P.A.left), D.toPre.P.A.hom x = (IsLocalRing.closedPoint R : PrimeSpectrum R) ∧ GlobalTheory.MumMult.NonzeroAt D a N σ₀ x := by
  first | exact @GlobalTheory.MumMult.exists_N_sec | exact GlobalTheory.MumMult.exists_N_sec | (intros; apply GlobalTheory.MumMult.exists_N_sec <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
open GlobalTheory.UU GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit

noncomputable section

namespace GlobalTheory.MumInt

theorem bal_part {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (k : D.X → (FractionRing R)ˣ) (hk : PsiScal D ga k) {a a' : D.P.A ⟶ D.P.A} {h h' : D.X →+ D.X}
    (hE : EndData D a a' h h') (y w : D.X) :
    ∃ u ∈ unitsK R, k (h y + w) * k y * k (h' w) = u * (k (y + h' w) * k (h y) * k w) := by
  obtain ⟨ha, ha', hr, -, -, hb⟩ := hE
  obtain ⟨t, ht, t₀⟩ := exists_ros GlobalTheory.globalFns_holds D.P.isAb D.P.isLB a a' hr
  obtain ⟨z⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  obtain ⟨J, hJ, iJ⟩ := GlobalTheory.Mum.TensPos.exists_int D.P z
  let E : (FractionRing R)ˣ →* ((TK R).left.presheaf.stalk z)ˣ := Units.map (ev z).toMonoidHom
  have hψ : ∀ χ, val (D.psi χ) (𝟙 _) z J = E (k χ) * val (ga χ) (toUnit (TK R)).left z J := fun χ =>
    Units.ext (((hk χ).2 (TK R) (𝟙 _) z J hJ).trans (congrArg₂ (· * ·) (ev_eq z _) rfl))
  have vτ : ∀ a b : D.X, val (D.tau a b) (𝟙 _) z J =
      val (D.psi (a + b)) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ * (val (D.psi b) (𝟙 _) z J)⁻¹ *
        (val D.rigK (𝟙 _) z J)⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  have mg : ∀ χ, val (ga χ) (toUnit (TK R)).left z J ∈ unitsS z := fun χ => GlobalTheory.Mum.TensPos.val_mem D.P z iJ _ _ _
  have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm.trans
    (val_corr hJ (hb t ht t₀ y w) (𝟙 _))
  have ep : 𝟙 _ ≫ D.pt2 y w = (toUnit (TK R)).left ≫ (lift (D.c y) (D.c w)).left := by
    rw [Category.id_comp, ← Over.comp_left, comp_lift]; rfl
  have mt : val t (𝟙 _ ≫ D.pt2 y w) z J ∈ unitsS z := by
    rw [ep, ← val_pull hJ]
    refine GlobalTheory.Mum.TensPol.val_mem z iJ _ (fun i => ?_) _ _
    have hφ : rosatiφ D.P.A a a' i ≫ D.P.A.hom = (D.P.A ⊗ D.P.A).hom := by
      fin_cases i <;> exact Over.w _
    rw [Category.assoc, hφ]
    exact Over.w _
  rw [vτ, vτ] at e
  simp only [hψ] at e
  generalize val t (𝟙 _ ≫ D.pt2 y w) z J = v at e mt
  refine ⟨k (h y + w) * k y * k (h' w) * (k (y + h' w) * k (h y) * k w)⁻¹, GlobalTheory.Mum.TensPol.mem_unitsK z ?_,
    by rw [inv_mul_cancel_right]⟩
  have : E (k (h y + w) * k y * k (h' w) * (k (y + h' w) * k (h y) * k w)⁻¹) =
      val (ga (y + h' w)) (toUnit (TK R)).left z J * val (ga (h y)) (toUnit (TK R)).left z J *
        val (ga w) (toUnit (TK R)).left z J * (val (ga (h y + w)) (toUnit (TK R)).left z J *
        val (ga y) (toUnit (TK R)).left z J * val (ga (h' w)) (toUnit (TK R)).left z J * v)⁻¹ := by
    simp only [map_mul, map_inv]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  exact this ▸ mul_mem (mul_mem (mul_mem (mg _) (mg _)) (mg _))
    (inv_mem (mul_mem (mul_mem (mul_mem (mg _) (mg _)) (mg _)) mt))

theorem scalars_int {R : Type} [CommRing R] [IsDomain R] {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    (k : X → (FractionRing R)ˣ) (h h' : X →+ X) (N : ℕ)
    (hn : ∀ x, ∃ u ∈ unitsK R, k (-x) = u * k x)
    (hc : ∀ x y w, ∃ u ∈ unitsK R, k (x + y + w) * k x * k y * k w = u * (k (x + y) * k (x + w) * k (y + w)))
    (hi : ∀ x, x ≠ 0 → ∃ s : R, (k x : FractionRing R) = algebraMap R _ s)
    (hb : ∀ y w, ∃ u ∈ unitsK R, k (h y + w) * k y * k (h' w) = u * (k (y + h' w) * k (h y) * k w))
    (hP : ∀ (κ : X → (FractionRing R)ˣ), (∀ y, κ (-y) = κ y) → κ 0 = 1 →
      (∀ x y z, κ (x + y + z) * κ x * κ y * κ z = κ (x + y) * κ (x + z) * κ (y + z)) →
      (∀ y, ∃ r : R, (κ y : FractionRing R) = algebraMap R _ r) →
      (∀ y z, ∃ u : Rˣ, ((κ (h y + z) * κ y * κ (h' z) : (FractionRing R)ˣ) : FractionRing R) =
        algebraMap R _ (u : R) * ((κ (y + h' z) * κ (h y) * κ z : (FractionRing R)ˣ) : FractionRing R)) →
      ∀ y, ∃ r : R, ((κ y ^ N : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ r * κ y * κ (h y)) (y : X) :
    (∃ s : R, (k y : FractionRing R) = algebraMap R _ s) ∧
      ∃ ρ : R, ((k y ^ N * (k (h y))⁻¹ : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ ρ * k y := by
  obtain ⟨B, hB⟩ := exists_exact (unitsK R) k hn hc
  choose u hu eu using hB
  let κ : X → (FractionRing R)ˣ := fun x => (B x x).toMul
  have eκ : ∀ x, k x = u x * κ x := eu
  have κn : ∀ x, κ (-x) = κ x := fun x => by simp [κ]
  have κ0 : κ 0 = 1 := by simp [κ]
  have κc : ∀ x y w, κ (x + y + w) * κ x * κ y * κ w = κ (x + y) * κ (x + w) * κ (y + w) := fun x y w => by
    apply Additive.ofMul.injective
    simp only [κ, ofMul_mul, ofMul_toMul, map_add (f := _), LinearMap.add_apply]
    abel
  have κi : ∀ x, ∃ s : R, (κ x : FractionRing R) = algebraMap R _ s := fun x => by
    by_cases hx : x = 0
    · exact ⟨1, by rw [hx, κ0, map_one, Units.val_one]⟩
    · obtain ⟨s, hs⟩ := hi x hx
      obtain ⟨s', -, e⟩ := mem_of_unit ⊤ ((unitsK R).inv_mem (hu x)) ⟨s, trivial, hs⟩
      rw [eκ x, inv_mul_cancel_left] at e
      exact ⟨s', e⟩
  have κb : ∀ y z, ∃ v : Rˣ, ((κ (h y + z) * κ y * κ (h' z) : (FractionRing R)ˣ) : FractionRing R) =
      algebraMap R _ (v : R) * ((κ (y + h' z) * κ (h y) * κ z : (FractionRing R)ˣ) : FractionRing R) := fun y z => by
    obtain ⟨v, hv, e⟩ := hb y z
    obtain ⟨v', ev'⟩ := mul_mem (mul_mem hv (mul_mem (mul_mem (hu (y + h' z)) (hu (h y))) (hu z)))
      (inv_mem (mul_mem (mul_mem (hu (h y + z)) (hu y)) (hu (h' z))))
    refine ⟨v', congrArg Units.val (?_ : _ = Units.map (algebraMap R (FractionRing R)).toMonoidHom v' * _)⟩
    rw [ev']
    simp only [eκ] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  obtain ⟨ρ, eρ⟩ := hP κ κn κ0 κc κi κb y
  obtain ⟨v, ev'⟩ := mul_mem (pow_mem (hu y) N) (inv_mem (mul_mem (hu y) (hu (h y))))
  refine ⟨?_, v * ρ, ?_⟩
  · obtain ⟨s, hs⟩ := κi y
    obtain ⟨s', -, e⟩ := mem_of_unit ⊤ (hu y) ⟨s, trivial, hs⟩
    exact ⟨s', eκ y ▸ e⟩
  · have e1 : algebraMap R (FractionRing R) v = ((u y ^ N * (u y * u (h y))⁻¹ : (FractionRing R)ˣ) : FractionRing R) :=
      congrArg Units.val ev'
    rw [map_mul, e1, eκ y, eκ (h y), mul_pow]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, eρ]
    have := (u y).ne_zero
    have := (u (h y)).ne_zero
    have := (κ (h y)).ne_zero
    field_simp

theorem gs_scal {R : Type} [CommRing R] [IsDomain R] (z : (TK R).left) (r : R) :
    gs (𝟙 _) z ⊤ (scal (jK R) r) = ev z (algebraMap R _ r) := by
  have nat := congrArg (fun g => g.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
  rw [gs_eq _ z ⊤ trivial]
  exact congrArg ((TK R).left.presheaf.germ ⊤ z trivial).hom nat.symm

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ N : ℕ, 1 ≤ N → GlobalTheory.MumMult.PosN D a h h' N → ∃ (r : D.toPre.X → R) (g : ∀ y : D.toPre.X, LB.Gen (LB.LinComb D.toPre.P.L (K := PUnit) (fun _ => (D.toPre.c y).left) (fun _ => -1))), (∀ y, (g y).IsGen) ∧ (∀ y, y ≠ 0 → r y ∈ maximalIdeal R) ∧ (∀ e : ℕ, {y | r y ∉ maximalIdeal R ^ e}.Finite) ∧ ∀ y (z : (TK R).left) (J), Good D.toPre.P.L z J → (val (D.toPre.psi y) (𝟙 _) z J ^ N * (val (D.toPre.psi (h y)) (𝟙 _) z J)⁻¹).val = gs (𝟙 _) z ⊤ (scal (jK R) (r y)) * (val (g y) (toUnit (TK R)).left z J ^ N * (val (g (h y)) (toUnit (TK R)).left z J)⁻¹).val := by
  intro R _ _ _ _ D a a' h h' hE N _ hP
  obtain ⟨ga, k, hk⟩ := exists_psiScal R D.toPre
  have key := scalars_int k h h' N
    (fun x => by
      obtain ⟨u, e⟩ := even_part D.toPre ga k hk D.psi_even x
      exact ⟨_, ⟨u, rfl⟩, Units.ext e⟩)
    (fun x y w => by
      obtain ⟨u, e⟩ := cub_part D.toPre ga k hk D.tau_bimult x y w
      exact ⟨_, ⟨u, rfl⟩, Units.ext e⟩)
    (fun x hx => by
      obtain ⟨s, -, e⟩ := (PsiScalIn.main_local D.toPre ga k hk x _).1 (D.psi_pos x hx)
      exact ⟨s, e.symm⟩)
    (bal_part D.toPre ga k hk hE) hP.2
  choose s hs using fun y => (key y).1
  choose ρ hρ using fun y => (key y).2
  have hm : ∀ y (I : Ideal R), D.toPre.PsiIn y I → ρ y * s y ∈ I := fun y I hy => by
    obtain ⟨t, ht, e⟩ := (PsiScalIn.main_local D.toPre ga k hk y _).1 hy
    obtain rfl : t = s y := IsFractionRing.injective R (FractionRing R) (e.trans (hs y))
    exact I.mul_mem_left _ ht
  refine ⟨fun y => ρ y * s y, ga, fun y => (hk y).1, fun y hy => hm y _ (D.psi_pos y hy),
    fun e => (D.psi_tendsto e).subset fun y hy hi => hy (hm y _ hi), fun y z J hJ => ?_⟩
  have hψ : ∀ χ, val (D.toPre.psi χ) (𝟙 _) z J =
      Units.map (ev z).toMonoidHom (k χ) * val (ga χ) (toUnit (TK R)).left z J := fun χ =>
    Units.ext (((hk χ).2 (TK R) (𝟙 _) z J hJ).trans (congrArg₂ (· * ·) (ev_eq z _) rfl))
  have e : algebraMap R (FractionRing R) (ρ y * s y) = (k y ^ N * (k (h y))⁻¹).val := by
    rw [hρ, map_mul, hs]
  rw [gs_scal, e, hψ, hψ]
  refine congrArg Units.val (?_ : _ = Units.map (ev z).toMonoidHom (k y ^ N * (k (h y))⁻¹) * _)
  rw [map_mul, map_pow, map_inv, mul_pow, mul_inv, _root_.mul_mul_mul_comm]

end GlobalTheory.MumInt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.chartValue_isIntegral_of_integral_at_points : ∀ {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) (k : ℕ) (s : SecK L α k) (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j), IsAffineOpen W → IsAffineOpen (α ⁻¹ᵁ W) → (∀ x ∈ W, IntAt L α s x) → (α.app W).hom.IsIntegralElem (chartVal L α s j W hW) := by
  first | exact @GlobalTheory.Mum.chartVal_isIntegral_of_intAt | exact GlobalTheory.Mum.chartVal_isIntegral_of_intAt | (intros; apply GlobalTheory.Mum.chartVal_isIntegral_of_intAt <;> assumption)
end
