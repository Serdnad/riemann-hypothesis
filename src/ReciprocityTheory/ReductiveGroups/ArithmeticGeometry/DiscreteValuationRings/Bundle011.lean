module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle008
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle006

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing QForm
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem app_fst_eq_zero_of_snd {X T S : Scheme.{0}} (p : X ⟶ S) (t : T ⟶ S) (W : X.Opens) (d : Γ(X, W))
    (h : ((pullback.snd t p).app W).hom d = 0) : ((pullback.fst p t).app W).hom d = 0 := by
  rw [← CategoryTheory.Limits.pullbackSymmetry_hom_comp_snd, AlgebraicGeometry.Scheme.Hom.comp_app]
  erw [CommRingCat.hom_comp, RingHom.comp_apply, h, map_zero]

theorem snd_app_eq_zero {X T S : Scheme.{0}} (p : X ⟶ S) (t : T ⟶ S) (W : X.Opens) (d : Γ(X, W))
    (h : ∀ y : ↥(CategoryTheory.Limits.pullback t p : Scheme.{0}), CategoryTheory.Limits.pullback.snd t p y ∈ W → gs (CategoryTheory.Limits.pullback.snd t p) y W d = 0) :
    ((CategoryTheory.Limits.pullback.snd t p).app W).hom d = 0 := by
  refine TopCat.Presheaf.section_ext (CategoryTheory.Limits.pullback t p).sheaf _ _ _ fun y hy => ?_
  have hy' : CategoryTheory.Limits.pullback.snd t p y ∈ W := hy
  have := h y hy'
  simp only [gs, dif_pos hy'] at this
  erw [this]
  exact (map_zero _).symm

theorem secB_dvd_of_vge {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) {D : Out.DegData V (IsLocalRing.maximalIdeal V)}
    {vK : AddValuation (FractionRing V) (WithTop ℚ)} (hv : ValOver ϖ (FractionRing V) vK) {k : ℕ}
    {α : D.toPre.X}
    {E : LB.Sec (LB.LinComb D.toPre.P.L (Out.DegPre.famφ D.toPre (FractionRing V) α) (Out.DegPre.famε k))}
    (hE : VGe D (FractionRing V) vK k α E 0) {r : V} (hr : r ≠ 0) (f : D.toPre.SecB k α)
    (hf : Out.GeneratorPullback.SecScal D.toPre.P.L (Out.DegPre.famφ D.toPre (FractionRing V) α) (Out.DegPre.famε k) E
      (D.toPre.famφB α) (Out.DegPre.famε k) f (Out.DegPre.prB D.toPre (FractionRing V)).left
      (Out.scal (Out.DegPre.BF D.toPre (FractionRing V)).hom r)) :
    ∀ j, ∃ g : Γ(D.toPre.P.A.left, LB.wchart D.toPre.P.L (D.toPre.famφB α) j),
      f.f j = Geo.Tor.constFn D.toPre.P.A.hom _ r * g := by
  obtain ⟨n, a, σ, σF, hscal, hva, hsum⟩ := hE
  have hb : ∀ i, ∃ b : V, algebraMap V (FractionRing V) b = a i := fun i => by
    obtain ⟨b, hb⟩ := mem_range_of_val_nonneg hϖ hv (a i) (by simpa using hva i)
    exact ⟨b, hb⟩
  choose b hb using hb
  have hflat : Flat D.toPre.P.A.hom := by
    have := D.toPre.P.smoothDim
    have := SmoothOfRelativeDimension.smooth D.toPre.P.g D.toPre.P.A.hom
    infer_instance
  have hjK : IsOpenImmersion (jK V) := by
    obtain ⟨ϖ₀, h₀⟩ := IsDiscreteValuationRing.exists_irreducible V
    have := away_fractionRing h₀
    exact IsOpenImmersion.of_isLocalization ϖ₀
  have hjFK : IsIso (jFK (R := V) (FractionRing V)) := by
    show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id (FractionRing V))))
    rw [CommRingCat.ofHom_id, Spec.map_id]
    infer_instance
  have ht : IsOpenImmersion (TF (R := V) (FractionRing V)).hom := by
    show IsOpenImmersion (jFK (R := V) (FractionRing V) ≫ jK V)
    infer_instance
  have : Nonempty (TF (R := V) (FractionRing V)).left := ⟨IsLocalRing.closedPoint (FractionRing V)⟩

  have hBF : (Out.DegPre.BF D.toPre (FractionRing V)).hom =
      pullback.snd (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom ≫ D.toPre.P.A.hom := pullback.condition
  have hnat : ∀ {R S : CommRingCat.{0}} (g : R ⟶ S) (x : R),
      (Spec.map g).appTop.hom ((Scheme.ΓSpecIso R).inv.hom x) = (Scheme.ΓSpecIso S).inv.hom (g.hom x) := by
    intro R S g x
    exact (congrArg (fun q => q.hom x) (Scheme.ΓSpecIso_inv_naturality g)).symm
  have hTF : ∀ c : V, (TF (R := V) (FractionRing V)).hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom c) =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom (algebraMap V (FractionRing V) c) := by
    intro c
    show (jFK (R := V) (FractionRing V) ≫ jK V).appTop.hom _ = _
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, hnat, hnat]
    rfl

  have H : ∀ j : (LB.LinComb D.toPre.P.L (D.toPre.famφB α) (Out.DegPre.famε k)).ι,
      f.f j - constFn D.toPre.P.A.hom _ r * ∑ i, constFn D.toPre.P.A.hom _ (b i) * (σ i).f j = 0 := by
    intro j
    refine eq_zero_of_app_fst_open D.toPre.P.A.hom (TF (R := V) (FractionRing V)).hom _ _
      (app_fst_eq_zero_of_snd _ _ _ _ (snd_app_eq_zero _ _ _ _ fun y hy => ?_))
    choose J hJ using fun ψ : (Out.DegPre.BF D.toPre (FractionRing V)).left ⟶ D.toPre.P.A.left =>
      exists_chart D.toPre.P.isLB (ψ y)
    have hG : Good D.toPre.P.L y J := hJ
    set π := pullback.snd (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom
    set U := (LB.LinComb D.toPre.P.L (D.toPre.famφB α) (Out.DegPre.famε k)).U j
    obtain ⟨tj, htj⟩ : ∃ tj, (trF (L := D.toPre.P.L) (D.toPre.famφB α) (Out.DegPre.famε k) π y j
        (fun k => J (π ≫ D.toPre.famφB α k))).val = tj := ⟨_, rfl⟩
    have e_f : gs π y U (f.f j) = tj * sval f π y J :=
      (sec_trans f π y hy (hG.mem _ π)).trans (congrArg (· * sval f π y J) htj)
    have e_σ : ∀ i, gs π y U ((σ i).f j) = tj * sval (σ i) π y J := fun i =>
      (sec_trans (σ i) π y hy (hG.mem _ π)).trans (congrArg (· * sval (σ i) π y J) htj)
    have hf' : sval f (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom) ≫ π) y J = gs (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y ⊤ (Out.scal (Out.DegPre.BF D.toPre (FractionRing V)).hom r) *
        sval E (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y J := secScal_sval_c hf (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y hG
    have hσ' : ∀ i, sval (σ i) (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom) ≫ π) y J = sval (σF i) (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y J := fun i =>
      SectionScalarValuation.secScal_sval (hscal i) (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y hG
    rw [Category.id_comp] at hf'
    simp only [Category.id_comp] at hσ'
    let bg : Fin n → Γ((pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom), ⊤) := fun i =>
      (pullback.fst (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom (a i))
    have hE' : sval E (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y J = ∑ i, gs (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y ⊤ (bg i) * sval (σF i) (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y J :=
      SectionScalarValuation.sval_lin bg σF hsum (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y hG
    have c1 : gs (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y ⊤ (Out.scal (Out.DegPre.BF D.toPre (FractionRing V)).hom r) = cst (π ≫ D.toPre.P.A.hom) y r :=
      (gs_pull (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) _ y ⊤ trivial _).trans (by rw [Category.id_comp, hBF]; rfl)
    have c2 : ∀ i, gs (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y ⊤ (bg i) = cst (π ≫ D.toPre.P.A.hom) y (b i) := by
      intro i
      refine (gs_pull (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) _ y ⊤ trivial _).trans ?_
      rw [Category.id_comp, cst, ← pullback.condition, ← gs_pull _ _ y ⊤ trivial]
      exact (congrArg (fun z => gs (pullback.fst (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom) y ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom z)) (hb i).symm).trans
        (congrArg (gs (pullback.fst (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom) y ⊤) (hTF (b i)).symm)
    have e_sub : gs π y U (f.f j - constFn D.toPre.P.A.hom U r * ∑ i, constFn D.toPre.P.A.hom U (b i) * (σ i).f j) =
        gs π y U (f.f j) - gs π y U (constFn D.toPre.P.A.hom U r) *
          ∑ i, gs π y U (constFn D.toPre.P.A.hom U (b i)) * gs π y U ((σ i).f j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [gs_eq π y U hy, map_sub, map_mul, map_sum]
    rw [e_sub, e_f, hf', hE', gs_constFn _ _ _ _ hy]
    simp only [e_σ, hσ', c1, c2, gs_constFn _ _ _ _ hy]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_eq_zero fun i _ => by ring
  intro j
  exact ⟨_, sub_eq_zero.1 (H j)⟩

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor TWO TWM SectionScalarValuation IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]

theorem gs_sub {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a - b) = gs f y U a - gs f y U b := by
  simp only [gs, dif_pos h, map_sub]

def RepF {k : ℕ} {ρ : D.toPre.X} {m : ℕ}
    (bF : Fin m → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k)))
    (t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k))) (c : Fin m → F) : Prop :=
  ∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
    sval t (𝟙 _) y J = ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c i)) * sval (bF i) (𝟙 _) y J

theorem coordsO {ϖ : V} (hϖ : Irreducible ϖ) {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)
    {k : ℕ} {ρ : D.toPre.X} {m : ℕ} (b : Fin m → D.toPre.SecB k ρ)
    (hb : ∀ (R' : Type) [CommRing R'] (f : V →+* R'),
      ∀ b' : Fin m → LB.Sec (LB.LinComb D.toPre.P.L
          (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.toPre.P.A).left ≫ DegPre.famφB D.toPre ρ i)
          (DegPre.famε k)),
        (∀ i, IsPullSecLC D.toPre.P.L (DegPre.famφB D.toPre ρ) (DegPre.famε k)
          (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.toPre.P.A).left (b i) (b' i)) →
        IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom f))) (A := D.toPre.P.A) _ b')
    (bF : Fin m → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k)))
    (hbF : ∀ i (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
      sval (bF i) (𝟙 _) y J = sval (b i) (DegPre.prB D.toPre F).left y J)
    (σ : D.toPre.SecB k ρ) (σF : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k)))
    (hσF : ∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
      sval σF (𝟙 _) y J = sval σ (DegPre.prB D.toPre F).left y J) :
    ∃ c : Fin m → F, (∀ i, (0 : WithTop ℚ) ≤ v (c i)) ∧ RepF bF σF c := by
  let bO := fun i => pullSec D.toPre.P.L (DegPre.famφB D.toPre ρ) (DegPre.famε k) (b i)
    (snd (TO hϖ hv) D.toPre.P.A).left
  have hBO := hb (Ov v) (fO v hϖ hv) bO (fun i j => rfl)
  obtain ⟨r, hr, -⟩ := hBO (pullSec D.toPre.P.L (DegPre.famφB D.toPre ρ) (DegPre.famε k) σ
    (snd (TO hϖ hv) D.toPre.P.A).left)
  refine ⟨fun i => ιr (v := v) (r i), fun i => v_ιr _, fun y J hJ => ?_⟩
  have e := sval_lin (fun i => (fst (TO hϖ hv) D.toPre.P.A).left.appTop.hom (r i)) bO hr (jO hϖ hv (D := D)).left y hJ
  rw [sval_pullSec _ _ _ _ _ y hJ, jO_snd] at e
  rw [hσF y J hJ, e]
  refine Finset.sum_congr rfl fun i _ => ?_
  have g := gs_jO hϖ hv (D := D) (𝟙 _) y (r i)
  rw [Category.id_comp] at g
  rw [g, hbF i y J hJ]
  show _ * sval (pullSec _ _ _ (b i) _) _ y J = _
  rw [sval_pullSec _ _ _ _ _ y hJ, jO_snd]

theorem repF_unique {k : ℕ} {ρ : D.toPre.X} {m : ℕ}
    {bF : Fin m → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k))}
    (hU : ∀ c : Fin m → F, (∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
        ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c i)) * sval (bF i) (𝟙 _) y J = 0) → c = 0)
    {t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k))} {c c' : Fin m → F}
    (h : RepF bF t c) (h' : RepF bF t c') : c = c' := by
  have hsub : ∀ (y : (DegPre.BF D.toPre F).left) (a b : Γ((DegPre.BF D.toPre F).left, ⊤)),
      gs (𝟙 _) y ⊤ (a - b) = gs (𝟙 _) y ⊤ a - gs (𝟙 _) y ⊤ b :=
    fun y a b => gs_sub _ y ⊤ (by first | trivial | simp) a b
  have h0 := hU (c - c') (fun y J hy => by
    have e1 := h y J hy
    have e2 := h' y J hy
    simp only [Pi.sub_apply, map_sub, hsub, sub_mul, Finset.sum_sub_distrib]
    rw [← e1, ← e2, sub_self])
  exact sub_eq_zero.mp h0

end ReciprocityTheory.ChartRestriction.G.DVR.UUA
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

section Values

variable {T : Over (Spec (CommRingCat.of R))} (σ : T ⟶ TF (R := R) F) {z : T.left}
  {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J)
include hJ

theorem tau_nsmul (hB : D.TauBimult) (ρ mu nu : D.X) (k : ℕ) :
    val (D.tau (ρ + k • mu) nu) (σ.left ≫ jFK (R := R) F) z J * cubN (th D z J) k (cP D T ρ) (cP D T mu) (cP D T nu) =
      val (D.tau ρ nu) (σ.left ≫ jFK (R := R) F) z J * val (D.tau mu nu) (σ.left ≫ jFK (R := R) F) z J ^ k := by
  induction k with
  | zero => rw [zero_nsmul, add_zero]; simp [cubN]
  | succ k ih =>
    have e := tau_mul σ hJ hB (ρ + k • mu) mu nu
    rw [cPoint_add, cPoint_nsmul] at e
    rw [succ_nsmul, ← add_assoc, cubN, Finset.prod_range_succ, pow_succ]
    apply Additive.ofMul.injective
    have a1 := congrArg Additive.ofMul e
    have a2 := congrArg Additive.ofMul ih
    simp only [ofMul_mul, ofMul_pow, cubN] at a1 a2 ⊢
    linear_combination (norm := abel) a1 + a2

theorem psi_add (a b : D.X) : val (D.psi (a + b)) (σ.left ≫ jFK (R := R) F) z J =
    val (D.tau a b) (σ.left ≫ jFK (R := R) F) z J * val (D.psi a) (σ.left ≫ jFK (R := R) F) z J *
      val (D.psi b) (σ.left ≫ jFK (R := R) F) z J * val D.rigK (σ.left ≫ jFK (R := R) F) z J := by
  have e : val (D.tau a b) (σ.left ≫ jFK (R := R) F) z J =
      val (D.psi (a + b)) (σ.left ≫ jFK (R := R) F) z J * (val (D.psi a) (σ.left ≫ jFK (R := R) F) z J)⁻¹ *
        (val (D.psi b) (σ.left ≫ jFK (R := R) F) z J)⁻¹ * (val D.rigK (σ.left ≫ jFK (R := R) F) z J)⁻¹ :=
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  rw [e]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Values

theorem val_powGen' {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    val (GeneratorPullback.powGen L φ ε t n) r z J = val t r z J ^ n :=
  map_pow _ _ _

theorem fe_cocycle (hB : D.TauBimult) {T : Over (Spec (CommRingCat.of R))} (ρ' : T ⟶ DegPre.BF D F) {z : T.left}
    {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (k : ℕ) (ρ mu nu : D.X) :
    (uVal D F k ρ (cP D _ mu) (ρ' ≫ DegPre.trF D F nu) z J *
        val (DegPre.famMult D F k mu ρ) (ρ' ≫ fst _ _).left z J) *
      (uVal D F k (ρ + k • mu) (cP D _ nu) ρ' z J * val (DegPre.famMult D F k nu (ρ + k • mu)) (ρ' ≫ fst _ _).left z J) =
    uVal D F k ρ (cP D _ (mu + nu)) ρ' z J * val (DegPre.famMult D F k (mu + nu) ρ) (ρ' ≫ fst _ _).left z J := by
  have C : IsCub (th D z J) := isCub_cubV D.cub hJ
  have hf : (ρ' ≫ DegPre.trF D F nu) ≫ fst (TF (R := R) F) D.P.A = ρ' ≫ fst _ _ := by
    rw [Category.assoc, trF_eq, tr_fst]
  have hp : (ρ' ≫ DegPre.trF D F nu) ≫ DegPre.prB D F = (ρ' ≫ DegPre.prB D F) * cP D T nu := by
    rw [Category.assoc, trF_eq, tr_pr, MonObj.comp_mul, ← Category.assoc, comp_cP]
  have hc : ∀ χ, ρ' ≫ fst (TF (R := R) F) D.P.A ≫ cP D _ χ = cP D T χ := fun χ => by
    rw [← Category.assoc, comp_cP]
  have u1 : uVal D F k ρ (cP D _ mu) (ρ' ≫ DegPre.trF D F nu) z J =
      hv (th D z J) k (cP D T ρ) (cP D T mu) ((ρ' ≫ DegPre.prB D F) * cP D T nu) := by
    rw [uVal, hp, ← Category.assoc (ρ' ≫ DegPre.trF D F nu), hf, Category.assoc, hc]; rfl
  have u2 : uVal D F k (ρ + k • mu) (cP D _ nu) ρ' z J =
      hv (th D z J) k (cP D T ρ * cP D T mu ^ k) (cP D T nu) (ρ' ≫ DegPre.prB D F) := by
    rw [uVal, hc, cPoint_add, cPoint_nsmul]; rfl
  have u3 : uVal D F k ρ (cP D _ (mu + nu)) ρ' z J =
      hv (th D z J) k (cP D T ρ) (cP D T mu * cP D T nu) (ρ' ≫ DegPre.prB D F) := by
    rw [uVal, hc, cPoint_add]; rfl
  have hvc := hv_comp C k (cP D T ρ) (cP D T mu) (cP D T nu) (ρ' ≫ DegPre.prB D F)
  have σσ := ρ' ≫ fst (TF (R := R) F) D.P.A
  have fM : ∀ ν α, val (DegPre.famMult D F k ν α) (ρ' ≫ fst _ _).left z J =
      val (D.tau ν α) ((ρ' ≫ fst _ _).left ≫ jFK (R := R) F) z J *
        (val (D.psi ν) ((ρ' ≫ fst _ _).left ≫ jFK (R := R) F) z J ^ k *
          val D.rigK ((ρ' ≫ fst _ _).left ≫ jFK (R := R) F) z J ^ k) := fun ν α => by
    rw [val_famMult (ρ' ≫ fst _ _) hJ k ν α, val_powGen', val_powGen']
  have t1 := tau_mul (ρ' ≫ fst _ _) hJ hB mu nu ρ
  have t2 := tau_nsmul (ρ' ≫ fst _ _) hJ hB ρ mu nu k
  have t3 := tau_symm (ρ' ≫ fst _ _) hJ nu (ρ + k • mu)
  have t4 := tau_symm (ρ' ≫ fst _ _) hJ ρ nu
  have p1 := psi_add (ρ' ≫ fst _ _) hJ mu nu
  have sy : th D z J (cP D T ρ) (cP D T nu) (cP D T mu) = th D z J (cP D T mu) (cP D T nu) (cP D T ρ) := by
    rw [C.s01, C.s12, C.s01]
  have h8 : hv (th D z J) k (cP D T ρ) (cP D T mu) (cP D T nu) =
      cubN (th D z J) k (cP D T ρ) (cP D T mu) (cP D T nu) * (th D z J (cP D T ρ) (cP D T nu) (cP D T mu))⁻¹ := rfl
  rw [u1, u2, u3, fM, fM, fM]
  apply Additive.ofMul.injective
  have a1 := congrArg Additive.ofMul hvc
  have a2 := congrArg (fun q => (k : ℕ) • Additive.ofMul q) p1
  have a3 := congrArg Additive.ofMul t1
  have a4 := congrArg Additive.ofMul t2
  have a5 := congrArg Additive.ofMul t3
  have a6 := congrArg Additive.ofMul t4
  have a7 := congrArg Additive.ofMul sy
  have a8 := congrArg Additive.ofMul h8
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, smul_add] at a1 a2 a3 a4 a5 a6 a7 a8 ⊢
  linear_combination (norm := abel) a1 - a2 - a3 + a4 + a5 + a6 - a7 + a8

end ReciprocityTheory.ChartRestriction.G.DVR.UUA
end
end
