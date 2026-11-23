module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle007
public import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IsMixedOver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section



noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

section Calc

variable {X Y Z : Scheme.{0}}

theorem sval_zCast {S : Scheme.{0}} (A : Over S) {L : LB A.left} {T : Over S} {k₁ k₂ : ℤ} (h : k₁ = k₂)
    (F : LB.Sec (LPow A L k₁ T)) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) :
    sval (zCast A h F) r z J = sval F r z J := by
  subst h
  rfl

def pull1 (L : LB X) (h : Y ⟶ X) (s : LB.Sec L) : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => h) (fun _ => 1)) :=
  thfPull1 L (F := 𝟙 X) h (Category.comp_id h) (thfPull L (𝟙 X) s)

theorem gs_pull1 (L : LB X) (h : Y ⟶ X) (s : LB.Sec L) (r : Z ⟶ Y) (z : Z) (j : Fin 1 → L.ι)
    (hz : r z ∈ LB.wchart L (fun _ : Fin 1 => h) j) :
    gs r z _ ((pull1 L h s).f j) = gs (r ≫ h) z (L.U (j 0)) (s.f (j 0)) := by
  simp only [pull1, thfPull1, thfPull]
  refine Eq.trans (gs_appLE h _ _ _ r z ?_ _) ?_
  · exact hz
  refine Eq.trans (gs_appLE (𝟙 X) _ _ _ (r ≫ h) z ?_ _) ?_
  · exact chart_le_pullback_open L h (Category.comp_id h) j hz
  rw [Category.comp_id]

def secOne (L : LB X) (s : LB.Sec L) : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)) :=
  pull1 L (𝟙 X) s

theorem plain_le (L : LB X) (i : L.ι) : L.U i ≤ (𝟙 X) ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) := by
  intro y hy
  exact Set.mem_iInter.mpr fun _ => hy

def plainOf (L : LB X) (σ : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1))) : LB.Sec L where
  f i := (Scheme.Hom.appLE (𝟙 X) _ _ (plain_le L i)).hom (σ.f (fun _ => i))
  compat i j := fn_ext fun y hy => by
    have m₁ : (𝟙 X ≫ 𝟙 X) y ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) := plain_le L i hy.1
    have m₂ : (𝟙 X ≫ 𝟙 X) y ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j) := plain_le L j hy.2
    have g : gm (𝟙 X ≫ 𝟙 X) y _ ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)).g (fun _ => i) (fun _ => j)) =
        gm (𝟙 X) y (L.U i ⊓ L.U j) (L.g i j) :=
      (gm_linComb L _ _ (𝟙 X ≫ 𝟙 X) y _ _ m₁ m₂).trans (by simp only [Fin.prod_univ_one, zpow_one, Category.comp_id])
    refine (gs_res _ y _ hy _).trans ((gs_appLE (𝟙 X) _ _ _ (𝟙 _) y hy.1 _).trans ((gs_compat σ (𝟙 X ≫ 𝟙 X) y m₁ m₂).trans
      (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans (congrArg Units.val g.symm))
        ((gs_res _ y _ hy _).trans (gs_appLE (𝟙 X) _ _ _ (𝟙 _) y hy.2 _)))))))

theorem gs_plainOf (L : LB X) (σ : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1))) (y : X) (i : L.ι)
    (hy : y ∈ L.U i) :
    gs (𝟙 X) y (L.U i) ((plainOf L σ).f i) =
      gs (𝟙 X) y (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i)) (σ.f (fun _ => i)) := by
  simp only [plainOf]
  refine Eq.trans (gs_appLE (𝟙 X) _ _ _ (𝟙 X) y ?_ _) ?_
  · exact hy
  rw [Category.comp_id]

theorem gs_resTop (r : Z ⟶ X) (z : Z) {U : X.Opens} (hz : r z ∈ U) (a : Γ(X, ⊤)) :
    gs r z U (resG X (le_top : U ≤ ⊤) a) = gs r z ⊤ a := by
  exact gs_res r z le_top hz a

theorem secOne_gen {S : Type} [CommRing S] (G : Over (Sp S)) (L : LB G.left) (θ : LB.Sec L)
    (hθ : ∀ σ : LB.Sec L, ∃! a : S, ∀ i, σ.f i = resG G.left le_top ((G.hom).appTop.hom (toΓ S a)) * θ.f i) :
    ∀ σ : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ))),
      ∃! a : S, ∀ i, σ.f i = resG G.left le_top ((G.hom).appTop.hom (toΓ S a)) * (secOne L θ).f i := by
  show ∀ σ : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 1)),
    ∃! a : S, ∀ i, σ.f i = resG G.left le_top ((G.hom).appTop.hom (toΓ S a)) * (secOne L θ).f i
  have e3 : ∀ (i : L.ι) (y : G.left)
      (hy : y ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 1)).U (fun _ => i)),
      gs (𝟙 G.left) y _ ((secOne L θ).f (fun _ => i)) = gs (𝟙 G.left) y (L.U i) (θ.f i) := by
    intro i y hy
    refine (gs_pull1 L (𝟙 _) θ (𝟙 _) y (fun _ => i) hy).trans ?_
    rw [Category.comp_id]
  intro σ
  obtain ⟨a, ha, huniq⟩ := hθ (plainOf L σ)
  refine ⟨a, ?_, fun b hb => huniq b ?_⟩
  · rintro (j : Fin 1 → L.ι)
    obtain ⟨i, rfl⟩ : ∃ i : L.ι, j = fun _ => i := ⟨j 0, funext fun k => by rw [Subsingleton.elim k 0]⟩
    refine fn_ext fun y hy => ?_
    have hyi : y ∈ L.U i := LB.wchart_le L _ (fun _ : Fin 1 => i) 0 hy
    rw [gs_mul _ y _ hy, gs_resTop _ y hy, e3 i y hy]
    refine (gs_plainOf L σ y i hyi).symm.trans ?_
    rw [ha i, gs_mul _ y _ hyi, gs_resTop _ y hyi]
  · intro i
    refine fn_ext fun y hyi => ?_
    have hy : y ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 1)).U (fun _ => i) := plain_le L i hyi
    rw [gs_mul _ y _ hyi, gs_resTop _ y hyi]
    refine (gs_plainOf L σ y i hyi).trans ?_
    show gs (𝟙 G.left) y ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 1)).U (fun _ => i))
      (σ.f (fun _ => i)) = _
    rw [hb (fun _ => i), gs_mul _ y _ hy, gs_resTop _ y hy, e3 i y hy]

theorem gs_isoMaps {L M : LB X} {w : LB.Iso L M} {s : LB.Sec L} {s' : LB.Sec M} (h : IsoMaps w s s') (r : Z ⟶ X)
    (z : Z) (i : M.ι) (k : L.ι) (hi : r z ∈ M.U i) (hk : r z ∈ L.U k) :
    gs r z (M.U i) (s'.f i) = (gv w r z i k).val * gs r z (L.U k) (s.f k) := by
  unfold Formalism.L2.Pj.IsoMaps at h
  have hV : r z ∈ M.U i ⊓ L.U k := ⟨hi, hk⟩
  have h' := congrArg (gs r z (M.U i ⊓ L.U k)) (h i k)
  rw [gs_res r z _ hV, gs_mul _ z _ hV, gs_res r z _ hV] at h'
  rw [h']
  congr 1
  exact gs_unit _ z _ hV _

end Calc

theorem thetaTie : ThetaTieSt := by
  intro E _ _ _ H Dw l Xo c Tc io y I
  let _ := io.toAlgebra
  let A := Xo.univ.t.G
  let θK : LB.Sec (LPow I.t'.G I.t'.PP.L ((1 : ℕ) : ℤ) (𝟙_ (Over (Sp Tc.Fr)))) :=
    pull1 I.t'.PP.L (snd (𝟙_ (Over (Sp Tc.Fr))) I.t'.G).left I.σ
  have gθK : ∀ (Z : Scheme.{0}) (zp : Z ⟶ (𝟙_ (Over (Sp Tc.Fr)) ⊗ I.t'.G).left) (z : Z)
      (J' : (Z ⟶ I.t'.G.left) → I.t'.PP.L.ι), Good I.t'.PP.L z J' →
      sval θK zp z J' = gs (zp ≫ (snd (𝟙_ (Over (Sp Tc.Fr))) I.t'.G).left) z
        (I.t'.PP.L.U (J' (zp ≫ (snd (𝟙_ (Over (Sp Tc.Fr))) I.t'.G).left)))
        (I.σ.f (J' (zp ≫ (snd (𝟙_ (Over (Sp Tc.Fr))) I.t'.G).left))) :=
    fun Z zp z J' hJ' => gs_pull1 I.t'.PP.L _ I.σ zp z _ (hJ'.mem _ zp)
  refine ⟨secOne I.G.PP.L I.θ, secOne_gen I.G.G I.G.PP.L I.θ I.θgen, θK, ?_, ?_⟩
  · intro Z r zp zp' h1 h2 h3 z J J' hJ hJ'
    let a0 : Over.mk (I.t'.G.hom ≫ y.x) ⟶ Over.mk y.x := Over.homMk I.t'.G.hom rfl
    let b0 : Over.mk (I.t'.G.hom ≫ y.x) ⟶ A := Over.homMk I.m1.φ I.m1.cart.1.w
    let g0 : I.t'.G.left ⟶ Gx y.x := (lift a0 b0).left
    have g0f : g0 ≫ (fst (Over.mk y.x) A).left = I.t'.G.hom := congrArg (fun q => q.left) (lift_fst a0 b0)
    have g0s : g0 ≫ (snd (Over.mk y.x) A).left = I.m1.φ := congrArg (fun q => q.left) (lift_snd a0 b0)
    have hzp : zp = r ≫ g0 := by
      apply pullback.hom_ext
      · show zp ≫ (fst (Over.mk y.x) A).left = (r ≫ g0) ≫ (fst (Over.mk y.x) A).left
        rw [Category.assoc, g0f, h2]
      · show zp ≫ (snd (Over.mk y.x) A).left = (r ≫ g0) ≫ (snd (Over.mk y.x) A).left
        rw [Category.assoc, g0s, h1]
    subst hzp
    have hj : ∀ j : PUnit → Xo.univ.t.PP.L.ι,
        (Xo.univ.t.PP.L.pull I.m1.φ).U j ≤ g0 ⁻¹ᵁ (PPx y.x).U (fun _ => j PUnit.unit) := fun j y' hy' =>
      Set.mem_iInter.2 fun _ => (congrArg (fun q => q y' ∈ Xo.univ.t.PP.L.U (j PUnit.unit)) g0s).mpr (mem_pull.1 hy')
    have mJ : r z ∈ (Xo.univ.t.PP.L.pull I.m1.φ).U (fun _ => J (r ≫ I.m1.φ)) := mem_pull.2 (hJ (r ≫ I.m1.φ))
    have mK : r z ∈ I.t'.PP.L.U (J' (r ≫ 𝟙 _)) := by simpa using hJ' (r ≫ 𝟙 _)
    have e1 : sval (zCast A Nat.cast_one.symm y.s) (r ≫ g0) z J =
        gs (r ≫ g0) z _ (y.s.f (fun _ => J (r ≫ I.m1.φ))) := by
      rw [sval_zCast]
      exact sval_of (L := Xo.univ.t.PP.L) (φ := fun _ : Fin 1 => (snd (Over.mk y.x) A).left) (ε := fun _ => 1) y.s
        (r ≫ g0) z J (fun _ => J (r ≫ I.m1.φ)) (fun _ => by rw [Category.assoc, g0s])
    have e2 : gs (r ≫ g0) z _ (y.s.f (fun _ => J (r ≫ I.m1.φ))) =
        gs r z _ (I.s1.f (fun _ => J (r ≫ I.m1.φ))) := by
      rw [I.gen1 g0 g0s g0f _ (hj _)]
      erw [gs_appLE g0 _ _ (hj _) r z mJ]
    erw [e1, e2, gs_isoMaps I.maps1 r z _ _ mJ mK, gθK Z zp' z J' hJ', h3, pow_one, Category.comp_id]
  · intro Z r zp h3 z J J' hJ hJ'
    have mJ : r z ∈ (I.G.PP.L.pull I.m2.φ).U (fun _ => J (r ≫ I.m2.φ)) := mem_pull.2 (hJ (r ≫ I.m2.φ))
    have mK : r z ∈ I.t'.PP.L.U (J' (r ≫ 𝟙 _)) := by simpa using hJ' (r ≫ 𝟙 _)
    have hpl : (I.G.PP.L.pull I.m2.φ).U (fun _ => J (r ≫ I.m2.φ)) ≤ I.m2.φ ⁻¹ᵁ I.G.PP.L.U (J (r ≫ I.m2.φ)) :=
      fun _ hy' => mem_pull.1 hy'
    have e1 : sval (secOne I.G.PP.L I.θ) (r ≫ I.m2.φ) z J =
        gs (r ≫ I.m2.φ) z (I.G.PP.L.U (J (r ≫ I.m2.φ))) (I.θ.f (J (r ≫ I.m2.φ))) := by
      erw [sval_of _ _ z J (fun _ => J (r ≫ I.m2.φ)) (fun _ => by rw [Category.comp_id])]
      rw [secOne]
      erw [gs_pull1 _ _ _ _ z _ (plain_le _ _ (hJ (r ≫ I.m2.φ)))]
      rw [Category.comp_id]
    have e2 : gs (r ≫ I.m2.φ) z (I.G.PP.L.U (J (r ≫ I.m2.φ))) (I.θ.f (J (r ≫ I.m2.φ))) =
        gs r z _ (I.θ2.f (fun _ => J (r ≫ I.m2.φ))) := by
      rw [I.pull _ hpl]
      erw [gs_appLE I.m2.φ _ _ hpl r z mJ]
    erw [e1, e2, gs_isoMaps I.maps2 r z _ _ mJ mK, gθK Z zp z J' hJ', h3, pow_one, Category.comp_id]

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section

set_option autoImplicit false


noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V]

def iotaK {t : SAB H (Sp V)} {tK : SAB H (Sp (FractionRing V))} (m : SABMap tK t (Out.jK V)) :
    tK.G.left ⟶ pullback t.G.hom (Out.jK V) :=
  pullback.lift m.φ tK.G.hom m.cart.1.w

def secU {t : SAB H (Sp V)} (P : PELUnif (IsLocalRing.maximalIdeal V) t) {k : ℕ} (s : P.U.SecK k) :
    LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => pullback.fst t.G.hom (Out.jK V)) (fun _ => (k : ℤ))) :=
  P.bundle ▸ s

def SecTieGK {t : SAB H (Sp V)} {tK : SAB H (Sp (FractionRing V))} (m : SABMap tK t (Out.jK V))
    (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)) (P : PELUnif (IsLocalRing.maximalIdeal V) t) (k : ℕ)
    (F : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp (FractionRing V)))))) (s : P.U.SecK k) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ tK.G.left) (zp : Z ⟶ (𝟙_ (Over (Sp (FractionRing V))) ⊗ tK.G).left),
    zp ≫ (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left = r →
    ∀ (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι) (J' : (Z ⟶ tK.G.left) → tK.PP.L.ι),
      Good t.PP.L z J → Good tK.PP.L z J' →
      sval (secU P s) (r ≫ iotaK m) z J = ((gv w r z (fun _ => J (r ≫ m.φ)) (J' (r ≫ 𝟙 _))).val) ^ k * sval F zp z J'

def NuK {t : SAB H (Sp V)} (P : PELUnif (IsLocalRing.maximalIdeal V) t)
    (Q : P.D.toPre.X → ℤ) (vK : AddValuation (FractionRing V) (WithTop ℚ)) {tK : SAB H (Sp (FractionRing V))}
    (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)) (k : ℕ)
    (F : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp (FractionRing V)))))) : Prop :=
  ∃ (s : P.U.SecK k) (Ex : Fam P.D.toPre (FractionRing V) k),
    SecTieGK m w P k F s ∧ P.U.Expands k s Ex ∧ NuGe P.D Q (FractionRing V) vK k Ex 0

end Defs

def NuDataSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t),
    ∃ (ϖ : V) (Q : P.D.toPre.X → ℤ) (vK : AddValuation (FractionRing V) (WithTop ℚ)),
      Irreducible ϖ ∧ QForm.IsQ P.D.toPre ϖ Q ∧ ValOver ϖ (FractionRing V) vK

def ThetaNuSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t), P.TorsionIso →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (tK : SAB H (Sp (FractionRing V))) (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)),
      RigIso m w →
    ∀ (θ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => ((1 : ℕ) : ℤ))))
      (θK : LB.Sec (LPow tK.G tK.PP.L ((1 : ℕ) : ℤ) (𝟙_ (Over (Sp (FractionRing V)))))), SecTieK m w 1 θK θ → NuK P Q vK m w 1 θK

def MulNuSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t), P.TorsionIso →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (tK : SAB H (Sp (FractionRing V))) (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)),
      RigIso m w →
    ∀ (N : ℕ), 1 ≤ N → ∀ (s : LB.Sec (LPow tK.G tK.PP.L 1 (𝟙_ (Over (Sp (FractionRing V))))))
      (α₀ : LB.Gen (LB.LinComb tK.PP.L (K := Fin 2) ![𝟙 tK.G.left, (mulA tK.G N).left] ![(N : ℤ) ^ 2, -1]))
      (α : LB.Gen (LB.LinComb tK.PP.L (K := Fin 2)
        ![(snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left, (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G ^ N).left] ![(N : ℤ) ^ 2, -1]))
      (s₁ : LB.Sec (LPow tK.G tK.PP.L ((N : ℤ) ^ 2) (𝟙_ (Over (Sp (FractionRing V)))))),
      NuK P Q vK m w 1 (zCast tK.G Nat.cast_one.symm s) → α₀.IsGen → IsNormMul tK.G tK.PP.L tK.PP.rig N α₀ →
      LB.Gen.Corr tK.PP.L _ _ _ _ α (LB.pullGen tK.PP.L _ _ α₀ (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left) →
      IsTwistPull tK.G tK.PP.L (mulT tK.G (𝟙_ (Over (Sp (FractionRing V)))) N) (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α s s₁ →
      NuK P Q vK m w (N ^ 2) (zCast tK.G (natCast_sq N) s₁)

def EndNuSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t), P.TorsionIso →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (tK : SAB H (Sp (FractionRing V))) (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)),
      RigIso m w →
    ∀ (π : 𝓞 E) (n k : ℕ), 0 < k → ∀ (F₁ : LB.Sec (LPow tK.G tK.PP.L ((n : ℤ) ^ 2) (𝟙_ (Over (Sp (FractionRing V))))))
      (α₀ : LB.Gen (LB.LinComb tK.PP.L (K := Fin 2) ![𝟙 tK.G.left, (tK.act.act π).left] ![(k : ℤ), -((n : ℤ) ^ 2)]))
      (α : LB.Gen (LB.LinComb tK.PP.L (K := Fin 2)
        ![(snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left, (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G ≫ tK.act.act π).left] ![(k : ℤ), -((n : ℤ) ^ 2)]))
      (h₁ : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp (FractionRing V)))))),
      NuK P Q vK m w (n ^ 2) (zCast tK.G (natCast_sq n) F₁) → α₀.IsGen →
      IsNormEnd tK.G tK.PP (tK.act.act π) (k : ℤ) ((n : ℤ) ^ 2) α₀ →
      LB.Gen.Corr tK.PP.L _ _ _ _ α (LB.pullGen tK.PP.L _ _ α₀ (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left) →
      IsTwistPull tK.G tK.PP.L (endT tK.G (𝟙_ (Over (Sp (FractionRing V)))) (tK.act.act π)) (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G ≫ tK.act.act π)
        (lift_snd _ _) (k : ℤ) ((n : ℤ) ^ 2) α F₁ h₁ →
      NuK P Q vK m w k h₁

def FinNuSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t), P.TorsionIso →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (tK : SAB H (Sp (FractionRing V))) (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)),
      RigIso m w →
    ∀ (a : ℤ) (k : ℕ) (ha : a = k), 0 < k → ∀ (h hh : LB.Sec (LPow tK.G tK.PP.L a (𝟙_ (Over (Sp (FractionRing V))))))
      (b : (𝟙_ (Over (Sp (FractionRing V)))) ⟶ tK.G) (U : ThetaGrp tK.G tK.PP.L a (𝟙_ (Over (Sp (FractionRing V))))),
      NuK P Q vK m w k (zCast tK.G ha h) → b ^ k = 1 → SymLift tK.G tK.PP.L a k b U → IsActOf tK.G tK.PP.L a U h hh →
      NuK P Q vK m w k (zCast tK.G ha hh)

def NuRegSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t), P.TorsionIso →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (tK : SAB H (Sp (FractionRing V))) (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)),
      RigIso m w →
    ∀ (k : ℕ), 0 < k → ∀ F : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp (FractionRing V))))), NuK P Q vK m w k F →
      ∃ σ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => (k : ℤ))), SecTieK m w k F σ

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end
