module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwistCheck

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix

variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}

theorem cc_log (G : FGLaw S d) (i : Fin d) : constantCoeff (logOf G i) = 0 := constantCoeff_prim _

theorem additive_eq (G : FGLaw S d) (g : PS S 1 d)
    (hg : ev (n := 2) ![G.F] g = ev (n := 2) ![pt S d 0] g + ev (n := 2) ![pt S d 1] g) :
    g = ∑ j, C (constantCoeff (pderiv (R := S) ((0 : Fin 1), j) g)) * logOf G j := by
  have hx : ∀ h : PS S 1 d, ev (n := 1) ![pt S d 0, 0] (ev (n := 2) ![G.F] h) = h := by
    intro h
    rw [ev_ev cz1 (czFF G)]
    have : (fun j i => ev (n := 1) ![pt S d 0, 0] ((![G.F] : Fin 1 → Pt S 2 d) j i)) = fun j => pt S (n := 1) d j := by
      funext j i
      fin_cases j
      show ev (n := 1) ![pt S d 0, 0] (G.F i) = X ((0 : Fin 1), i)
      rw [← G.unit i]
      conv_lhs => rw [← G.comm i, ev_ev cz1 czSw]
      congr 1
      funext j c
      fin_cases j <;> simp [pt_apply, LogPf.ev_X cz1]
    rw [this, ev_pt]
  have h1 : ∀ b, ∑ e, pderiv (R := S) ((0 : Fin 1), e) g * Jac G e b = C (constantCoeff (pderiv (R := S) ((0 : Fin 1), b) g)) := by
    intro b
    have d_evF : pderiv (R := S) ((1 : Fin 2), b) (ev (n := 2) ![G.F] g) =
        ∑ c, ev (n := 2) ![G.F] (pderiv (R := S) ((0 : Fin 1), c) g) *
          pderiv (R := S) ((1 : Fin 2), b) (G.F c) := by
      rw [pderiv_ev (czFF G), Fintype.sum_prod_type]
      simp
    have := congrArg (fun f => ev (n := 1) ![pt S d 0, 0] (pderiv (R := S) ((1 : Fin 2), b) f)) hg
    simp only [map_add (f := _), d_evF, pderiv_second_ev_first_point_eq_zero, d_evY, zero_add, ez_y, LogPf.ev_sum cz1, LogPf.ev_mul cz1, hx, Jac] at this
    exact this
  have h2 : ∀ a, pderiv (R := S) ((0 : Fin 1), a) g =
      ∑ b, C (constantCoeff (pderiv (R := S) ((0 : Fin 1), b) g)) * Om G b a := by
    intro a
    have e1 : pderiv (R := S) ((0 : Fin 1), a) g = ∑ e, pderiv (R := S) ((0 : Fin 1), e) g * (JM G * Om G) e a := by
      rw [mul_om]; simp [Matrix.one_apply]
    rw [e1]
    simp only [Matrix.mul_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← h1 b, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [JM, Matrix.of_apply]; ring
  have h0 : constantCoeff g = 0 := by
    have := congrArg constantCoeff hg
    rw [map_add (f := _), cc_ev (czFF G), cc_ev czX, cc_ev czY] at this
    simpa using this
  rw [← sub_eq_zero]
  have hd : ∀ v, pderiv (R := S) v (g - ∑ j, C (constantCoeff (pderiv (R := S) ((0 : Fin 1), j) g)) * logOf G j) = 0 := by
    rintro ⟨j, c⟩
    obtain rfl : j = 0 := Subsingleton.elim _ _

    rw [map_sub, map_sum, h2 c, sub_eq_zero]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← smul_eq_C_mul, ← smul_eq_C_mul, Derivation.map_smul, pderiv_logOf]
  rw [eq_C_of_pderiv_zero hd]
  simp [h0, cc_log]

theorem cc_pderiv (f : PS S 1 d) (j : Fin d) :
    constantCoeff (pderiv (R := S) ((0 : Fin 1), j) f) = coeff (Finsupp.single ((0 : Fin 1), j) 1) f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add]; simp

theorem log_act {O : Type} [CommRing O] (G : FGLaw S d) (A : OAct O G) (a : O) (i : Fin d) :
    ev (n := 1) ![A.act a] (logOf G i) = ∑ j, C (dLin (A.act a) i j) * logOf G j := by
  have hA : CZ (![A.act a] : Fin 1 → Pt S 1 d) := CZ.cons (A.const a) CZ.nil
  have hc : ∀ l : Fin 2, ∀ c, constantCoeff (comp1 (A.act a) (pt S (n := 2) d l) c) = 0 := fun l c => by
    rw [comp1, cc_ev (CZ.cons (cc_pt l) CZ.nil)]; exact A.const a c
  have hP : CZ (![comp1 (A.act a) (pt S (n := 2) d 0), comp1 (A.act a) (pt S d 1)] : Fin 2 → Pt S 2 d) :=
    CZ.cons (hc 0) (CZ.cons (hc 1) CZ.nil)
  have hadd : ev (n := 2) ![G.F] (ev (n := 1) ![A.act a] (logOf G i)) =
      ev (n := 2) ![pt S d 0] (ev (n := 1) ![A.act a] (logOf G i)) +
        ev (n := 2) ![pt S d 1] (ev (n := 1) ![A.act a] (logOf G i)) := by
    have h := congrArg (ev (n := 2) ![comp1 (A.act a) (pt S (n := 2) d 0), comp1 (A.act a) (pt S d 1)]) (logOf_add G i)
    rw [ev_add hP, ev_ev hP (czFF G), ev_ev hP czX, ev_ev hP czY] at h
    rw [ev_ev (czFF G) hA, ev_ev czX hA, ev_ev czY hA]
    convert h using 2
    · funext j c
      fin_cases j
      have := congrFun (A.hom a) c
      simp only [comp1] at this
      rw [addPt] at this
      exact this
    · congr 1; funext j c; fin_cases j; simp [pt_apply, LogPf.ev_X hP, comp1]
    · congr 1; funext j c; fin_cases j; simp [pt_apply, LogPf.ev_X hP, comp1]
  rw [additive_eq G _ hadd]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2

  rw [pderiv_ev hA, Fintype.sum_prod_type, Fin.sum_univ_one, map_sum]
  have hO : ∀ c, constantCoeff (Om G i c) = if i = c then 1 else 0 := fun c => by
    have := congrFun (congrFun (cc_om G) i) c
    simpa [Matrix.one_apply] using this
  simp only [map_mul, cc_ev hA, pderiv_logOf, hO, cc_pderiv]
  simp [dLin]

theorem ev_bilL {n : ℕ} (G : FGLaw S d) (cc : Fin d → Fin d → S) {a : Fin 2 → Pt S n d} (ha : CZ a) :
    ev a (bilL G cc) = ∑ i, ∑ l, C (cc i l) * (ev ![a 0] (logOf G i) * ev ![a 1] (logOf G l)) := by
  simp only [bilL, LogPf.ev_sum ha, smul_eq_C_mul, LogPf.ev_mul ha, LogPf.ev_C ha, lg, ev_ev ha czX, ev_ev ha czY]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  congr 3 <;> funext j c <;> fin_cases j <;> simp [pt_apply, LogPf.ev_X ha]

theorem log_act_at {O : Type} [CommRing O] (G : FGLaw S d) (A : OAct O G) (a : O) (l : Fin 2) (i : Fin d) :
    ev (n := 2) ![comp1 (A.act a) (pt S d l)] (logOf G i) = ∑ j, C (dLin (A.act a) i j) * lg G l j := by
  have hA : CZ (![A.act a] : Fin 1 → Pt S 1 d) := CZ.cons (A.const a) CZ.nil
  have hl : CZ (![pt S (n := 2) d l] : Fin 1 → Pt S 2 d) := CZ.cons (cc_pt l) CZ.nil
  have h := congrArg (ev (n := 2) ![pt S d l]) (log_act G A a i)
  rw [ev_ev hl hA] at h
  simp only [LogPf.ev_sum hl, LogPf.ev_mul hl, LogPf.ev_C hl] at h
  convert h using 2
  · funext j c; fin_cases j; rfl
  · rfl

theorem bilL_act_left {O : Type} [CommRing O] (G : FGLaw S d) (A : OAct O G) (a : O) (cc : Fin d → Fin d → S) :
    ev (n := 2) ![comp1 (A.act a) (pt S d 0), pt S d 1] (bilL G cc) =
      bilL G ((dLin (A.act a)).transpose * Matrix.of cc) := by
  have hP : CZ (![comp1 (A.act a) (pt S (n := 2) d 0), pt S d 1] : Fin 2 → Pt S 2 d) :=
    CZ.cons (fun c => by rw [comp1, cc_ev czX]; exact A.const a c) czY
  rw [ev_bilL G cc hP]

  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, log_act_at, bilL, Matrix.mul_apply, Matrix.transpose_apply,
  Matrix.of_apply, smul_eq_C_mul, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [lg]; ring

theorem bilL_act_right {O : Type} [CommRing O] (G : FGLaw S d) (A : OAct O G) (b : O) (cc : Fin d → Fin d → S) :
    ev (n := 2) ![pt S d 0, comp1 (A.act b) (pt S d 1)] (bilL G cc) =
      bilL G (Matrix.of cc * dLin (A.act b)) := by
  have hP : CZ (![pt S (n := 2) d 0, comp1 (A.act b) (pt S d 1)] : Fin 2 → Pt S 2 d) :=
    CZ.cons (cc_pt 0) (CZ.cons (fun c => by rw [comp1, cc_ev czY]; exact A.const b c) CZ.nil)
  rw [ev_bilL G cc hP]

  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, log_act_at, bilL, Matrix.mul_apply,
  Matrix.of_apply, smul_eq_C_mul, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [lg]; ring

theorem bilL_mixed (G : FGLaw S d) (cc : Fin d → Fin d → S) (i l : Fin d) :
    constantCoeff (pderiv (R := S) ((0 : Fin 2), i) (pderiv (R := S) ((1 : Fin 2), l) (bilL G cc))) = cc i l := by
  have hO : ∀ a c, constantCoeff (Om G a c) = if a = c then 1 else 0 := fun a c => by
    have := congrFun (congrFun (cc_om G) a) c
    simpa [Matrix.one_apply] using this

  simp only [bilL, lg, map_sum, Derivation.map_smul, Derivation.leibniz, smul_eq_mul, d_evX, d_evY, pderiv_second_ev_first_point_eq_zero, pderiv_first_ev_second_point_eq_zero,
  pderiv_logOf, mul_zero, add_zero, zero_add, map_add, map_mul, constantCoeff_smul, cc_ev czX, cc_ev czY, hO]
  simp

theorem bilL_injective (G : FGLaw S d) : Function.Injective (bilL G) := fun c c' h => by
  funext i l
  rw [← bilL_mixed G c, h, bilL_mixed]

theorem balanced_iff {O : Type} [CommRing O] (G : FGLaw S d) (A : OAct O G) (a b : O) (cc : Fin d → Fin d → S) :
    (dLin (A.act a)).transpose * Matrix.of cc = Matrix.of cc * dLin (A.act b) ↔
      ev (n := 2) ![comp1 (A.act a) (pt S d 0), pt S d 1] (bilL G cc) =
        ev (n := 2) ![pt S d 0, comp1 (A.act b) (pt S d 1)] (bilL G cc) := by
  rw [bilL_act_left, bilL_act_right]
  exact ⟨fun h => by rw [h], fun h => bilL_injective G h⟩

end GlobalTheory.TwistCheck
end
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FieldRestrictionTest

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {T : Over (Spec (CommRingCat.of R))}

def toT (g : GtPtF D F) : GtPt D (TF (R := R) F) := ⟨g.b, g.s, g.isGen, g.s_zero, g.mult⟩

theorem isZero_toT (g : GtPtF D F) : (toT g).IsZero ↔ g.IsZero := Iff.rfl

theorem maps_eq {x : Spec (CommRingCat.of F) ⟶ T.left} {g : GtPt D T} {g' : GtPtF D F}
    (H : GtPt.IsPullF F x g g') (χ : D.X) (k : Fin 4) :
    DegPre.gtφ D F g'.b χ k = x ≫ DegPre.gtφT D T g.b χ k := by
  have e := (GlobalTheory.TorusCoord.comp_eq_of_left g.b g'.b x (𝟙 _) (H.1.symm.trans (Category.id_comp _).symm)).1 χ k
  exact ((e.trans (Category.id_comp _)).trans (congrFun (GlobalTheory.TorusCoord.gtφT_eq g'.b χ) k).symm).symm

theorem isPullF_iff (σ : TF (R := R) F ⟶ T) (g : GtPt D T) (g' : GtPtF D F) :
    GtPt.IsPullF F σ.left g g' ↔ g'.b = σ ≫ g.b ∧
      ∀ χ y J, Good D.P.L y J → val (g'.s χ) (𝟙 _) y J = val (g.s χ) σ.left y J :=
  and_congr ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg (·.left) h⟩ (forall_congr' fun _ =>
    ⟨fun h _ _ hJ => (val_corr hJ h _).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp])),
     fun h => corr_of_val D.P.isLB fun y J hJ => (h y J hJ).trans
      ((val_pull hJ _ _ _).trans (by rw [Category.id_comp])).symm⟩)

theorem ext_valF {g g' : GtPtF D F} (hb : g.b = g'.b)
    (hs : ∀ χ y J, Good D.P.L y J → val (g.s χ) (𝟙 _) y J = val (g'.s χ) (𝟙 _) y J) : g = g' := by
  obtain ⟨b, s, h, _, _⟩ := g
  obtain ⟨b', s', h', _, _⟩ := g'
  obtain rfl : b = b' := hb
  obtain rfl : s = s' := funext fun χ =>
    GlobalTheory.TorusCoord.gen_eq_of_corr D.P.isLB (h χ) (h' χ) (corr_of_val D.P.isLB (hs χ))
  rfl

theorem isPullF_unique {x : Spec (CommRingCat.of F) ⟶ T.left} {g : GtPt D T} {a a' : GtPtF D F}
    (H : GtPt.IsPullF F x g a) (H' : GtPt.IsPullF F x g a') : a = a' :=
  ext_valF (Over.OverMorphism.ext (H.1.trans H'.1.symm)) fun χ _ _ hJ =>
    (val_corr hJ (H.2 χ) (𝟙 _)).trans (val_corr hJ (H'.2 χ) (𝟙 _)).symm

theorem exists_isPullF (σ : TF (R := R) F ⟶ T) (ξ : GtPt D T) : ∃ g, GtPt.IsPullF F σ.left ξ g := by
  have e := GlobalTheory.TorusCoord.comp_eq_of_left ξ.b (σ ≫ ξ.b) σ.left (𝟙 _) (Category.id_comp _).symm
  have vp : ∀ χ y J, Good D.P.L y J →
      val (LB.pullGen D.P.L _ _ (ξ.s χ) σ.left) (𝟙 _) y J = val (ξ.s χ) σ.left y J := fun χ y J hJ => by
    rw [val_pull hJ, Category.id_comp]
  obtain ⟨g, hb, hv⟩ := exists_gt (σ ≫ ξ.b) (fun χ => LB.pullGen D.P.L _ _ (ξ.s χ) σ.left)
    (fun χ => DVR.pullGen_isGen _ _ _ _ (ξ.isGen χ) _)
    (fun χ U _ f => Finset.prod_congr rfl fun k _ => congrArg (fun q => f q ^ DegPre.gtε k)
      ((e.1 χ k).trans ((Category.id_comp _).trans (congrFun (GlobalTheory.TorusCoord.gtφT_eq (σ ≫ ξ.b) χ) k).symm)))
    (fun y J hJ => (vp 0 y J hJ).trans ((val_corr hJ ξ.s_zero _).trans (val_one _)))
    (fun χ χ' y J hJ => by
      rw [vp _ y J hJ, vp _ y J hJ, vp _ y J hJ, ← GlobalTheory.TorusCoord.val_s_mul ξ σ.left χ χ' y J hJ, e.2 χ χ',
        ← val_cubAt hJ]
      exact congrArg (_ * ·) (val_pull hJ _ _ _))
  exact ⟨g, (isPullF_iff σ ξ g).2 ⟨hb, fun χ y J hJ => (hv χ y J hJ).trans (vp χ y J hJ)⟩⟩

theorem formEq_zero (χ : D.X) : FormEq (K' := PEmpty) (DegPre.gtφT D T (DegPre.zeroT D T) χ) DegPre.gtε
    PEmpty.elim PEmpty.elim := fun U _ h => by
  rw [Fin.prod_univ_four]
  show h (cP D T χ * 1).left ^ (-1 : ℤ) * h (cP D T χ).left ^ (1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (1 : ℤ) *
    h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) = _
  rw [_root_.mul_one]; simp

theorem isZero_restrict {σ : TF (R := R) F ⟶ T} {g : GtPt D T} {g' : GtPtF D F} (H : GtPt.IsPullF F σ.left g g')
    (h : g.IsZero) : g'.IsZero := by
  obtain ⟨hb, hv⟩ := (isPullF_iff σ g g').1 H
  refine (isZero_iff g').2 ⟨?_, fun χ y J hJ => (hv χ y J hJ).trans ((val_corr hJ (h.2 χ) _).trans (val_one _))⟩
  rw [hb, h.1]; exact MonObj.comp_one σ

theorem isAdd_restrict {σ : TF (R := R) F ⟶ T} {a b c : GtPt D T} {a' b' c' : GtPtF D F}
    (Ha : GtPt.IsPullF F σ.left a a') (Hb : GtPt.IsPullF F σ.left b b') (Hc : GtPt.IsPullF F σ.left c c')
    (h : a.IsAdd b c) : a'.IsAdd b' c' := by
  obtain ⟨ab, av⟩ := (isPullF_iff σ _ _).1 Ha
  obtain ⟨bb, bv⟩ := (isPullF_iff σ _ _).1 Hb
  obtain ⟨cb, cv⟩ := (isPullF_iff σ _ _).1 Hc
  refine (isAdd_iff _ _ _).2 ⟨?_, fun χ y J hJ => ?_⟩
  · rw [cb, ab, bb, h.1]; exact MonObj.comp_mul _ _ _
  · have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub σ hJ _ _ _))).symm.trans
      ((val_corr hJ (h.2 χ) σ.left).trans (val_mul hJ _ _ _))
    have c : σ ≫ DegPre.cT D T χ = cP D _ χ := by rw [cP, comp_toUnit_assoc]
    rw [c, ← ab, ← bb] at e
    rw [av χ y J hJ, bv χ y J hJ, cv χ y J hJ]
    exact e

theorem isNsmul_restrict {σ : TF (R := R) F ⟶ T} {k : ℕ} {a c : GtPt D T} {a' c' : GtPtF D F}
    (Ha : GtPt.IsPullF F σ.left a a') (Hc : GtPt.IsPullF F σ.left c c') (h : GtPt.IsNsmul k a c) :
    GtPtF.IsNsmul k a' c' := by
  obtain ⟨u, u0, us, rfl⟩ := h
  choose v hv using fun i => exists_isPullF σ (u i)
  exact ⟨v, isZero_restrict (hv _) u0, fun i => isAdd_restrict (hv _) Ha (hv _) (us i), isPullF_unique (hv _) Hc⟩

variable {W : (Spec (CommRingCat.of R)).Opens} {ψW : PsiOn D W} {S : Over W.toScheme}

end GlobalTheory.FieldRestrictionTest
end
end
