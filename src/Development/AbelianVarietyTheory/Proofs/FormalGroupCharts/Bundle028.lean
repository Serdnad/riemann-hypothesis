module

public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle025
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumSupportRename
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameSecondPartialLawIffPullback
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBSer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AxisPderivComp
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalSecondPointDerivativeSecondCoordinate
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.NabTrans
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.TruncatedExpSecondEqFull

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.universalJetCoordinates_dim_unique : ∀ (V : Type) [CommRing V] [Nontrivial V] (G : Over (Sp V)) [GrpObj G] (d d' : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (x' : ∀ m, jOG (𝟙 (Sp V)) d' m 1 ⟶ G), GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d') x' → d = d' := by
  first | exact @GlobalTheory.ChartCmp.univJ_dim_unique | exact GlobalTheory.ChartCmp.univJ_dim_unique | (intros; apply GlobalTheory.ChartCmp.univJ_dim_unique <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.ChartTrans GlobalTheory.NabCol

namespace GlobalTheory.ChartTransN

variable {k : Type} [CommRing k] {d n : ℕ}

theorem dofN_ev {m : ℕ} (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) (V : Fin m → Pt k n d)
    (hV : ∀ j, GP (V j)) (g : PS k m d) :
    DofN F b u (ev V g) = ∑ c : Fin m, ∑ l : Fin d, ev V (pderiv (c, l) g) * DofN F b u (V c l) := by
  unfold DofN
  simp only [pderiv_ev V hV]
  simp only [Finset.mul_sum (s := (Finset.univ : Finset (Fin m))), Finset.mul_sum (f := fun l => ev V _ * _)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dofN_inCol_ne (F : Fin d → PS k 2 d) {b c : Fin n} (h : c ≠ b) (u : Fin d → k) (f : PS k 1 d) :
    DofN F b u (inCol c f) = 0 := by
  unfold DofN
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [pderiv_inCol, if_neg h, mul_zero]

theorem dofN_eq_sum (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) (g : PS k n d) :
    DofN F b u g = ∑ l, inCol b (Dof F u (X ((0 : Fin 1), l))) * pderiv (b, l) g := by
  have hX : ∀ l, inCol b (X ((0 : Fin 1), l) : PS k 1 d) = X (b, l) := fun l => gt_ev_X _ (gp b) 0 l
  simp only [← dofN_inCol, hX]
  conv_lhs => unfold DofN
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  unfold DofN
  symm
  rw [Finset.sum_eq_single l]
  · rw [pderiv_X_self, mul_one]
  · intro j _ hj
    rw [pderiv_X_of_ne (fun h => hj (congrArg Prod.snd h).symm), mul_zero]
  · simp

theorem unit_right (G : FGLaw k d) (i : Fin d) :
    ev (n := 1) ![pt k (n := 1) d 0, 0] (G.F i) = (X ((0 : Fin 1), i) : PS k 1 d) := by
  conv_lhs => rw [← G.comm i]
  rw [gt_ev_ev' _ _ axis_GP (pair_points_zero_constant (gp_pt 1) (gp_pt 0)), eval_pair_points, evP_pt _ axis_GP,
    evP_pt _ axis_GP]
  exact G.unit i

theorem dofN_transF (G : FGLaw k d) (φ φi : Pt k 1 d) (hinv : IsInvPair φ φi) (b : Fin n) (u : Fin d → k)
    (g : PS k n d) :
    DofN (transF G.F φ φi) b u (ev (n := n) (fun c => comp1 φ (pt k (n := n) d c)) g) =
      ev (n := n) (fun c => comp1 φ (pt k (n := n) d c)) (DofN G.F b ((dLin φ).mulVec u) g) := by
  have hφ : GP φ := hinv.1
  have hΦ : ∀ c : Fin n, GP (comp1 φ (pt k (n := n) d c)) := fun c => gp_comp1 φ _ hφ (gp_pt c)
  have hc : ∀ (c : Fin n) l, comp1 φ (pt k (n := n) d c) l = inCol c (φ l) := fun _ _ => rfl
  have hcol : ∀ f : PS k 1 d, ev (n := n) (fun c => comp1 φ (pt k (n := n) d c)) (inCol b f) =
      inCol b (ev (n := 1) ![φ] f) := by
    intro f
    unfold inCol
    rw [gt_ev_ev' _ _ hΦ (gp b), gt_ev_ev' _ _ (gp b) (single_point_zero_constant hφ), vec1, vec1, evP_pt _ hΦ]
    rfl
  rw [dofN_ev _ _ _ _ hΦ, dofN_eq_sum G.F, ev_sum _ hΦ, Finset.sum_eq_single b]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [gt_ev_mul _ hΦ, hcol, ← dof_transF G.F G.const (unit_right G) φ φi hinv, gt_ev_X _ (single_point_zero_constant hφ), hc,
      dofN_inCol, mul_comm]
    rfl
  · intro c _ hcb
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [hc, dofN_inCol_ne _ hcb, mul_zero]
  · simp

theorem dpolyN_transF : ∀ (k : Type) [CommRing k] (d n : ℕ) (G : FGLaw k d) (φ φi : Pt k 1 d), IsInvPair φ φi → ∀ (Ix : Type) [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k) (P : MvPolynomial Ix k) (g : PS k n d), DpolyN (transF G.F φ φi) cp u P (ev (n := n) (fun b => comp1 φ (pt k (n := n) d b)) g) = ev (n := n) (fun b => comp1 φ (pt k (n := n) d b)) (DpolyN G.F cp (fun l => (dLin φ).mulVec (u l)) P g) := by
  intro k _ d n G φ φi hinv Ix _ cp u P g
  have hΦ : ∀ c : Fin n, GP (comp1 φ (pt k (n := n) d c)) := fun c => gp_comp1 φ _ hinv.1 (gp_pt c)
  have hit : ∀ (b : Fin n) (v : Fin d → k) (r : ℕ) (g : PS k n d),
      (DofN (transF G.F φ φi) b v)^[r] (ev (n := n) (fun c => comp1 φ (pt k (n := n) d c)) g) =
        ev (n := n) (fun c => comp1 φ (pt k (n := n) d c)) ((DofN G.F b ((dLin φ).mulVec v))^[r] g) := by
    intro b v r
    induction r with
    | zero => intro g; rfl
    | succ r ih =>
      intro g
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, dofN_transF G φ φi hinv, ih]
  have hmon : ∀ m : Ix →₀ ℕ,
      DmonN (transF G.F φ φi) cp u m (ev (n := n) (fun c => comp1 φ (pt k (n := n) d c)) g) =
        ev (n := n) (fun c => comp1 φ (pt k (n := n) d c))
          (DmonN G.F cp (fun l => (dLin φ).mulVec (u l)) m g) := by
    intro m
    unfold DmonN
    induction (Finset.univ : Finset Ix).toList with
    | nil => rfl
    | cons a L ih => rw [List.foldr_cons, List.foldr_cons, ih, hit]
  unfold DpolyN
  rw [ev_sum _ hΦ]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ev_C_mul _ hΦ, hmon]

end GlobalTheory.ChartTransN
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

noncomputable section

theorem GlobalTheory.units_cancel_first_law {U : Type} [CommGroup U] (g p q r abc ab ac bc a b c o : U) :
    g * ((abc * ab⁻¹ * c⁻¹ * o * p) * ((ac * a⁻¹ * c⁻¹ * o * q)⁻¹ * (bc * b⁻¹ * c⁻¹ * o * r)⁻¹)) =
      (abc * ab⁻¹ * ac⁻¹ * bc⁻¹ * a * b * c * o⁻¹) * (g * (p * (q⁻¹ * r⁻¹))) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel


open GlobalTheory.FramePartialLawTwo in
theorem GlobalTheory.frame_first_partial_law_iff_pullback :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → LB.Gen.Maps (LB.linCombIso w (thφ t'.G (x3 t'.G)) thε) t'.cub.t (mp.cm.thetaPull t.PP.L t.cub.t) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (F : Fin d → PS S 2 d) (ph1 : PS S 3 d), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ m, homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x' m = jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2) * jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)) → ((∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph1 ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (lift (jptG t x0 d x m (0 : Fin 3)) (lift (jptG t x0 d x m (1 : Fin 3)) (jptG t x0 d x m (2 : Fin 3)))).left) (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x e m ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)]) (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])) (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))) ↔ (∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph1 ∧ LB.Gen.Corr t'.PP.L _ _ _ _ (LB.pullGen t'.PP.L (thφ t'.G (x3 t'.G)) thε t'.cub.t (lift (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 3)) (lift (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 3)) (jptG t' (𝟙 (Sp S)) d x' m (2 : Fin 3)))).left) (scaleGenG t' _ _ (unitΓ u) (LB.mulGen t'.PP.L _ _ _ _ (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)]) (LB.mulGen t'.PP.L _ _ _ _ (LB.invGen t'.PP.L _ _ (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])) (LB.invGen t'.PP.L _ _ (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)]))))))) := by
  intro E _ _ _ H X0 t S _ x0 t' mp w _ d x x' hx hθ e e' _ _ he F ph1 hF law
  refine forall_congr' fun m => exists_congr fun u => and_congr_right fun _ => ?_
  obtain ⟨c₁, h₁, h₂⟩ := he m
  refine corr_iff_of_val t.PP.isLB t'.PP.isLB fun y J J' hJ hJ' => ?_
  have eθ := val_cubic hθ (jptG t x0 d x m (0 : Fin 3)) (jptG t x0 d x m (1 : Fin 3)) (jptG t x0 d x m (2 : Fin 3))
    (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 3)) (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 3))
    (jptG t' (𝟙 (Sp S)) d x' m (2 : Fin 3)) (jpt_push hx m 0) (jpt_push hx m 1) (jpt_push hx m 2) hJ hJ'
  have eA := val_frame h₁ h₂ ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)] _ _
    (subst_law t' _ d x' m F hF (law m) ![0, 1]) (subst_X t' _ d x' m 2) hJ hJ'
  have eB := val_frame h₁ h₂ ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] _ _
    (subst_X t' _ d x' m 0) (subst_X t' _ d x' m 2) hJ hJ'
  have eC := val_frame h₁ h₂ ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)] _ _
    (subst_X t' _ d x' m 1) (subst_X t' _ d x' m 2) hJ hJ'
  refine ⟨_, eθ, ?_⟩
  refine ((GermB.val_scale t _ _ _ _ _ _ _ hJ).trans (congrArg₂ (· * ·) rfl ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) eA ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_inv _ _).trans (congrArg (·⁻¹) eB))
      ((val_inv _ _).trans (congrArg (·⁻¹) eC)))))))).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) rfl ((GermB.val_scale t' _ _ _ _ _ _ _ hJ').trans
    (congrArg₂ (· * ·) rfl ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) rfl ((val_mul hJ' _ _ _).trans
      (congrArg₂ (· * ·) (val_inv _ _) (val_inv _ _))))))).symm)
  exact GlobalTheory.units_cancel_first_law _ _ _ _ _ _ _ _ _ _ _ _
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

theorem _root_.GlobalTheory.T.frame_second_partial_law_iff_pullback_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → LB.Gen.Maps (LB.linCombIso w (thφ t'.G (x3 t'.G)) thε) t'.cub.t (mp.cm.thetaPull t.PP.L t.cub.t) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (F : Fin d → PS S 2 d) (ph2 : PS S 3 d), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ m, homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x' m = jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2) * jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)) → ((∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph2 ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (lift (jptG t x0 d x m (1 : Fin 3)) (lift (jptG t x0 d x m (2 : Fin 3)) (jptG t x0 d x m (0 : Fin 3)))).left) (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)]) (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)])) (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))) ↔ (∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph2 ∧ LB.Gen.Corr t'.PP.L _ _ _ _ (LB.pullGen t'.PP.L (thφ t'.G (x3 t'.G)) thε t'.cub.t (lift (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 3)) (lift (jptG t' (𝟙 (Sp S)) d x' m (2 : Fin 3)) (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 3)))).left) (scaleGenG t' _ _ (unitΓ u) (LB.mulGen t'.PP.L _ _ _ _ (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)]) (LB.mulGen t'.PP.L _ _ _ _ (LB.invGen t'.PP.L _ _ (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)])) (LB.invGen t'.PP.L _ _ (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)]))))))) := by
  first | exact @GlobalTheory.frame_second_partial_law_iff_pullback | exact GlobalTheory.frame_second_partial_law_iff_pullback | (intros; apply GlobalTheory.frame_second_partial_law_iff_pullback <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem gaugeExp_holds : GaugeExpSt :=
  GE.gauge_exp_identity germ_expAdd_and_evConst.1 germ_expAdd_and_evConst.2 canonGauge_sub_isBiadd
    quadDeriv_of_biadditive HalfIdentity.halfSt

theorem canonGauge_independence_all : AdmissibilitySecond ∧ GaugeExpSt ∧ GaugeIndependenceColumns ∧ NabTransSt :=
  ⟨G2.galois_twist_preserves_siegel_bound germ_expAdd_and_evConst.1 germ_expAdd_and_evConst.2 canonGauge_sub_isBiadd
      quadDeriv_of_biadditive (wickVanish_of_half HalfIdentity.halfSt),
    gaugeExp_holds, WickVanishing.gauge_second_columns_of_exp gaugeExp_holds, WickVanishing.connection_translation_of_poly ChartTrans.transPolySt⟩

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.CanonGaugeAssembly

variable {k : Type} [CommRing k] {d : ℕ}

theorem const_of_ax {h : PS k 2 d} (h0 : ev (n := 1) ![0, pt k d 0] h = 0) :
    constantCoeff h = 0 := by
  have := congrArg constantCoeff h0
  rwa [gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_zero] at this

theorem cancel_expS [Algebra ℚ k] {n : ℕ} {p c : PS k n d} (hc : constantCoeff c = 0)
    (e : FB.expS k c = p * FB.expS k c) : p = 1 := by
  have u : FB.expS k c * FB.expS k (-c) = 1 := by
    rw [← gt_expS_add _ _ hc (by rw [map_neg, hc, neg_zero]), add_neg_cancel, nt_expS_zero]
  calc p = p * FB.expS k c * FB.expS k (-c) := by rw [mul_assoc, u, mul_one]
    _ = 1 := by rw [← e, u]

structure Cob {n : ℕ} (c : PS k 2 d → PS k n d) : Prop where
  add : ∀ f g, c (f + g) = c f + c g
  const : ∀ f, constantCoeff f = 0 → constantCoeff (c f) = 0

theorem cob_three {n : ℕ} (U V W : Fin 2 → Pt k n d) (hU : ∀ j, GP (U j)) (hV : ∀ j, GP (V j))
    (hW : ∀ j, GP (W j)) : Cob (fun h : PS k 2 d => ev U h + ev V h - ev W h) := by
  constructor
  · intro f g
    rw [gt_ev_add U hU, gt_ev_add V hV, gt_ev_add W hW]; ring
  · intro f hf
    rw [map_sub, map_add constantCoeff, gt_const_ev U hU f hf, gt_const_ev V hV f hf,
      gt_const_ev W hW f hf]; simp

theorem cob_two {n : ℕ} (U V : Fin 2 → Pt k n d) (hU : ∀ j, GP (U j)) (hV : ∀ j, GP (V j)) :
    Cob (fun h : PS k 2 d => ev U h - ev V h) := by
  constructor
  · intro f g
    rw [gt_ev_add U hU, gt_ev_add V hV]; ring
  · intro f hf
    rw [map_sub, gt_const_ev U hU f hf, gt_const_ev V hV f hf]; simp

theorem cob_swap (U : Fin 2 → Pt k 2 d) (hU : ∀ j, GP (U j)) :
    Cob (fun h : PS k 2 d => ev U h - h) := by
  constructor
  · intro f g
    rw [gt_ev_add U hU]; ring
  · intro f hf
    rw [map_sub, gt_const_ev U hU f hf, hf]; simp

theorem Cob.chain [Algebra ℚ k] {n : ℕ} {c : PS k 2 d → PS k n d} (hc : Cob c)
    {h₁ h₂ h₃ h₄ : PS k 2 d} (c₁ : constantCoeff h₁ = 0) (c₂ : constantCoeff h₂ = 0)
    (c₃ : constantCoeff h₃ = 0) (c₄ : constantCoeff h₄ = 0) {p₀ p₁ p₂ p₃ : PS k n d}
    (e₁ : p₀ = p₁ * FB.expS k (c h₁)) (e₂ : p₁ = p₂ * FB.expS k (c h₂))
    (e₃ : p₂ = p₃ * FB.expS k (c h₃)) (e₄ : p₃ = FB.expS k (c h₄)) :
    p₀ = FB.expS k (c (h₁ + h₂ + h₃ + h₄)) := by
  have k₁ := hc.const _ c₁
  have k₂ := hc.const _ c₂
  have k₃ := hc.const _ c₃
  have k₄ := hc.const _ c₄
  rw [hc.add, hc.add, hc.add, gt_expS_add _ _ (by simp [k₁, k₂, k₃]) k₄,
    gt_expS_add _ _ (by simp [k₁, k₂]) k₃, gt_expS_add _ _ k₁ k₂, e₁, e₂, e₃, e₄]
  ring

end GlobalTheory.CanonGaugeAssembly


open GlobalTheory.CanonGaugeAssembly in
theorem GlobalTheory.canonGauge_of_steps :
    (∀ (R k : Type) [CommRing R] [CommRing k] (f : R →+* k) (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), ∃ B' : FB k d O, (∀ i, B'.G.F i = MvPowerSeries.map f (B.G.F i)) ∧ (∀ a i, B'.A.act a i = MvPowerSeries.map f (B.A.act a i)) ∧ B'.ph1 = MvPowerSeries.map f B.ph1 ∧ B'.ph2 = MvPowerSeries.map f B.ph2 ∧ B'.sy = MvPowerSeries.map f B.sy ∧ ∀ a, B'.ad a = MvPowerSeries.map f (B.ad a)) → (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O) (h : PS k 2 d), (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) → ∃ B' : FB k d O, B'.G.F = B.G.F ∧ B'.A.act = B.A.act ∧ B.ph1 = B'.ph1 * FB.expS k (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) ∧ B.ph2 = B'.ph2 * FB.expS k (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h) ∧ B.sy = B'.sy * FB.expS k (ev (n := 2) ![pt k d 1, pt k d 0] h - h) ∧ ∀ a : O, B.ad a = B'.ad a * FB.expS k (ev (n := 2) ![comp1 (B.A.act a) (pt k d 0), pt k d 1] h - ev (n := 2) ![pt k d 0, comp1 (B.A.act (star a)) (pt k d 1)] h)) → (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O), ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ B.ph1 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h)) → (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O), B.ph1 = 1 → ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) = 0 ∧ B.ph2 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h)) → (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (B : FB k d O), B.ph1 = 1 → B.ph2 = 1 → ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) = 0 ∧ (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h) = 0 ∧ ∀ a : O, B.ad a = FB.expS k (ev (n := 2) ![comp1 (B.A.act a) (pt k d 0), pt k d 1] h - ev (n := 2) ![pt k d 0, comp1 (B.A.act (star a)) (pt k d 1)] h)) → (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O), B.ph1 = 1 → B.ph2 = 1 → (∀ a, B.ad a = 1) → ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) = 0 ∧ (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h) = 0 ∧ (∀ a : O, (ev (n := 2) ![comp1 (B.A.act a) (pt k d 0), pt k d 1] h - ev (n := 2) ![pt k d 0, comp1 (B.A.act (star a)) (pt k d 1)] h) = 0) ∧ B.sy = FB.expS k (ev (n := 2) ![pt k d 1, pt k d 0] h - h)) → CanonGaugeSt := by
  intro hbc hrg s1 s2 s3 s4 R _ d O _ _ _ _ _ k _ _ _ B
  obtain ⟨B0, hF0, hA0, hp10, hp20, hsy0, had0⟩ := hbc R k (algebraMap R k) d O B
  have eF : B.FK k = B0.G.F := funext fun i => (hF0 i).symm
  have eA : ∀ a, B.actK k a = B0.A.act a := fun a => funext fun i => (hA0 a i).symm
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt k (n := n) d j) := fun j => gp_pt j
  have C1 := cob_three (n := 3) ![pt k d 0, pt k d 2] ![pt k d 1, pt k d 2]
    ![addOf B0.G.F (pt k d 0) (pt k d 1), pt k d 2] (pair_points_zero_constant (hp _) (hp _)) (pair_points_zero_constant (hp _) (hp _))
    (pair_points_zero_constant (gp_addOf _ B0.G.const _ _ (hp _) (hp _)) (hp _))
  have C2 := cob_three (n := 3) ![pt k d 0, pt k d 1] ![pt k d 0, pt k d 2]
    ![pt k d 0, addOf B0.G.F (pt k d 1) (pt k d 2)] (pair_points_zero_constant (hp _) (hp _)) (pair_points_zero_constant (hp _) (hp _))
    (pair_points_zero_constant (hp _) (gp_addOf _ B0.G.const _ _ (hp _) (hp _)))
  have CS := cob_swap ![pt k d 1, pt k d 0] (pair_points_zero_constant (hp _) (hp _))
  have CA := fun a : O => cob_two (n := 2) ![comp1 (B0.A.act a) (pt k d 0), pt k d 1]
    ![pt k d 0, comp1 (B0.A.act (star a)) (pt k d 1)]
    (pair_points_zero_constant (gp_comp1 _ _ (B0.A.const a) (hp _)) (hp _))
    (pair_points_zero_constant (hp _) (gp_comp1 _ _ (B0.A.const (star a)) (hp _)))

  obtain ⟨h1, ax1, t1⟩ := s1 k d O B0
  have c1 := const_of_ax ax1.1
  obtain ⟨B1, F1, A1, p11, p21, sy1, ad1⟩ := hrg k d O B0 h1 ax1
  have q11 : B1.ph1 = 1 := cancel_expS (C1.const _ c1) (t1.symm.trans p11)

  obtain ⟨h2, ax2, z12, t2⟩ := s2 k d O B1 q11
  have c2 := const_of_ax ax2.1
  obtain ⟨B2, F2, A2, p12, p22, sy2, ad2⟩ := hrg k d O B1 h2 ax2
  have q12 : B2.ph1 = 1 := by
    rw [z12, nt_expS_zero, mul_one, q11] at p12; exact p12.symm
  rw [F1] at t2 p12 p22
  rw [A1] at ad2
  have q22 : B2.ph2 = 1 := cancel_expS (C2.const _ c2) (t2.symm.trans p22)

  obtain ⟨h3, ax3, z13, z23, t3⟩ := s3 k d O B2 q12 q22
  have c3 := const_of_ax ax3.1
  obtain ⟨B3, F3, A3, p13, p23, sy3, ad3⟩ := hrg k d O B2 h3 ax3
  have q13 : B3.ph1 = 1 := by
    rw [z13, nt_expS_zero, mul_one, q12] at p13; exact p13.symm
  have q23 : B3.ph2 = 1 := by
    rw [z23, nt_expS_zero, mul_one, q22] at p23; exact p23.symm
  rw [F2, F1] at p13 p23
  rw [A2, A1] at ad3 t3
  have qa3 : ∀ a, B3.ad a = 1 := fun a =>
    cancel_expS ((CA a).const _ c3) ((t3 a).symm.trans (ad3 a))

  obtain ⟨h4, ax4, z14, z24, za4, t4⟩ := s4 k d O B3 q13 q23 qa3
  have c4 := const_of_ax ax4.1
  rw [F3, F2, F1] at z14 z24
  rw [A3, A2, A1] at za4
  have g0 : ∀ j, GP ((![0, pt k d 0] : Fin 2 → Pt k 1 d) j) := pair_points_zero_constant gp_zero₂ (hp _)
  have g1 : ∀ j, GP ((![pt k d 0, 0] : Fin 2 → Pt k 1 d) j) := pair_points_zero_constant (hp _) gp_zero₂
  refine ⟨h1 + h2 + h3 + h4, ?_, ?_, ?_, ?_, ?_, fun a => ?_⟩
  · rw [gt_ev_add _ g0, gt_ev_add _ g0, gt_ev_add _ g0, ax1.1, ax2.1, ax3.1, ax4.1]; simp
  · rw [gt_ev_add _ g1, gt_ev_add _ g1, gt_ev_add _ g1, ax1.2, ax2.2, ax3.2, ax4.2]; simp
  · rw [eF]
    exact hp10.symm.trans (C1.chain c1 c2 c3 c4 p11 p12 p13 (by
      rw [q13, z14, nt_expS_zero]))
  · rw [eF]
    exact hp20.symm.trans (C2.chain c1 c2 c3 c4 p21 p22 p23 (by
      rw [q23, z24, nt_expS_zero]))
  · exact hsy0.symm.trans (CS.chain c1 c2 c3 c4 sy1 sy2 sy3 t4)
  · rw [eA, eA]
    exact (had0 a).symm.trans ((CA a).chain c1 c2 c3 c4 (ad1 a) (ad2 a) (ad3 a) (by
      rw [qa3 a, za4 a, nt_expS_zero]))
end
end
