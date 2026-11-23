module

import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle030
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle031
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle072
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumSupportRename
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartPrimTrPfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAdjointnessSeriesOfFrames
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameAdjointnessSeriesOfPullback
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle027
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle024
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
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle005
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JetSubstPCompJetBC

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.FrameDown

open TopologicalSpace ReciprocityTheory.ChartRestriction.G.DVR

section

variable {X0 X' Y : Scheme.{0}} {L : LB X0} {L' : LB X'} {F : X' ⟶ X0} {K : Type} [Fintype K]

theorem exists_down_val {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (Y ⟶ X')} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι),
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
        gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) =
          pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) := by
  apply GlobalTheory.PrimDown.exists_down_all <;> assumption

end

theorem frames_pull_back : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ∀ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) → ∃ e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m, (∀ m, (e' m).IsGen) ∧ (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) := by
  intro E _ _ _ H X0 t S _ x0 t' mp w hw d x x' hx e he
  have hφ : ∀ m, (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) =
      cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] := by
    intro m
    funext J
    let U : Over.mk ((jOG (𝟙 (Sp S)) d m 2).hom ≫ x0) ⟶ jOG x0 d m 2 :=
      Over.homMk (𝟙 _) (by simp [overAt])
    have hj : ∀ i : Fin 2, pushPt mp.cart.1.w (jptG t' (𝟙 (Sp S)) d x' m i) = U ≫ jptG t x0 d x m i := fun i =>
      Over.OverMorphism.ext (by
        show ((homAt (𝟙 (Sp S)) (jetCopy d m i)).left ≫ (x' m).left) ≫ mp.φ =
          𝟙 _ ≫ (homAt x0 (jetCopy d m i)).left ≫ (x m).left
        rw [Category.assoc, hx, Category.id_comp]
        rfl)
    refine (psum_push mp.cart _ ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] U
      (fun i => ?_) J.down).trans (Category.id_comp _)
    fin_cases i
    · exact hj 0
    · exact hj 1
  choose c₁ hc₁ hcorr using fun m => ChartPrimTrPf.exists_reindex t.PP.L (hφ m) (cε 2) (e m) (he m)
  choose a ha hv using fun m => exists_down_val ((isGen_iff w).1 hw.1) t.PP.isLB t'.PP.isLB (c₁ m) (hc₁ m)
  exact ⟨a, ha, fun m => ⟨c₁ m, hcorr m, ChartPrimTrPf.maps_flat w _ _ (a m) (c₁ m) (hv m)⟩⟩

end GlobalTheory.FrameDown
end
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.HarmCopies

open GlobalTheory.PowGerm

theorem monomial_eq_boxSer {k : Type} [CommRing k] {n d : ℕ} (e : Fin n × Fin d →₀ ℕ) :
    (MvPowerSeries.monomial e 1 : PS k n d) =
      boxSer fun b => ∏ j : Fin d, (MvPowerSeries.X ((0 : Fin 1), j) : PS k 1 d) ^ e (b, j) := by
  unfold boxSer
  simp only [map_prod, map_pow, MvPowerSeries.rename_X]
  rw [← Fintype.prod_prod_type' (fun b j => (MvPowerSeries.X (b, j) : PS k n d) ^ e (b, j)),
    MvPowerSeries.monomial_one_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]

theorem exists_jet {k : Type} [CommRing k] {n d : ℕ} (N : ℕ) (f : PS k n d) :
    ∃ S : Finset (Fin n × Fin d →₀ ℕ), ∀ e : Fin n × Fin d →₀ ℕ, e.degree ≤ N →
      MvPowerSeries.coeff e f =
        MvPowerSeries.coeff e (∑ j : S, MvPowerSeries.coeff j.1 f • (MvPowerSeries.monomial j.1 1 : PS k n d)) := by
  classical
  refine ⟨(Finsupp.finite_of_degree_le N).toFinset, fun e he => ?_⟩

  rw [map_sum, Finset.sum_eq_single ⟨e, by simpa using he⟩]
  · simp
  · intro j _ hj
    rw [map_smul, MvPowerSeries.coeff_monomial_ne (fun h => hj (Subtype.ext h.symm)), smul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

def letterEquiv (T : Type) (r : T → ℕ) (n : ℕ) : (Σ τ : T, Fin (r τ)) × Fin n ≃ Formalism.L2.Pj.Letter T r n where
  toFun p := ⟨p.1.1, p.1.2, p.2⟩
  invFun l := (⟨l.1, l.2.1⟩, l.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem const_eq_zero {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type} [CommRing k]
    [Algebra ℚ k] [Algebra R k] {B : FB R d O} {h : PS k 2 d} (hh : B.IsCanonGauge k h) :
    MvPowerSeries.constantCoeff h = 0 := by
  rw [← TB.WickVanishing.gt_const_ev_eq _ (TB.WickVanishing.pair_points_zero_constant TB.WickVanishing.gp_zero₂ (TB.WickVanishing.gp_pt (n := 1) 0)) h, hh.ax0, map_zero]

theorem col_sum_eq_zero {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k] {cc : T → T} {isX : T → Prop}
    (Q : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)
    (hQ : MvPolynomial.rename (letterEquiv T r n) Q ∈ harmK r n k cc isX (fun _ => 1))
    (τ : T) (hτ : isX τ) (i : Fin (r τ)) (i' : Fin (r (cc τ))) :
    ∑ b : Fin n, MvPolynomial.pderiv (((⟨τ, i⟩ : Σ τ : T, Fin (r τ))), b)
      (MvPolynomial.pderiv (((⟨cc τ, i'⟩ : Σ τ : T, Fin (r τ))), b) Q) = 0 := by
  simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at hQ
  have h := hQ τ hτ i i'
  apply MvPolynomial.rename_injective _ (letterEquiv T r n).injective

  rw [map_zero, ← h, map_sum, lap, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [LinearMap.sum_apply, Finset.sum_eq_single b]
  · rw [Matrix.one_apply_eq, one_smul, ← MvPolynomial.pderiv_rename (letterEquiv T r n).injective,
      ← MvPolynomial.pderiv_rename (letterEquiv T r n).injective]
    rfl
  · intro b' _ hb
    rw [Matrix.one_apply_ne (Ne.symm hb), zero_smul, LinearMap.zero_apply]
  · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.HarmCopies

namespace GlobalTheory


open HarmCopies PowGerm in
theorem nabValN_harmonic_gauge_independent :
    ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (k : Type) [Field k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h h' : PS k 2 d), B.IsCanonGauge k h → B.IsCanonGauge k h' → ∀ (T : Type) [Fintype T] (r : T → ℕ) (cc : T → T) (isX : T → Prop) (σ : T → O →+* k), (∀ τ, cc (cc τ) = τ) → (∀ τ, isX τ ∨ isX (cc τ)) → (∀ τ a, σ (cc τ) a = σ τ (star a)) → (∀ τ τ', τ ≠ τ' → ∃ a, IsUnit (σ τ a - σ τ' a)) → ∀ u : (Σ τ : T, Fin (r τ)) → Fin d → k, (∀ l a, (dAct k B a).mulVec (u l) = σ l.1 a • u l) → ∀ (n : ℕ) (P : MvPolynomial (Letter T r n) k), P ∈ harmK r n k cc isX (fun _ => 1) → ∀ (w0 : O) (q : ℕ) (f : PS k n d), nabValN B k h w0 q f (fun ℓ : Letter T r n => ℓ.2.2) (fun ℓ : Letter T r n => u ⟨ℓ.1, ℓ.2.1⟩) P = nabValN B k h' w0 q f (fun ℓ : Letter T r n => ℓ.2.2) (fun ℓ : Letter T r n => u ⟨ℓ.1, ℓ.2.1⟩) P := by
  intro R _ d O _ _ _ _ _ k _ _ _ B h h' hh hh' T _ r cc isX σ hcc hX hσ hsep u hu n P hP w0 q f
  obtain ⟨Q, rfl⟩ : ∃ Q, MvPolynomial.rename (letterEquiv T r n) Q = P :=
    MvPolynomial.rename_surjective _ (letterEquiv T r n).surjective P
  obtain ⟨S, hS⟩ := exists_jet (MvPolynomial.rename (letterEquiv T r n) Q).totalDegree f
  rw [(nabJet R d O B k h w0 q n _ _ _).1 _ _ _ hS, (nabJet R d O B k h' w0 q n _ _ _).1 _ _ _ hS,
    (nabJet R d O B k h w0 q n _ _ _).2.1, (nabJet R d O B k h' w0 q n _ _ _).2.1]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [monomial_eq_boxSer,
    nabValN_boxSer R d O B k h w0 (const_eq_zero hh) q n _ _ _ (letterEquiv T r n) _ u _ (fun _ => rfl) (fun _ => rfl),
    nabValN_boxSer R d O B k h' w0 (const_eq_zero hh') q n _ _ _ (letterEquiv T r n) _ u _ (fun _ => rfl) (fun _ => rfl)]
  exact canonGauge_independence_harmonic R d O k B h h' hh hh' T r cc isX σ hcc hX hσ hsep u hu n Q
    (col_sum_eq_zero Q hP) w0 q _

end GlobalTheory
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.FrameAdjDown

section General

variable {X0 X' Y Z A A' : Scheme.{0}} {L : LB X0} {L' : LB X'} {F : X' ⟶ X0} {K K₂ : Type} [Fintype K] [Fintype K₂]

def scl {φ : K → (Y ⟶ X0)} {ε : K → ℤ} (u : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb L φ ε)) : LB.Gen (LB.LinComb L φ ε) :=
  ⟨fun j => res le_top u * g.s j⟩

theorem val_scl {φ : K → (Y ⟶ X0)} {ε : K → ℤ} (u : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) {z : Z}
    {J : (Z ⟶ X0) → L.ι} (hJ : Good L z J) : val (scl u g) r z J = gm r z ⊤ u * val g r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) u) rfl)

theorem pmaps_of_flat (w : LB.Iso L' (L.pull F)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε))
    (c : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε))
    (h : LB.Gen.Maps (LB.linCombIso w φ' ε) a (flatGen L F φ' ε c)) :
    PMaps w φ' (fun k => φ' k ≫ F) ε a c (𝟙 Y) := by
  refine (maps_iff w φ' (fun k => φ' k ≫ F) ε a c (𝟙 Y) (flatGen L F φ' ε c)
    (fun j x hx => wchart_pull_le L F φ' j hx) (fun j => ?_)).1 h
  refine unit_ext fun y hy => ?_
  have hyV : (𝟙 Y : Y ⟶ Y) y ∈ ((L.pull F).LinComb φ' ε).U j := hy
  have hyU : (𝟙 Y : Y ⟶ Y) ((𝟙 Y : Y ⟶ Y) y) ∈ LB.wchart L (fun k => φ' k ≫ F) (fun k => j k ⟨⟩) :=
    wchart_pull_le L F φ' j hy
  refine (gm_res (𝟙 Y) y _ hyV _).trans ?_
  refine Eq.trans ?_ (gm_res (𝟙 Y) y _ hyV _).symm
  have e := gm_pull (𝟙 Y) (𝟙 Y) y _ hyU (c.s fun k => j k ⟨⟩)
  rw [Category.comp_id] at e
  exact e.symm

theorem corr_down (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F))
    {ψ : K → (A ⟶ X0)} {ψ' : K → (A' ⟶ X')} {ε : K → ℤ} {U : A' ⟶ A} (hψ : ∀ k, ψ' k ≫ F = U ≫ ψ k)
    {g : LB.Gen (LB.LinComb L ψ ε)} {g' : LB.Gen (LB.LinComb L' ψ' ε)} (hg : PMaps w ψ' ψ ε g' g U)
    {φ : K₂ → (Y ⟶ X0)} {φ' : K₂ → (Y ⟶ X')} {δ : K₂ → ℤ} {e : LB.Gen (LB.LinComb L φ δ)}
    {e' : LB.Gen (LB.LinComb L' φ' δ)} {c : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) δ)}
    (hc : LB.Gen.Corr L _ _ _ _ c e) (hm : LB.Gen.Maps (LB.linCombIso w φ' δ) e' (flatGen L F φ' δ c))
    {l : Y ⟶ A} {l' : Y ⟶ A'} (hl : l' ≫ U = l) (σ₁ σ₂ : Y ⟶ Y) (u : Γ(Y, ⊤)ˣ)
    (hF : ∀ (V : Type) [CommGroup V] (h : (Y ⟶ X') → V),
      (∏ k, h (l' ≫ ψ' k) ^ ε k) * ∏ k, h (σ₁ ≫ φ' k) ^ δ k = ∏ k, h (σ₂ ≫ φ' k) ^ δ k)
    (H : LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ g l) (LB.pullGen L _ _ e σ₁))
      (scl u (LB.pullGen L _ _ e σ₂))) :
    LB.Gen.Corr L' _ _ _ _ (LB.mulGen L' _ _ _ _ (LB.pullGen L' _ _ g' l') (LB.pullGen L' _ _ e' σ₁))
      (scl u (LB.pullGen L' _ _ e' σ₂)) := by
  refine corr_of_val hL' fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := DegPull.exists_good' hL y
  have h0 := val_corr hJ H (𝟙 Y)
  rw [val_mul hJ, val_scl _ _ _ hJ, val_pull hJ, val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp,
    Category.id_comp] at h0
  rw [val_mul hJ', val_scl _ _ _ hJ', val_pull hJ', val_pull hJ', val_pull hJ', Category.id_comp, Category.id_comp,
    Category.id_comp]
  have he : ∀ σ : Y ⟶ Y, val e σ y J =
      (∏ k, gw w (σ ≫ φ' k) y (J ((σ ≫ φ' k) ≫ F)) (J' (σ ≫ φ' k)) ^ δ k) * val e' σ y J' := fun σ => by
    have := DegPull.pmaps_val (fun k => (Category.id_comp _).symm) (pmaps_of_flat w φ' δ e' c hm) σ y hJ hJ'
    rw [Category.comp_id] at this
    exact (val_corr hJ hc σ).symm.trans this
  have h1 := DegPull.pmaps_val hψ hg l' y hJ hJ'
  rw [hl] at h1
  have h2 := hF _ (fun q => gw w q y (J (q ≫ F)) (J' q))
  rw [h1, he, he, ← h2, _root_.mul_mul_mul_comm, mul_left_comm (gm (𝟙 Y) y ⊤ u)] at h0
  exact mul_left_cancel h0

end General

open Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun GlobalTheory.FrameAdjSeries

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem pt_act' {X0 : Scheme.{0}} {t : SAB H X0} {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ}
    {x : ∀ m, jOG x0 d m 1 ⟶ t.G} {act : 𝓞 E → Fin d → PS S 1 d}
    (h : ∀ m (b : 𝓞 E), x m ≫ t.act.act b =
      homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x m)
    (m : ℕ) {n : ℕ} (r : Fin 1 → Fin n) (a : 𝓞 E) :
    homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => psIn d m r (act a p.2))) ≫ x m =
      jptG t x0 d x m (r 0) ≫ t.act.act a := by
  rw [subst_psIn, ← homAt_comp, Category.assoc, ← h m a, ← Category.assoc, ren_one]
  try rfl

theorem push_act {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (mp : SABMap t' t f) {T : Over S'}
    (p : T ⟶ t'.G) (a : 𝓞 E) : pushPt mp.cart.1.w (p ≫ t'.act.act a) = pushPt mp.cart.1.w p ≫ t.act.act a :=
  Over.OverMorphism.ext (by
    show (p.left ≫ _) ≫ _ = (p.left ≫ _) ≫ _
    rw [Category.assoc, mp.act, Category.assoc])

def sqMap {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (mp : SABMap t' t f) :
    Over.mk ((t'.G ⊗ t'.G).hom ≫ f) ⟶ t.G ⊗ t.G :=
  lift (pushPt mp.cart.1.w (fst t'.G t'.G)) (pushPt mp.cart.1.w (snd t'.G t'.G))

theorem adj_comm {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (mp : SABMap t' t f) (a b : 𝓞 E)
    (k : ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2))) :
    Sum.elim (cφG t' ![fst t'.G t'.G, snd t'.G t'.G ≫ t'.act.act b])
        (cφG t' ![fst t'.G t'.G ≫ t'.act.act a, snd t'.G t'.G]) k ≫ mp.φ =
      (sqMap mp).left ≫ Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act b])
        (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) k := by
  rcases k with I | I
  · refine psum_push mp.cart _ _ (sqMap mp) (fun i => ?_) I.down
    fin_cases i
    · simp [sqMap]
    · exact (push_act mp _ _).trans (by simp [sqMap])
  · refine psum_push mp.cart _ _ (sqMap mp) (fun i => ?_) I.down
    fin_cases i
    · exact (push_act mp _ _).trans (by simp [sqMap])
    · simp [sqMap]

theorem lift_sqMap {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (mp : SABMap t' t f)
    {T' : Over S'} {T : Over S} (p' q' : T' ⟶ t'.G) (p q : T ⟶ t.G) (h : T'.left ⟶ T.left)
    (hp : p'.left ≫ mp.φ = h ≫ p.left) (hq : q'.left ≫ mp.φ = h ≫ q.left) :
    (lift p' q').left ≫ (sqMap mp).left = h ≫ (lift p q).left := by
  apply pullback.hom_ext
  · show ((lift p' q').left ≫ (sqMap mp).left) ≫ (fst t.G t.G).left = (h ≫ (lift p q).left) ≫ (fst t.G t.G).left
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, sqMap, lift_fst, lift_fst, ← hp]
    show (lift p' q').left ≫ (fst t'.G t'.G).left ≫ mp.φ = _
    rw [← Category.assoc, ← Over.comp_left, lift_fst]
  · show ((lift p' q').left ≫ (sqMap mp).left) ≫ (snd t.G t.G).left = (h ≫ (lift p q).left) ≫ (snd t.G t.G).left
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, sqMap, lift_snd, lift_snd, ← hq]
    show (lift p' q').left ≫ (snd t'.G t'.G).left ≫ mp.φ = _
    rw [← Category.assoc, ← Over.comp_left, lift_snd]



theorem adjoint_series_pull_back : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (act : 𝓞 E → Fin d → PS S 1 d) (ad : 𝓞 E → PS S 2 d) (a : 𝓞 E), (∀ b j, MvPowerSeries.constantCoeff (act b j) = 0) → (∀ m (b : 𝓞 E), x' m ≫ t'.act.act b = homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x' m) → (∃ wL : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G])) (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧ ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.mulGen t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left) (peG t x0 d x e m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)])) (scaleGenG t _ _ (unitΓ u) (peG t x0 d x e m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))) → (∃ wL : LB.Gen (LB.LinComb t'.PP.L (Sum.elim (cφG t' ![fst t'.G t'.G, snd t'.G t'.G ≫ t'.act.act (H.bar a)]) (cφG t' ![fst t'.G t'.G ≫ t'.act.act a, snd t'.G t'.G])) (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧ ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧ LB.Gen.Corr t'.PP.L _ _ _ _ (LB.mulGen t'.PP.L _ _ _ _ (LB.pullGen t'.PP.L _ _ wL (lift (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2)) (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2))).left) (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)])) (scaleGenG t' _ _ (unitΓ u) (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))) := by
  intro E _ _ _ H X0 t S _ x0 t' mp w hw d x x' hx e e' _ _ htie act ad a _ hact ⟨wL, hwL, hu⟩
  obtain ⟨wL', hwL', hp⟩ := DegPull.exists_pmaps ((isGen_iff w).1 hw.1) t.PP.isLB t'.PP.isLB (sqMap mp).left
    (adj_comm mp a (H.bar a)) wL hwL
  refine ⟨wL', hwL', fun m => ?_⟩
  obtain ⟨u, hu1, hu2⟩ := hu m
  obtain ⟨c, hc, hm⟩ := htie m
  refine ⟨u, hu1, ?_⟩
  have hj : ∀ i : Fin 2, (jptG t' (𝟙 (Sp S)) d x' m i).left ≫ mp.φ = 𝟙 _ ≫ (jptG t x0 d x m i).left := fun i => by
    show ((homAt (𝟙 (Sp S)) (jetCopy d m i)).left ≫ (x' m).left) ≫ mp.φ =
      𝟙 _ ≫ (homAt x0 (jetCopy d m i)).left ≫ (x m).left
    rw [Category.assoc, hx, Category.id_comp]
    rfl
  have hl₀ := lift_sqMap mp (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2)) (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2))
    (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2)) (𝟙 (Sp (Jet S (Fin 2 × Fin d) m))) (hj 0) (hj 1)
  have hl : (lift (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2)) (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2))).left ≫
      (sqMap mp).left = (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left :=
    hl₀.trans (Category.id_comp _)
  refine corr_down (Y := (jOG (𝟙 (Sp S)) d m 2).left) t.PP.isLB t'.PP.isLB w (adj_comm mp a (H.bar a)) hp hc hm hl
    _ _ (unitΓ u) (fun V _ h => ?_) hu2
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, wl_pt, wl_pt', pe_pt, pt_sub, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, pt_X, pt_act' hact, zpow_neg, Finset.prod_inv_distrib]
  simp only [inv_mul_cancel_right]

end GlobalTheory.FrameAdjDown
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

theorem _root_.GlobalTheory.T.frame_adjointness_series_of_pullback : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → IsAbelianScheme t'.G → (homAt (𝟙 (Sp S)) (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S) ≫ x' 0 = 1) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (act : 𝓞 E → Fin d → PS S 1 d) (ad : 𝓞 E → PS S 2 d) (a : 𝓞 E), (∀ m (b : 𝓞 E), x' m ≫ t'.act.act b = homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x' m) → (∀ b j, MvPowerSeries.constantCoeff (act b j) = 0) → MvPowerSeries.constantCoeff (ad a) = 1 → (∃ wL : LB.Gen (LB.LinComb t'.PP.L (Sum.elim (cφG t' ![fst t'.G t'.G, snd t'.G t'.G ≫ t'.act.act (H.bar a)]) (cφG t' ![fst t'.G t'.G ≫ t'.act.act a, snd t'.G t'.G])) (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧ ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧ LB.Gen.Corr t'.PP.L _ _ _ _ (LB.mulGen t'.PP.L _ _ _ _ (LB.pullGen t'.PP.L _ _ wL (lift (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2)) (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2))).left) (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)])) (scaleGenG t' _ _ (unitΓ u) (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))) → (∃ wL : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G])) (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧ ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.mulGen t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left) (peG t x0 d x e m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)])) (scaleGenG t _ _ (unitΓ u) (peG t x0 d x e m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))) := by
  first | exact @GlobalTheory.FrameAdjUp.frame_adj_up | exact GlobalTheory.FrameAdjUp.frame_adj_up | (intros; apply GlobalTheory.FrameAdjUp.frame_adj_up <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.ChartRigBC

open GlobalTheory.RawChartGermBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0) (x1 : Sp S' ⟶ X0) (d : ℕ)

theorem jetCoef_eq (κ : Type) (m : ℕ) : jetCoef ψ κ m = jetBC ψ κ m :=
  RingHom.ext fun a => by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    rfl

theorem subst_jetCoef (m n n' : ℕ) (φ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S)
    (φ' : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S') (h : ∀ p, φ' p = MvPolynomial.map ψ (φ p)) :
    (Formalism.L2.Pj.homAt x1 (jetSubstP m φ')).left ≫ spMap (jetCoef ψ (Fin n × Fin d) m) =
      spMap (jetCoef ψ (Fin n' × Fin d) m) ≫ (Formalism.L2.Pj.homAt x0 (jetSubstP m φ)).left := by
  obtain rfl : φ' = fun p => MvPolynomial.map ψ (φ p) := funext h
  rw [jetCoef_eq, jetCoef_eq]
  exact spMap_comp_eq _ _ _ _ (PullbackSections.jetSubstP_comp_jetBC ψ m φ)

theorem aug_jetCoef (m n : ℕ) :
    (Formalism.L2.Pj.homAt x1 (jetAug : Jet S' (Fin n × Fin d) m →ₐ[S'] S')).left ≫ spMap (jetCoef ψ (Fin n × Fin d) m) =
      spMap ψ ≫ (Formalism.L2.Pj.homAt x0 (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S)).left := by
  rw [jetCoef_eq]
  exact spMap_comp_eq _ _ _ _ (PullbackSections.jetAug_comp_jetBC ψ _ m)

theorem overAt_hom_comp :
    (overAt (spMap ψ ≫ x0) S').hom = spMap ψ ≫ (overAt x0 S).hom := by
  change spMap (algebraMap S' S') ≫ spMap ψ ≫ x0 = spMap ψ ≫ spMap (algebraMap S S) ≫ x0
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  exact spMap_comp_eq _ _ _ _ (RingHom.ext fun _ => rfl)

theorem val_eLG_bc (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG x1 d m 1 ⟶ t.G)
    (hx : ∀ m, (x' m).left = spMap (jetCoef ψ (Fin 1 × Fin d) m) ≫ (x m).left)
    (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t x1 d x' m)
    (he : ∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (e' m) (LB.pullGen t.PP.L _ _ (e m) (spMap (jetCoef ψ (Fin 2 × Fin d) m))))
    (wP : PrimTyG t) (m : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (jOG x1 d m 1).left) (z : Z) {J}
    (hJ : Good t.PP.L z J) :
    val (eLG t x1 d x' (fun a i => MvPowerSeries.map ψ (act a i)) e' wP m) r z J =
      val (eLG t x0 d x act e wP m) (r ≫ spMap (jetCoef ψ (Fin 1 × Fin d) m)) z J := by
  refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
  refine congrArg₂ (· * ·) ?_ ?_
  · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    refine congrArg (fun q => val wP q z J) ?_
    exact (congrArg (r ≫ ·) (hx m)).trans (Category.assoc _ _ _).symm
  · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    refine (val_corr hJ (he m) _).trans ((val_pull hJ _ _ _).trans ?_)
    refine congrArg (fun q => val (e m) q z J) ?_
    refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
    refine congrArg (r ≫ ·) (subst_jetCoef ψ x0 x1 d m 2 1 _ _ ?_)
    rintro ⟨i, j⟩
    fin_cases i
    · exact (MvPolynomial.map_X ψ _).symm
    · exact (map_psIn ψ d m _ _).symm

end GlobalTheory.ChartRigBC

namespace GlobalTheory


open ChartRigBC in
theorem rigidificationAtOrigin_baseChange :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0) (x1 : Sp S' ⟶ X0), x1 = spMap ψ ≫ x0 → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG x1 d m 1 ⟶ t.G), (∀ m, (x' m).left = spMap (jetCoef ψ (Fin 1 × Fin d) m) ≫ (x m).left) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t x1 d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (e' m) (LB.pullGen t.PP.L _ _ (e m) (spMap (jetCoef ψ (Fin 2 × Fin d) m)))) → ∀ (act : 𝓞 E → Fin d → PS S 1 d) (wP : PrimTyG t), wP.IsGen → Rig0G t x0 d x act e wP → Rig0G t x1 d x' (fun a i => (MvPowerSeries.map ψ (act a i))) e' wP := by
  intro E _ _ _ H X0 t S S' _ _ ψ x0 x1 hx1 d x x' hx e e' _ _ he act wP _ h0
  have hL := t.PP.isLB
  refine corr_of_val hL fun y J hJ => ?_
  refine (val_pull hJ _ _ _).trans ((val_eLG_bc t ψ x0 x1 d act x x' hx e e' he wP 0 _ y hJ).trans ?_)
  refine Eq.trans ?_ (GermB.val_rigT _ _ _ _ _ y J hJ).symm
  have h1 := (val_pull hJ _ _ _).symm.trans ((val_corr hJ h0 (spMap ψ)).trans (GermB.val_rigT _ _ _ _ _ y J hJ))
  refine (congrArg (fun q => val (eLG t x0 d x act e wP 0) q y J) ?_).trans
    (h1.trans (congrArg (fun q => val t.PP.rig q y J) ?_))
  · rw [Category.id_comp]; exact aug_jetCoef ψ x0 x1 d 0 1
  · subst hx1
    rw [Category.id_comp]; exact (overAt_hom_comp ψ x0).symm

end GlobalTheory
end
end
