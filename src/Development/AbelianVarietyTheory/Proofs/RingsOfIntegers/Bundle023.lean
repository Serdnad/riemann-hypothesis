module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ThetaGrpActIterateEqOfPowEqOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle016
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle018
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle020
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInOfIsPullDeg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ThetaNu

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

private theorem units_mul_eq_mul_of_eq_mul {R : Type*} [CommRing R] (a b c : Rˣ) (x y : R) (h : x = y * c) :
    (a : R) * x = ((a * b⁻¹ * c : Rˣ) : R) * ((b : R) * y) := by
  rw [h, Units.val_mul, Units.val_mul]
  have hb : ((b⁻¹ : Rˣ) : R) * b = 1 := Units.inv_mul b
  linear_combination (-((a : R) * c * y)) * hb

theorem isActOf_of_sval {L : LB A.left} (hL : L.IsLB) {k : ℤ} {T : Over S} {θ : ThetaGrp A L k T}
    {s s' : LB.Sec (LPow A L k T)}
    (h : ∀ y J, Good L y J → sval (L := L) s' (𝟙 _) y J =
      sval (L := L) s (𝟙 _ ≫ (translT A θ.pt).left) y J * (val (L := L) θ.φ (𝟙 _) y J).val) :
    IsActOf A L k θ s s' := by
  have hcomp : (translT A θ.pt).left ≫ (snd T A).left = (translPt A θ.pt).left := by
    rw [← Over.comp_left]
    unfold translT
    simp
  intro j
  refine fn_ext fun x hx => ?_
  obtain ⟨J, hJ, -⟩ := exists_good L hL x (K := Empty) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim)
    (fun e => e.elim)
  have hx0 : x ∈ L.wchart (fun _ : Fin 1 => (snd T A).left) (fun _ => j 0) :=
    Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx 0
  have hx1 : (𝟙 _ ≫ (translT A θ.pt).left) x ∈ L.wchart (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1) := by
    refine Set.mem_iInter.2 fun _ => ?_
    have h1 := Set.mem_iInter.1 hx 1
    simpa [← hcomp] using h1
  have e1 := sec_trans s' (𝟙 _) x hx0 (hJ.mem _ (𝟙 _))
  have e2 := sec_trans s (𝟙 _ ≫ (translT A θ.pt).left) x hx1 (hJ.mem _ _)
  have e3 := gen_trans θ.isGen (𝟙 _) x hx (hJ.mem _ (𝟙 _))
  have key := h x J hJ
  unfold sval val at key
  refine (gs_res (𝟙 _) x _ hx _).trans (e1.trans ?_)
  refine Eq.trans ?_ (gs_mul (𝟙 _) x _ hx _ _).symm
  refine Eq.trans ?_ (congrArg₂ (· * ·) (gs_unit (𝟙 _) x _ hx _)
    ((gs_res (𝟙 _) x _ hx _).trans (gs_pull _ _ x _ hx1 _))).symm
  rw [e2, e3]
  have htr : trF ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] (𝟙 _) x j
        (fun i => J (𝟙 _ ≫ ![(snd T A).left, (translPt A θ.pt).left] i)) =
      trF (fun _ : Fin 1 => (snd T A).left) (fun _ => k) (𝟙 _) x (fun _ => j 0) (fun _ => J (𝟙 _ ≫ (snd T A).left)) *
        (trF (fun _ : Fin 1 => (snd T A).left) (fun _ => k) (𝟙 _ ≫ (translT A θ.pt).left) x (fun _ => j 1)
          (fun _ => J ((𝟙 _ ≫ (translT A θ.pt).left) ≫ (snd T A).left)))⁻¹ := by
    simp only [trF, Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      zpow_neg, Category.assoc, hcomp]
    rw [show J ((𝟙 _ ≫ (translT A θ.pt).left) ≫ (snd T A).left) = J (𝟙 _ ≫ (translPt A θ.pt).left) by
      rw [Category.assoc, hcomp]]
    rfl
  rw [htr]
  exact units_mul_eq_mul_of_eq_mul _ _ _ _ _ key

theorem exists_isActOf {L : LB A.left} (hL : L.IsLB) {k : ℤ} {T : Over S} (θ : ThetaGrp A L k T)
    (s : LB.Sec (LPow A L k T)) : ∃ s', IsActOf A L k θ s s' := by
  have hcomp : (translT A θ.pt).left ≫ (snd T A).left = (translPt A θ.pt).left := by
    rw [← Over.comp_left]
    unfold translT
    simp
  have hform : FormEq (Sum.elim (fun _ : Fin 1 => (translT A θ.pt).left ≫ (snd T A).left)
      ![(snd T A).left, (translPt A θ.pt).left]) (Sum.elim (fun _ => k) ![k, -k])
      (fun _ : Fin 1 => (snd T A).left) (fun _ => k) := by
    intro U _ h
    simp only [Fintype.prod_sum_type, Finset.univ_unique, Finset.prod_singleton, Sum.elim_inl, Sum.elim_inr,
      Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, hcomp]
    rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]
  obtain ⟨s₁, hs₁⟩ := exists_sec hL hform (pullMulSec s (translT A θ.pt).left θ.φ θ.isGen)
  refine ⟨s₁, isActOf_of_sval hL fun y J hJ => ?_⟩
  rw [hs₁ _ _ y J hJ]
  exact sval_pullMulSec _ _ _ _ _ _ hJ

end GlobalTheory.ThetaNu

namespace GlobalTheory


open ThetaNu in
theorem nuGe_iff_of_isActOf_of_pow_eq_one : Laws → TWStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t₀ : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t₀), P.TorsionIso → Geo.Tor.ExpBijF P.U.toUnifPre → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (k : ℕ), 1 ≤ k → ∀ (w : LB.Iso (P.A.L.pull P.U.gen.hom.left) (P.U.LG.L.pull (pullback.fst t₀.G.hom (jK V)))), w.IsGen → ∀ (θ : ThetaGrp P.A.A P.A.L (k : ℤ) (TFK (R := V) F)) (n : ℕ), 1 ≤ n → θ.pt ^ k = 1 → θ.pt ^ n = 1 → LB.Gen.Corr P.A.L _ _ _ _ (Out.powGen P.A.A P.A.L (k : ℤ) θ n) (LB.oneGen P.A.L) → ∀ (t t' : LB.Sec (LPow P.A.A P.A.L (k : ℤ) (TFK (R := V) F))) (s s' : Fam P.D.toPre F k), P.U.ExpandsF F k w t s → P.U.ExpandsF F k w t' s' → IsActOf P.A.A P.A.L (k : ℤ) θ t t' → ∀ r : ℚ, NuGe P.D Q F v k s r ↔ NuGe P.D Q F v k s' r := by
  intro hLaws hTW V _ _ _ ϖ hϖ E _ _ _ H t₀ P hTI hEB Q hQ F _ _ _ v hv k hk w hw θ n hn hθk hθn hc t t' s s' hs hs'
    hact r

  obtain ⟨f, hf, hsurj, -⟩ := hTI F k hk
  obtain ⟨p, hp⟩ := hsurj θ.pt hθk
  have hpt := (hf p θ.pt).2 hp.symm
  unfold Geo.Tor.PELUnif.ToA QkToAkU QkToAk at hpt
  obtain ⟨w₁, hw₁, hΦ⟩ := (hpt w hw).2 θ rfl

  obtain ⟨c, hTWc⟩ := hTW V ϖ hϖ P.D Q hQ F v hv k hk p w₁ hw₁ 1 one_ne_zero
  have step : ∀ (u u' : LB.Sec (LPow P.A.A P.A.L (k : ℤ) (TFK (R := V) F))) (e e' : Fam P.D.toPre F k),
      P.U.ExpandsF F k w u e → P.U.ExpandsF F k w u' e' → IsActOf P.A.A P.A.L (k : ℤ) θ u u' →
      ∀ q : ℚ, NuGe P.D Q F v k e q ↔ NuGe P.D Q F v k e' (q + c) := fun u u' e e' he he' ha q =>
    hTWc e e' e' (hΦ u u' e e' he he' ha) ((ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff 1 e' e').2 (one_smul F e').symm) q

  have hL : P.A.L.IsLB := P.A.isLB
  choose g hg using fun u => exists_isActOf hL θ u
  have horb : ∀ m : ℕ, IsActOf P.A.A P.A.L (k : ℤ) θ (g^[m] t) (g^[m + 1] t) := fun m => by
    rw [Function.iterate_succ_apply']
    exact hg _
  have hexp := hEB F k hk w hw
  choose e he using fun m : ℕ => (hexp.1 (g^[m] t)).exists
  have hshift : ∀ (m : ℕ) (q : ℚ), NuGe P.D Q F v k (e 0) q ↔ NuGe P.D Q F v k (e m) (q + m * c) := by
    intro m
    induction m with
    | zero => intro q; simp
    | succ m ih =>
      intro q
      rw [ih q, step _ _ _ _ (he m) (he (m + 1)) (horb m)]
      push_cast
      ring_nf

  have hback : g^[n] t = t := by
    have hf := thetaGrp_act_iterate_eq_of_pow_eq_one _ P.A.A P.A.L hL (k : ℤ) (TFK (R := V) F) θ n hθn hc
      (fun i => g^[i] t) (fun i => by simpa using horb i)
    generalize hu : g^[n] t = u at hf
    simp only [Fin.val_last, Fin.val_zero, hu, Function.iterate_zero, id] at hf
    obtain ⟨uf, uc⟩ := u
    obtain ⟨tf, tc⟩ := t
    obtain rfl : uf = tf := funext hf
    rfl
  have he0 : e 0 = s := (hexp.1 t).unique (he 0) hs
  have hen : e n = s := (hexp.1 t).unique (by rw [← hback]; exact he n) hs
  have hper : ∀ q : ℚ, NuGe P.D Q F v k s q ↔ NuGe P.D Q F v k s (q + n * c) := by
    intro q
    rw [← he0, hshift n q, he0, hen]

  have hmono : ∀ q q' : ℚ, q' ≤ q → NuGe P.D Q F v k s q → NuGe P.D Q F v k s q' := by
    intro q q' hqq h χ
    obtain ⟨m, a, σ, σF, h1, h2, h3⟩ := h χ
    exact ⟨m, a, σ, σF, h1, fun i => le_trans (WithTop.coe_le_coe.2 (by linarith)) (h2 i), h3⟩
  have hs's : NuGe P.D Q F v k s (r - c) ↔ NuGe P.D Q F v k s' r := by
    simpa using step t t' s s' hs hs' hact (r - c)
  rw [← hs's]
  by_cases hc0 : c = 0
  · simp [hc0]
  · have hd : (n : ℚ) * c ≠ 0 := mul_ne_zero (by exact_mod_cast (show n ≠ 0 by omega)) hc0
    exact ⟨fun h => PeriodicValuation.all_of_periodic hmono hd hper r _ h, fun h => PeriodicValuation.all_of_periodic hmono hd hper _ r h⟩

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.TauBimultBox

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.TauBalBox

theorem val_lhs {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {y : (TK R).left} {J} (hJ : Good D.P.L y J)
    (a a' b : D.X) :
    val (LB.mulGen D.P.L _ _ _ _ (D.tau (a + a') b)
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b))) (𝟙 _) y J =
      val (D.tau (a + a') b) (𝟙 _) y J * cubV D.cub y J (cP D (TK R) a) (cP D (TK R) a') (cP D (TK R) b) := by
  refine (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ?_)
  refine (val_cub D.cub (𝟙 (TK R)) hJ (cP D _ a) (cP D _ a') (cP D _ b)).trans ?_
  rw [Category.id_comp, Category.id_comp, Category.id_comp]

theorem tauBimult_pow : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j), D.TauBimult → D'.TauBimult := by
  intro hG R _ _ j D D' pD hB a a' b
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
  have key : cubV D'.cub y J' (cP D' (TK R) a) (cP D' (TK R) a') (cP D' (TK R) b) *
      (om pD.w y J J' (cP D' (TK R) a * cP D' (TK R) a' * cP D' (TK R) b).left *
        (om pD.w y J J' (cP D' (TK R) a * cP D' (TK R) a').left)⁻¹ *
        (om pD.w y J J' (cP D' (TK R) a * cP D' (TK R) b).left)⁻¹ *
        (om pD.w y J J' (cP D' (TK R) a' * cP D' (TK R) b).left)⁻¹ *
        om pD.w y J J' (cP D' (TK R) a).left * om pD.w y J J' (cP D' (TK R) a').left *
        om pD.w y J J' (cP D' (TK R) b).left *
        (om pD.w y J J' (1 : TK R ⟶ D'.P.A).left)⁻¹) = _ :=
    GlobalTheory.CubBox.cubV_box hG R j D D' pD (TK R) y J J' hJ hJ' _ _ _
  have o : (1 : TK R ⟶ D'.P.A).left = 𝟙 _ ≫ (toUnit (TK R)).left ≫ eSec D'.P.A := (Category.id_comp _).symm
  rw [o] at key
  have t₁ := tau_box pD hJ hJ' (a + a') b
  have t₂ := tau_box pD hJ hJ' a b
  have t₃ := tau_box pD hJ hJ' a' b
  rw [cPoint_add] at t₁
  have e : ∀ i, val (D.tau (pD.xe (a + a') i) (pD.xe b i)) (𝟙 _) y J *
      cubV D.cub y J (cP D' (TK R) a ≫ pD.pw.pr i) (cP D' (TK R) a' ≫ pD.pw.pr i) (cP D' (TK R) b ≫ pD.pw.pr i) =
      val (D.tau (pD.xe a i) (pD.xe b i)) (𝟙 _) y J * val (D.tau (pD.xe a' i) (pD.xe b i)) (𝟙 _) y J := fun i => by
    have := (val_lhs D hJ _ _ _).symm.trans
      ((val_corr hJ (hB (pD.xe a i) (pD.xe a' i) (pD.xe b i)) (𝟙 _)).trans (val_mul hJ _ _ _))
    rw [show pD.xe (a + a') i = pD.xe a i + pD.xe a' i by rw [map_add (f := _)]; rfl, cP, cP, cP, Category.assoc,
      Category.assoc, Category.assoc, pD.c_pr, pD.c_pr, pD.c_pr]
    exact this
  have E := (Finset.prod_mul_distrib).symm.trans ((Finset.prod_congr rfl fun i (_ : i ∈ Finset.univ) => e i).trans
    Finset.prod_mul_distrib)
  rw [← t₁, ← t₂, ← t₃, ← key] at E
  refine (val_lhs D' hJ' a a' b).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)
  have E' := congrArg Additive.ofMul E
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at E' ⊢
  rw [← sub_eq_zero] at E' ⊢
  refine Eq.trans ?_ E'
  abel

end GlobalTheory.TauBimultBox
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace PsiInProd

theorem map_ideal_prod {A B K : Type} [CommRing A] [CommRing B] [Fintype K] (f : A →+* B) (J : K → Ideal A) :
    (∏ i, J i).map f = ∏ i, (J i).map f :=
  map_prod (Ideal.mapHom f) J Finset.univ

end PsiInProd


open PsiInPull PsiInPow PsiInProd in
theorem psiIn_prod_of_isPowDeg : ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R)
    (pD : IsPowDeg D' D j) (x : D'.X) (J : Fin j → Ideal R),
    (∀ i, D.PsiIn (pD.xe x i) (J i)) → D'.PsiIn x (∏ i, J i) := by
  intro R _ _ j D D' pD χ J H
  classical
  refine psiIn_of_gs D' χ _ fun q V' hV' hle' z hz => exists_of_locally _ z _ V' hV' hz fun v hv => ?_
  have : IsDominant (jK R) := isDominant_jK
  choose pick hpk using fun p : Spec (CommRingCat.of R) ⟶ D.P.A.left => exists_chart D.P.isLB (p v)
  have hcp : ∀ i, (D'.c χ).left ≫ (pD.pw.pr i).left = (D.c (pD.xe χ i)).left := fun i =>
    congrArg (fun m => m.left) (pD.c_pr χ i)
  have hxp : ∀ i, D'.xK χ ≫ (pD.pw.pr i).left = D.xK (pD.xe χ i) := fun i =>
    (Category.assoc (jK R) _ _).trans (congrArg (jK R ≫ ·) (hcp i))
  let p : Fin j → D.P.L.ι := fun i => pick (D.c (pD.xe χ i)).left
  obtain ⟨_, ⟨V, hV, rfl⟩, hvV, hVp⟩ := (Spec (CommRingCat.of R)).isBasis_affineOpens.exists_subset_of_mem_open
    (show v ∈ (V' ⊓ LB.wchart D.P.L (fun i => (D.c (pD.xe χ i)).left) p : (Spec (CommRingCat.of R)).Opens) from
      ⟨hv, Set.mem_iInter.2 fun i => hpk _⟩)
    (V' ⊓ LB.wchart D.P.L (fun i => (D.c (pD.xe χ i)).left) p : (Spec (CommRingCat.of R)).Opens).isOpen
  have hVV : V ≤ V' := fun y hy => (hVp hy).1
  have hVi : ∀ i, V ≤ (D.c (pD.xe χ i)).left ⁻¹ᵁ D.P.L.U (p i) := fun i y hy => Set.mem_iInter.1 (hVp hy).2 i
  have hzV : jK R z ∈ V := jK_mem z _ (fun h0 => (h0.le hvV : v ∈ (⊥ : (Spec (CommRingCat.of R)).Opens)))
  choose r hr er using fun i => gs_of_psiIn D _ _ (H i) (p i) V hV (hVi i) z hzV
  obtain ⟨I, hI, eI⟩ := exists_good D.P.L D.P.isLB (Z := (TK R).left) z (fun i => D.xK (pD.xe χ i)) p
    (fun a b h => congrArg pick (ext_of_isDominant_of_isSeparated (X := Spec (CommRingCat.of R)) D.P.A.hom
      ((Over.w (D.c (pD.xe χ a))).trans (Over.w (D.c (pD.xe χ b))).symm) (jK R) h))
    (fun i => hVi i hzV)
  obtain ⟨I', hI', eI'⟩ := exists_good D'.P.L D'.P.isLB (Z := (TK R).left) z (K := PUnit) (fun _ => D'.xK χ)
    (fun _ => q) (fun _ _ _ => rfl) (fun _ => hle' hz)
  have e0 : I' (D'.xK χ) = q := eI' PUnit.unit
  obtain ⟨b, hb, hcorr⟩ := pD.w_psi χ
  have e1 := QBox.mapsAt_val pD.w _ _ _ b hb z hI hI'
  have e2 := (val_corr hI hcorr (𝟙 _)).trans (QBox.val_finProdGen _ _ _ _ _ hI)
  have ep : (fun i => I (D'.xK χ ≫ (pD.pw.pr i).left)) = p := funext fun i => (congrArg I (hxp i)).trans (eI i)
  rw [ep, e0, zpow_neg_one, eq_inv_mul_iff_mul_eq, e2,
    val_of (D'.psi χ) _ z I' (fun _ => q) (fun _ => (congrArg I' (Category.id_comp _)).trans e0)] at e1
  have hU : V ≤ (D'.c χ).left ⁻¹ᵁ (LB.wchart D.P.L (fun i => (pD.pw.pr i).left) p ⊓ D'.P.L.U q) := fun y hy =>
    ⟨Set.mem_iInter.2 fun i => (congrArg (fun m => m y ∈ D.P.L.U (p i)) (hcp i)).mpr (hVi i hy), hle' (hVV hy)⟩
  refine ⟨V, hVV, hvV, (res hU (pullU (D'.c χ).left _ (pD.w.s (p, q)))).val * ∏ i, r i,
    Ideal.mul_mem_left _ _ ?_, ?_⟩
  · rw [map_ideal_prod]
    exact Ideal.prod_mem_prod fun i _ => hr i
  · refine Eq.trans ?_ (congrArg Units.val e1)
    refine (gs_mul _ _ _ hzV _ _).trans (congrArg₂ (· * ·) ?_ ?_)
    · exact (gs_unit _ _ _ hzV _).trans (congrArg Units.val ((gm_res _ _ hU hzV _).trans
        (gm_pull (jK R) (D'.c χ).left z _ (hU hzV) _)))
    · rw [gs_prod _ _ _ hzV, Units.coe_prod]
      refine Finset.prod_congr rfl fun i _ => (er i).trans (congrArg Units.val ?_)
      exact (val_of (D.psi (pD.xe χ i)) _ z I (fun _ => p i) (fun _ => (congrArg I (Category.id_comp _)).trans (eI i))).symm

end GlobalTheory
end
end
