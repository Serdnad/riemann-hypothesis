module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullbackValuationInvarianceOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.IntegralRingEmbedding

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftValuation

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem ros_snd_one (hG : GlobalFnsSt) (f g : D.toPre.P.A ⟶ D.toPre.P.A) [IsMonHom f] [IsMonHom g]
    (r : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A f g) rosatiε)) (hr : r.IsGen)
    (hr0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ r (zero2 D.toPre.P.A)) (LB.oneGen D.toPre.P.L))
    {T : Over (Spec (CommRingCat.of V))} {z : T.left} {J} (hJ : Good D.toPre.P.L z J) (y : T ⟶ D.toPre.P.A) :
    val₂ r z J y 1 = 1 := by
  have face (x y : T ⟶ D.toPre.P.A) : cubV D.toPre.cub z J 1 x y = 1 := by
    have h := val_corr hJ (D.toPre.cub.face 0) (lift x y).left
    rw [val_one] at h
    refine Eq.trans ?_ h
    refine Eq.trans ?_ (val_cub D.toPre.cub (lift x y) hJ (pzero D.toPre.P.A _) (x2 D.toPre.P.A 0) (x2 D.toPre.P.A 1)).symm
    congr 1 <;> simp [x2, pzero, Hom.one_def]
  have c11 (a : T ⟶ D.toPre.P.A) : cubV D.toPre.cub z J a 1 1 = 1 := by
    have h := (val_corr hJ D.toPre.cub.cubeSymmetric_swap_first (lift a (lift (1 : T ⟶ D.toPre.P.A) 1)).left).trans
      (val_cub D.toPre.cub (lift a (lift (1 : T ⟶ D.toPre.P.A) 1)) hJ _ _ _)
    refine h.trans ?_
    simpa [x3] using face a 1
  have h := (ros_add D.toPre.cub hG D.toPre.P.isAb f g r hr hr0 hJ 1 1 y).2
  rw [_root_.mul_one, MonObj.one_comp g, c11 y, c11 (y ≫ f), _root_.mul_one, _root_.one_mul] at h
  have h' : val₂ r z J y 1 * val₂ r z J y 1 = val₂ r z J y 1 * 1 := by
    rw [_root_.mul_one]; exact h.symm
  exact mul_left_cancel h'

private theorem formEq_sumElim_pullφ_rosatiφ (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (χ : D.toPre.X) :
    FormEq (Sum.elim (pullφ D F oa a 0) (fun j => (lift (cP D.toPre _ χ) (DegPre.prB D.toPre F)).left ≫
        rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a) j))
      (Sum.elim (pullε k N) rosatiε) (pullφ D F oa a χ) (pullε k N) := by
  intro U _ h
  haveI := oa.onB.hom a
  haveI := oa.onB.hom (star a)
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, pullφ, pullε]
  rw [prod_ros]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, DegPre.famφ, DegPre.famε, Matrix.cons_val_zero,
    Matrix.cons_val_succ, smul_zero]
  have E1 : (padd D.toPre.P.A (DegPre.prB D.toPre F) (toUnit _ ≫ D.toPre.c 0)).left =
      (DegPre.prB D.toPre F).left := by
    congr 1
    change DegPre.prB D.toPre F * cP D.toPre _ 0 = _
    rw [cPoint_zero, _root_.mul_one]
  have E2 : (toUnit (DegPre.BF D.toPre F) ≫ D.toPre.c 0).left =
      (toUnit (DegPre.BF D.toPre F) ≫ η[D.toPre.P.A]).left := by
    congr 1
    exact cPoint_zero (D := D.toPre) _
  have E5 : (cP D.toPre _ χ ≫ oa.onB.act (star a)).left =
      (toUnit (DegPre.BF D.toPre F) ≫ D.toPre.c (star a • χ)).left := by
    congr 1
    rw [oa.c_lin]
    simp [cP]
  have E4 : ((cP D.toPre _ χ ≫ oa.onB.act (star a)) * DegPre.prB D.toPre F).left =
      (padd D.toPre.P.A (DegPre.prB D.toPre F) (toUnit _ ≫ D.toPre.c (star a • χ))).left := by
    congr 1
    change _ = DegPre.prB D.toPre F * (toUnit _ ≫ D.toPre.c (star a • χ))
    rw [mul_comm]
    congr 1
    rw [oa.c_lin]
    simp [cP]
  have E6 : (cP D.toPre _ χ * (DegPre.prB D.toPre F ≫ oa.onB.act a)).left =
      (aF D F oa a).left ≫ (padd D.toPre.P.A (DegPre.prB D.toPre F) (toUnit _ ≫ D.toPre.c χ)).left := by
    rw [← Over.comp_left]
    congr 1
    change _ = aF D F oa a ≫ (DegPre.prB D.toPre F * (toUnit _ ≫ D.toPre.c χ))
    rw [mul_comm]
    first
    | rw [MonObj.comp_mul]
    | rw [comp_mul]
    | rw [Hom.comp_mul]
    simp [aF, cP]
  have E7 : (cP D.toPre (DegPre.BF D.toPre F) χ).left =
      (aF D F oa a).left ≫ (toUnit _ ≫ D.toPre.c χ).left := by
    rw [← Over.comp_left]
    congr 1
    simp [aF, cP]
  have E8 : (DegPre.prB D.toPre F ≫ oa.onB.act a).left = (aF D F oa a).left ≫ (DegPre.prB D.toPre F).left := by
    rw [← Over.comp_left]
    congr 1
    simp [aF]
  have E9 : (aF D F oa a).left ≫ (toUnit (DegPre.BF D.toPre F) ≫ η[D.toPre.P.A]).left =
      (toUnit (DegPre.BF D.toPre F) ≫ η[D.toPre.P.A]).left := by
    rw [← Over.comp_left]
    congr 1
    simp
  rw [E1, E2, E4, E5, E6, E7, E8, E9]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  abel

theorem pull_val_chi (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (χ : D.toPre.X)
    (u : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k N))) (hu : u.IsGen)
    (hc : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)))
    (u0 : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a 0) (pullε k N))) (hu0 : u0.IsGen)
    (hc0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u0 (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)))
    (r : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε))
    (hr : r.IsGen)
    (hr0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ r (zero2 D.toPre.P.A)) (LB.oneGen D.toPre.P.L))
    (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J) (hJ : Good D.toPre.P.L z J) :
    val u ρ z J = val u0 ρ z J *
      val (LB.pullGen D.toPre.P.L _ _ r (lift (cP D.toPre _ χ) (DegPre.prB D.toPre F)).left) ρ z J := by
  haveI := oa.onB.hom a
  haveI := oa.onB.hom (star a)
  refine (gen_unique' D.toPre.P.isLB (formEq_sumElim_pullφ_rosatiφ oa a k N χ) (fst (TF (R := V) F) D.toPre.P.A).left
    (DegPre.zF D.toPre F).left GC.zF_fst (surj_appTop (D := D.toPre) (F := F) hG) hu
    (mulGen_isGen _ _ _ _ _ _ _ hu0 (pullGen_isGen _ _ _ _ hr _)) ?_ Z ρ z J hJ).trans (val_mul hJ _ _ _)
  intro y J' hJ'
  rw [val_mul hJ']
  have e1 : val u (DegPre.zF D.toPre F).left y J' = val (LB.pullGen D.toPre.P.L _ _
      (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)) (𝟙 _) y J' := by
    rw [← Category.id_comp (DegPre.zF D.toPre F).left, ← val_pull hJ']
    exact val_corr hJ' hc _
  have e2 : val u0 (DegPre.zF D.toPre F).left y J' = val (LB.pullGen D.toPre.P.L _ _
      (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)) (𝟙 _) y J' := by
    rw [← Category.id_comp (DegPre.zF D.toPre F).left, ← val_pull hJ']
    exact val_corr hJ' hc0 _
  have hz : DegPre.zF D.toPre F ≫ lift (cP D.toPre _ χ) (DegPre.prB D.toPre F) =
      lift (cP D.toPre (TF (R := V) F) χ) 1 := by
    simp [DegPre.zF, cP, Hom.one_def]
  have e3 : val (LB.pullGen D.toPre.P.L _ _ r (lift (cP D.toPre _ χ) (DegPre.prB D.toPre F)).left)
      (DegPre.zF D.toPre F).left y J' = 1 := by
    rw [val_pull hJ', ← Over.comp_left, hz]
    exact ros_snd_one hG _ _ r hr hr0 hJ' _
  rw [e1, e2, e3]
  exact (_root_.mul_one _).symm
end CanonicalLiftValuation
end H1
end G
end ChartRestriction
end ReciprocityTheory
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

private theorem oneC_of_lemma {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (ζ : F) (s : Fam D F k) : Fam.IsSmul D F ζ s (ζ • s) := by
  intro α j
  rfl

private theorem oneC_of_lemma_2 {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (p : QkPt D F k) :
    ∃ w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)), w.IsGen :=
  ClosedPointWeilPower.gen_local_linComb (V := F) D.P.L D.P.isLB _ _

private theorem oneC_of_lemma_3 (F : Type) [Field F] (c : (Γ(Sp F, ⊤))ˣ) : ∃ z : Fˣ, unitOn z = c :=
  ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom c, by
    ext
    simp [unitOn]⟩

private theorem oneC_of_lemma_4 {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (s s' : Fam D F k)
    (h : ∀ α j, (s.s α).f j = (s'.s α).f j) : s = s' := by
  obtain ⟨s, hs⟩ := s
  obtain ⟨s', hs'⟩ := s'
  have key : ∀ α, s α = s' α := by
    intro α
    have hab : (s α).f = (s' α).f := funext (h α)
    revert hab
    generalize s α = a
    generalize s' α = b
    cases a
    cases b
    intro hab
    cases hab
    rfl
  have e : s = s' := funext key
  subst e
  rfl

private theorem oneC_of_lemma_5 {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (ζ : F) (s s' : Fam D F k) (h : Fam.IsSmul D F ζ s s') :
    s' = ζ • s :=
  oneC_of_lemma_4 D F k s' (ζ • s) fun α j => (h α j).trans (oneC_of_lemma D F k ζ s α j).symm

private theorem oneC_of_lemma_6 (F : Type) [Field F] (z : Fˣ) (n : ℕ) (h : unitOn z ^ n = 1) :
    (z : F) ^ n = 1 := by
  have key : ∀ u : Fˣ,
      Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom (unitOn u) = u := by
    intro u
    ext
    simp [unitOn]
  have e := congrArg (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom) h
  rw [map_pow, key, map_one] at e
  simpa using congrArg Units.val e

theorem oneC_of (hL : Laws) (hΦ : PhiFunStatement) (h1c : PositiveValuationMaximalIdeal) (h2 : PullbackValuationForwardBound)
    (h2f : DvrLevelFrame) (h3 : FiniteOrderValuationInvariance) (hU : UUStatement) (hE : FinOrdExistsStatement) (hB : AlphaBarEnumStatement)
    (hC : CanonLiftFixStatement) (hD : AlphaPairStatement) (hdim : DimSplitStatement) :
    OneCStatement := by
  intro E _ _ _ H V _ _ _ t P hT α N hN hαN hcop hNu ϖ hϖ Q hQ F _ _ _ v hv Dw I θ hθ hprim θα hpull s hs
  letI := H.starRing
  have hk : 1 ≤ 1 * N := by omega
  have hαN' : star α * α = (N : 𝓞 E) := by rw [_root_.mul_comm]; exact hαN

  have htor : ∀ (a b : 𝓞 E) (y : TFK (R := V) F ⟶ P.A.A), a * b = (N : 𝓞 E) →
      y ≫ P.oA.act b = 1 → y ^ (1 * N) = 1 := by
    intro a b y hab hy
    rw [_root_.one_mul, ← ClosedPointWeilPower.comp_act_nat P.oA.toRingAct y N hN, ← hab, P.oA.map_mul,
      ← Category.assoc, hy]
    exact ClosedPointWeilPower.one_comp_hom _ (P.oA.hom a)

  obtain ⟨p, x, hpx, hxα, hinj, -⟩ := hB E H V t P hT α N hN hαN hcop hNu F Dw I
  have hcop' : ∃ u u' : 𝓞 E, u * star α + u' * star (star α) = 1 := by
    obtain ⟨u, u', h⟩ := hcop
    exact ⟨u', u, by rw [star_star, _root_.add_comm]; exact h⟩
  obtain ⟨p', x', hpx', hxα', -, hsurj'⟩ :=
    hB E H V t P hT (star α) N hN (by rw [star_star]; exact hαN') hcop' hNu F Dw I
  have hxa : ∀ gm, x' gm ≫ P.oA.act α = 1 := fun gm => by simpa only [star_star] using hxα' gm
  obtain ⟨f, hfToA, -, -, -, -, hfW⟩ := hT F (1 * N) hk
  have hfp : ∀ i, x i = f (p i) := fun i => (hfToA (p i) (x i)).mp (hpx i)
  have hfq : ∀ gm, x' gm = f (p' gm) := fun gm => (hfToA (p' gm) (x' gm)).mp (hpx' gm)
  have htx : ∀ i, x i ^ (1 * N) = 1 := fun i => htor α (star α) (x i) hαN (hxα i)
  have htx' : ∀ gm, x' gm ^ (1 * N) = 1 := fun gm => htor (star α) α (x' gm) hαN' (hxa gm)

  have hw : ∀ b, ∃ w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F (p b).g.b)
      (DegPre.lineε (1 * N))), w.IsGen := fun b => oneC_of_lemma_2 P.D.toPre F (1 * N) (p b)
  choose w hwg using hw
  have hz : ∀ b, ∃ ζ : F, ζ ≠ 0 ∧ FinOrd P.D F (1 * N) (p b) (w b) ζ :=
    fun b => hE V P.D F (1 * N) hk (p b) (w b) (hwg b)
  choose ζ hζ0 hfin using hz
  choose Φ hΦb using fun b => hΦ V (maximalIdeal V) P.D F (1 * N) hk (p b) (w b) (hwg b)
  choose wq hwqg hwq1 hfix using fun gm =>
    hC E H V t P hT α N hN hαN hcop hNu F θ θα hpull (p' gm) (x' gm) (hpx' gm) (hxa gm)
  choose Φq hΦq using fun gm => hΦ V (maximalIdeal V) P.D F (1 * N) hk (p' gm) (wq gm) (hwqg gm)

  have hWex : ∀ i gm, ∃ z : Fˣ, WeilIs P.A.A P.A.L ((1 * N : ℕ) : ℤ) (x' gm) (x i) (unitOn z) := by
    intro i gm
    obtain ⟨c, hc, -⟩ := (hL.weil _ P.A (1 * N) _).1 (x' gm) (x i) (htx' gm) (htx i)
    obtain ⟨z, rfl⟩ := oneC_of_lemma_3 F c
    exact ⟨z, hc⟩
  choose χz hχz using hWex
  have hEig : ∀ i gm, Φq gm (Φ i θα) = (χz i gm : F) • Φ i θα := by
    intro i gm
    apply oneC_of_lemma_5
    have hW' : WeilQkIs P.D.toPre F (1 * N) (p' gm) (p i) (χz i gm) :=
      (hfW (p' gm) (p i) (χz i gm)).mpr (by rw [← hfq gm, ← hfp i]; exact hχz i gm)
    exact hW' (wq gm) (w i) (hwqg gm) (hwg i) θα (Φ i θα) (Φq gm (Φ i θα)) θα (Φ i θα)
      ((hΦb i θα _).mpr rfl) ((hΦq gm (Φ i θα) _).mpr rfl) (hfix gm) ((hΦb i θα _).mpr rfl)

  have hvN : v (((1 * N : ℕ)) : F) = 0 := by
    have h := hv ((N : ℕ) : FractionRing V) 0 ⟨hNu.unit, by simp⟩
    simpa using h
  have hπ : ∃ π : F, 0 < v π := by
    refine ⟨algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ), ?_⟩
    rw [hv _ 1 ⟨1, by simp⟩]
    exact_mod_cast (show (0 : ℚ) < ((1 : ℤ) : ℚ) by norm_num)

  have hθα0 : NuGe P.D Q F v (1 * N) θα 0 :=
    h2 V ϖ hϖ P.D Q hQ F v hv (𝓞 E) P.oD H.w0 P.w0 α N hN hαN hαN' 1 le_rfl θ θα hpull 0 hθ
  have hsm1 : ∀ {k : ℕ} (u : Fam P.D.toPre F k), Fam.IsSmul P.D.toPre F 1 u u := by
    intro k u
    have h := oneC_of_lemma P.D.toPre F k 1 u
    rwa [one_smul] at h
  have hnotpos : ∀ r : ℚ, 0 < r → ¬ NuGe P.D Q F v (1 * N) θα r := by
    intro r hr h
    obtain ⟨σ, σF, hscal, hσ, hnd⟩ := hprim
    have hb := h2f V ϖ hϖ P.D Q hQ F v hv (𝓞 E) P.oD H.w0 P.w0 α N hN hαN 1 le_rfl θ θα hpull 0
      σ σF 1 hscal (fun j => by rw [← hσ j]; exact hsm1 θ 0 j) hnd r h
    rw [AddValuation.map_one, QForm.Q_zero hϖ P.D hQ] at hb
    have h' : ((r : ℚ) : WithTop ℚ) ≤ ((0 : ℚ) : WithTop ℚ) := by simpa using hb
    have := WithTop.coe_le_coe.mp h'
    linarith
  have hN3 : ∀ i r, NuGe P.D Q F v (1 * N) θα r ↔ NuGe P.D Q F v (1 * N) (ζ i • Φ i θα) r :=
    fun i r => h3 V ϖ hϖ P.D Q hQ F v hv (1 * N) hk (p i) (w i) (hwg i) (ζ i) (hζ0 i) (hfin i)
      θα (Φ i θα) (ζ i • Φ i θα) ((hΦb i θα _).mpr rfl) (oneC_of_lemma _ _ _ _ _) r

  obtain ⟨bb, hbli, -, hbspan⟩ := hU V ϖ hϖ P.D Q hQ F v hv (Or.inl inferInstance) (1 * N) hk
  have hcard : Fintype.card (Fin (N ^ P.A.g)) = (1 * N) ^ (P.D.toPre.rank + P.D.toPre.P.g) := by
    rw [Fintype.card_fin, hdim E H V t P, _root_.one_mul]
  obtain ⟨a, ha0, hsa⟩ := IntegralRingEmbedding.span_of_eigen (F := F) (v := v) (b := bb) (n := _)
    (fun u => NuGe P.D Q F v (1 * N) u 0) (fun u => ∃ r : ℚ, 0 < r ∧ NuGe P.D Q F v (1 * N) u r)
    hbli hbspan
    (fun s0 hs0 ζ0 s' hζ hs' he => (h1c V ϖ hϖ P.D Q hQ F v hv (1 * N) hk s0 hs0).mpr
      ⟨ζ0, s', hζ, hs', by rw [he]; exact oneC_of_lemma _ _ _ ζ0 s'⟩)
    hπ hcard (fun i => ζ i • Φ i θα) (fun i => (hN3 i 0).mp hθα0)
    (fun i hp => by
      obtain ⟨r, hr, hr'⟩ := hp
      exact hnotpos r hr ((hN3 i r).mpr hr'))
    Φq
    (fun gm s0 hs0 => (h3 V ϖ hϖ P.D Q hQ F v hv (1 * N) hk (p' gm) (wq gm) (hwqg gm) 1 one_ne_zero
      (hwq1 gm) s0 (Φq gm s0) (Φq gm s0) ((hΦq gm s0 _).mpr rfl) (hsm1 _) 0).mp hs0)
    hk hvN (fun i gm => (χz i gm : F))
    (fun i gm => oneC_of_lemma_6 F (χz i gm) (1 * N)
      (ClosedPointWeilPower.weil_pow_eq_one hL.weil P.A (1 * N) (x' gm) (x i) (htx' gm) (htx i) _ (hχz i gm)))
    (fun i gm => by
      show Φq gm (ζ i • Φ i θα) = (χz i gm : F) • (ζ i • Φ i θα)
      rw [map_smul, hEig i gm, smul_comm])
    (fun i j hij => by
      obtain ⟨z, hz, c, c', hc, hc', hne⟩ := hD E H V t P hT α N hN hαN hcop hNu F Dw I (x i) (x j)
        (hxα i) (hxα j) (fun h => hij (hinj h))
      obtain ⟨gm, rfl⟩ := hsurj' z (by rw [star_star]; exact hz)
      refine ⟨gm, fun heq => hne ?_⟩
      have hc1 : WeilIs P.A.A P.A.L ((1 * N : ℕ) : ℤ) (x' gm) (x i) c := by rw [_root_.one_mul]; exact hc
      have hc1' : WeilIs P.A.A P.A.L ((1 * N : ℕ) : ℤ) (x' gm) (x j) c' := by
        rw [_root_.one_mul]; exact hc'
      rw [ClosedPointWeilPower.weil_unique hL.weil P.A (1 * N) (x' gm) (x i) (htx' gm) (htx i) _ _ hc1 (hχz i gm),
        ClosedPointWeilPower.weil_unique hL.weil P.A (1 * N) (x' gm) (x j) (htx' gm) (htx j) _ _ hc1' (hχz j gm),
        Units.ext heq])
    s hs
  exact ⟨N ^ P.A.g, p, x, w, ζ, fun i => ζ i • Φ i θα, a, hpx, hxα, fun i => ⟨hwg i, hζ0 i, hfin i⟩,
    fun i => ⟨Φ i θα, (hΦb i θα _).mpr rfl, oneC_of_lemma _ _ _ _ _⟩, ha0, hsa⟩

end ReciprocityTheory.ChartRestriction.G.H1
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftTraces

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem comp_famφ {T : Over (Spec (CommRingCat.of V))} (X : T ⟶ DegPre.BF D.toPre F) (ξ : D.toPre.X) (i : Fin 4) :
    X.left ≫ DegPre.famφ D.toPre F ξ i =
      (![X ≫ DegPre.prB D.toPre F, (X ≫ DegPre.prB D.toPre F) * cP D.toPre T ξ, cP D.toPre T ξ, 1] i).left := by
  fin_cases i
  · simp [DegPre.famφ]
  · show X.left ≫ (DegPre.prB D.toPre F * (toUnit _ ≫ D.toPre.c ξ)).left =
      ((X ≫ DegPre.prB D.toPre F) * cP D.toPre T ξ).left
    rw [← Over.comp_left, comp_mul, ← Category.assoc, comp_toUnit]
    rfl
  · show X.left ≫ (toUnit _ ≫ D.toPre.c ξ).left = (cP D.toPre T ξ).left
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
    rfl
  · show X.left ≫ (toUnit _ ≫ η[D.toPre.P.A]).left = (1 : T ⟶ D.toPre.P.A).left
    rw [← Over.comp_left, ← Hom.one_def, comp_one]

theorem zF_tr_pr (b : TF (R := V) F ⟶ D.toPre.P.A) :
    (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b) ≫ DegPre.prB D.toPre F = b := by
  simp [DegPre.trPt, DegPre.zF, DegPre.prB, padd, ← Hom.mul_def, ← Hom.one_def, comp_mul]

theorem zF_aF (oa : D.toPre.OAct O) (a : O) : DegPre.zF D.toPre F ≫ aF D F oa a = DegPre.zF D.toPre F := by
  haveI := oa.onB.hom a
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [aF, DegPre.zF, DegPre.prB, IsMonHom.one_hom]

theorem exists_w (oa : D.toPre.OAct O) (a : O) (N : ℕ) (hN : 1 ≤ N) (b : TF (R := V) F ⟶ D.toPre.P.A)
    (z : D.toPre.X) (hb : b ≫ oa.onB.act a = cP D.toPre _ (-z))
    (u0 : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a 0) (pullε 1 N))) (hu0 : u0.IsGen) :
    ∃ w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F b) (DegPre.lineε (1 * N))), w.IsGen ∧
      ∀ (y : (TF (R := V) F).left) J, Good D.toPre.P.L y J → val w (𝟙 (TF (R := V) F).left) y J =
        val (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (1 * (N - 1))) (jFK (R := V) F))
            (𝟙 (TF (R := V) F).left) y J *
          val (LB.pullGen D.toPre.P.L _ _ (LB.mulGen D.toPre.P.L _ _ _ _
            (GeneratorPullback.powGen D.toPre.P.L _ _ (D.toPre.psi (-z)) 1) (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK 1))
              (jFK (R := V) F)) (𝟙 (TF (R := V) F).left) y J *
          (val u0 (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b).left y J)⁻¹ := by
  have := oa.onB.hom a
  have h1 : (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b) ≫ DegPre.prB D.toPre F = b := zF_tr_pr b
  have h2 : ((DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b) ≫ aF D F oa a) ≫ DegPre.prB D.toPre F =
      cP D.toPre _ (-z) := by
    rw [Category.assoc, show aF D F oa a ≫ DegPre.prB D.toPre F = DegPre.prB D.toPre F ≫ oa.onB.act a by
      simp [aF, DegPre.prB], ← Category.assoc, h1, hb]
  have e2 : ∀ i, (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b).left ≫ (aF D F oa a).left ≫
      DegPre.famφ D.toPre F 0 i = ((DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b) ≫ aF D F oa a).left ≫
      DegPre.famφ D.toPre F 0 i := fun i => by rw [← Category.assoc, ← Over.comp_left]
  have c0 : cP D.toPre (TF (R := V) F) 0 = 1 := cPoint_zero _
  have p0 : (DegPre.zeroF D.toPre F).left = (1 : TF (R := V) F ⟶ D.toPre.P.A).left := rfl
  have p1 : jFK (R := V) F ≫ (toUnit (TK V)).left ≫ eSec D.toPre.P.A = (1 : TF (R := V) F ⟶ D.toPre.P.A).left :=
    (Category.assoc _ _ _).symm
  have p2 : jFK (R := V) F ≫ D.toPre.xK (-z) = (cP D.toPre (TF (R := V) F) (-z)).left := (Category.assoc _ _ _).symm
  have hN' : ((1 * (N - 1) : ℕ) : ℤ) = ((1 * N : ℕ) : ℤ) - 1 := by omega
  obtain ⟨w, hw, hv⟩ := exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre F b) (ε' := DegPre.lineε (1 * N))
    (fun U _ h => by
      simp only [pullφ, pullε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, e2, p1, p2]
      simp only [comp_famφ, h1, h2, Fin.prod_univ_four, Fin.prod_univ_two, Matrix.cons_val, DegPre.famε, smul_zero, c0,
        _root_.mul_one, DegPre.lineφ, DegPre.lineε, p0, hN']
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      push_cast
      module)
    (LB.mulGen D.toPre.P.L _ _ _ _ (LB.mulGen D.toPre.P.L _ _ _ _
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (1 * (N - 1))) (jFK (R := V) F))
      (LB.pullGen D.toPre.P.L _ _ (LB.mulGen D.toPre.P.L _ _ _ _
        (GeneratorPullback.powGen D.toPre.P.L _ _ (D.toPre.psi (-z)) 1) (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK 1)) (jFK (R := V) F)))
      (LB.invGen D.toPre.P.L _ _ (LB.pullGen D.toPre.P.L _ _ u0 (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b).left)))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _
      (pullGen_isGen _ _ _ _ (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.toPre.rig_gen _) _) _)
      (pullGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ (D.toPre.psi_gen _) _)
        (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.toPre.rig_gen _) _)) _))
      (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hu0 _)))
  refine ⟨w, hw, fun y J hJ => ?_⟩
  rw [hv _ _ y J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ u0, Category.id_comp]
end CanonicalLiftTraces
end H1
end G
end ChartRestriction
end ReciprocityTheory
end
end
