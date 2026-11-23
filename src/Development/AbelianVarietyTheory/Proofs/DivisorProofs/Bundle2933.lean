module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2680
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle815
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle112
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1574
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle004
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle072
import Development.AbelianVarietyTheory.Definitions.Divisors.LeTwoMulOfForallScale
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1914
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.PsiMono
variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]

def fracPt (ρ : V →+* V₁) (hρ : Function.Injective ρ) : (TK V₁).left ⟶ (TK V).left :=
  spMap (IsFractionRing.map (K := FractionRing V) (L := FractionRing V₁) hρ)

theorem fracPt_comp (ρ : V →+* V₁) (hρ : Function.Injective ρ) : fracPt ρ hρ ≫ jK V = jK V₁ ≫ spMap ρ := by
  simp only [fracPt, spMap, jK, TK, Over.mk_hom, ← Spec.map_comp]
  congr 1
  ext x
  simp [IsFractionRing.map, IsLocalization.map_eq]

theorem gm_spMap_unitOn {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (z : Sp R') (k : Rˣ) :
    gm (spMap f) z ⊤ (unitOn k) = gm (𝟙 _) z ⊤ (unitOn (Units.map f.toMonoidHom k)) := by
  have h := gm_pull (𝟙 _) (spMap f) z ⊤ trivial (unitOn k)
  rw [Category.id_comp] at h
  refine h.symm.trans (congrArg _ ?_)
  ext
  have e := congrArg (fun g => g.hom (k : R)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [unitOn, pullU, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  exact e.symm

theorem val_scaleGen {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (c : Γ(Y, ⊤)ˣ) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val (scaleGen t c) r z J = gm r z ⊤ c * val t r z J :=
  gm_scaleGen t c r z _ (hJ.mem φ r)

theorem prod_zpow_swap {F : Type} [Field F] {I C : Type} [Fintype I] [Fintype C] (x : I → F) (e : C → I → ℤ)
    (w : C → ℤ) (h : ∀ c, ∏ i, x i ^ e c i ≠ 0) :
    ∏ c, (∏ i, x i ^ e c i) ^ w c = ∏ i, x i ^ ∑ c, w c * e c i := by
  classical
  have hz : ∀ i, x i = 0 → ∀ c, e c i = 0 := by
    intro i hi c
    by_contra hne
    exact h c (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, zero_zpow _ hne]))
  set y : I → F := fun i => if x i = 0 then 1 else x i with hy
  have hy0 : ∀ i, y i ≠ 0 := fun i => by
    by_cases hi : x i = 0 <;> simp [hy, hi]
  have hxy : ∀ i (n : ℤ), (x i = 0 → n = 0) → x i ^ n = y i ^ n := by
    intro i n hn
    by_cases hi : x i = 0
    · rw [hn hi]; simp
    · simp [hy, hi]
  have l1 : ∀ c, ∏ i, x i ^ e c i = ∏ i, y i ^ e c i :=
    fun c => Finset.prod_congr rfl fun i _ => hxy i _ fun hi => hz i hi c
  have l2 : ∀ i, x i ^ ∑ c, w c * e c i = y i ^ ∑ c, w c * e c i := fun i => hxy i _ fun hi => by
    simp [hz i hi]
  simp_rw [l1, l2, ← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  have key : ∀ (a : F), a ≠ 0 → ∀ (s : Finset C) (n : C → ℤ), ∏ c ∈ s, a ^ n c = a ^ ∑ c ∈ s, n c := by
    intro a ha s n
    induction s using Finset.induction_on with
    | empty => simp
    | insert c s hc ih => rw [Finset.prod_insert hc, Finset.sum_insert hc, ih, zpow_add₀ ha]
  rw [key _ (hy0 i)]
  exact congrArg _ (Finset.sum_congr rfl fun c _ => mul_comm _ _)

abbrev fracOver (ρ : V →+* V₁) (hρ : Function.Injective ρ) : Over (Sp V) := Over.mk (fracPt ρ hρ ≫ jK V)

theorem psi_val (W : Matrix (Fin 8) (Fin 8) ℤ) (Q : Data V) (ρ : V →+* V₁) (hρ : Function.Injective ρ) (D : DegPre V₁)
    (e : (Fin 8 → Q.X) ≃+ D.X) (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B))
    (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4)
      (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2))))
    (hw : ∀ κ : (TK V₁).left ⟶ (TK V).left, κ ≫ jK V = jK V₁ ≫ spMap ρ → ∀ mu z J J', Good Q.M.L z J → Good D.P.L z J' →
      val (D.psi (e mu)) (𝟙 _) z J' =
        gm (D.xK (e mu)) z _ (w.s (fun k : (Fin 8 × Fin 8) × Fin 4 => J (D.xK (e mu) ≫ lamPts (pr k.1.1) (pr k.1.2) k.2 ≫
            pullback.fst Q.B.hom (spMap ρ)), J' (D.xK (e mu)))) *
          ∏ a, ∏ b, val (Q.tau (mu a) (mu b)) κ z J ^ W a b)
    (τ₀ : Gens Q) {n : ℕ} (s : Fin n → V) (ε : Fin n → LinearMap.BilinForm ℤ Q.X) (hτ : TauIn Q τ₀ s ε)
    {W₀ : Type} [CommRing W₀] (ib : W₀ →+* V) (B₀ : Over (Sp W₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left)
    (c₀ : Q.X → (𝟙_ (Over (Sp W₀)) ⟶ B₀)) (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (lamPts (c₀ a) (c₀ b)) negε))
    (β₂ : (G2 Q.B).left ⟶ (G2 B₀).left) (w₀ : LB.Iso (abelian₂ Q.B Q.M.L) ((abelian₂ B₀ M₀).pull β₂))
    (h₀ : ∀ (T : Over (Sp V)) (a b : Q.X) z J J', Good M₀ z J → Good Q.M.L z J' →
      val (τ₀ a b) (toUnit T).left z J' =
        lamVal w₀ (lift (toUnit T ≫ Q.c a) (toUnit T ≫ Q.c b)).left z J J' * val (τ₁ a b) (T.hom ≫ spMap ib) z J)
    (mu : Fin 8 → Q.X) (z : (TK V₁).left) (J : ((TK V₁).left ⟶ Q.B.left) → Q.M.L.ι)
    (J' : ((TK V₁).left ⟶ D.P.A.left) → D.P.L.ι) (J₀ : ((TK V₁).left ⟶ B₀.left) → M₀.ι)
    (hJ : Good Q.M.L z J) (hJ' : Good D.P.L z J') (hJ₀ : Good M₀ z J₀) :
    ∃ u : (FractionRing V₁)ˣ, (u : FractionRing V₁) = ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (s i)) ^ qW W (ε i) mu ∧
      val (D.psi (e mu)) (𝟙 _) z J' =
        gm (D.xK (e mu)) z _ (w.s (fun k : (Fin 8 × Fin 8) × Fin 4 => J (D.xK (e mu) ≫ lamPts (pr k.1.1) (pr k.1.2) k.2 ≫
            pullback.fst Q.B.hom (spMap ρ)), J' (D.xK (e mu)))) *
          (∏ a, ∏ b, (lamVal (Z := (TK V₁).left) w₀ (lift (toUnit (fracOver ρ hρ) ≫ Q.c (mu a)) (toUnit (fracOver ρ hρ) ≫ Q.c (mu b))).left
              z J₀ J * val (τ₁ (mu a) (mu b)) ((fracPt ρ hρ ≫ jK V) ≫ spMap ib) z J₀) ^ W a b) *
          gm (𝟙 _) z ⊤ (unitOn u) := by
  classical
  have hL : Q.M.L.IsLB := Q.M.isLB
  choose k hk hkv using fun a b => (hτ a b).2
  have htau : ∀ a b, val (Q.tau a b) (fracPt ρ hρ) z J =
      gm (fracPt ρ hρ) z ⊤ (unitOn (k a b)) * val (τ₀ a b) (fracPt ρ hρ ≫ jK V) z J := by
    intro a b
    let t₁ := scaleGen (LB.pullGen Q.M.L (lamPts (Q.c a) (Q.c b)) negε (τ₀ a b) (toUnit (TK V)).left) (unitOn (k a b))
    have hc : LB.Gen.Corr Q.M.L _ _ _ _ (Q.tau a b) t₁ := corr_of_val hL fun y J₁ hJ₁ => by
      rw [val_scaleGen _ _ _ _ hJ₁, val_pull hJ₁, Category.id_comp]
      exact hkv a b y J₁ hJ₁
    rw [val_corr hJ hc (fracPt ρ hρ), val_scaleGen _ _ _ _ hJ, val_pull hJ]
    rfl
  have hunit : ∀ a b, gm (fracPt ρ hρ) z ⊤ (unitOn (k a b)) =
      gm (𝟙 _) z ⊤ (unitOn (Units.map (IsFractionRing.map (K := FractionRing V) (L := FractionRing V₁) hρ).toMonoidHom
        (k a b))) := fun a b => gm_spMap_unitOn _ z _
  have hbase : ∀ a b, val (τ₀ a b) (fracPt ρ hρ ≫ jK V) z J =
      lamVal (Z := (TK V₁).left) w₀ (lift (toUnit (fracOver ρ hρ) ≫ Q.c a) (toUnit (fracOver ρ hρ) ≫ Q.c b)).left z J₀ J *
        val (τ₁ a b) ((fracPt ρ hρ ≫ jK V) ≫ spMap ib) z J₀ := fun a b => h₀ (fracOver ρ hρ) a b z J₀ J hJ₀ hJ
  have hfk : ∀ a b, ((Units.map (IsFractionRing.map (K := FractionRing V) (L := FractionRing V₁) hρ).toMonoidHom
      (k a b) : (FractionRing V₁)ˣ) : FractionRing V₁) =
        ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (s i)) ^ ε i a b := by
    intro a b
    show IsFractionRing.map (K := FractionRing V) (L := FractionRing V₁) hρ (k a b : FractionRing V) = _
    rw [hk a b, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow₀]
    simp [IsFractionRing.map, IsLocalization.map_eq]
  refine ⟨∏ a, ∏ b, Units.map (IsFractionRing.map (K := FractionRing V) (L := FractionRing V₁) hρ).toMonoidHom
      (k (mu a) (mu b)) ^ W a b, ?_, ?_⟩
  · simp_rw [Units.coe_prod, Units.val_zpow_eq_zpow_val, hfk]
    have hne : ∀ c : Fin 8 × Fin 8, ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (s i)) ^ ε i (mu c.1) (mu c.2) ≠ 0 :=
      fun c => by rw [← hfk]; exact Units.ne_zero _
    have e := prod_zpow_swap (fun i => algebraMap V₁ (FractionRing V₁) (ρ (s i)))
      (fun (c : Fin 8 × Fin 8) i => ε i (mu c.1) (mu c.2)) (fun (c : Fin 8 × Fin 8) => W c.1 c.2) hne
    rw [Fintype.prod_prod_type] at e
    simp only [Fintype.sum_prod_type] at e
    rw [e]
    rfl
  · rw [hw (fracPt ρ hρ) (fracPt_comp ρ hρ) mu z J J' hJ hJ', _root_.mul_assoc]
    congr 1
    clear hw h₀ hkv hk hτ hfk
    simp only [htau, hunit, hbase]
    simp only [unitOn, map_prod, map_zpow, mul_zpow, Finset.prod_mul_distrib]
    exact _root_.mul_comm _ _

theorem psi_val_of (W : Matrix (Fin 8) (Fin 8) ℤ) (Q : Data V) (ρ : V →+* V₁) (hρ : Function.Injective ρ) (D : DegPre V₁)
    (e : (Fin 8 → Q.X) ≃+ D.X) (hS : SharpRef W Q ρ D e) (τ₀ : Gens Q) {n : ℕ} (s : Fin n → V)
    (ε : Fin n → LinearMap.BilinForm ℤ Q.X) (hτ : TauIn Q τ₀ s ε) {W₀ : Type} [CommRing W₀] (ib : W₀ →+* V)
    (hB : FromBase Q τ₀ ib) :
    ∃ (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B))
      (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4)
        (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2)))),
      (∀ a, IsMonHom (pr a)) ∧
      (∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)), ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a) ∧
      w.IsGen ∧ (∀ mu a, (D.c (e mu) ≫ pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) = spMap ρ ≫ (Q.c (mu a)).left) ∧
      ∃ (B₀ : Over (Sp W₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (𝟙_ (Over (Sp W₀)) ⟶ B₀))
        (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (lamPts (c₀ a) (c₀ b)) negε))
        (β : Q.B.left ⟶ B₀.left) (β₂ : (G2 Q.B).left ⟶ (G2 B₀).left)
        (w₀ : LB.Iso (abelian₂ Q.B Q.M.L) ((abelian₂ B₀ M₀).pull β₂)),
        IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback Q.B B₀ (spMap ib) β ∧ IsSquare β β₂ ∧ w₀.IsGen ∧
        (∀ a, (Q.c a).left ≫ β = spMap ib ≫ (c₀ a).left) ∧ (∀ a b, (τ₁ a b).IsGen) ∧
        (∀ (T : Over (Sp V)) (a b : Q.X) z J J', Good M₀ z J → Good Q.M.L z J' →
          val (τ₀ a b) (toUnit T).left z J' =
            lamVal w₀ (lift (toUnit T ≫ Q.c a) (toUnit T ≫ Q.c b)).left z J J' * val (τ₁ a b) (T.hom ≫ spMap ib) z J) ∧
        ∀ (mu : Fin 8 → Q.X) (z : (TK V₁).left) (J : ((TK V₁).left ⟶ Q.B.left) → Q.M.L.ι)
          (J' : ((TK V₁).left ⟶ D.P.A.left) → D.P.L.ι) (J₀ : ((TK V₁).left ⟶ B₀.left) → M₀.ι),
          Good Q.M.L z J → Good D.P.L z J' → Good M₀ z J₀ →
          ∃ u : (FractionRing V₁)ˣ,
            (u : FractionRing V₁) = ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (s i)) ^ qW W (ε i) mu ∧
            val (D.psi (e mu)) (𝟙 _) z J' =
              gm (D.xK (e mu)) z _ (w.s (fun k : (Fin 8 × Fin 8) × Fin 4 => J (D.xK (e mu) ≫ lamPts (pr k.1.1) (pr k.1.2) k.2 ≫
                  pullback.fst Q.B.hom (spMap ρ)), J' (D.xK (e mu)))) *
                (∏ a, ∏ b, (lamVal (Z := (TK V₁).left) w₀
                    (lift (toUnit (fracOver ρ hρ) ≫ Q.c (mu a)) (toUnit (fracOver ρ hρ) ≫ Q.c (mu b))).left
                    z J₀ J * val (τ₁ (mu a) (mu b)) ((fracPt ρ hρ ≫ jK V) ≫ spMap ib) z J₀) ^ W a b) *
                gm (𝟙 _) z ⊤ (unitOn u) := by
  obtain ⟨pr, w, h1, h2, h3, h4, hw⟩ := hS
  obtain ⟨B₀, _, _, M₀, c₀, τ₁, β, β₂, w₀, g1, g2, g3, g4, g5, g6, g7, h₀⟩ := hB
  exact ⟨pr, w, h1, h2, h3, h4, B₀, inferInstance, inferInstance, M₀, c₀, τ₁, β, β₂, w₀, g1, g2, g3, g4, g5, g6, g7, h₀,
    fun mu z J J' J₀ hJ hJ' hJ₀ => psi_val W Q ρ hρ D e pr w hw τ₀ s ε hτ ib B₀ M₀ c₀ τ₁ β₂ w₀ h₀ mu z J J' J₀ hJ hJ' hJ₀⟩

end GlobalTheory.Poinc.PsiMono

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.SameComb

theorem sp_endo_eq_id {o K : Type} [CommRing o] [Field K] [Algebra o K] (R : Subalgebra o K)
    (frac : ∀ x : K, ∃ a ∈ R, ∃ b ∈ R, x = a / b) (g : Sp K ⟶ Sp K)
    (h : g ≫ spMap R.val.toRingHom = spMap R.val.toRingHom) : g = 𝟙 _ := by
  rw [← Spec.map_preimage g] at h ⊢
  set ψ := Spec.preimage g
  have h' : CommRingCat.ofHom R.val.toRingHom ≫ ψ = CommRingCat.ofHom R.val.toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp]; exact h
  have hψ : ψ = 𝟙 _ := by
    ext x
    obtain ⟨a, ha, b, hb, rfl⟩ := frac x
    have ea := congrArg (fun f => f.hom ⟨a, ha⟩) h'
    have eb := congrArg (fun f => f.hom ⟨b, hb⟩) h'
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at ea eb
    change ψ.hom (a / b) = a / b
    rw [map_div₀]
    exact congrArg₂ (· / ·) ea eb
  rw [hψ, Spec.map_id]

theorem lbIso_pull_along {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {φ : Y ⟶ X} (h : LBIso M (L.pull φ)) (r : Z ⟶ Y)
    {ψ : Z ⟶ X} (e : ψ = r ≫ φ) : LBIso (M.pull r) (L.pull ψ) :=
  h.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M r r rfl) (chartPullSame L (fun _ => ψ) (fun _ => φ) _ r fun _ => e)

theorem sec_of_pt {o K : Type} [CommRing o] [Field K] [Algebra o K] (R : Subalgebra o K)
    (frac : ∀ x : K, ∃ a ∈ R, ∃ b ∈ R, x = a / b) {Q : PolAV (Sp K)} {P : PolAV (Sp R)} {a : Q.A.left ⟶ P.A.left}
    (ha : IsGrpPullback Q.A P.A (spMap R.val.toRingHom) a) (t : baseOver (Sp R) ⟶ P.A) (w : Sp K ⟶ Q.A.left)
    (hw : w ≫ a = spMap R.val.toRingHom ≫ t.left) : w ≫ Q.A.hom = 𝟙 _ := by
  apply sp_endo_eq_id R frac
  have e := congrArg (· ≫ P.A.hom) hw
  simp only [Category.assoc, ha.1.w, Over.w t] at e
  simpa using e

theorem combine : ∀ (o Ω o₁ o₂ Ω' : Type) [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o₁] [CommRing o₂] [Field Ω'] [Algebra o₁ Ω'] [Algebra o₂ Ω'] (S : ThetaSys o Ω) (S₁ : ThetaSys o₁ Ω') (S₂ : ThetaSys o₂ Ω') (ρ : S.Real) (ρ₁ : S₁.Real) (ρ₂ : S₂.Real) (ε : Matrix (Fin 8) (Fin 8) ℤ → (ρ.P.A ⟶ ρ.P.A)) (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₁.P.A ⟶ ρ₁.P.A)) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)) (lab₁ : S.Gam → S₁.Gam) (lab₂ : S.Gam → S₂.Gam) (φ : Ω →+* Ω'), Same ρ ε ρ₁ ε₁ lab₁ φ → Same ρ ε ρ₂ ε₂ lab₂ φ → SameAt ρ₁.P ρ₂.P S₁.R.val.toRingHom S₂.R.val.toRingHom ε₁ ε₂ (fun x => ρ₁.pt (lab₁ x)) (fun x => ρ₂.pt (lab₂ x)) := by
  intro o Ω o₁ o₂ Ω' _ _ _ _ _ _ _ _ S S₁ S₂ ρ ρ₁ ρ₂ ε ε₁ ε₂ lab₁ lab₂ φ h₁ h₂
  obtain ⟨P₀, a, a₁, ε₀, ha, ha₁, hLa, hLa₁, hε, hw⟩ := h₁
  obtain ⟨P₀', b, b₂, ε₀', hb, hb₂, hLb, hLb₂, hε', hw'⟩ := h₂
  obtain ⟨θ, hθm, hθ⟩ := grpPullback_iso ha hb
  haveI := hθm

  have ext : ∀ {T : Scheme.{0}} (u v : T ⟶ P₀'.A.left), u ≫ b = v ≫ b → u ≫ P₀'.A.hom = v ≫ P₀'.A.hom → u = v :=
    fun u v e₁ e₂ => hb.1.hom_ext e₁ e₂
  refine ⟨P₀, a₁, θ.hom.left ≫ b₂, ha₁, ((isGrpPullback_of_iso θ).comp hb₂).congr (Category.id_comp _) rfl, hLa₁, ?_,
    fun E => ⟨ε₀ E, (hε E).2, ?_⟩, fun x => ?_⟩
  · refine LBIso.trans P₀.isLB (pull_isLB ρ.P.isLB _) (pull_isLB ρ₂.P.isLB _) hLa ?_
    refine LBIso.trans (pull_isLB ρ.P.isLB _) (pull_isLB P₀'.isLB θ.hom.left) (pull_isLB ρ₂.P.isLB _)
      (lbIso_pull_along hLb θ.hom.left hθ.symm).symm (lbIso_pull_along hLb₂ θ.hom.left rfl)
  · have key : (ε₀ E).left ≫ θ.hom.left = θ.hom.left ≫ (ε₀' E).left := by
      apply ext
      · rw [Category.assoc, hθ, (hε E).1, Category.assoc, (hε' E).1, ← Category.assoc, hθ]
      · simp only [Category.assoc, Over.w]
    rw [← Category.assoc, key, Category.assoc, (hε' E).2, Category.assoc]
  · obtain ⟨w, hwa, hwa₁⟩ := hw x
    obtain ⟨w', hwb, hwb₂⟩ := hw' x
    refine ⟨w, hwa₁, ?_⟩
    have s₁ := sec_of_pt S₁.R S₁.frac ha₁ _ w hwa₁
    have s₂ := sec_of_pt S₂.R S₂.frac hb₂ _ w' hwb₂
    have hww : w ≫ θ.hom.left = w' := by
      apply ext
      · rw [Category.assoc, hθ, hwa, hwb]
      · rw [Category.assoc, Over.w, s₁, s₂]
    rw [← Category.assoc, hww, hwb₂]

end GlobalTheory.Poinc.SameComb
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ValField

theorem exists_fg_values {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
    (M : RatModel o Ω) {K : Type} [Field K] (y : Sp K ⟶ M.Z) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra.FiniteType ℤ R) (y₀ : R →+* K),
      ∀ E : Subfield K, (∀ r, y₀ r ∈ E) → ∀ a ∈ M.O (y (closedPoint K)), M.val y a ∈ E := by
  set z := y (closedPoint K) with hz
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset (X := M.Z) (x := z) (U := ⊤) trivial
  have hne : (U : Set M.Z).Nonempty := ⟨z, hzU⟩
  have hr : Set.range y = {z} := RatModel.range_eq_singleton y _
  let φ : M.O z →+* K := RatModel.valHom y z hr
  let y₀ : Γ(M.Z, U) →+* K :=
    φ.comp ((Subalgebra.inclusion (RatModel.ringOn_le_O (M := M) hzU)).toRingHom.comp
      (M.sectionsEquiv U hne).toRingHom)
  have hy₀ : ∀ f, y₀ f = φ ⟨valF M.pt U f, RatModel.valF_mem_O hzU f⟩ := fun f => by
    show φ _ = φ _
    congr 1
    exact Subtype.ext (RatModel.coe_sectionsEquiv U hne f)
  have hft : Algebra.FiniteType ℤ Γ(M.Z, U) := by
    have h1 : (M.s.appLE ⊤ U (by simp)).hom.FiniteType :=
      M.lft.finiteType_appLE (isAffineOpen_top _) hU _
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of o)).commRingCatIsoToRingEquiv.symm.surjective
    have h3 : (algebraMap ℤ o).FiniteType := RingHom.finiteType_algebraMap.2 (ArithBase.ft (o := o) (Ω := Ω))
    have h4 := (h1.comp h2).comp h3
    rw [← RingHom.finiteType_algebraMap]
    convert h4
    exact Subsingleton.elim _ _
  refine ⟨Γ(M.Z, U), inferInstance, hft, y₀, fun E hE a ha => ?_⟩
  let Wo : M.Z.Opens := ⟨{w | a ∈ M.O w}, M.isOpen_setOf_mem_O a⟩
  obtain ⟨f, hfW, hzf⟩ := hU.exists_basicOpen_le (V := Wo) ⟨z, ha⟩ hzU
  have hnef : ((M.Z.basicOpen f : M.Z.Opens) : Set M.Z).Nonempty := ⟨z, hzf⟩
  have har : a ∈ M.ringOn (M.Z.basicOpen f) := RatModel.mem_ringOn.2 fun w hw => hfW hw
  obtain ⟨s, hs⟩ := (RatModel.mem_ringOn_iff_exists hnef).1 har
  letI := hU.isLocalization_basicOpen f
  obtain ⟨n, r, hrn⟩ := IsLocalization.Away.surj f s
  have halg : ∀ g : Γ(M.Z, U), algebraMap Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen f) g = resG M.Z (M.Z.basicOpen_le f) g :=
    fun _ => rfl
  have he := congrArg (M.res _ hnef) hrn
  rw [map_mul, map_pow, halg, halg, RatModel.res_resG, RatModel.res_resG, RatModel.res_apply, hs,
    RatModel.res_apply, RatModel.res_apply] at he

  have hO : (⟨a, ha⟩ : M.O z) * ⟨valF M.pt U f, RatModel.valF_mem_O hzU f⟩ ^ n =
      ⟨valF M.pt U r, RatModel.valF_mem_O hzU r⟩ := Subtype.ext (by simpa using he)
  have hφ := congrArg φ hO
  rw [map_mul, map_pow, ← hy₀, ← hy₀] at hφ
  have hf0 : y₀ f ≠ 0 := by
    rw [hy₀]
    exact (RatModel.val_ne_zero_iff hr _).2 ((RatModel.isUnit_valF_iff hzU f).2 hzf)
  have hval : M.val y a = y₀ r / y₀ f ^ n := by
    rw [← hφ, mul_div_cancel_right₀ _ (pow_ne_zero _ hf0)]
    rfl
  rw [hval]
  exact div_mem (hE r) (pow_mem (hE f) n)

end GlobalTheory.ValField

namespace GlobalTheory.Poinc

theorem exists_complete_dvr_values : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra (FractionRing V) (PadicAlgCl p)], IsAdicComplete (IsLocalRing.maximalIdeal V) V → (∀ x : FractionRing V, ‖algebraMap (FractionRing V) (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) →
  ∃ (V₂ : Type) (_ : CommRing V₂) (_ : IsDomain V₂) (_ : IsDiscreteValuationRing V₂) (_ : Algebra (FractionRing V₂) (PadicAlgCl p)), IsAdicComplete (IsLocalRing.maximalIdeal V₂) V₂ ∧ (∀ x : FractionRing V₂, ‖algebraMap (FractionRing V₂) (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V₂ (FractionRing V₂))) ∧
    ∃ σ : FractionRing V →+* FractionRing V₂, (algebraMap (FractionRing V₂) (PadicAlgCl p)).comp σ = algebraMap (FractionRing V) (PadicAlgCl p) ∧
      ∀ a ∈ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))), D.X.M.val (gPt p ≫ y) a ∈ (algebraMap (FractionRing V₂) (PadicAlgCl p)).range := by
  intro g n F W Z i X₁ _ _ _ _ _ _ _ ε₁ _ D p _ z₁ c y h V _ _ _ _ hc hV
  obtain ⟨R, _, hR, y₀, hval⟩ := GlobalTheory.ValField.exists_fg_values D.X.M (gPt p ≫ y)
  let κ : FractionRing V →+* PadicAlgCl p := algebraMap (FractionRing V) (PadicAlgCl p)
  haveI : CharZero V := RingHom.charZero (κ.comp (algebraMap V (FractionRing V)))
  have hQ := GlobalTheory.PadicUnitBall.padic_mem_range p V hc κ hV
  obtain ⟨W₂, i₁, i₂, i₃, hcW, -, fV, fK, κ', -, -, -, -, hκ', hunit, hy⟩ :=
    GlobalTheory.DvrFinExt.exists_finite_extension p V hc κ hV hQ R y₀
  letI : Algebra (FractionRing W₂) (PadicAlgCl p) := κ'.toAlgebra
  refine ⟨W₂, i₁, i₂, i₃, κ'.toAlgebra, hcW, hunit, fK, hκ', fun a ha => ?_⟩
  have hm := hval κ'.fieldRange (fun r => by obtain ⟨x, hx⟩ := hy r; exact ⟨x, hx⟩) a ha
  obtain ⟨x, hx⟩ := hm
  exact ⟨x, hx⟩

end GlobalTheory.Poinc
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AV.AbVar

theorem memKL_of_lam_geom_eq_zero {K : Type} [Field K] (A : AbVar K) {L : LB A.X.left} (hL : L.IsLB)
    (x : A.Pt) (h : AbVar.lam (cls L hL) (fst A.X (ptOver K (AlgebraicClosure K))) (snd A.X _ ≫ x) = 0) :
    MemKL A.X L x := by
  set P := ptOver K (AlgebraicClosure K)
  have h1 := congrArg (CechPic.pull (lift (snd P A.X) (fst P A.X)).left) h
  rw [lam_eq, pull_lam, map_zero, lift_fst, lift_snd_assoc, lam_comm, ← lam_eq] at h1
  have h0 : CechPic.pull (fst P A.X ≫ x).left (cls L hL) = 0 := by
    rw [Over.comp_left, pull_comp, GlobalTheory.PrimitiveOverField.pic_field (K := AlgebraicClosure K) (CechPic.pull x.left (cls L hL)), map_zero]
  rw [AbVar.lam, h0, sub_zero] at h1
  intro p
  refine ⟨⊤, trivial, ?_⟩
  have hD : (Out.translDiff A.X L x).IsLB := LB.isLB_linComb hL _ _
  refine (cls_eq_zero_iff (pull_isLB hD _)).1 ?_
  rw [cls_pull hD]
  refine (congrArg _ ?_).trans (map_zero _)
  refine (cls_linComb hL _ _ hD).trans (Eq.trans ?_ h1)
  rw [Fin.sum_univ_two, sub_eq_add_neg]
  exact congrArg₂ (· + ·) (one_zsmul _) (neg_one_zsmul _)

end GlobalTheory.AV.AbVar

theorem GlobalTheory.AV.AbVar.finite_lam_eq_zero : ∀ (K : Type) [Field K] (A : AbVar K) (c : Pic A.X.left), IsAmpleCls c → Finite {x : A.Pt // AbVar.lam c (fst A.X (ptOver K (AlgebraicClosure K))) (snd A.X _ ≫ x) = 0} := by
  intro K _ A c ⟨L, hL, ha, hc⟩
  subst hc
  obtain ⟨H, _, i, -, hmono, hfin, -, hH⟩ := GlobalTheory.kernel_finiteFlat_subgroup K A.X A.ab L hL ha
  have hF := GlobalTheory.FlagCovQF.finite_points H.hom (AlgebraicClosure K) (spMap (algebraMap K (AlgebraicClosure K)))
  haveI := hF.to_subtype
  have hz : ∀ x : {x : A.Pt // AbVar.lam (cls L hL) (fst A.X (ptOver K (AlgebraicClosure K))) (snd A.X _ ≫ x) = 0},
      ∃ z : ptOver K (AlgebraicClosure K) ⟶ H, z ≫ i = x.1 := fun x =>
    (hH _ x.1).1 (memKL_of_lam_geom_eq_zero A hL x.1 x.2)
  choose z hz using hz
  refine Finite.of_injective (fun x => (⟨(z x).left, Over.w (z x)⟩ :
    {y : Sp (AlgebraicClosure K) ⟶ H.left | y ≫ H.hom = spMap (algebraMap K (AlgebraicClosure K))})) ?_
  intro a b hab
  have e : z a = z b := Over.OverMorphism.ext (congrArg Subtype.val hab)
  exact Subtype.ext ((hz a).symm.trans (e ▸ hz b))
end
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.GenericChart

theorem exists_isClosed_chart : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∃ T : Set X, IsClosed T ∧ genericPoint X ∉ T ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), y.1 (IsLocalRing.closedPoint ℂ) ∉ T → ∃ c : AlgChart p σ D, y ∈ c.e.source := by
  intro k _ X _ p D h
  obtain ⟨U, hU, hη, t, ht⟩ := GlobalTheory.GenericCoords.exists_affine_etale_coords h
  refine ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl, fun h' => h' hη, fun σ y hy => ?_⟩
  obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale (σ := σ) hU t ht (y := y)
    (mem_ptsIn.2 (not_not.1 hy))
  exact ⟨c, hc⟩

end GlobalTheory.GenericChart
end
