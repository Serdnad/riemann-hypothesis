module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFramePowEqIntegralGenerator
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueRigidifiedGeneratorExtendNormal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle050
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle075
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Mathlib.Tactic.ENatToNat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle008
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle077
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenMove

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.ZH.MulExtend
open GlobalTheory.TorsFrameInt

variable {X H Y : Scheme.{0}} {L : LB X} {M : LB H} {K K' : Type} [Fintype K] [Fintype K']

theorem exists_move_charts (hL : L.IsLB) (hM : M.IsLB) {f : Y ⟶ H} {ψ : Y ⟶ X} (w : LB.Iso (M.pull f) (L.pull ψ))
    (hw : w.IsGen) (φX : K → (X ⟶ X)) (φY : K → (Y ⟶ Y)) (φH : K → (H ⟶ H)) (ε : K → ℤ)
    (h₁ : ∀ k, φY k ≫ ψ = ψ ≫ φX k) (h₂ : ∀ k, φY k ≫ f = f ≫ φH k)
    (α : LB.Gen (LB.LinComb L φX ε)) (hα : α.IsGen) :
    ∃ a : LB.Gen (LB.LinComb M (fun k => f ≫ φH k) ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → M.ι),
        (∀ k, (r ≫ φY k ≫ ψ) z ∈ L.U (p k)) → (∀ k, (r ≫ φY k ≫ f) z ∈ M.U (q k)) →
        gm (r ≫ ψ) z (LB.wchart L φX p) (α.s p) = (∏ k, gw w (r ≫ φY k) z (p k) (fun _ => q k) ^ ε k) *
          gm r z (LB.wchart M (fun k => f ≫ φH k) q) (a.s q) := by
  obtain ⟨b, hb, H⟩ := H1.exists_gen_move hL (pull_isLB hM f) w ((isGen_iff w).1 hw) φX φY ε ψ h₁ α hα
  have le : ∀ j : K → M.ι, LB.wchart M (fun k => f ≫ φH k) j ≤ LB.wchart (M.pull f) φY (fun k _ => j k) :=
    fun j y hy => Set.mem_iInter.2 fun k => mem_pull.2 (by
      have : (f ≫ φH k) y ∈ M.U (j k) := Set.mem_iInter.1 hy k
      rw [← h₂ k] at this; exact this)
  refine ⟨⟨fun j => res (le j) (b.s fun k _ => j k)⟩, isGen_of_gm _ fun y j j' hj hj' => ?_,
    fun Z r z p q hp hq => ?_⟩
  · refine (gm_res _ y _ hj _).trans ((gen_trans hb (𝟙 Y) y (le j hj) (le j' hj')).trans
      (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_) (gm_res _ y _ hj' _).symm))
    refine (gm_pull_g M f (𝟙 Y ≫ φY k) y _ _ (Set.mem_iInter.1 (le j hj) k) (Set.mem_iInter.1 (le j' hj') k)).trans ?_
    rw [Category.assoc, h₂]
  · have m : r z ∈ LB.wchart M (fun k => f ≫ φH k) q := Set.mem_iInter.2 fun k => by
      have := hq k
      rw [h₂ k] at this; exact this
    exact (H Z r z p (fun k _ => q k) hp (fun k => Set.mem_iInter.1 (le _ m) k)).trans
      (congrArg₂ (· * ·) rfl (gm_res _ z _ m _).symm)

theorem corr_of_field [IsReduced Y] [Nonempty K] (hL : L.IsLB) {φ : K → (Y ⟶ X)} {φ' : K → (Y ⟶ X)} {ε ε' : K → ℤ}
    (ψ : Y ⟶ X) (h : ∀ k, φ k = ψ) (h' : ∀ k, φ' k = ψ)
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (H : ∀ (F : Type) [Field F] (r : Sp F ⟶ Y) (z : Sp F) J, Good L z J → val t r z J = val t' r z J) :
    LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' c₁ c₂ c₃
  refine Units.ext (GenericExtend.eq_of_valR_eq fun x hx ↦ ⟨Y.residueField x, inferInstance,
    Y.fromSpecResidueField x, fun o ↦ Scheme.fromSpecResidueField_apply x o, ?_⟩)
  have ho : ∀ o, (Y.fromSpecResidueField x : Sp (Y.residueField x) ⟶ Y) o = x :=
    fun o ↦ Scheme.fromSpecResidueField_apply x o
  generalize (Y.fromSpecResidueField x : Sp (Y.residueField x) ⟶ Y) = r at ho
  have z : Sp (Y.residueField x) := IsLocalRing.closedPoint _
  have hz : r z ∈ LB.wchart L φ j ⊓ LB.wchart L φ' j' := (ho z).symm ▸ hx
  obtain ⟨k₀⟩ := ‹Nonempty K›
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (K := PUnit) (fun _ => r ≫ ψ) (fun _ => j k₀) (fun _ _ _ => rfl)
    (fun _ => by rw [← h k₀]; exact Set.mem_iInter.1 hz.1 k₀)
  have q := H _ r z J hJ
  rw [val_of t r z J j (fun k => by rw [h]; exact (e PUnit.unit).trans (c₁ _ _ ((h _).trans (h _).symm))),
    val_of t' r z J j' (fun k => by rw [h']; exact (e PUnit.unit).trans (c₃ _ _ ((h _).trans (h' _).symm)))] at q
  refine (toStk z).injective ?_
  exact (toStk_valF r _ z hz _).trans ((congrArg Units.val ((gm_res r z _ hz _).trans
    (q.trans (gm_res r z _ hz _).symm))).trans (toStk_valF r _ z hz _).symm)

theorem core {S U HU B : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] (hS : Geo.Tor.IsNormalScheme S)
    [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (p : H ⟶ S) (e : S ⟶ H) (jH : HU ⟶ H) (pU : HU ⟶ U) (eU : U ⟶ HU)
    (hs : Smooth p) (hg : GeometricallyIntegral p) (he : e ≫ p = 𝟙 _) (hP : IsPullback jH pU p j)
    (h₁ : eU ≫ jH = j ≫ e) (hL : L.IsLB) (hM : M.IsLB) (eX : B ⟶ X) (u : U ⟶ B) (ψ : HU ⟶ X)
    (h₃ : eU ≫ ψ = u ≫ eX) (nH : H ⟶ H) (nU : HU ⟶ HU) (nX : X ⟶ X)
    (c₁ : nU ≫ ψ = ψ ≫ nX) (c₂ : nU ≫ jH = jH ≫ nH) (c₃ : eU ≫ nU = eU) (c₄ : e ≫ nH = e)
    (w : LB.Iso (M.pull jH) (L.pull ψ)) (hw : w.IsGen)
    (rig : LB.Gen (L.pull eX)) (rigM : LB.Gen (M.pull e)) (hrigM : rigM.IsGen) (N : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, nX] ![N, -1])) (hα : α.IsGen)
    (hn : ∀ (Z : Scheme.{0}) (t : Z ⟶ B) (z : Z) J, Good L z J →
      val α (t ≫ eX) z J = val rig t z J ^ N * (val rig t z J)⁻¹)
    (hr : ∀ (F : Type) [Field F] (x : Sp F ⟶ U) (z : Sp F) J J', Good L z J → Good M z J' →
      val rig (x ≫ u) z J = wv w (x ≫ eU) z J J' * val rigM (x ≫ j) z J') :
    ∃ κ : LB.Gen (LB.LinComb M (K := Fin 2) ![𝟙 H, nH] ![N, -1]), κ.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ HU) (z : Z) (a a' : L.ι) (b b' : M.ι),
        (r ≫ ψ) z ∈ L.U a → ((r ≫ nU) ≫ ψ) z ∈ L.U a' → (r ≫ jH) z ∈ M.U b → ((r ≫ nU) ≫ jH) z ∈ M.U b' →
        gm (r ≫ ψ) z (LB.wchart L ![𝟙 X, nX] ![a, a']) (α.s ![a, a']) * gw w (r ≫ nU) z a' (fun _ => b') =
          gw w r z a (fun _ => b) ^ N * gm (r ≫ jH) z (LB.wchart M ![𝟙 H, nH] ![b, b']) (κ.s ![b, b']) := by
  have : IsIntegral U := isIntegral_of_isOpenImmersion j
  have d₁ : ∀ k : Fin 2, ![𝟙 _, nU] k ≫ ψ = ψ ≫ ![𝟙 X, nX] k := fun k => by
    fin_cases k; exacts [(Category.id_comp _).trans (Category.comp_id _).symm, c₁]
  have d₂ : ∀ k : Fin 2, ![𝟙 _, nU] k ≫ jH = jH ≫ ![𝟙 H, nH] k := fun k => by
    fin_cases k; exacts [(Category.id_comp _).trans (Category.comp_id _).symm, c₂]
  obtain ⟨t, ht, htv⟩ := exists_move_charts hL hM w hw ![𝟙 X, nX] ![𝟙 _, nU] ![𝟙 H, nH] ![N, -1] d₁ d₂ α hα
  have ee : ∀ k : Fin 2, e ≫ ![𝟙 H, nH] k = e := fun k => by fin_cases k; exacts [Category.comp_id _, c₄]
  have eeU : ∀ k : Fin 2, eU ≫ ![𝟙 _, nU] k = eU := fun k => by fin_cases k; exacts [Category.comp_id _, c₃]
  let σ : LB.Gen (LB.LinComb M (K := PUnit) (fun _ => e) (fun _ => N - 1)) := ⟨fun i => rigM.s i ^ (N - 1)⟩
  have hσ : σ.IsGen := isGen_of_gm _ fun y i i' hi hi' => by
    refine (map_zpow _ _ _).trans ((congrArg (· ^ (N - 1)) (gen_trans hrigM (𝟙 _) y hi hi')).trans
      ((mul_zpow _ _ _).trans (congrArg₂ (· * ·) ?_ (map_zpow _ _ _).symm)))
    simp only [trF, Fintype.prod_unique, zpow_one]
  obtain ⟨ρ, hρ, hρv⟩ := exists_gen hM (φ' := fun k : Fin 2 => e ≫ ![𝟙 H, nH] k) (ε' := ![N, -1])
    (fun G _ h => by
      simp only [ee, Fintype.prod_unique, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← zpow_add]; rfl) σ hσ
  obtain ⟨κ, ⟨hκ, hc⟩, -⟩ := GenExtendNormal.existsUnique_gen_extend S hS U H HU H j p e jH pU eU hs hg he hP h₁ M hM
    (Fin 2) ![𝟙 H, nH] ![N, -1] t ρ ht hρ (corr_of_field hM (j ≫ e)
      (fun k => by rw [← Category.assoc, h₁, Category.assoc, ee]) (fun k => by rw [ee])
      fun F _ x z J' hJ' => by
        choose J hJ using fun χ : Sp F ⟶ X => exists_chart hL (χ z)
        rw [val_pull hJ', val_pull hJ', hρv _ _ z J' hJ']
        have q := htv _ (x ≫ eU) z (fun k => J (((x ≫ eU) ≫ ψ) ≫ ![𝟙 X, nX] k))
          (fun k => J' ((x ≫ eU) ≫ jH ≫ ![𝟙 H, nH] k))
          (fun k => by rw [d₁, ← Category.assoc]; exact hJ _) (fun k => by rw [d₂]; exact hJ' _)
        have q₁ : ∀ k : Fin 2, gw w ((x ≫ eU) ≫ ![𝟙 _, nU] k) z (J (((x ≫ eU) ≫ ψ) ≫ ![𝟙 X, nX] k))
            (fun _ => J' ((x ≫ eU) ≫ jH ≫ ![𝟙 H, nH] k)) = wv w (x ≫ eU) z J J' := fun k => by
          rw [Category.assoc (x ≫ eU) ψ, ← d₁, ← d₂, ← Category.assoc _ _ ψ, ← Category.assoc _ _ jH,
            Category.assoc x eU, eeU]
          rfl
        simp only [q₁] at q
        have q₂ : val α ((x ≫ eU) ≫ ψ) z J = _ * val t (x ≫ eU) z J' := q
        rw [Category.assoc, h₃, ← Category.assoc, hn _ _ z J hJ, hr F x z J J' hJ hJ', Fin.prod_univ_two] at q₂
        refine Eq.trans ?_ (map_zpow _ _ _).symm
        change _ = val rigM (x ≫ j) z J' ^ (N - 1)
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at q₂
        apply Additive.ofMul.injective
        replace q₂ := congrArg Additive.ofMul q₂
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at q₂ ⊢
        linear_combination (norm := module) -q₂)
  refine ⟨κ, hκ, fun Z r z a a' b b' ha ha' hb hb' => ?_⟩
  have hq : ∀ k : Fin 2, (r ≫ ![𝟙 _, nU] k ≫ jH) z ∈ M.U (![b, b'] k) := fun k => by
    fin_cases k; exacts [hb, hb']
  have q := htv _ r z ![a, a'] ![b, b'] (fun k => by fin_cases k; exacts [ha, ha']) hq
  rw [← hc, gm_pullGen M _ _ κ jH r z _ (Set.mem_iInter.2 fun k => by
    have := hq k
    rw [d₂] at this; exact this), Fin.prod_univ_two] at q
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id] at q
  rw [q, zpow_neg_one, mul_right_comm, inv_mul_cancel_right]

theorem exists_gen_mulRel : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → ∀ (n : ℕ) (α : LB.Gen (LB.LinComb ρ.P.L (K := Fin 2) ![𝟙 ρ.P.A.left, (mulA ρ.P.A n).left] ![((n : ℕ) : ℤ) ^ 2, -1])), α.IsGen → IsNormMul ρ.P.A ρ.P.L ρ.rig n α → ∃ κ, κ.IsGen ∧ Q.MulRel n α κ := by
  intro o Ω _ _ _ _ S ρ M U₀ Q hS n α hα hn
  have := ArithBase.ded (o := o) (Ω := Ω)
  have := M.lft
  have : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  have := Q.semi.smooth
  have := Q.semi.geomConnected
  have : Nonempty U₀.toScheme := hS.ne.to_subtype
  have gq := isGrpPullback_pullback ρ.P.A Q.u₀
  let eU : U₀.toScheme ⟶ pullback ρ.P.A.hom Q.u₀ := η[(Over.pullback Q.u₀).obj ρ.P.A].left
  let nU : pullback ρ.P.A.hom Q.u₀ ⟶ pullback ρ.P.A.hom Q.u₀ := (mulA ((Over.pullback Q.u₀).obj ρ.P.A) n).left
  have h₁ : eU ≫ Q.φ = U₀.ι ≫ eSec Q.G := one_comm Q.cart
  have h₃ : eU ≫ pullback.fst _ _ = Q.u₀ ≫ eSec ρ.P.A := one_comm gq
  have c₁ : nU ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (mulA ρ.P.A n).left := mulA_comm gq n
  have c₅ : nU ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w (mulA ((Over.pullback Q.u₀).obj ρ.P.A) n)
  have rg : ∀ {F : Type} [Field F] {Y : Scheme.{0}} (g : Sp F ⟶ Y) (V : Y.Opens) (z : Sp F), g z ∈ V →
      Set.range g ⊆ V := fun g V z hz => by
    rintro _ ⟨y, rfl⟩
    exact (top_le_iff_mem g V z).2 hz (x := y) trivial
  obtain ⟨κ, hκ, H⟩ := core hS.normal U₀.ι Q.G.hom (eSec Q.G) Q.φ _ eU Q.semi.smooth
    (grpObj_geometricallyIntegral_of_smooth _ Q.G) (Over.w η[Q.G]) Q.cart.1 h₁ ρ.P.isLB Q.L.isLB (eSec ρ.P.A) Q.u₀
    (pullback.fst _ _) h₃ (mulA Q.G n).left nU (mulA ρ.P.A n).left c₁ (mulA_comm Q.cart n) (one_mulA n) (one_mulA n)
    Q.w Q.w_gen ρ.rig Q.L.rig Q.L.rigGen ((n : ℤ) ^ 2) α hα (fun Z t z J hJ => by
      have q := val_corr hJ hn t
      rw [val_pull hJ, val_mul hJ, val_inv] at q
      exact q.trans (congrArg (· * _) (map_zpow _ _ _))) (fun F _ x z J J' hJ hJ' => by
      have e₁ : (x ≫ eU) ≫ Q.φ = (x ≫ U₀.ι) ≫ eSec Q.G := by rw [Category.assoc, h₁, Category.assoc]
      have e₃ : (x ≫ eU) ≫ pullback.fst _ _ = (x ≫ Q.u₀) ≫ eSec ρ.P.A := by rw [Category.assoc, h₃, Category.assoc]
      have q := congrArg (toStk z) (Q.w_rig F (x ≫ eU) (x ≫ U₀.ι) (x ≫ Q.u₀) _ _ e₁ e₃ (rg _ _ z (hJ _))
        (rg _ _ z (hJ' _)))
      rw [map_mul, toStk_valF _ _ z (mem_pull.2 (by have := hJ ((x ≫ eU) ≫ pullback.fst _ _); rwa [e₃] at this ⊢)),
        toStk_valF (x ≫ eU) _ z (And.intro (mem_pull.2 (hJ ((x ≫ eU) ≫ pullback.fst _ _)))
          (mem_pull.2 (hJ' ((x ≫ eU) ≫ Q.φ)))),
        toStk_valF _ _ z (mem_pull.2 (by have := hJ' ((x ≫ eU) ≫ Q.φ); rwa [e₁] at this ⊢))] at q
      rw [val_of _ _ z J (fun _ => J ((x ≫ eU) ≫ pullback.fst _ _)) (fun _ => by rw [e₃]),
        val_of _ _ z J' (fun _ => J' ((x ≫ eU) ≫ Q.φ)) (fun _ => by rw [e₁])]
      exact Units.ext q)
  refine ⟨κ, hκ, fun K _ g g' jP jP' jL jL' k₁ k₂ m₁ m₂ m₃ m₄ => ?_⟩
  obtain rfl : g' = g ≫ nU := pullback.hom_ext (by rw [k₁, Category.assoc, c₁]) (by rw [k₂, Category.assoc, c₅])
  have z : Sp K := IsLocalRing.closedPoint _
  have a₁ := m₁ ⟨z, rfl⟩
  have a₂ := m₂ ⟨z, rfl⟩
  have a₃ := m₃ ⟨z, rfl⟩
  have a₄ := m₄ ⟨z, rfl⟩
  have q := congrArg Units.val (H _ g z jP jP' jL jL' a₁ a₃ a₂ a₄)
  have pw : ∀ {G : Type} [Group G] (x : G), x ^ ((n : ℤ) ^ 2) = x ^ (n ^ 2) := fun x => by
    rw [← Nat.cast_pow, zpow_natCast]
  rw [pw] at q
  refine (toStk z).injective ?_
  rw [map_mul, map_mul, map_pow, toStk_valF _ _ z (Set.mem_iInter.2 fun k => by
      fin_cases k
      · exact a₁
      · rw [Category.assoc, c₁] at a₃; exact a₃),
    toStk_valF (g ≫ nU) _ z (And.intro (mem_pull.2 a₃) (mem_pull.2 a₄)),
    toStk_valF g _ z (And.intro (mem_pull.2 a₁) (mem_pull.2 a₂)),
    toStk_valF _ _ z (Set.mem_iInter.2 fun k => by
      fin_cases k
      · exact a₂
      · rw [Category.assoc, show nU ≫ Q.φ = _ from mulA_comm Q.cart n] at a₄; exact a₄)]
  exact q

end GlobalTheory.ZH.MulExtend
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight

noncomputable section
namespace GlobalTheory.ZH.CrdMove

theorem stk_onto {F : Type} [Field F] (z : Sp F) : Function.Surjective (toStk z) := fun a => by
  obtain ⟨U, hU, f, rfl⟩ := (Sp F).presheaf.exists_germ_eq a
  obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => (Subsingleton.elim (α := PrimeSpectrum F) z y) ▸ hU
  obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 f
  exact ⟨x, rfl⟩

theorem stk_valR {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F) (h : x z ∈ U)
    (a : Γ(X, U)) : toStk z (valR x U a) = gs x z U a := by
  rw [valR_of_field, valF, dite_eq_left ((top_le_iff_mem x U z).2 h), gs_eq x z U h]
  show ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _)) = _
  rw [Iso.hom_inv_id_apply]
  exact TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE ((top_le_iff_mem x U z).2 h)) z trivial _

theorem crd_iff {F : Type} [Field F] {X : Scheme.{0}} {H : LB X} {J : Type} (s : J → H.Sec) (x : Sp F ⟶ X)
    (v : J → F) (z : Sp F) : Crd H s x v ↔ ∃ (l : H.ι) (c : ((Sp F).presheaf.stalk z)ˣ), x z ∈ H.U l ∧
      ∀ j, toStk z (v j) = c.val * gs x z (H.U l) ((s j).f l) := by
  constructor
  · rintro ⟨l, c, hl, hv⟩
    have hz := (top_le_iff_mem x _ z).1 hl
    refine ⟨l, Units.map (toStk z).toMonoidHom c, hz, fun j => ?_⟩
    rw [hv, map_mul, stk_valR x _ z hz]
    rfl
  · rintro ⟨l, c, hz, hv⟩
    obtain ⟨d, hd⟩ := stk_onto z c.val
    have d0 : d ≠ 0 := fun h0 => by
      have : Nontrivial ((Sp F).presheaf.stalk z) := inferInstance
      rw [h0, map_zero] at hd
      exact Units.ne_zero _ hd.symm
    refine ⟨l, Units.mk0 d d0, (top_le_iff_mem x _ z).2 hz, fun j => (toStk z).injective ?_⟩
    rw [hv, map_mul, stk_valR x _ z hz, Units.val_mk0, hd]

theorem crd_move {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
    {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
    {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
    {L₀ : LB G.left} {L₁ : LB A.left} (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) {n : ℤ} {I : Type}
    (t : I → LB.Sec (LPow A L₁ n T)) (s : I → LB.Sec (LPow G L₀ n T₀))
    (h : ∀ i, ThetaPtMove.SecRel hp τ hτ w (t i) (s i)) {F : Type} [Field F] (r : Sp F ⟶ (T ⊗ A).left) (v : I → F)
    (hv : Crd (LPow A L₁ n T) t r v) : Crd (LPow G L₀ n T₀) s (r ≫ ThetaPtMove.psi hp τ hτ) v := by
  let z : Sp F := IsLocalRing.closedPoint F
  obtain ⟨l, c, hl, hc⟩ := (crd_iff t r v z).1 hv
  obtain ⟨J, hJ, -⟩ := exists_good L₀ hL₀ z (K := Empty) (fun k => k.elim) (fun k => k.elim) (fun k => k.elim)
    (fun k => k.elim)
  obtain ⟨J', hJ', e⟩ := exists_good L₁ hL₁ z (fun _ : Fin 1 => r ≫ (snd T A).left) l
    (fun a b _ => congrArg l (Subsingleton.elim a b)) (fun k => Set.mem_iInter.1 hl k)
  obtain ⟨d, hd⟩ : ∃ d : ((Sp F).presheaf.stalk z)ˣ, ∀ j,
      VVRank.sv G (s j) (r ≫ ThetaPtMove.psi hp τ hτ) z J = d.val * VVRank.sv A (t j) r z J' :=
    ⟨_, fun j => h j _ r z J J' hJ hJ'⟩
  refine (crd_iff s _ v z).2 ⟨fun _ => J ((r ≫ ThetaPtMove.psi hp τ hτ) ≫ (snd T₀ G).left),
    c * d⁻¹,
    hJ.mem (fun _ : Fin 1 => (snd T₀ G).left) _, fun j => ?_⟩
  have q := hd j
  have q' := sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => n) (t j) r z J' l e
  refine (hc j).trans ?_
  rw [Units.val_mul, _root_.mul_assoc]
  refine congrArg (c.val * ·) ?_
  rw [Units.eq_inv_mul_iff_mul_eq]
  exact (congrArg (_ * ·) q'.symm).trans q.symm

theorem crd_of_moved : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (w : LB.Iso u.A.L (ρ.P.L.pull u.φ)), w.IsGen → ∀ t : S.J → SecA u.A (PadicAlgCl p) S.N, (∀ i, Moved u w (t i) (ρ.s i)) → ∀ (a : u.PtC) (v : S.J → PadicAlgCl p), Crd (LPow u.A.A u.A.L (S.N : ℤ) (TFK (R := u.V) (PadicAlgCl p))) t (show Sp (PadicAlgCl p) ⟶ _ from (ptSecT u.A.A (a ≫ u.U.gen.hom)).left) v → ρ.Crd (u.toA a) v := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u w _ t ht a v hv
  refine ⟨_, ?_, crd_move u.cart (T := TFK (R := u.V) (PadicAlgCl p)) (T₀ := baseOver (Sp S.R)) (spMap y₀)
    (base_eq u) ρ.P.isLB u.A.isLB w t ρ.s ht _ v hv⟩
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (ThetaPtMove.psi_snd' _ _ _)).trans ?_)
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ u.φ) (ThetaPtMove.ptSecT_snd _)).trans ?_)
  exact Category.assoc _ _ _

end GlobalTheory.ZH.CrdMove
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight

noncomputable section
namespace GlobalTheory.ZH.SecProp
open GlobalTheory.ZH.CrdCalc

section
variable {F : Type} [Field F] [IsAlgClosed F] {Y : Scheme.{0}} (p : Y ⟶ Sp F) [LocallyOfFiniteType p]

theorem exists_point {Z : Set Y} (hZ : IsLocallyClosed Z) (hn : Z.Nonempty) :
    ∃ r : Sp F ⟶ Y, r ≫ p = 𝟙 _ ∧ ∀ z, r z ∈ Z := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨c, hcW, hc⟩ := nonempty_inter_closedPoints hn hZ
  exact ⟨pointOfClosedPoint p c hc, pointOfClosedPoint_comp p c hc,
    fun z => (congrArg (· ∈ Z) (pointOfClosedPoint_apply p c hc z)).mpr hcW⟩

theorem fn_ext_valR [IsReduced Y] {U : Y.Opens} {a b : Γ(Y, U)}
    (h : ∀ r : Sp F ⟶ Y, r ≫ p = 𝟙 _ → ⊤ ≤ r ⁻¹ᵁ U → valR r U a = valR r U b) : a = b := by
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
  by_contra hne
  have hn : ((Y.basicOpen (a - b) : Y.Opens) : Set Y).Nonempty :=
    Set.nonempty_iff_ne_empty.2 fun e => hne (SetLike.coe_injective e)
  obtain ⟨r, hr, hz⟩ := exists_point p (Y.basicOpen (a - b)).isOpen.isLocallyClosed hn
  have hU : ⊤ ≤ r ⁻¹ᵁ U := fun z _ => Y.basicOpen_le _ (hz z)
  have hu := (isUnit_valR_iff r U hU (a - b)).2 fun z _ => hz z
  have e := h r hr hU
  rw [valR_eq r U hU, valR_eq r U hU, ← sub_eq_zero, ← map_sub] at e
  rw [valR_eq r U hU, e] at hu
  exact not_isUnit_zero hu

variable {H : LB Y} {I : Type} {a b : I → H.Sec}

theorem exists_mem_basicOpen (h : ∀ r : Sp F ⟶ Y, r ≫ p = 𝟙 _ → ∃ w, w ≠ 0 ∧ Crd H b r w) (l : H.ι) (y : Y)
    (hy : y ∈ H.U l) : ∃ i, y ∈ Y.basicOpen ((b i).f l) := by
  by_contra hne
  let V : Y.Opens := ⨆ i, Y.basicOpen ((b i).f l)
  have hyV : y ∉ V := fun e => hne (TopologicalSpace.Opens.mem_iSup.1 e)
  obtain ⟨r, hr, hz⟩ := exists_point p
    ((H.U l).isOpen.isLocallyClosed.inter V.isOpen.isClosed_compl.isLocallyClosed) ⟨y, hy, hyV⟩
  obtain ⟨w, hw, hc⟩ := h r hr
  have hU : ⊤ ≤ r ⁻¹ᵁ H.U l := fun z _ => (hz z).1
  obtain ⟨c, hc'⟩ := crd_unique hc
    (⟨l, 1, hU, fun j => by simp⟩ : Crd H b r (fun i => valR r (H.U l) ((b i).f l)))
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hw
  have hu : IsUnit (valR r (H.U l) ((b i).f l)) := by
    rw [hc' i]
    exact c.isUnit.mul (Ne.isUnit hi)
  have z : Sp F := IsLocalRing.closedPoint F
  exact (hz z).2 (TopologicalSpace.Opens.mem_iSup.2 ⟨i, (isUnit_valR_iff r _ hU _).1 hu (Set.mem_univ z)⟩)

theorem cross_eq [IsReduced Y] (h : ∀ r : Sp F ⟶ Y, r ≫ p = 𝟙 _ → ∃ w, Crd H a r w ∧ Crd H b r w) (l : H.ι)
    (i i' : I) : (a i).f l * (b i').f l = (a i').f l * (b i).f l := by
  refine fn_ext_valR p fun r hr hU => ?_
  obtain ⟨w, ha, hb⟩ := h r hr
  obtain ⟨c, hc⟩ := crd_unique ha
    (⟨l, 1, hU, fun j => by simp⟩ : Crd H a r (fun i => valR r (H.U l) ((a i).f l)))
  obtain ⟨d, hd⟩ := crd_unique hb
    (⟨l, 1, hU, fun j => by simp⟩ : Crd H b r (fun i => valR r (H.U l) ((b i).f l)))
  rw [valR_mul r _ hU, valR_mul r _ hU, hc i, hc i', hd i, hd i']
  ring

end

theorem valR_const {F : Type} [Field F] {Y : Scheme.{0}} (p : Y ⟶ Sp F) (r : Sp F ⟶ Y) (hr : r ≫ p = 𝟙 _)
    (U : Y.Opens) (hU : ⊤ ≤ r ⁻¹ᵁ U) (a : F) :
    valR r U (resG Y le_top (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom a))) = a := by
  rw [valR_res r le_top hU, valR_eq r ⊤ le_rfl]
  have e : r.appLE ⊤ ⊤ le_rfl = r.appTop := (Scheme.Hom.app_eq_appLE r).symm
  have e₂ : p.appTop ≫ r.appTop = 𝟙 _ := by rw [← Scheme.Hom.comp_appTop, hr, Scheme.Hom.id_appTop]
  change (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom ((p.appTop ≫ r.appLE ⊤ ⊤ le_rfl).hom _) = a
  rw [e, e₂]
  exact (Scheme.ΓSpecIso (CommRingCat.of F)).inv_hom_id_apply a

theorem proportional_of_crd : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ) (I J : Type) [Fintype J] (t : I → SecA A F k) (s : J → SecA A F k) (b : Matrix I J F), (∀ x : TFK (R := R) F ⟶ A.A, ∃ v : J → F, b.mulVec v ≠ 0 ∧ Crd (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) s (show Sp F ⟶ _ from (ptSecT A.A x).left) v ∧ Crd (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) t (show Sp F ⟶ _ from (ptSecT A.A x).left) (b.mulVec v)) → ∃ c : F, ∀ i, ∑ j, kf R F (b i j) • SecM.ofSec A.A (s j) = kf R F c • SecM.ofSec A.A (t i) := by
  intro hG R _ _ A F _ _ _ k I J _ t s b H
  have hsm := A.isAb.smooth
  let T : Over (Spec (CommRingCat.of (FractionRing R))) := TFK (R := R) F
  let p : (T ⊗ A.A).left ⟶ Sp F := (fst T A.A).left
  have hp : Smooth p := inferInstanceAs (Smooth (pullback.fst T.hom A.A.hom))
  have : IsReduced (T ⊗ A.A).left := GlobalTheory.isReduced_of_smooth_of_isReduced p
  let m : I → SecM A.A A.L (k : ℤ) T := fun i => ∑ j, kf R F (b i j) • SecM.ofSec A.A (s j)
  let t' : I → SecA A F k := fun i => SecM.toSec A.A (m i)
  have key : ∀ r : Sp F ⟶ (T ⊗ A.A).left, r ≫ p = 𝟙 _ →
      ∃ w, w ≠ 0 ∧ Crd (LPow A.A A.L (k : ℤ) T) t' r w ∧ Crd (LPow A.A A.L (k : ℤ) T) t r w := by
    intro r hr
    let r' : T ⟶ T ⊗ A.A := Over.homMk r (by
      rw [← Over.w (fst T A.A), ← Category.assoc]
      exact (congrArg (· ≫ T.hom) hr).trans (Category.id_comp _))
    have er : ptSecT A.A (r' ≫ snd _ _) = r' := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ (lift_snd _ _)
      rw [ptSecT, lift_fst]
      exact Over.OverMorphism.ext hr.symm
    obtain ⟨v, hv, hs, ht⟩ := H (r' ≫ snd _ _)
    have er' : (ptSecT A.A (r' ≫ snd _ _)).left = r := congrArg (·.left) er
    replace hs : Crd (LPow A.A A.L (k : ℤ) T) s r v := er' ▸ hs
    replace ht : Crd (LPow A.A A.L (k : ℤ) T) t r (b.mulVec v) := er' ▸ ht
    refine ⟨_, hv, ?_, ht⟩
    obtain ⟨l, c, hl, hc⟩ := hs
    refine ⟨l, c, hl, fun i => ?_⟩
    have e : (t' i).f l = ∑ j, resG _ le_top (p.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (b i j))) * (s j).f l := by
      change (m i).1 l = _
      simp only [m, Submodule.coe_sum, Finset.sum_apply]
      rfl

    rw [e, valR_eq r _ hl, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← valR_eq r _ hl, valR_mul r _ hl, valR_const p r hr _ hl, hc j, mul_left_comm]
  obtain ⟨c₀, hc₀⟩ := SectionRatio.exists_ratio A.isLB (φ := fun _ : Fin 1 => (snd T A.A).left)
    (ε := fun _ => (k : ℤ)) t' t
    (fun y J hJ => by
      have hm := hJ.mem (fun _ : Fin 1 => (snd T A.A).left) (𝟙 _)
      obtain ⟨i, hi⟩ := exists_mem_basicOpen p (H := LPow A.A A.L (k : ℤ) T) (b := t)
        (fun r hr => (key r hr).imp fun w hw => ⟨hw.1, hw.2.2⟩) _ y hm
      exact ⟨i, (SectionRatio.mem_basicOpen_iff_gs _ y hm).1 hi⟩)
    (fun i i' y J hJ => by
      have hm := hJ.mem (fun _ : Fin 1 => (snd T A.A).left) (𝟙 _)
      have e := cross_eq p (H := LPow A.A A.L (k : ℤ) T) (a := t') (b := t)
        (fun r hr => (key r hr).imp fun w hw => hw.2) (fun _ => J (𝟙 _ ≫ (snd T A.A).left)) i i'
      exact (gs_mul _ y _ hm _ _).symm.trans ((congrArg (gs (𝟙 _) y _) e).trans (gs_mul _ y _ hm _ _)))
  obtain ⟨d, hd⟩ := CommPairing.surj_fst hG A.isAb T c₀
  obtain ⟨c, rfl⟩ := (kf_bijective R F).2 d
  refine ⟨c, fun i => ThetaAct.sv_ext A.isLB fun y J hJ => ?_⟩
  refine (hc₀ i y J hJ).trans (Eq.trans ?_ (ThetaAct.sv_smul _ _ _ _ hJ).symm)
  exact congrArg (· * _) ((congrArg (gs (𝟙 _) y ⊤) hd.symm).trans (gs_pull (𝟙 _) _ y ⊤ trivial _))

end GlobalTheory.ZH.SecProp
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem _root_.GlobalTheory.T.exists_orderAction_descent_field_extension : GlobalFnsSt → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (D : DegPre K₀) (D' : DegPre K) (hD : IsPullDeg i D D') (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X] (oB : D.P.OAct O) (oa' : D'.OAct O), (∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, (oa'.onB.act a).left ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ (oB.act a).left) → ∃ oa : D.OAct O, oa.onB = oB := by
  first | exact @GlobalTheory.exists_oAct_of_field_extension | exact GlobalTheory.exists_oAct_of_field_extension | (intros; apply GlobalTheory.exists_oAct_of_field_extension <;> assumption)
end
