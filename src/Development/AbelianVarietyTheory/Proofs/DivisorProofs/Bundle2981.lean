module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2839
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegOfSameTorusTwist
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2882
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle126
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle133
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2857
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2858
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.TwPsi

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.PsiCompare GlobalTheory.MumCmp.Point

variable {R : Type} [CommRing R] [IsDomain R]

theorem toUnit_left_eq {S : Scheme.{0}} (X : Over S) : (toUnit X).left = X.hom := by
  simpa using Over.w (toUnit X)

theorem cancel {A : Type} [CommRing A] [IsDomain A] {S S₂ : A} {ψ rig G N W Wc W1 ψ₂ rig₂ : Aˣ} (hs : S₂ ≠ 0)
    (e : S * (ψ * rig).val * (G * N).val = (W * Wc⁻¹ * W1).val * (S₂ * (ψ₂ * rig₂).val))
    (e4 : S * N.val = W.val * S₂) : ψ * G * rig = Wc⁻¹ * W1 * (ψ₂ * rig₂) := by
  refine Units.ext (mul_left_cancel₀ (mul_ne_zero W.ne_zero hs) ?_)
  simp only [Units.val_mul] at e ⊢
  linear_combination e - ((ψ : A) * G * rig) * e4

theorem core {D D₂ : DegPre R} (g : GtPt D (𝟙_ (Over (Sp R)))) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β]
    (xe : D₂.X ≃+ D.X) (hc : ∀ χ, D₂.c χ ≫ β = D.c (xe χ))
    (w : LB.Iso D₂.P.L (LB.LinComb D.P.L (twφ D₂ D β g.b) twε))
    (f : ∀ α : D.X, D.SecB 1 α) (f₂ : ∀ α : D₂.X, D₂.SecB 1 α)
    (ν : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![g.b.left, η[D.P.A].left] ![-1, 1]))
    (h : LevelOneEq D f) (h₂ : LevelOneEq D₂ f₂)
    (hf : ∀ (χ : D₂.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι)
      (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D.P.L z J → Good D₂.P.L z J' →
      sval (f (xe χ)) (r ≫ twφ D₂ D β g.b 0) z J *
        (val (g.s (xe χ)) (r ≫ (toUnit D₂.P.A).left) z J * val ν (r ≫ (toUnit D₂.P.A).left) z J).val =
      (∏ κ, gv w (r ≫ D₂.famφB χ κ) z (fun i => J ((r ≫ D₂.famφB χ κ) ≫ twφ D₂ D β g.b i))
        (J' (r ≫ D₂.famφB χ κ)) ^ DegPre.famε 1 κ).val * sval (f₂ χ) r z J')
    [IsIntegral (DegPre.BF D₂ (FractionRing R)).left]
    (χ : D₂.X) (z : (DegPre.BF D₂ (FractionRing R)).left) (J : _ → D.P.L.ι) (J' : _ → D₂.P.L.ι)
    (hJ : Good D.P.L z J) (hJ' : Good D₂.P.L z J')
    (ne : sval (f₂ 0) (DegPre.prB D₂ (FractionRing R)).left z J' ≠ 0) :
    val (D.psi (xe χ)) ((fst (TF (R := R) (FractionRing R)) D₂.P.A).left ≫ jFK (R := R) (FractionRing R)) z J *
        val (g.s (xe χ)) (toUnit (DegPre.BF D₂ (FractionRing R))).left z J *
        val D.rig (DegPre.BF D₂ (FractionRing R)).hom z J =
      (wv w (cP D₂ (DegPre.BF D₂ (FractionRing R)) χ).left z J J')⁻¹ *
        wv w (1 : DegPre.BF D₂ (FractionRing R) ⟶ D₂.P.A).left z J J' *
        (val (D₂.psi χ) ((fst (TF (R := R) (FractionRing R)) D₂.P.A).left ≫ jFK (R := R) (FractionRing R)) z J' *
          val D₂.rig (DegPre.BF D₂ (FractionRing R)).hom z J') := by
  let T := DegPre.BF D₂ (FractionRing R)
  let κ : T ⟶ TF (R := R) (FractionRing R) := fst _ _
  let Φ : D₂.P.A ⟶ D.P.A := padd D.P.A β (toUnit D₂.P.A ≫ g.b)
  have hΦ : ∀ u : T ⟶ D₂.P.A, u ≫ Φ = (u ≫ β) * (toUnit T ≫ g.b) := fun u => by
    show u ≫ (β * (toUnit D₂.P.A ≫ g.b)) = _
    rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (u ≫ toUnit D₂.P.A) (toUnit T)]
  have hU : ∀ u : T ⟶ D₂.P.A, u.left ≫ (toUnit D₂.P.A).left = (toUnit T).left := fun u => by
    rw [← Over.comp_left, toUnit_unique (u ≫ toUnit D₂.P.A) (toUnit T)]
  obtain ⟨y, hy⟩ : ∃ y : T ⟶ D₂.P.A, y * cP D₂ T χ = DegPre.prB D₂ (FractionRing R) :=
    ⟨_, inv_mul_cancel_right _ _⟩
  have hyΦ : (y ≫ Φ) * cP D T (xe χ) = DegPre.prB D₂ (FractionRing R) ≫ Φ := by
    rw [hΦ, hΦ, ← hy, MonObj.mul_comp, cP_comp β (hc χ), mul_right_comm]
  have e₁ := h (xe χ) 0 rfl T κ (y ≫ Φ) z J hJ
  have e₂ := h₂ χ 0 rfl T κ y z J' hJ'
  have e₃ := hf χ _ y.left z J J' hJ hJ'
  have e₄ := hf 0 _ (DegPre.prB D₂ (FractionRing R)).left z J J' hJ hJ'
  have p₃ := prod_famB D₂ y χ (fun q => wv w q z J J')
  have p₄ := prod_famB D₂ (DegPre.prB D₂ (FractionRing R)) 0 (fun q => wv w q z J J')
  rw [hy] at p₃ e₂
  rw [cPoint_zero, _root_.mul_one, inv_mul_cancel_right] at p₄
  rw [hyΦ] at e₁
  change _ = (∏ κ, wv w (y.left ≫ D₂.famφB χ κ) z J J' ^ DegPre.famε 1 κ).val * _ at e₃
  change _ = (∏ κ, wv w ((DegPre.prB D₂ (FractionRing R)).left ≫ D₂.famφB 0 κ) z J J' ^ DegPre.famε 1 κ).val * _ at e₄
  rw [p₃, hU, show y.left ≫ twφ D₂ D β g.b 0 = (y ≫ Φ).left from rfl, e₁, e₂] at e₃
  rw [p₄, hU, map_zero xe, val_corr hJ g.s_zero, val_one, _root_.one_mul,
    show (DegPre.prB D₂ (FractionRing R)).left ≫ twφ D₂ D β g.b 0 = (DegPre.prB D₂ (FractionRing R) ≫ Φ).left from rfl] at e₄
  exact cancel ne e₃ e₄

theorem grp {U : Type} [CommGroup U] {ψ0 ψ₂0 rig rig₂ W1 ψ G Wc ψ₂ : U} (h0 : ψ0 = W1⁻¹ * ψ₂0)
    (c0 : ψ0 * rig = ψ₂0 * rig₂) (c : ψ * G * rig = Wc⁻¹ * W1 * (ψ₂ * rig₂)) : ψ * G = Wc⁻¹ * ψ₂ := by
  subst h0
  apply Additive.ofMul.injective
  have e0 := congrArg Additive.ofMul c0
  have e := congrArg Additive.ofMul c
  simp only [ofMul_mul, ofMul_inv] at e0 e ⊢
  linear_combination (norm := abel) e - e0

theorem formEq {D D₂ : DegPre R} (g : GtPt D (𝟙_ (Over (Sp R)))) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β]
    (xe : D₂.X ≃+ D.X) (hc : ∀ χ, D₂.c χ ≫ β = D.c (xe χ)) (χ : D₂.X) :
    FormEq (Sum.elim (fun _ : PUnit => ptK (D.c (xe χ)))
        (fun k => (toUnit (TK R)).left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b (xe χ) k))
      (Sum.elim (fun _ => -1) DegPre.gtε) (fun i => D₂.xK χ ≫ twφ D₂ D β g.b i) (fun i => -1 * twε i) := by
  let u := toUnit (TK R)
  have k : ∀ a : TK R ⟶ 𝟙_ (Over (Sp R)), a = u := fun a => toUnit_unique _ _
  have m0 : u.left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b (xe χ) 0 = D₂.xK χ ≫ twφ D₂ D β g.b 0 := by
    show u.left ≫ ((toUnit _ ≫ D.c (xe χ)) * g.b).left = (u ≫ D₂.c χ).left ≫ (β * (toUnit _ ≫ g.b)).left
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    simp only [MonObj.comp_mul, ← Category.assoc]
    rw [k (u ≫ toUnit _), k ((u ≫ D₂.c χ) ≫ toUnit _), Category.assoc, hc]
  have m1 : u.left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b (xe χ) 1 = ptK (D.c (xe χ)) := by
    show u.left ≫ (toUnit _ ≫ D.c (xe χ)).left = (u ≫ D.c (xe χ)).left
    rw [← Over.comp_left, ← Category.assoc, k (u ≫ toUnit _)]
  have m2 : u.left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b (xe χ) 2 = D₂.xK χ ≫ twφ D₂ D β g.b 1 := by
    show u.left ≫ g.b.left = (u ≫ D₂.c χ).left ≫ (toUnit _ ≫ g.b).left
    rw [← Over.comp_left, ← Over.comp_left, ← Category.assoc, k ((u ≫ D₂.c χ) ≫ toUnit _)]
  have m3 : u.left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b (xe χ) 3 = D₂.xK χ ≫ twφ D₂ D β g.b 2 := by
    show u.left ≫ (toUnit _ ≫ η[D.P.A]).left = (u ≫ D₂.c χ).left ≫ (toUnit _ ≫ η[D.P.A]).left
    rw [← Over.comp_left, ← Over.comp_left, ← Category.assoc, ← Category.assoc, k (u ≫ toUnit _),
      k ((u ≫ D₂.c χ) ≫ toUnit _)]
  intro U _ h
  simp only [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_three, Fintype.prod_unique, Sum.elim_inl,
    Sum.elim_inr]
  rw [m0, m1, m2, m3]
  simp only [DegPre.gtε, twε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Matrix.cons_val_succ]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  abel

end GlobalTheory.MumCmp.TwPsi

namespace GlobalTheory.MumCmp


open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.PsiCompare GlobalTheory.MumCmp.Point GlobalTheory.MumCmp.TwPsi in
theorem psi_maps_twist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₂ : DegData R (maximalIdeal R)) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))) (β : D₂.toPre.P.A ≅ D.toPre.P.A), IsMonHom β.hom → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → (∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK 0 ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK 0) (-1) (D₂.toPre.psi 0) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi 0) (LB.pullGen D.toPre.P.L _ _ (g.s 0) (toUnit (TK R)).left))) → ∀ (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB 1 α) (ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1])), ν.IsGen → GlobalTheory.PsiCompare.LevelOneEq D.toPre f → GlobalTheory.PsiCompare.LevelOneEq D₂.toPre f₂ → (¬ ∀ mu j, (f₂ mu).f j = 0) → (∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.toPre.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.toPre.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.toPre.famφB χ κ) z (fun i => J ((r ≫ D₂.toPre.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i)) (J' (r ≫ D₂.toPre.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J') → ∀ χ : D₂.toPre.X, ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK χ ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK χ) (-1) (D₂.toPre.psi χ) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi (xe χ)) (LB.pullGen D.toPre.P.L _ _ (g.s (xe χ)) (toUnit (TK R)).left)) := by
  intro R _ _ _ _ D D₂ g β hβ xe hc w hw ⟨t₀, m₀, c₀⟩ f f₂ ν _ h h₂ hne hf χ
  have hL := D.toPre.P.isLB
  have hL' := D₂.toPre.P.isLB
  have := D₂.toPre.P.isAb.smooth
  have := D₂.toPre.P.isAb.geomConnected
  have : IsIntegral (DegPre.BF D₂.toPre (FractionRing R)).left :=
    (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres D₂.toPre.P.A.hom).geometrically_isIntegral
      (TF (R := R) (FractionRing R)).hom _ _ (IsPullback.of_hasPullback _ D₂.toPre.P.A.hom).flip
  let T := DegPre.BF D₂.toPre (FractionRing R)
  let π : T.left ⟶ (TK R).left :=
    (fst (TF (R := R) (FractionRing R)) D₂.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)
  have hπ : π ≫ jK R = T.hom := by
    rw [Category.assoc]; exact Over.w (fst (TF (R := R) (FractionRing R)) D₂.toPre.P.A)
  have hT0 : π ≫ D₂.toPre.xK 0 = (1 : T ⟶ D₂.toPre.P.A).left := by
    rw [Uniq.xK_zero, ← Category.assoc, hπ]; rfl
  have hTχ : π ≫ D₂.toPre.xK χ = (cP D₂.toPre T χ).left := by
    let k : T ⟶ TK R := Over.homMk π hπ
    exact congrArg (fun q => q.left) (comp_cP D₂.toPre k χ)
  have hTU : π ≫ (toUnit (TK R)).left = (toUnit T).left := by
    rw [toUnit_left_eq, toUnit_left_eq]; exact hπ
  have key : ∀ (z : T.left) J J', Good D.toPre.P.L z J → Good D₂.toPre.P.L z J' →
      val (D.toPre.psi (xe χ)) π z J * val (g.s (xe χ)) (π ≫ (toUnit (TK R)).left) z J =
        (wv w (π ≫ D₂.toPre.xK χ) z J J')⁻¹ * val (D₂.toPre.psi χ) π z J' := by
    intro z J J' hJ hJ'
    have ne : sval (f₂ 0) (DegPre.prB D₂.toPre (FractionRing R)).left z J' ≠ 0 := fun e => hne (h₂.eq_zero z hJ' e)
    have cχ := core g β.hom xe hc w f f₂ ν h h₂ hf χ z J J' hJ hJ' ne
    have c0 := core g β.hom xe hc w f f₂ ν h h₂ hf 0 z J J' hJ hJ' ne
    rw [map_zero xe, val_corr hJ g.s_zero, val_one, _root_.mul_one, cPoint_zero, inv_mul_cancel, _root_.one_mul] at c0
    have h0 : val (D.toPre.psi 0) π z J = (wv w (π ≫ D₂.toPre.xK 0) z J J')⁻¹ * val (D₂.toPre.psi 0) π z J' := by
      have e := Uniq.gm_mapsAtExp m₀ π z (fun k => J ((π ≫ D₂.toPre.xK 0) ≫ twφ D₂.toPre D.toPre β.hom g.b k))
        (J' (π ≫ D₂.toPre.xK 0)) (Set.mem_iInter.2 fun k => hJ _) (hJ' _)
      rw [← val_of t₀ π z J (fun k => J ((π ≫ D₂.toPre.xK 0) ≫ twφ D₂.toPre D.toPre β.hom g.b k))
          (fun k => congrArg J (Category.assoc π _ _).symm), val_corr hJ c₀, val_mul hJ, val_pull hJ,
        val_corr hJ g.s_zero, val_one, _root_.mul_one] at e
      rw [e, zpow_neg_one]; rfl
    rw [hT0] at h0
    rw [hTχ, hTU]
    exact grp h0 c0 cχ
  obtain ⟨t₁, ht₁, hv₁⟩ := exists_gen hL (formEq g β.hom xe hc χ)
    (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi (xe χ)) (LB.pullGen D.toPre.P.L _ _ (g.s (xe χ)) (toUnit (TK R)).left))
    (mulGen_isGen _ _ _ _ _ _ _ (D.toPre.psi_gen _) (pullGen_isGen _ _ _ _ (g.isGen _) _))
  have R₁ := reg_val (L' := D₂.toPre.P.L) ht₁ π
  have R₂ := reg_wv (L := D.toPre.P.L) (L' := D₂.toPre.P.L) hw (π ≫ D₂.toPre.xK χ)
  have R₃ := (reg_val' (L := D.toPre.P.L) (D₂.toPre.psi_gen χ) π).inv
  obtain ⟨a, ha⟩ := ((R₁.mul R₂).mul R₃).glue hL hL' (fun U _ h h' => by
    simp only [Category.assoc, Fintype.prod_unique, zpow_neg_one, inv_inv]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_inv, ofMul_prod, ofMul_one]
    simp only [neg_mul, _root_.one_mul, neg_zsmul, Finset.sum_neg_distrib]
    abel)
  have ha1 : a = 1 := unit_ext fun x _ => by
    obtain ⟨J, hJ⟩ := good_exists hL x
    obtain ⟨J', hJ'⟩ := good_exists hL' x
    rw [← ha _ (𝟙 _) x J J' hJ hJ', map_one]
    show val t₁ (𝟙 _ ≫ π) x J * wv w (𝟙 _ ≫ π ≫ D₂.toPre.xK χ) x J J' * (val (D₂.toPre.psi χ) (𝟙 _ ≫ π) x J')⁻¹ = 1
    rw [Category.id_comp, Category.id_comp, hv₁ _ _ x J hJ, val_mul hJ, val_pull hJ, key x J J' hJ hJ']
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one]
    abel
  have H : ∀ (y : (TK R).left) J J', Good D.toPre.P.L y J → Good D₂.toPre.P.L y J' →
      val t₁ (𝟙 _) y J = wv w (D₂.toPre.xK χ) y J J' ^ (-1 : ℤ) * val (D₂.toPre.psi χ) (𝟙 _) y J' := by
    intro y J J' hJ hJ'
    have e := ha _ (DegPre.zF D₂.toPre (FractionRing R)).left y J J' hJ hJ'
    rw [ha1, map_one] at e
    have hz : (DegPre.zF D₂.toPre (FractionRing R)).left ≫ π = 𝟙 _ := PsiCompare.zF_fst D₂.toPre
    change val t₁ ((DegPre.zF D₂.toPre (FractionRing R)).left ≫ π) y J *
      wv w ((DegPre.zF D₂.toPre (FractionRing R)).left ≫ π ≫ D₂.toPre.xK χ) y J J' *
      (val (D₂.toPre.psi χ) ((DegPre.zF D₂.toPre (FractionRing R)).left ≫ π) y J')⁻¹ = 1 at e
    have hz' : (DegPre.zF D₂.toPre (FractionRing R)).left ≫ π ≫ D₂.toPre.xK χ = D₂.toPre.xK χ := by
      rw [← Category.assoc (DegPre.zF D₂.toPre (FractionRing R)).left π, hz, Category.id_comp]
    rw [hz', hz] at e
    rw [zpow_neg_one, ← mul_inv_eq_one, mul_inv, inv_inv, ← _root_.mul_assoc]
    exact e
  exact ⟨t₁, mapsAtExp_of_val hL hL' hw (D₂.toPre.psi_gen χ) ht₁ H, corr_of_val hL fun y J hJ => hv₁ _ _ y J hJ⟩

end GlobalTheory.MumCmp
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic GlobalTheory.PrincipalIntegral
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArtinPrinc

theorem surj_of_isPullback {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂} {g₁ : R₁ ⟶ R₀} {g₂ : R₂ ⟶ R₀}
    (hP : IsPullback f₁ f₂ g₁ g₂) (hs : Function.Surjective g₂) : Function.Surjective f₁ := by
  have h := hP.map (forget CommRingCat)
  intro r
  obtain ⟨r₂, hr₂⟩ := hs (g₁ r)
  obtain ⟨x, hx, -⟩ := ((Types.isPullback_iff _ _ _ _).1 h).2.2 r r₂ hr₂.symm
  exact ⟨x, hx⟩

theorem principal_of_pull : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → Nontrivial R₁ → ∀ (β : CommRingCat.of (cycAway n) ⟶ P) (c : SiegPre g n (zetaAway n) (Spec.map β)) (c₁ : SiegPre g n (zetaAway n) (Spec.map f₁ ≫ Spec.map β)), SiegPB c₁ c (Spec.map f₁) → c₁.Principal → c.Principal := by
  intro g n _ _ P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart _ hs₂ _ β c c₁ hpb hc₁
  obtain ⟨φ, φ₂, hφ, hsq, hw, -⟩ := hpb
  obtain ⟨hA₁, hK₁⟩ := hc₁
  have hl : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hf₁ : Function.Surjective f₁.hom := surj_of_isPullback hP hs₂
  let f := Spec.map f₁
  have hPc : cls c₁.P c₁.isLB = pull φ₂ (cls c.P c.isLB) := (cls_eq_iff _ (pull_isLB c.isLB _)).2 hw
  have hpair : ∀ {T : Over (Spec P)} {T' : Over (Spec R₁)} (u : T'.left ⟶ T.left) (a b : T ⟶ c.A)
      (a' b' : T' ⟶ c₁.A), a'.left ≫ φ = u ≫ a.left → b'.left ≫ φ = u ≫ b.left →
      GlobalTheory.PrincipalIntegral.pair (cls c₁.P c₁.isLB) a' b' = pull u (GlobalTheory.PrincipalIntegral.pair (cls c.P c.isLB) a b) := fun u a b a' b' ha hb => by
    rw [GlobalTheory.PrincipalIntegral.pair, GlobalTheory.PrincipalIntegral.pair, hPc, ← pull_comp, ← pull_comp, SiegelDescent.lift_comp_square hsq u a b a' b' ha hb]
  have hD : c.diag.IsLB := pull_isLB c.isLB _
  have hD₁ : c₁.diag.IsLB := pull_isLB c₁.isLB _
  have hd : cls c₁.diag hD₁ = pull φ (cls c.diag hD) :=
    hpair φ (𝟙 c.A) (𝟙 c.A) (𝟙 c₁.A) (𝟙 c₁.A) (by simp) (by simp)
  have hdiso : LBIso c₁.diag (c.diag.pull φ) := by
    refine (cls_eq_iff hD₁ (pull_isLB hD _)).1 ?_
    rw [cls_pull hD, hd]
  haveI := c.ab.proper
  haveI := c.ab.smooth
  have hA : Out.RelAmple c.A c.diag :=
    GlobalTheory.SharpLift.relAmple_of_closed_proper P c.A c.diag hD R₁ f₁.hom hf₁ c₁.A φ hφ.1 c₁.diag hD₁ hdiso hA₁
  refine ⟨hA, fun T x hx => ?_⟩
  obtain ⟨hpos, hdet⟩ := isE8_W8
  let G := Out.powObj c.A 8
  let pr : Fin 8 → (G ⟶ c.A) := Out.powPr c.A
  have hmon : ∀ u, IsMonHom (pr u) := fun u => inferInstance
  have huniv : ∀ (T : Over (Spec P)) (y : Fin 8 → (T ⟶ c.A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u := fun T y =>
    ⟨(Out.powIsLimit c.A 8).lift (Fan.mk T y), fun u => (Out.powIsLimit c.A 8).fac (Fan.mk T y) ⟨u⟩,
      fun x hx => (Out.powIsLimit c.A 8).uniq (Fan.mk T y) x fun u => hx u.as⟩
  have hG : IsAbelianScheme G := AbelianSchemeGerms.isAbelianScheme_powObj c.A c.ab 7
  let G' := (Over.pullback f).obj G
  letI : (Over.pullback f).Monoidal := (Over.instBraidedPullback (f := f)).toMonoidal
  letI : GrpObj G' := Functor.grpObjObj (F := Over.pullback f)
  let ψ : G'.left ⟶ G.left := Pdiv.PullbackComparison.pφ f G
  have hψ : IsGrpPullback G' G f ψ := Pdiv.PullbackComparison.isGrpPullback f G
  choose pr' hpr using fun u => SharpPull.exists_lift hψ hφ (pr u)
  have hmon' : ∀ u, IsMonHom (pr' u) := fun u => SharpPull.isMonHom_lift hψ hφ (hpr u)
  have huniv' : ∀ (T : Over (Spec R₁)) (y : Fin 8 → (T ⟶ c₁.A)), ∃! x : T ⟶ G', ∀ u, x ≫ pr' u = y u :=
    fun T y => by
    obtain ⟨x₀, hx₀, hu⟩ := huniv (Over.mk (T.hom ≫ f)) (fun u => pushHom hφ T (y u))
    obtain ⟨x, rfl⟩ := SharpPull.push_surj hψ x₀
    refine ⟨x, fun u => SharpPull.push_inj hφ ?_, fun x' hx' => SharpPull.push_inj hψ (hu _ fun u => ?_)⟩
    · rw [SharpPull.push_comp hψ hφ (hpr u), hx₀ u]
    · rw [← SharpPull.push_comp hψ hφ (hpr u), hx' u]
  let L := LB.LinComb c.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) fun uv => W8 uv.1 uv.2
  let L' := LB.LinComb c₁.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr' uv.1) (pr' uv.2)).left)
    fun uv => W8 uv.1 uv.2
  have hL : L.IsLB := LB.isLB_linComb c.isLB _ _
  have hL' : L'.IsLB := LB.isLB_linComb c₁.isLB _ _
  have hLW : cls L hL = quad (cls c.P c.isLB) W8 pr := cls_linComb c.isLB _ _ _
  have hLW' : cls L' hL' = quad (cls c₁.P c₁.isLB) W8 pr' := cls_linComb c₁.isLB _ _ _
  have hiso : LBIso L' (L.pull ψ) := by
    refine (cls_eq_iff hL' (pull_isLB hL _)).1 ?_

    rw [cls_pull hL, hLW, hLW', quad, quad, map_sum]
    exact Finset.sum_congr rfl fun uv _ => by rw [map_zsmul, hpair ψ _ _ _ _ (hpr uv.1) (hpr uv.2)]
  have hadd := pair_mul c hl.globalFns hA
  have hadd' := pair_mul c₁ hl.globalFns hA₁
  have hK' : Out.KTriv G' L' := kTriv_of_kernel hadd' (pair_comm c₁) hmon' huniv' hL' hLW' hdet fun T x hx =>
    hK₁ T x ((cls_eq_zero_iff (pull_isLB c₁.isLB _)).1 hx)
  have hAL : Out.RelAmple G L :=
    PosDefAmple.relAmple_linComb_of_posDef hl.globalFns g n 8 _ _ _ _ c G pr W8 hmon huniv hA hpos
  haveI : IsLocalRing R₁ := IsLocalRing.of_surjective' f₁.hom hf₁
  haveI : IsLocalHom f₁.hom := Function.Surjective.isLocalHom f₁.hom hf₁
  have hK : Out.KTriv G L := GlobalTheory.SharpLift.kTriv_of_localHom P R₁ f₁.hom G hG L hL hAL G' ψ hψ L' hL' hiso hK'
  have hx' : GlobalTheory.PrincipalIntegral.pair (cls c.P c.isLB) (snd c.A T ≫ x) (fst c.A T) = 0 := (cls_eq_zero_iff (pull_isLB c.isLB _)).2 hx
  exact kernel_of_kTriv (n := 8) (G := G) hadd (pair_comm c) hmon huniv hL hLW (0 : Fin 8) hK T x hx'

end GlobalTheory.ArtinPrinc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.isSeparated_siegelModuli_over_integers : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)), IsSeparated (toZ F.X) := by
  first | exact @GlobalTheory.SepSiegel.isSeparated_toZ | exact GlobalTheory.SepSiegel.isSeparated_toZ | (intros; apply GlobalTheory.SepSiegel.isSeparated_toZ <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

noncomputable section

namespace GlobalTheory.CycAwayCover

theorem isUnit_natCast_cycAway {M : ℕ} (hM : M ≠ 0) : IsUnit (M : cycAway M) := by
  refine isUnit_iff_exists_inv.2 ⟨⟨(M : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩, ?_⟩
  exact Subtype.ext (by simpa using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hM : (M : ℂ) ≠ 0))

def awayToCyc (M : ℕ) (hM : M ≠ 0) : Localization.Away (M : ℤ) →+* cycAway M :=
  IsLocalization.Away.lift (S := Localization.Away (M : ℤ)) (M : ℤ) (g := Int.castRingHom (cycAway M))
    (by simpa using isUnit_natCast_cycAway hM)

theorem awayToCyc_injective {M : ℕ} (hM : M ≠ 0) : Function.Injective (awayToCyc M hM) := by
  have hle : Submonoid.powers (M : ℤ) ≤ nonZeroDivisors ℤ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (by exact_mod_cast hM)
  rw [awayToCyc, IsLocalization.Away.lift, IsLocalization.lift_injective_iff]
  intro x y
  rw [(IsLocalization.injective (Localization.Away (M : ℤ)) hle).eq_iff,
    (Int.castRingHom (cycAway M)).injective_int.eq_iff]

theorem finite_awayToCyc {M : ℕ} (hM : M ≠ 0) : (awayToCyc M hM).Finite := by
  letI := (awayToCyc M hM).toAlgebra
  have hv : ∀ hx, (⟨(M : ℂ)⁻¹, hx⟩ : cycAway M) =
      algebraMap (Localization.Away (M : ℤ)) (cycAway M) (IsLocalization.Away.invSelf (M : ℤ)) := by
    intro hx
    have h1 : (M : cycAway M) * ⟨(M : ℂ)⁻¹, hx⟩ = 1 :=
      Subtype.ext (by simpa using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hM : (M : ℂ) ≠ 0))
    have h2 : (M : cycAway M) * algebraMap (Localization.Away (M : ℤ)) (cycAway M)
        (IsLocalization.Away.invSelf (M : ℤ)) = 1 := by
      have := congrArg (algebraMap (Localization.Away (M : ℤ)) (cycAway M))
        (IsLocalization.Away.mul_invSelf (S := Localization.Away (M : ℤ)) (M : ℤ))
      simpa using this
    exact (isUnit_natCast_cycAway hM).mul_left_cancel (h1.trans h2.symm)
  have hint : Algebra.IsIntegral (Localization.Away (M : ℤ)) (cycAway M) := by
    constructor
    rintro ⟨x, hx⟩
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨Polynomial.X ^ M - Polynomial.C 1, Polynomial.monic_X_pow_sub_C _ hM, by
          simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, map_one, Polynomial.eval₂_one]
          exact sub_eq_zero.2 (GlobalTheory.SiegelTor.zetaAway_pow_self hM)⟩
      · convert (isIntegral_algebraMap (R := Localization.Away (M : ℤ)) (x := IsLocalization.Away.invSelf (M : ℤ)) : IsIntegral _ (algebraMap (Localization.Away (M : ℤ)) (cycAway M) _)) using 1
        exact hv _
    | zero => exact isIntegral_zero
    | one => exact isIntegral_one
    | add x y _ _ hx hy => exact hx.add hy
    | neg x _ hx => exact hx.neg
    | mul x y _ _ hx hy => exact hx.mul hy
  haveI : Algebra.FiniteType (Localization.Away (M : ℤ)) (cycAway M) := by
    refine ⟨⟨{zetaAway M}, eq_top_iff.2 ?_⟩⟩
    rintro ⟨x, hx⟩ -
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_singleton_self _))
      · convert Subalgebra.algebraMap_mem (Algebra.adjoin (Localization.Away (M : ℤ)) ((({zetaAway M} : Finset (cycAway M)) : Set (cycAway M)))) (IsLocalization.Away.invSelf (M : ℤ)) using 1
        exact hv _
    | zero => exact Subalgebra.zero_mem _
    | one => exact Subalgebra.one_mem _
    | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
    | neg x _ hx => exact Subalgebra.neg_mem _ hx
    | mul x y _ _ hx hy => exact Subalgebra.mul_mem _ hx hy
  exact (Algebra.IsIntegral.finite : Module.Finite (Localization.Away (M : ℤ)) (cycAway M))

theorem etale_awayToCyc {M : ℕ} (hM : M ≠ 0) : (awayToCyc M hM).Etale := by
  letI := (awayToCyc M hM).toAlgebra
  have hle : Submonoid.powers (M : ℤ) ≤ nonZeroDivisors ℤ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (by exact_mod_cast hM)
  haveI : IsDomain (Localization.Away (M : ℤ)) := IsLocalization.isDomain_localization hle
  haveI : IsDedekindDomain (Localization.Away (M : ℤ)) :=
    IsLocalization.isDedekindDomain ℤ hle (Localization.Away (M : ℤ))
  haveI : Module.Finite (Localization.Away (M : ℤ)) (cycAway M) := finite_awayToCyc hM
  haveI : FaithfulSMul (Localization.Away (M : ℤ)) (cycAway M) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (awayToCyc_injective hM)
  haveI : Module.Flat (Localization.Away (M : ℤ)) (cycAway M) := inferInstance
  haveI : Algebra.FinitePresentation (Localization.Away (M : ℤ)) (cycAway M) :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  haveI := formallyUnramified_cycAway hM (Localization.Away (M : ℤ))
  exact (Algebra.Etale.of_formallyUnramified_of_flat : Algebra.Etale (Localization.Away (M : ℤ)) (cycAway M))

theorem exists_cycAway_cover : ∀ (M : ℕ) (S : Scheme.{0}), 0 < M → IsUnit (M : Γ(S, ⊤)) → ∃ (S' : Over S) (t₀ : S'.left ⟶ Sp (cycAway M)), IsFinite S'.hom ∧ Etale S'.hom ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (t₁ : T ⟶ Sp (cycAway M)), ∃! g : T ⟶ S'.left, g ≫ S'.hom = f ∧ g ≫ t₀ = t₁ := by
  intro M S hM hS
  have hM0 : M ≠ 0 := hM.ne'
  have hSu : IsUnit ((Int.castRingHom Γ(S, ⊤)) (M : ℤ)) := by simpa using hS
  let φ : S ⟶ Sp (Localization.Away (M : ℤ)) :=
    S.toSpecΓ ≫ spMap (IsLocalization.Away.lift (S := Localization.Away (M : ℤ)) (M : ℤ) hSu)
  let S' : Over S := Over.mk (pullback.fst φ (spMap (awayToCyc M hM0)))
  haveI : IsFinite (spMap (awayToCyc M hM0)) := (IsFinite.SpecMap_iff _).2 (finite_awayToCyc hM0)
  haveI : Etale (spMap (awayToCyc M hM0)) := HasRingHomProperty.Spec_iff.2 (etale_awayToCyc hM0)
  refine ⟨S', pullback.snd φ (spMap (awayToCyc M hM0)), ?_, ?_, ?_⟩
  · exact (inferInstance : IsFinite (pullback.fst φ (spMap (awayToCyc M hM0))))
  · exact (inferInstance : Etale (pullback.fst φ (spMap (awayToCyc M hM0))))
  · intro T f t₁
    haveI : IsOpenImmersion (spMap (algebraMap ℤ (Localization.Away (M : ℤ)))) :=
      inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (M : ℤ))))))
    have e : f ≫ φ = t₁ ≫ spMap (awayToCyc M hM0) :=
      (cancel_mono (spMap (algebraMap ℤ (Localization.Away (M : ℤ))))).1 (specZIsTerminal.hom_ext _ _)
    refine ⟨pullback.lift f t₁ e, ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩, ?_⟩
    rintro g ⟨h1, h2⟩
    exact pullback.hom_ext (h1.trans (pullback.lift_fst _ _ e).symm) (h2.trans (pullback.lift_snd _ _ e).symm)

end GlobalTheory.CycAwayCover
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_inclusion_cyclotomicAwayRing_finite_etale : ∀ n N : ℕ, N ≠ 0 → n ∣ N → ∃ j : cycAway n →+* cycAway N, Function.Injective j ∧ j (zetaAway n) = zetaAway N ^ (N / n) ∧ ((∃ a, N ∣ n ^ a) → IsFinite (spMap j) ∧ Etale (spMap j) ∧ Surjective (spMap j)) := by
  first | exact @GlobalTheory.SiegelTor.exists_inclusion_cycAway | exact GlobalTheory.SiegelTor.exists_inclusion_cycAway | (intros; apply GlobalTheory.SiegelTor.exists_inclusion_cycAway <;> assumption)
end
