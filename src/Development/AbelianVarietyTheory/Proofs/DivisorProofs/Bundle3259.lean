module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3236
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2339
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3210
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2795
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle621
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3189
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle731
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.GmCharPow
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGrpPullbackThick
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericSectionExtendsNormal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3204
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2995
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFourthPowerUnderIsogeny
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3234
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3230
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

noncomputable section

namespace GlobalTheory.USep.EvG.SymVal

theorem sym_val : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ a : D.X, ∃ c ∈ k₀, (val D.sym (spMap ev ≫ (D.c a).left) z J).val =
      ((GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c (-a)).left))⁻¹ * GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c a).left)).val * toStk z c := by
  intro V₁ _ _ _ _ _ D τ₀ W₀ _ ib B₀ _ M₀ c₀ τ₁ β w hFB K _ _ ev k₀ hk₀ hk z J J₀ hJ hJ₀ a
  obtain ⟨-, hM₀, hpb, hw, hc, -, -⟩ := hFB
  set φ' : Fin 2 → (D.P.A.left ⟶ D.P.A.left) := ![(ι[D.P.A]).left, 𝟙 D.P.A.left] with hφ'
  obtain ⟨t, ht, hmap⟩ := GlobalTheory.T.exists_generator_transport_down_lineBundleIso w hw hM₀ D.P.isLB φ' ![1, -1] D.sym D.sym_gen
  have hφ : ∀ k, φ' k ≫ β = β ≫ (![(ι[B₀]).left, 𝟙 B₀.left] : Fin 2 → (B₀.left ⟶ B₀.left)) k := by
    intro k
    fin_cases k
    · exact GlobalTheory.PolDeg.SymPol.inv_comm hpb
    · simp [hφ']
  have hpt : ∀ b : D.X, (spMap ev ≫ (D.c b).left) ≫ D.P.A.hom = spMap ev := fun b => by
    rw [Category.assoc, Over.w (D.c b)]; rfl
  have hdef : ∀ b : D.X, DefOver k₀ ((spMap ev ≫ (D.c b).left) ≫ β) := fun b => by
    have e : (spMap ev ≫ (D.c b).left) ≫ β = spMap (ev.comp ib) ≫ c₀ b := by
      rw [Category.assoc]
      erw [hc b]
      rw [← Category.assoc]
      congr 1
      simp only [spMap, ← Spec.map_comp]
      rfl
    rw [e]
    exact GlobalTheory.Poinc.Sep.defOver_comp k₀ (GlobalTheory.Poinc.Sep.defOver_spMap k₀ _ hk) _

  have read : ∀ (x : Sp K ⟶ D.P.A.left) (z' : Sp K) (I : (Sp K ⟶ D.P.A.left) → D.P.L.ι)
      (I₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z' I → Good M₀ z' I₀ →
      val t x z' I₀ = gwx w z' I I₀ (x ≫ (ι[D.P.A]).left) * (gwx w z' I I₀ x)⁻¹ * val D.sym x z' I := by
    intro x z' I I₀ hI hI₀
    have H := hmap (Sp K) x z' (fun k => I₀ ((x ≫ φ' k) ≫ β)) (fun k => I (x ≫ φ' k))
      (fun k => hI₀ ((x ≫ φ' k) ≫ β)) (fun k => hI (x ≫ φ' k))
    rw [Category.comp_id, Fin.prod_univ_two] at H
    rw [val_of t x z' I₀ (fun k => I₀ ((x ≫ φ' k) ≫ β)) (fun k => by rw [Category.assoc]), H]
    simp only [hφ', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, zpow_one, zpow_neg, Category.comp_id]
    rfl
  have hx₁ : (spMap ev ≫ (D.c 0).left) ≫ (ι[D.P.A]).left = spMap ev ≫ (D.c 0).left := by
    rw [Category.assoc, ← Over.comp_left, ← GlobalTheory.PsiEvenPull.c_neg, neg_zero]
  have hnorm : ∀ (z' : Sp K) (I₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good M₀ z' I₀ →
      val t (spMap ev ≫ (D.c 0).left) z' I₀ = 1 := by
    intro z' I₀ hI₀
    choose I hI using fun χ : Sp K ⟶ D.P.A.left => exists_chart D.P.isLB (χ z')
    have hIg : Good D.P.L z' I := hI
    rw [read _ z' I I₀ hIg hI₀, hx₁, _root_.mul_inv_cancel, _root_.one_mul, GlobalTheory.Poinc.ThetaOne.c_zero]
    have e1 : (1 : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A).left = eSec D.P.A := rfl
    rw [e1, ← val_pull hIg, val_corr hIg D.sym_rig, val_one]
  obtain ⟨c, hc₀, hv⟩ := GlobalTheory.T.generator_values_mem_subfield_galoisDescent V₁ W₀ ib D.P.A D.P.isAb B₀ β hpb.1 M₀ hM₀ (Fin 2) (fun k => φ' k ≫ β) _ hφ
    ![1, -1] t ht K ev k₀ hk₀ hk _ (hpt 0) (hdef 0) hnorm _ (hpt a) (hdef a) z J₀ hJ₀
  refine ⟨c, hc₀, ?_⟩
  have r := read (spMap ev ≫ (D.c a).left) z J J₀ hJ hJ₀
  have hneg : (spMap ev ≫ (D.c a).left) ≫ (ι[D.P.A]).left = spMap ev ≫ (D.c (-a)).left := by
    rw [Category.assoc, ← Over.comp_left, ← GlobalTheory.PsiEvenPull.c_neg]
  rw [hneg] at r
  have key : val D.sym (spMap ev ≫ (D.c a).left) z J =
      (gwx w z J J₀ (spMap ev ≫ (D.c (-a)).left))⁻¹ * gwx w z J J₀ (spMap ev ≫ (D.c a).left) *
        val t (spMap ev ≫ (D.c a).left) z J₀ := by
    rw [r]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [key, Units.val_mul, hv]

end GlobalTheory.USep.EvG.SymVal
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

noncomputable section

namespace GlobalTheory.MumProd

theorem adj_inl : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₁ D₂ : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → (∀ y, q₁ (j₁ y) = y) → (∀ y, q₂ (j₁ y) = 0) → Adj (pol D₁) (pol D) i₁ p₁ j₁ q₁ :=
  GlobalTheory.MumProdAdj.adj_first_factor

end GlobalTheory.MumProd
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem thick_apply_eq_closedPoint {R : Type} [CommRing R] [IsLocalRing R] (e : ℕ)
    (p : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))) :
    thick R (maximalIdeal R) e p = closedPoint R := by
  haveI : p.asIdeal.IsPrime := p.isPrime
  apply PrimeSpectrum.ext
  show Ideal.comap (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))) p.asIdeal = maximalIdeal R
  have hle : maximalIdeal R ^ (e + 1) ≤ Ideal.comap (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))) p.asIdeal := by
    intro a ha
    simp [Ideal.Quotient.eq_zero_iff_mem.2 ha]
  have hm : maximalIdeal R ≤ Ideal.comap (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))) p.asIdeal :=
    (Ideal.IsPrime.comap _).le_of_pow_le hle
  exact ((maximalIdeal.isMaximal R).eq_of_le (Ideal.IsPrime.comap _).ne_top hm).symm

theorem exists_thick_zero {R : Type} [CommRing R] [IsLocalRing R] (e : ℕ) (G : Over (Sp R))
    (y : (thickObj R (maximalIdeal R) e G).left) :
    ∃ y₀ : (thickObj R (maximalIdeal R) 0 G).left,
      (fstG (maximalIdeal R) 0 G).left y₀ = (fstG (maximalIdeal R) e G).left y := by
  have hne : maximalIdeal R ^ (0 + 1) ≠ ⊤ := by
    rw [zero_add, pow_one]; exact (maximalIdeal.isMaximal R).ne_top
  haveI : Nontrivial (R ⧸ maximalIdeal R ^ (0 + 1)) := Ideal.Quotient.nontrivial_iff.2 hne
  haveI : IsLocalRing (R ⧸ maximalIdeal R ^ (0 + 1)) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have h1 : G.hom (pullback.fst G.hom (thick R (maximalIdeal R) e) y) = closedPoint R := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, thick_apply_eq_closedPoint]
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := thick R (maximalIdeal R) 0)
    (pullback.fst G.hom (thick R (maximalIdeal R) e) y) (closedPoint _)
    (h1.trans (thick_apply_eq_closedPoint 0 _).symm)
  exact ⟨z, hz⟩

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem mem_basicOpen_of_secRatioEq : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (e k k' : ℕ), 3 ≤ k → ∀ (x : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G) (T : H0 U.LG.L k → H0 U.LG.L k'), (∀ s₁ s₂ : H0 U.LG.L k, SecRatioEq U.LG.L (x.left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (T s₁) (T s₂)) → ∀ (y : (thickObj R (maximalIdeal R) e G).left) (s₀ : H0 U.LG.L k) (i' : Fin 1 → U.LG.L.ι), y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen (((fstG (maximalIdeal R) e G).left.app (secChart U.LG.L i')).hom ((T s₀).f i')) → ∃ i : Fin 1 → U.LG.L.ι, y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen ((((x).left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L i)).hom (s₀.f i)) := by
  intro R _ _ _ hB D A G _ _ hG U e k k' hk x T hT y s₀ i' hy
  obtain ⟨y₀, hy₀⟩ := exists_thick_zero e G (x.left y)
  obtain ⟨s₁, j, hs₁⟩ := GlobalTheory.T.exists_section_nonvanishing_closedFibre_of_three_le R hB D A G hG U k hk y₀
  refine ⟨j, ?_⟩
  have hs₁' : (fstG (maximalIdeal R) 0 G).left y₀ ∈ G.left.basicOpen (s₁.f j) :=
    (Scheme.preimage_basicOpen (fstG (maximalIdeal R) 0 G).left (s₁.f j)).ge hs₁
  have hu : y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen
      (((x.left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L j)).hom (s₁.f j)) := by
    refine (Scheme.preimage_basicOpen (x.left ≫ (fstG (maximalIdeal R) e G).left) (s₁.f j)).le ?_
    show (x.left ≫ (fstG (maximalIdeal R) e G).left) y ∈ G.left.basicOpen (s₁.f j)
    rw [Scheme.Hom.comp_apply, ← hy₀]
    exact hs₁'
  by_contra hn
  have hE := congrArg (thickObj R (maximalIdeal R) e G).left.basicOpen (hT s₁ s₀ j i')
  simp only [Scheme.basicOpen_mul, Scheme.basicOpen_res] at hE
  have hmem : y ∈ ((x.left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L j ⊓
      (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i') := by
    rw [TopologicalSpace.Opens.mem_inf]
    exact ⟨Scheme.basicOpen_le _ _ hu, Scheme.basicOpen_le _ _ hy⟩
  have h2 := hE.le (by
    simp only [TopologicalSpace.Opens.mem_inf] at hmem ⊢
    exact ⟨⟨hmem, hu⟩, ⟨hmem, hy⟩⟩)
  simp only [TopologicalSpace.Opens.mem_inf] at h2
  exact hn h2.1.2

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

theorem _root_.GlobalTheory.T.harrisTaylor_levelForgetting_finite_etale_surjective : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N N' : ℕ) (hd : N ∣ N') (hc : N'.Coprime p), 3 ≤ N → ∀ (M : Model b N) (M' : Model b N') (t : M'.X ⟶ M.X), t ≫ M.s = M'.s → Nonempty (ObjMap (M'.univ.forget N hd hc) M.univ t) → IsFinite t ∧ Etale t ∧ Surjective t := by
  first | exact @GlobalTheory.UPel.HT.forget_map_finite_etale_surjective | exact GlobalTheory.UPel.HT.forget_map_finite_etale_surjective | (intros; apply GlobalTheory.UPel.HT.forget_map_finite_etale_surjective <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ClosedGen

theorem cst_eq_baseRingHom {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (W : X.Opens) :
    (GlobalTheory.QCoh.Qcqs.baseRingHom f W).hom = GlobalTheory.AbLaw.cst f W := by
  rfl

end GlobalTheory.Mum.ClosedGen


open GlobalTheory.Mum.ClosedGen in
theorem GlobalTheory.Mum.exists_ratio_gen_closed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∃ (n : ℕ) (τ : Fin n → H0 U.LG.L k), ∀ w : (thickObj R (maximalIdeal R) 0 G).left, ∃ (j : Fin n) (i : Fin 1 → U.LG.L.ι) (N : (thickObj R (maximalIdeal R) 0 G).left.Opens) (r : Fin n → Γ((thickObj R (maximalIdeal R) 0 G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ j) i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ j) i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) 0 G).left, N), ∃ P Q : MvPolynomial (Fin n) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r P := by
  intro R _ _ _ hB D A G _ _ hG U
  obtain ⟨Y⟩ : Nonempty (Ext D.toPre) := inferInstance
  obtain ⟨S, k₁, hk₁⟩ := GlobalTheory.T.exists_theta_immersion_torus_extension_projective R hB D Y
  choose k₀f hk₀f using (GlobalTheory.T.exists_integralThetaFamily_prescribed_leadingTerm R hB D).1
  refine ⟨max 3 (max k₁ (S.sup k₀f)), le_max_left _ _, ?_⟩
  intro k hk
  have hk3 : 3 ≤ k := le_trans (le_max_left _ _) hk
  have hkk₁ : k₁ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkS : S.sup k₀f ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  obtain ⟨N, α, b, τ, hτ, hαb, himm⟩ := hk₁ k hkk₁
  have hF : ∀ j, ∃ F : IntFam (maximalIdeal R) D.toPre k, F.Lead (α j) (b j) := fun j =>
    hk₀f (α j) k (le_trans (Finset.le_sup (hαb j).1) hkS) (b j)
  choose F hF using hF
  have hs : ∀ j, ∃ σ : H0 U.LG.L k, ∀ e, U.ExpandsAt e k σ (F j).f := fun j =>
    IntFam.exists_expandsAt R hB D A G U hG k (by omega) (F j)
  choose s hs using hs
  let T : Over (Sp R) := Over.mk ((thickObj R (maximalIdeal R) 0 G).hom ≫ thick R (maximalIdeal R) 0)
  obtain ⟨ξ, hξ⟩ := GlobalTheory.TorusCoord.exists_isPointOf (U.gt 0) (T := T) (𝟙 (thickObj R (maximalIdeal R) 0 G).left)
    (Category.id_comp _)
  let ψ : T ⟶ Y.H := (Y.Φ T).symm ξ
  have hψ : GlobalTheory.TorusCoord.IsPointOf (U.gt 0) (𝟙 (thickObj R (maximalIdeal R) 0 G).left) (Y.Φ T ψ) := by
    simp only [ψ, Equiv.apply_symm_apply]; exact hξ
  haveI hψi : IsImmersion ψ.left := GlobalTheory.T.closedFibre_torusCoordinates_isImmersion R D A G U.toUnifPre Y ψ hψ
  set p₀ := (fstG (maximalIdeal R) 0 G).left with hp₀
  let φ := ψ.left ≫ GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ
  haveI : IsImmersion φ := IsImmersion.comp _ _
  have hpre : ∀ j, φ ⁻¹ᵁ GlobalTheory.ProjSpace.chart R N j = ψ.left ⁻¹ᵁ nonzeroLocus (τ j) := fun j => by
    simp only [φ, Scheme.Hom.comp_preimage, GlobalTheory.ProjSpace.toProj_preimage_chart]
  have hstr : φ ≫ PSpace.str R N = p₀ ≫ G.hom := by
    simp only [φ, Category.assoc, GlobalTheory.ProjSpace.toProj_str]
    rw [Over.w ψ]
    exact (pullback.condition).symm
  refine ⟨N + 1, s, fun w => ?_⟩
  have hw : ψ.left w ∈ ⨆ i, nonzeroLocus (τ i) := by rw [hτ]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hw
  obtain ⟨J, hJ⟩ := GlobalTheory.TorusCoord.exists_good' U.LG.isLB w
  let i : Fin 1 → U.LG.L.ι := fun _ => J (p₀ ≫ 𝟙 G.left)
  have hi : p₀ w ∈ secChart U.LG.L i := hJ.mem (fun _ : Fin 1 => 𝟙 G.left) p₀
  have hφw : φ w ∈ GlobalTheory.ProjSpace.chart R N j := by
    show w ∈ φ ⁻¹ᵁ GlobalTheory.ProjSpace.chart R N j
    rw [hpre]; exact hj
  obtain ⟨W, hW, hwW, hWV, hWa, hgen⟩ := GlobalTheory.T.exists_affineOpen_fractions_projSpace_immersion R N _ φ inferInstance w (p₀ ⁻¹ᵁ secChart U.LG.L i) j hi hφw
  have hWψ : W ≤ ψ.left ⁻¹ᵁ nonzeroLocus (τ j) := hW.trans (hpre j).le
  have hr : ∀ l, GlobalTheory.ProjSpace.pullRatio φ W j hW l =
      (ψ.left.appLE (nonzeroLocus (τ j)) W hWψ).hom (GlobalTheory.ProjSpace.secRatio (τ j) (τ l)) := by
    intro l
    rw [← GlobalTheory.ProjSpace.pullRatio_toProj Y.H.hom τ hτ j l, GlobalTheory.ProjSpace.appLE_pullRatio]
  refine ⟨j, i, W, GlobalTheory.ProjSpace.pullRatio φ W j hW, hwW, hWa, hWV, fun y hy => ?_, fun g => ?_⟩
  · have hyψ : ψ.left y ∈ nonzeroLocus (τ j) := hWψ hy
    obtain ⟨hu, hl⟩ := GlobalTheory.T.closedFibre_thetaSectionGerm_eq_fourierRatio_mul R D A G U.toUnifPre Y ψ hψ k (N + 1) α b τ F s (fun j => (hαb j).2) hF
      (fun j => hs j 0) y j i hyψ (hWV hy)
    refine ⟨hu, fun l => ?_⟩
    rw [hl l, hr l, gs_appLE _ _ _ _ (𝟙 _) y hy, Category.id_comp]
  · obtain ⟨P, Q, hQ, hPQ⟩ := hgen g
    have hc : (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str R N) W).hom = GlobalTheory.AbLaw.cst (p₀ ≫ G.hom) W := by
      rw [hstr]; exact cst_eq_baseRingHom _ _
    rw [hc] at hQ hPQ
    exact ⟨P, Q, hQ, hPQ⟩

end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnifWeight

open ReciprocityTheory.ChartRestriction.G.DVR

section Char

variable {S : Scheme.{0}} {X X₁ X₂ : Type} [AddCommGroup X] [AddCommGroup X₁] [AddCommGroup X₂]

theorem gm_char_hom {j : X₁ → X} {τ : splitTorus S X ⟶ splitTorus S X₁} (hτ : TorusHomOf j τ) {T : Over S}
    (r : T ⟶ splitTorus S X) (y : T.left) (x : X₁) :
    gm (r ≫ τ).left y ⊤ (charUnit S X₁ x) = gm r.left y ⊤ (charUnit S X (j x)) := by
  rw [← hτ x]
  exact ((gm_res r.left y (V := ⊤) _ trivial _).trans (gm_pull r.left τ.left y ⊤ trivial _)).symm

theorem gm_char_add {T : Over S} (r : T ⟶ splitTorus S X) (y : T.left) (a b : X) :
    gm r.left y ⊤ (charUnit S X (a + b)) = gm r.left y ⊤ (charUnit S X a) * gm r.left y ⊤ (charUnit S X b) := by
  rw [PowTorusCoord.gm_char, PowTorusCoord.gm_char, PowTorusCoord.gm_char, ofAdd_add, map_mul, map_mul]

end Char

theorem val_weight {R : Type} [CommRing R] [IsDomain R] {D₁ : DegPre R} {S : Scheme.{0}} {s : S ⟶ Sp R}
    {X : Type} [AddCommGroup X] {G G₁ : Over S} [GrpObj G] [GrpObj G₁] (σ : G ⟶ G₁) [IsMonHom σ]
    {P₁ : (Over.map s).obj G₁ ⟶ D₁.P.A} {x : D₁.X} (t₁ : LB.Gen (LB.LinComb D₁.P.L (D₁.Oφ P₁ x) Oinvε))
    (κ : splitTorus S X ⟶ G) (κ₁ : splitTorus S D₁.X ⟶ G₁) (τ : splitTorus S X ⟶ splitTorus S D₁.X)
    (hκ : κ ≫ σ = τ ≫ κ₁)
    (hw : LB.Gen.Corr D₁.P.L _ _ _ _
      (LB.pullGen D₁.P.L _ _ t₁ (lift (fst (splitTorus S D₁.X) G₁ ≫ κ₁) (snd _ _) ≫ μ[G₁]).left)
      (LB.mulGen D₁.P.L _ _ _ _ (charGen D₁.X G₁ D₁.P.L x)
        (LB.pullGen D₁.P.L _ _ t₁ (snd (splitTorus S D₁.X) G₁).left)))
    (y : (splitTorus S X ⊗ G).left) {J} (hJ : Good D₁.P.L y J) :
    val (Y := G₁.left) t₁ ((lift (fst (splitTorus S X) G ≫ κ) (snd _ _) ≫ μ[G]) ≫ σ).left y J =
      gm (fst (splitTorus S X) G ≫ τ).left y ⊤ (charUnit _ D₁.X x) *
        val (Y := G₁.left) t₁ (snd (splitTorus S X) G ≫ σ).left y J := by
  let N : splitTorus S X ⊗ G ⟶ splitTorus S D₁.X ⊗ G₁ := τ ⊗ₘ σ
  have n₁ : N ≫ fst _ _ = fst _ _ ≫ τ := tensorHom_fst _ _
  have n₂ : N ≫ snd _ _ = snd _ _ ≫ σ := tensorHom_snd _ _
  have n₃ : N ≫ (lift (fst (splitTorus S D₁.X) G₁ ≫ κ₁) (snd _ _) ≫ μ[G₁]) =
      (lift (fst (splitTorus S X) G ≫ κ) (snd _ _) ≫ μ[G]) ≫ σ := by
    rw [← Hom.mul_def, ← Hom.mul_def, MonObj.comp_mul, MonObj.mul_comp, ← Category.assoc, n₁, n₂, Category.assoc,
      Category.assoc, hκ]
  rw [← n₁, ← n₂, ← n₃]
  exact (val_pull hJ _ _ _).symm.trans ((val_corr hJ hw N.left).trans ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (TorusCoordPull.val_charGen _ _ _ _ _ _ _) (val_pull hJ _ _ _))))

theorem weight_box₂ : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X) (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)) (S : Scheme.{0}) (s : S ⟶ Sp R) (G G₁ G₂ : Over S) [GrpObj G] [GrpObj G₁] [GrpObj G₂] (σ₁ : G ⟶ G₁) (σ₂ : G ⟶ G₂) (P : (Over.map s).obj G ⟶ D.P.A) (P₁ : (Over.map s).obj G₁ ⟶ D₁.P.A) (P₂ : (Over.map s).obj G₂ ⟶ D₂.P.A) (χ : D.X) (t : LB.Gen (LB.LinComb D.P.L (D.Oφ P χ) Oinvε)) (t₁ : LB.Gen (LB.LinComb D₁.P.L (D₁.Oφ P₁ (q₁ χ)) Oinvε)) (t₂ : LB.Gen (LB.LinComb D₂.P.L (D₂.Oφ P₂ (q₂ χ)) Oinvε)), IsMonHom σ₁ → IsMonHom σ₂ → IsBoxGen (Y := G.left) (Y₁ := G₁.left) (Y₂ := G₂.left) w σ₁.left σ₂.left t t₁ t₂ → ∀ (κ : splitTorus S D.X ⟶ G) (κ₁ : splitTorus S D₁.X ⟶ G₁) (κ₂ : splitTorus S D₂.X ⟶ G₂) (j₁ : D₁.X → D.X) (j₂ : D₂.X → D.X) (τ₁ : splitTorus S D.X ⟶ splitTorus S D₁.X) (τ₂ : splitTorus S D.X ⟶ splitTorus S D₂.X), j₁ (q₁ χ) + j₂ (q₂ χ) = χ → TorusHomOf j₁ τ₁ → TorusHomOf j₂ τ₂ → κ ≫ σ₁ = τ₁ ≫ κ₁ → κ ≫ σ₂ = τ₂ ≫ κ₂ → (Over.map s).map (lift (fst (splitTorus S D.X) G ≫ κ) (snd _ _) ≫ μ[G]) ≫ P = (Over.map s).map (snd (splitTorus S D.X) G) ≫ P → LB.Gen.Corr D₁.P.L _ _ _ _ (LB.pullGen D₁.P.L _ _ t₁ (lift (fst (splitTorus S D₁.X) G₁ ≫ κ₁) (snd _ _) ≫ μ[G₁]).left) (LB.mulGen D₁.P.L _ _ _ _ (charGen D₁.X G₁ D₁.P.L (q₁ χ)) (LB.pullGen D₁.P.L _ _ t₁ (snd (splitTorus S D₁.X) G₁).left)) → LB.Gen.Corr D₂.P.L _ _ _ _ (LB.pullGen D₂.P.L _ _ t₂ (lift (fst (splitTorus S D₂.X) G₂ ≫ κ₂) (snd _ _) ≫ μ[G₂]).left) (LB.mulGen D₂.P.L _ _ _ _ (charGen D₂.X G₂ D₂.P.L (q₂ χ)) (LB.pullGen D₂.P.L _ _ t₂ (snd (splitTorus S D₂.X) G₂).left)) → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ t (lift (fst (splitTorus S D.X) G ≫ κ) (snd _ _) ≫ μ[G]).left) (LB.mulGen D.P.L _ _ _ _ (charGen D.X G D.P.L χ) (LB.pullGen D.P.L _ _ t (snd (splitTorus S D.X) G).left)) := by
  intro R _ _ D D₁ D₂ p₁ p₂ q₁ q₂ w S s G G₁ G₂ _ _ _ σ₁ σ₂ P P₁ P₂ χ t t₁ t₂ hσ₁ hσ₂ H κ κ₁ κ₂ j₁ j₂ τ₁ τ₂ hχ
    hτ₁ hτ₂ hκ₁ hκ₂ aO hw₁ hw₂
  refine corr_of_val D.P.isLB fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at D₁.P.isLB y
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at D₂.P.isLB y
  have v₁ := val_weight σ₁ t₁ κ κ₁ τ₁ hκ₁ hw₁ y hJ₁
  have v₂ := val_weight σ₂ t₂ κ κ₂ τ₂ hκ₂ hw₂ y hJ₂
  rw [gm_char_hom hτ₁] at v₁
  rw [gm_char_hom hτ₂] at v₂
  have c := gm_char_add (fst (splitTorus S D.X) G) y (j₁ (q₁ χ)) (j₂ (q₂ χ))
  rw [hχ] at c
  have b₁ := H _ (lift (fst (splitTorus S D.X) G ≫ κ) (snd _ _) ≫ μ[G]).left y J₁ J₂ J hJ₁ hJ₂ hJ
  have b₂ := H _ (snd (splitTorus S D.X) G).left y J₁ J₂ J hJ₁ hJ₂ hJ
  have e : ∀ a, (lift (fst (splitTorus S D.X) G ≫ κ) (snd _ _) ≫ μ[G]).left ≫ D.Oφ P χ a =
      (snd (splitTorus S D.X) G).left ≫ D.Oφ P χ a := fun a =>
    (WeightPf.Oφ_comp ((Over.map s).map (lift (fst (splitTorus S D.X) G ≫ κ) (snd _ _) ≫ μ[G])) P χ a).trans
      ((congrArg (fun m => D.Oφ m χ a) aO).trans
        (WeightPf.Oφ_comp ((Over.map s).map (snd (splitTorus S D.X) G)) P χ a).symm)
  have o : (∏ a, om w y J₁ J₂ J ((lift (fst (splitTorus S D.X) G ≫ κ) (snd _ _) ≫ μ[G]).left ≫ D.Oφ P χ a) ^ Oinvε a) =
      ∏ a, om w y J₁ J₂ J ((snd (splitTorus S D.X) G).left ≫ D.Oφ P χ a) ^ Oinvε a :=
    Finset.prod_congr rfl fun a _ => congrArg (fun m => om w y J₁ J₂ J m ^ Oinvε a) (e a)
  have v₄ := (congrArg₂ (· * ·) o rfl).symm.trans (b₁.trans ((congrArg₂ (· * ·) v₁ v₂).trans
    ((_root_.mul_mul_mul_comm _ _ _ _).trans ((congrArg₂ (· * ·) c.symm b₂.symm).trans (mul_left_comm _ _ _)))))
  have v₅ := mul_left_cancel v₄
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (TorusCoordPull.val_charGen _ _ _ _ _ _ _) (val_pull hJ _ _ _))).symm)
  rw [Category.id_comp, Category.id_comp, Category.id_comp]
  exact v₅

end GlobalTheory.ProdUnifWeight
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TozCore

theorem exists_extension_of_cover_hodge : ∀ (o : Type) [CommRing o] (g : ℕ) (Z S' : Scheme.{0}) (z : Z ⟶ Sp o) (π : S' ⟶ Z) [IsProper z] [IsProper π] (OZ : LB Z), OZ.IsLB → GlobalTheory.IsAmpleLB OZ → ∀ (G : Over S') [GrpObj G] [IsCommMonObj G] (N : ℕ), IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → LBIso (OZ.pull π) (lbPow (hodge G g) N) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (b : o →+* R) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (y : Sp (FractionRing R) ⟶ S') (α : pullback G₁.hom (jK R) ⟶ G.left), IsGrpPullback ((Over.pullback (jK R)).obj G₁) G y α → y ≫ π ≫ z = jK R ≫ spMap b → ∃ a : Sp R ⟶ Z, jK R ≫ a = y ≫ π := by
  intro o _ g Z S' z π _ _ OZ hOZ hA G _ _ N hG hsm hw R _ _ _ _ _ _ b G₁ _ _ hG₁ y α hα hy
  have := hA.compactSpace
  have := hA.quasiSeparatedSpace
  have := hG.separated
  have : QuasiSeparated G.hom := inferInstance
  have hL : (hodge G g).IsLB := isLB_hodge G g
  obtain ⟨T, hT, hTv⟩ := GlobalTheory.T.exists_transport_generator_lbPow_to_ampleBundle S' Z π OZ (hodge G g) N hOZ hL hw
  obtain ⟨e₀, he₀, H⟩ := GlobalTheory.T.exists_integral_hodgeBundle_generator S' g G hG hsm R G₁ hG₁ y α hα
  have amp : ∀ z : Z, ∃ (d : ℕ) (s : H0 OZ d), 1 ≤ d ∧ z ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s) := by
    intro x
    obtain ⟨n, hn, s, hs, ha⟩ := hA.exists_affine x
    refine ⟨n, GlobalTheory.ThetaShift.secFinOne s, hn, ?_, ?_⟩
    · rw [GlobalTheory.ThetaShift.nonzeroLocus_secFinOne]; exact hs
    · rw [GlobalTheory.ThetaShift.nonzeroLocus_secFinOne]; exact ha
  refine GlobalTheory.ExtLB.exists_extension Z OZ hOZ amp R (y ≫ π) (T _ y e₀) (hT _ y e₀ he₀) ?_
  intro W _ _ _ hW φ gam hg
  have := hW.1
  have sq : spMap gam ≫ jK R = jK W ≫ spMap φ := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext hg)
  obtain ⟨χ', hχ', -⟩ := val_exists (π ≫ z) (spMap gam ≫ y) (spMap φ ≫ spMap b) (by
    rw [Category.assoc, hy, ← Category.assoc, sq, Category.assoc])
  obtain ⟨e₀', he₀', hv⟩ := H W hW φ gam hg χ' hχ'.symm
  refine ⟨χ' ≫ π, by rw [← Category.assoc, ← hχ', Category.assoc], T _ χ' e₀', hT _ χ' e₀' he₀', ?_⟩
  exact hTv _ _ _ y χ' e₀ e₀' (spMap gam) (jK W) he₀ he₀' hχ'.symm hv

end GlobalTheory.TozCore
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_unique_symplecticLevel_lift_closedPoint : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (K : Type) [Field K] [IsAlgClosed K] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (βV : cycAway n →+* V) (π : V →+* K), Function.Surjective π → ∀ (c : SiegPre g n (zetaAway n) (spMap (π.comp βV))), c.Principal → ∀ (AV : Over (Sp V)) [GrpObj AV] [IsCommMonObj AV] (φ : c.A.left ⟶ AV.left) (φ₂ : (G2 c.A).left ⟶ (G2 AV).left) (PV : LB (G2 AV).left), IsAbelianScheme AV → IsGrpPullback c.A AV (spMap π) φ → IsSquare φ φ₂ → PV.IsLB → (∃ t : (PV.pull (lift (1 : AV ⟶ AV) (𝟙 AV)).left).Gen, t.IsGen) → (∃ t : (PV.pull (lift (𝟙 AV) (1 : AV ⟶ AV)).left).Gen, t.IsGen) → LBIso PV (PV.pull (lift (snd AV AV) (fst AV AV)).left) → Out.RelAmple AV (PV.pull (lift (𝟙 AV) (𝟙 AV)).left) → (∀ (T : Over (Sp V)) (x : T ⟶ AV), (∃ t : (PV.pull (lift (snd AV T ≫ x) (fst AV T)).left).Gen, t.IsGen) → x = 1) → LBIso c.P (PV.pull φ₂) → ∃ lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp V)) ⟶ AV), (∀ a b, lev (a + b) = lev a * lev b) ∧ (∀ a, lev a ^ n = 1) ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp V) (β : cycAway n →+* k) (z : kˣ), x ≫ spMap βV = spMap β → (z : k) = β (zetaAway n) → (∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = n • b)) ∧ (∀ g' : Over.mk x ⟶ AV, g' ^ n = 1 → ∃ a, toUnit _ ≫ lev a = g') ∧ ∀ a b, Out.WeilIs AV (PV.pull (lift (𝟙 AV) (𝟙 AV)).left) n (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev b) (unitOn (z ^ (2 * omegaStd a b)))) ∧ ∀ a, (c.lev a).left ≫ φ = spMap π ≫ (lev a).left := by
  first | (exact @GlobalTheory.LevLift.exists_level_lift) | (exact GlobalTheory.LevLift.exists_level_lift) | (intros; apply GlobalTheory.LevLift.exists_level_lift  <;> assumption)
end
