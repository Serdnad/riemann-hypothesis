module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle536
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle643
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.TrCoef

theorem exists_nestSec {X X' Y : Scheme.{0}} {L : LB X} {J K : Type} [Fintype J] [Fintype K]
    (F : J → (X' ⟶ X)) (ε : J → ℤ) (ψ : K → (Y ⟶ X')) (δ : K → ℤ)
    (s : LB.Sec (LB.LinComb L (K := K × J) (fun p => ψ p.1 ≫ F p.2) (fun p => δ p.1 * ε p.2))) :
    ∃ T : LB.Sec (LB.LinComb (LB.LinComb L F ε) ψ δ), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z)
      (I : (Z ⟶ X) → L.ι), Good L z I → sval T r z (fun χ j => I (χ ≫ F j)) = sval s r z I := by
  have le : ∀ q : K → J → L.ι, LB.wchart (LB.LinComb L F ε) ψ q ≤
      LB.wchart L (K := K × J) (fun p => ψ p.1 ≫ F p.2) (fun p => q p.1 p.2) := fun q y hy =>
    Set.mem_iInter.2 fun p => Set.mem_iInter.1 (Set.mem_iInter.1 hy p.1) p.2
  have v : ∀ (q : K → J → L.ι) (y : Y) (hy : y ∈ LB.wchart (LB.LinComb L F ε) ψ q),
      gs (𝟙 Y) y _ ((Y.presheaf.map (homOfLE (le q)).op).hom (s.f fun p => q p.1 p.2)) =
        gs (𝟙 Y) y _ (s.f fun p => q p.1 p.2) := fun q y hy => gs_res _ y (le q) hy _
  refine ⟨⟨fun q => (Y.presheaf.map (homOfLE (le q)).op).hom (s.f fun p => q p.1 p.2),
    fun q q' => fn_ext fun y hy => ?_⟩, fun Z r z I hI => ?_⟩
  · have htr : trF (L := LB.LinComb L F ε) ψ δ (𝟙 Y) y q q' =
        trF (L := L) (K := K × J) (fun p => ψ p.1 ≫ F p.2) (fun p => δ p.1 * ε p.2) (𝟙 Y) y
          (fun p => q p.1 p.2) (fun p => q' p.1 p.2) := by
      refine (Finset.prod_congr rfl fun k _ => congrArg (· ^ δ k)
        (gm_linComb L F ε (𝟙 Y ≫ ψ k) y (q k) (q' k) (Set.mem_iInter.1 hy.1 k) (Set.mem_iInter.1 hy.2 k))).trans ?_
      simp only [trF, Fintype.prod_prod_type, ← Finset.prod_zpow, ← zpow_mul, Category.assoc, mul_comm]
    refine ((gs_res (𝟙 Y) y _ hy _).trans (v q y hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
        (congrArg Units.val (gm_linComb (LB.LinComb L F ε) ψ δ (𝟙 Y) y q q' hy.1 hy.2)))
        ((gs_res (𝟙 Y) y _ hy _).trans (v q' y hy.2)))).symm)
    refine (sec_trans s (𝟙 Y) y (le q hy.1) (le q' hy.2)).trans ?_
    rw [← htr]
    rfl
  · have hI' : Good (LB.LinComb L F ε) z (fun χ j => I (χ ≫ F j)) := fun χ => hI.mem F χ
    have hm := hI'.mem ψ r
    rw [sval_of s r z I (fun p => I ((r ≫ ψ p.1) ≫ F p.2)) (fun p => by rw [Category.assoc])]
    exact gs_res r z (le _) hm _

end GlobalTheory.MumCmp.TrCoef

namespace GlobalTheory.MumCmp.TrCoef

theorem formEq_coef {R : Type} [CommRing R] [IsDomain R] (D D₂ : DegPre R) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β]
    (g : GtPt D (𝟙_ (Over (Sp R)))) (χ₂ : D₂.X) (χ : D.X) (hc : D₂.c χ₂ ≫ β = D.c χ) :
    FormEq (Sum.elim (fun k => GlobalTheory.MumCmp.twφ D₂ D β g.b 0 ≫ D.famφB χ k)
        (Sum.elim (fun k => (toUnit D₂.P.A).left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b χ k)
          (fun k => (toUnit D₂.P.A).left ≫ (![g.b.left, η[D.P.A].left] : Fin 2 → _) k)))
      (Sum.elim (DegPre.famε 1) (Sum.elim DegPre.gtε ![-1, 1]))
      (fun p : Fin 4 × Fin 3 => D₂.famφB χ₂ p.1 ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b p.2)
      (fun p => DegPre.famε 1 p.1 * GlobalTheory.MumCmp.twε p.2) := by
  intro U _ h
  have hu : ∀ x : D₂.P.A ⟶ D₂.P.A, x ≫ toUnit D₂.P.A = toUnit D₂.P.A := fun x => toUnit_unique _ _
  have ht : ∀ x : D₂.P.A ⟶ D₂.P.A, ∏ i, h (x.left ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b i) ^ GlobalTheory.MumCmp.twε i =
      h ((x ≫ β) * (toUnit D₂.P.A ≫ g.b)).left * (h (toUnit D₂.P.A ≫ g.b).left)⁻¹ * h (1 : D₂.P.A ⟶ D.P.A).left := by
    intro x
    rw [Fin.prod_univ_three]
    show h (x ≫ (β * (toUnit D₂.P.A ≫ g.b))).left ^ (1 : ℤ) * h (x ≫ toUnit D₂.P.A ≫ g.b).left ^ (-1 : ℤ) *
      h (x ≫ toUnit D₂.P.A ≫ η[D.P.A]).left ^ (1 : ℤ) = _
    rw [MonObj.comp_mul, ← Category.assoc x, ← Category.assoc x, hu, zpow_one, zpow_one, zpow_neg_one]
    rfl
  have hx : ∀ k, D₂.famφB χ₂ k = ((![𝟙 D₂.P.A, 𝟙 D₂.P.A * (toUnit D₂.P.A ≫ D₂.c χ₂), toUnit D₂.P.A ≫ D₂.c χ₂, 1] :
      Fin 4 → (D₂.P.A ⟶ D₂.P.A)) k).left := by
    intro k; fin_cases k <;> rfl
  have hA : ∏ p : Fin 4 × Fin 3, h (D₂.famφB χ₂ p.1 ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b p.2) ^
      (DegPre.famε 1 p.1 * GlobalTheory.MumCmp.twε p.2) =
      ∏ k : Fin 4, (h (((![𝟙 D₂.P.A, 𝟙 D₂.P.A * (toUnit D₂.P.A ≫ D₂.c χ₂), toUnit D₂.P.A ≫ D₂.c χ₂, 1] :
        Fin 4 → (D₂.P.A ⟶ D₂.P.A)) k ≫ β) * (toUnit D₂.P.A ≫ g.b)).left *
        (h (toUnit D₂.P.A ≫ g.b).left)⁻¹ * h (1 : D₂.P.A ⟶ D.P.A).left) ^ DegPre.famε 1 k := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← ht, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_comm (DegPre.famε 1 k) (GlobalTheory.MumCmp.twε i), zpow_mul, hx]
  have hL1 : ∏ k, h (GlobalTheory.MumCmp.twφ D₂ D β g.b 0 ≫ D.famφB χ k) ^ DegPre.famε 1 k =
      h ((β * (toUnit D₂.P.A ≫ g.b)) * (toUnit D₂.P.A ≫ D.c χ)).left * (h (toUnit D₂.P.A ≫ D.c χ).left)⁻¹ *
        h (1 : D₂.P.A ⟶ D.P.A).left := by
    rw [Fin.prod_univ_four]
    show h ((β * (toUnit D₂.P.A ≫ g.b)) ≫ 𝟙 D.P.A).left ^ (((1 : ℕ) : ℤ) - 1) *
      h ((β * (toUnit D₂.P.A ≫ g.b)) ≫ (𝟙 D.P.A * (toUnit D.P.A ≫ D.c χ))).left ^ (1 : ℤ) *
      h ((β * (toUnit D₂.P.A ≫ g.b)) ≫ toUnit D.P.A ≫ D.c χ).left ^ (-1 : ℤ) *
      h ((β * (toUnit D₂.P.A ≫ g.b)) ≫ toUnit D.P.A ≫ η[D.P.A]).left ^ (1 : ℤ) = _
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc (β * (toUnit D₂.P.A ≫ g.b)),
      ← Category.assoc (β * (toUnit D₂.P.A ≫ g.b)),
      toUnit_unique ((β * (toUnit D₂.P.A ≫ g.b)) ≫ toUnit D.P.A) (toUnit D₂.P.A)]
    simp only [Nat.cast_one, sub_self, zpow_zero, _root_.one_mul, zpow_one, zpow_neg_one]
    rfl
  have hL2 : ∏ k, h ((toUnit D₂.P.A).left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b χ k) ^ DegPre.gtε k =
      (h ((toUnit D₂.P.A ≫ D.c χ) * (toUnit D₂.P.A ≫ g.b)).left)⁻¹ * h (toUnit D₂.P.A ≫ D.c χ).left *
        h (toUnit D₂.P.A ≫ g.b).left * (h (1 : D₂.P.A ⟶ D.P.A).left)⁻¹ := by
    rw [Fin.prod_univ_four]
    show h (toUnit D₂.P.A ≫ ((toUnit (𝟙_ (Over (Sp R))) ≫ D.c χ) * g.b)).left ^ (-1 : ℤ) *
      h (toUnit D₂.P.A ≫ toUnit (𝟙_ (Over (Sp R))) ≫ D.c χ).left ^ (1 : ℤ) *
      h (toUnit D₂.P.A ≫ g.b).left ^ (1 : ℤ) *
      h (toUnit D₂.P.A ≫ toUnit (𝟙_ (Over (Sp R))) ≫ η[D.P.A]).left ^ (-1 : ℤ) = _
    rw [MonObj.comp_mul, ← Category.assoc (toUnit D₂.P.A), ← Category.assoc (toUnit D₂.P.A),
      toUnit_unique (toUnit D₂.P.A ≫ toUnit (𝟙_ (Over (Sp R)))) (toUnit D₂.P.A)]
    simp only [zpow_one, zpow_neg_one]
    rfl
  have hL3 : ∏ k, h ((toUnit D₂.P.A).left ≫ (![g.b.left, η[D.P.A].left] : Fin 2 → _) k) ^ (![-1, 1] : Fin 2 → ℤ) k =
      (h (toUnit D₂.P.A ≫ g.b).left)⁻¹ * h (1 : D₂.P.A ⟶ D.P.A).left := by
    rw [Fin.prod_univ_two]
    show h (toUnit D₂.P.A ≫ g.b).left ^ (-1 : ℤ) * h (toUnit D₂.P.A ≫ η[D.P.A]).left ^ (1 : ℤ) = _
    rw [zpow_one, zpow_neg_one]
    rfl
  have h0 : (𝟙 D₂.P.A * (toUnit D₂.P.A ≫ D₂.c χ₂)) ≫ β = β * (toUnit D₂.P.A ≫ D.c χ) := by
    rw [MonObj.mul_comp, Category.id_comp, Category.assoc, hc]
  have h2 : (toUnit D₂.P.A ≫ D₂.c χ₂) ≫ β = toUnit D₂.P.A ≫ D.c χ := by rw [Category.assoc, hc]
  have h3 : (1 : D₂.P.A ⟶ D₂.P.A) ≫ β = 1 := MonObj.one_comp β
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [hL1, hL2, hL3, hA, Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, Category.id_comp, h0, h2, h3, _root_.one_mul]
  rw [mul_right_comm β (toUnit D₂.P.A ≫ D.c χ)]
  simp only [DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, Nat.cast_one, sub_self, zpow_zero, zpow_neg, zpow_one, inv_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem exists_translated_coef : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₂ : DegPre R) (β : D₂.P.A ⟶ D.P.A), IsMonHom β → ∀ (g : GtPt D (𝟙_ (Over (Sp R)))) (xe : D₂.X ≃+ D.X), (∀ χ : D₂.X, D₂.c χ ≫ β = D.c (xe χ)) → ∀ w : LB.Iso D₂.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∀ ν : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![g.b.left, η[D.P.A].left] ![-1, 1]), ν.IsGen → ∀ f : ∀ α : D.X, D.SecB 1 α, ∃ f₂ : ∀ α : D₂.X, D₂.SecB 1 α, ∀ (χ : D₂.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Geo.Tor.Good D.P.L z J → Geo.Tor.Good D₂.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.famφB χ κ) z (fun i => J ((r ≫ D₂.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b i)) (J' (r ≫ D₂.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J' := by
  intro R _ _ D D₂ β hβ g xe hc w hw ν hν f
  have key : ∀ χ : D₂.X, ∃ f₂ : D₂.SecB 1 χ, ∀ (Z : Scheme.{0}) (r : Z ⟶ D₂.P.A.left) (z : Z)
      (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι),
      Geo.Tor.Good D.P.L z J → Geo.Tor.Good D₂.P.L z J' →
      Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b 0) z J *
        (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.P.A).left) z J).val =
      (∏ κ, Geo.Tor.gv w (r ≫ D₂.famφB χ κ) z (fun i => J ((r ≫ D₂.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b i))
        (J' (r ≫ D₂.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval f₂ r z J' := by
    intro χ
    haveI := hβ
    let u := LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.s (xe χ)) (toUnit D₂.P.A).left)
      (LB.pullGen D.P.L _ _ ν (toUnit D₂.P.A).left)
    have hu : u.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ (g.isGen _) _)
      (DVR.pullGen_isGen _ _ _ _ hν _)
    let S := pullMulSec (f (xe χ)) (GlobalTheory.MumCmp.twφ D₂ D β g.b 0) u hu
    obtain ⟨S', hS'⟩ := exists_sec D.P.isLB (formEq_coef D D₂ β g χ (xe χ) (hc χ)) S
    obtain ⟨T, hT⟩ := exists_nestSec (GlobalTheory.MumCmp.twφ D₂ D β g.b) GlobalTheory.MumCmp.twε (D₂.famφB χ) (DegPre.famε 1) S'
    have hA := LB.isLB_linComb D₂.P.isLB (D₂.famφB χ) (DegPre.famε 1)
    have hB := LB.isLB_linComb (LB.isLB_linComb D.P.isLB (GlobalTheory.MumCmp.twφ D₂ D β g.b) GlobalTheory.MumCmp.twε)
      (D₂.famφB χ) (DegPre.famε 1)
    have hU := DVR.linCombIso_isGen w hw (D₂.famφB χ) (DegPre.famε 1)
    refine ⟨DVR.secOfIso (u := LB.linCombIso w (D₂.famφB χ) (DegPre.famε 1)) T hU hA hB,
      fun Z r z J J' hJ hJ' => ?_⟩
    have hJ'' : Good (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β g.b) GlobalTheory.MumCmp.twε) z
        (fun χ' j => J (χ' ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b j)) := fun χ' => hJ.mem _ χ'
    have m₁ := hJ'.mem (D₂.famφB χ) r
    have m₂ := hJ''.mem (D₂.famφB χ) r
    have e1 : Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b 0) z J *
        (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.P.A).left) z J).val =
        Geo.Tor.sval T r z (fun χ' j => J (χ' ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b j)) := by
      rw [hT Z r z J hJ, hS' Z r z J hJ, sval_pullMulSec _ _ _ hu r z hJ, val_mul hJ, val_pull hJ, val_pull hJ]
    rw [e1]
    have e2 := DVR.ps_gs_secOfIso (LB.linCombIso w (D₂.famφB χ) (DegPre.famε 1)) T hU hA hB
      (fun k => J' (r ≫ D₂.famφB χ k)) (fun k j => J ((r ≫ D₂.famφB χ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b j)) r z ⟨m₁, m₂⟩
    have e3 := DVR.ps_gm_linCombIso w (D₂.famφB χ) (DegPre.famε 1)
      ((fun k j => J ((r ≫ D₂.famφB χ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b j)), (fun k => J' (r ≫ D₂.famφB χ k))) r z ⟨m₂, m₁⟩
    rw [show Geo.Tor.sval (DVR.secOfIso (u := LB.linCombIso w (D₂.famφB χ) (DegPre.famε 1)) T hU hA hB) r z J' = _ from e2,
      e3]
    exact (Units.mul_inv_cancel_left _ _).symm
  choose f₂ hf₂ using key
  exact ⟨f₂, hf₂⟩

end GlobalTheory.MumCmp.TrCoef
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TwCoordInv

open GlobalTheory.CoordCompare TorusCoord

theorem ratio_translate_invariant : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D₂ : DegPre R} {e : ℕ} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g₂ : GtCoord I D₂ e G) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β] [Mono β.left], g₂.pG ≫ β = g.pG → ∀ (gp : GtPt D (𝟙_ (Over (Sp R)))) (w : LB.Iso D₂.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β gp.b) GlobalTheory.MumCmp.twε)) (χ₂ : D₂.X) (χ : D.X), (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D.P.L z J → Good D₂.P.L z J' → r ≫ g.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A → r ≫ g₂.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D₂.P.A → val (g.t χ) r z J = val (g₂.t χ₂) r z J') → ∀ (a : 𝟙_ (Over (Sp R)) ⟶ G) (h : (thickObj R I e G).left ⟶ (thickObj R I e G).left), h ≫ (thickObj R I e G).hom = (thickObj R I e G).hom → h ≫ (fstG I e G).left = (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → ∀ {Z : Scheme.{0}} (r r' : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D.P.L z J → Good D₂.P.L z J' → r ≫ g.q.left = r' ≫ g.q.left → val (g.t χ) (r ≫ h) z J * ((∏ k, gv w (r ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J ((r ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' (r ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) * val (g₂.t χ₂) r z J' * val (gp.s χ) (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J)⁻¹ = val (g.t χ) (r' ≫ h) z J * ((∏ k, gv w (r' ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J ((r' ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' (r' ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) * val (g₂.t χ₂) r' z J' * val (gp.s χ) (r' ≫ (thickObj R I e G).hom ≫ thick R I e) z J)⁻¹ := by
  intro R _ _ I D D₂ e G _ _ g g₂ β _ _ hβ gp w χ₂ χ hker a₀ h hh hf Z r r' z J J' hJ hJ' hq
  obtain ⟨h₁, h₂⟩ := ratio_invariant g g₂ β hβ χ χ₂ hker r r' z J J' hJ hJ' hq
  have hw : r ≫ (thickObj R I e G).hom = r' ≫ (thickObj R I e G).hom := by
    rw [← Over.w g.q, reassoc_of% hq]
  have hprod : ∀ k, r ≫ D₂.Oφ g₂.pG χ₂ k = r' ≫ D₂.Oφ g₂.pG χ₂ k := fun k =>
    Oφ_congr χ₂ g₂.pG r r' h₁ k
  let Z' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (r' ≫ (thickObj R I e G).hom)
  let b : Z' ⟶ thickObj R I e G := Over.homMk r hw
  let b' : Z' ⟶ thickObj R I e G := Over.homMk r' rfl
  obtain ⟨τ, hτ⟩ := exists_torus g b b' (Over.OverMorphism.ext hq)
  let hO : thickObj R I e G ⟶ thickObj R I e G := Over.homMk h hh
  have hfO : (Over.map (thick R I e)).map hO ≫ fstG I e G =
      fstG I e G ≫ ((toUnit G ≫ a₀) * 𝟙 G) := Over.OverMorphism.ext hf
  have hsh : ∀ x : Z' ⟶ thickObj R I e G, (Over.map (thick R I e)).map (x ≫ hO) ≫ fstG I e G =
      (toUnit _ ≫ a₀) * ((Over.map (thick R I e)).map x ≫ fstG I e G) := fun x => by
    rw [Functor.map_comp, Category.assoc, hfO, ← Category.assoc, MonObj.comp_mul, comp_toUnit_assoc,
      Category.comp_id]
  have hkey : b ≫ hO = (τ ≫ g.i) * (b' ≫ hO) := by
    apply FormalPoint.eq_of_map_fstG
    rw [hsh, FormalPoint.map_mul_fstG, hsh, hτ, FormalPoint.map_mul_fstG, mul_left_comm]
  have v₁ := val_torus_mul g χ (Z := Z') hJ τ _ (b ≫ hO) (b' ≫ hO) rfl hkey
  have v₂ := val_torus_mul g χ (Z := Z') hJ τ _ b b' rfl hτ
  let k : Z ⟶ (thickObj R I e G).left := (τ ≫ g.i).left
  have v₁' : val (g.t χ) (r ≫ h) z J = val (g.t χ) k z J * val (g.t χ) (r' ≫ h) z J := v₁
  have v₂' : val (g.t χ) r z J = val (g.t χ) k z J * val (g.t χ) r' z J := v₂
  have hB : val (g₂.t χ₂) r z J' = val (g.t χ) k z J * val (g₂.t χ₂) r' z J' := by
    rw [v₂'] at h₂
    rw [mul_inv_eq_iff_eq_mul.1 h₂]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have hP : (∏ k, gv w (r ≫ D₂.Oφ g₂.pG χ₂ k) z
        (fun i => J ((r ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i))
        (J' (r ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) =
      ∏ k, gv w (r' ≫ D₂.Oφ g₂.pG χ₂ k) z
        (fun i => J ((r' ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i))
        (J' (r' ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k :=
    Finset.prod_congr rfl fun k _ => by rw [hprod k]
  have hS : val (gp.s χ) (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J =
      val (gp.s χ) (r' ≫ (thickObj R I e G).hom ≫ thick R I e) z J := by
    rw [reassoc_of% hw]
  rw [hP, hS, v₁', hB]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.TwCoordInv
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.TwistedExpTransport



theorem expandsAt_twist : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₂ : DegData R I) (A A₂ : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (U₂ : UnifPre I D₂ A₂ G) (a : 𝟙_ (Over (Sp R)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))) (β : D₂.toPre.P.A ⟶ D.toPre.P.A) (xe : D₂.toPre.X ≃+ D.toPre.X) (w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b) GlobalTheory.MumCmp.twε)) (wL : LB.Iso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left)) (ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1])) (e : ℕ) (h : (thickObj R I e G).left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → h ≫ (U.gt e).pG.left = (U₂.gt e).pG.left ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b 0 → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι) (N : (Z ⟶ G.left) → U.LG.L.ι) (N' : (Z ⟶ G.left) → U₂.LG.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.Good U.LG.L z N → Geo.Tor.Good U₂.LG.L z N' → Geo.Tor.gv w (r ≫ (U₂.gt e).pG.left) z (fun i => J ((r ≫ (U₂.gt e).pG.left) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' (r ≫ (U₂.gt e).pG.left)) * Geo.Tor.gw (U₂.w e) r z (J' (r ≫ (U₂.gt e).pG.left)) (fun _ => N' (r ≫ (fstG I e G).left)) = Geo.Tor.gw (U.w e) (r ≫ h) z (J (r ≫ h ≫ (U.gt e).pG.left)) (fun _ => N (r ≫ h ≫ (fstG I e G).left)) * Geo.Tor.gw wL (r ≫ (fstG I e G).left) z (N (r ≫ (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' (r ≫ (fstG I e G).left)) * Geo.Tor.val ν (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J) → (∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.val ((U.gt e).t (xe χ)) (r ≫ h) z J = (∏ k, Geo.Tor.gv w (r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k) z (fun i => J ((r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' (r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k)) ^ Oinvε k) * Geo.Tor.val ((U₂.gt e).t χ) r z J' * Geo.Tor.val (g.s (xe χ)) (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J) → ∀ (σ : H0 U.LG.L 1) (σ₂ : H0 U₂.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB 1 α), (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι) (N' : (Z ⟶ G.left) → U₂.LG.L.ι), Geo.Tor.Good U.LG.L z N → Geo.Tor.Good U₂.LG.L z N' → Geo.Tor.sval σ (r ≫ ((toUnit G ≫ a) * 𝟙 G).left) z N = (Geo.Tor.gw wL r z (N (r ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' r)).val * Geo.Tor.sval σ₂ r z N') → (∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.toPre.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.toPre.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.toPre.famφB χ κ) z (fun i => J ((r ≫ D₂.toPre.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' (r ≫ D₂.toPre.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J') → U.ExpandsAt e 1 σ f → U₂.ExpandsAt e 1 σ₂ f₂ := by
  intro R _ _ I D D₂ A A₂ G _ _ U U₂ a g β xe w wL ν e h hG hp h1 h2 σ σ₂ f f₂ hσ hf hE
  classical
  have hu : (U₂.gt e).pG.left ≫ (toUnit D₂.toPre.P.A).left = (thickObj R I e G).hom ≫ thick R I e := by
    have e1 := Over.w (toUnit D₂.toPre.P.A)
    have e2 := Over.w (U₂.gt e).pG
    have e3 : (𝟙_ (Over (Spec (CommRingCat.of R)))).hom = 𝟙 _ := rfl
    rw [e3, Category.comp_id] at e1
    rw [e1, e2]
    rfl
  obtain ⟨S, hS⟩ := expandsAt_val U e 1 σ f hE
  refine expandsAt_of_val U₂ e 1 σ₂ f₂ (S.map xe.symm.toEquiv.toEmbedding) fun y J' hJ' => ?_
  choose J hJ using fun ψ : (thickObj R I e G).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
  have hJ : Good D.toPre.P.L y J := hJ
  choose N hN using fun ψ : (thickObj R I e G).left ⟶ G.left => exists_chart U.LG.isLB (ψ y)
  have hN : Good U.LG.L y N := hN

  let ω : ((thickObj R I e G).left ⟶ D₂.toPre.P.A.left) → ((thickObj R I e G).left.presheaf.stalk y)ˣ :=
    fun ψ => gv w ψ y (fun i => J (ψ ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' ψ)
  have hω := fun χ => GlobalTheory.ExpTrans.prod_fam U₂ e 1 ω χ
  have hF : ∀ χ, sval (f (xe χ)) (h ≫ pGl U e) y J *
      (val (g.s (xe χ)) ((thickObj R I e G).hom ≫ thick R I e) y J * val ν ((thickObj R I e G).hom ≫ thick R I e) y J).val =
      (∏ κ, ω (pGl U₂ e ≫ D₂.toPre.famφB χ κ) ^ DegPre.famε 1 κ).val * sval (f₂ χ) (pGl U₂ e) y J' := by
    intro χ
    have := hf χ _ (pGl U₂ e) y J J' hJ hJ'
    rw [hu] at this
    rw [hp]
    exact this
  have hT : ∀ χ, val ((U.gt e).t (xe χ)) h y J =
      (∏ k, ω (Oφl U₂ e χ k) ^ Oinvε k) * val (tG U₂ e χ) (𝟙 (thickObj R I e G).left) y J' *
        val (g.s (xe χ)) ((thickObj R I e G).hom ≫ thick R I e) y J := by
    intro χ
    have := h2 χ _ (𝟙 _) y J J' hJ hJ'
    simp only [Category.id_comp] at this
    exact this
  refine ⟨fun χ hχ => ?_, fun jL' hL' => ?_⟩
  · have hi : xe χ ∉ S := fun hc => hχ (Finset.mem_map.2 ⟨xe χ, hc, xe.symm_apply_apply χ⟩)
    have z0 := (hS _ h y J hJ).1 _ hi
    have := hF χ
    rw [z0, zero_mul] at this
    exact (Units.mul_right_eq_zero _).1 this.symm
  · obtain ⟨N', hN', eN'⟩ := exists_good U₂.LG.L U₂.LG.isLB y (K := PUnit) (fun _ => fGl I G e) (fun _ => jL')
      (fun _ _ _ => rfl) (fun _ => hL')
    have eN : N' (fGl I G e) = jL' := eN' PUnit.unit
    have hL₁ : fGl I G e (h y) ∈ U.LG.L.U (N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left)) := by
      have m := hN (h ≫ fGl I G e)
      have e' : N (h ≫ fGl I G e) = N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left) := congrArg N hG
      rw [e'] at m
      exact m
    have W' : ω (pGl U₂ e) * wv U₂ e (𝟙 _) y (J' (pGl U₂ e)) jL' =
        wv U e h y (J (h ≫ pGl U e)) (N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left)) *
          gw wL (fGl I G e) y (N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left)) jL' *
          val ν ((thickObj R I e G).hom ≫ thick R I e) y J := by
      have := h1 _ (𝟙 _) y J J' N N' hJ hJ' hN hN'
      simp only [Category.id_comp] at this
      rw [hG, eN] at this
      exact this
    have Sg : sv U 1 σ (h ≫ fGl I G e) y (N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left)) =
        (gw wL (fGl I G e) y (N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left)) jL').val * sv U₂ 1 σ₂ (fGl I G e) y jL' := by
      have := hσ _ (fGl I G e) y N N' hN hN'
      rw [sval_of σ _ y N (fun _ => N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (fun _ => by rw [Category.comp_id]),
        sval_of σ₂ _ y N' (fun _ => jL') (fun _ => by rw [Category.comp_id]; exact eN), eN] at this
      rw [hG]
      exact this
    have E := (hS _ h y J hJ).2 _ hL₁
    refine (ω (pGl U₂ e)).mul_right_inj.1 ?_
    have key : ∀ χ, (val ν ((thickObj R I e G).hom ≫ thick R I e) y J).val *
        (sval (f (xe χ)) (h ≫ pGl U e) y J * (val ((U.gt e).t (xe χ)) h y J).val) =
        (ω (pGl U₂ e)).val * (sval (f₂ χ) (pGl U₂ e) y J' * (val (tG U₂ e χ) (𝟙 (thickObj R I e G).left) y J').val) := by
      intro χ
      have hF' := hF χ
      have hω' := congrArg Units.val (hω χ)
      simp only [Units.val_mul, pow_one] at hF' hω'
      rw [hT χ]
      simp only [Units.val_mul]
      linear_combination ((∏ k, ω (Oφl U₂ e χ k) ^ Oinvε k).val * (val (tG U₂ e χ) (𝟙 (thickObj R I e G).left) y J').val) * hF' +
        (sval (f₂ χ) (pGl U₂ e) y J' * (val (tG U₂ e χ) (𝟙 (thickObj R I e G).left) y J').val) * hω'
    have L1 : (ω (pGl U₂ e)).val * ((wv U₂ e (𝟙 _) y (J' (pGl U₂ e)) jL' ^ 1).val * sv U₂ 1 σ₂ (fGl I G e) y jL') =
        (val ν ((thickObj R I e G).hom ≫ thick R I e) y J).val *
          ∑ α ∈ S, sval (f α) (h ≫ pGl U e) y J * (val ((U.gt e).t α) h y J).val := by
      rw [← E, pow_one, pow_one, Sg, ← _root_.mul_assoc, ← Units.val_mul, W']
      simp only [Units.val_mul]
      ring
    rw [L1, Finset.sum_map, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    obtain ⟨χ, rfl⟩ := xe.surjective x
    have e₀ : xe.symm.toEquiv.toEmbedding (xe χ) = χ := xe.symm_apply_apply χ
    rw [e₀]
    exact key χ

end GlobalTheory.TwistedExpTransport
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

namespace GlobalTheory.ThetaMove

theorem exists_down_three {XA XP XG XT Y Y' : Scheme.{0}} {LA : LB XA} {LP : LB XP} {LG : LB XG} {LT : LB XT}
    (hA : LA.IsLB) (hP : LP.IsLB) (hG : LG.IsLB) (hT : LT.IsLB) {α : XA ⟶ XP} {β : XG ⟶ XP} {c : XT ⟶ XG}
    (wA : LB.Iso LA (LP.pull α)) (hwA : wA.IsGen) (ℓ : LB.Iso LG (LP.pull β)) (hℓ : ℓ.IsGen)
    (w : LB.Iso LT (LG.pull c)) (hw : w.IsGen) (f : Y' ⟶ Y) (sA mA : Y ⟶ XA) (sT mT : Y' ⟶ XT) (e' : Y' ⟶ Y')
    (h₁ : f ≫ sA ≫ α = sT ≫ c ≫ β) (h₂ : e' ≫ sT = mT) (h₃ : e' ≫ f ≫ sA = f ≫ mA) (k : ℤ)
    (u : LB.Gen (LB.LinComb LA ![sA, mA] ![k, -k])) (hu : u.IsGen) :
    ∃ u' : LB.Gen (LB.LinComb LT ![sT, mT] ![k, -k]), u'.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y') (z : Z) JP JA JG Jt,
      Good LP z JP → Good LA z JA → Good LG z JG → Good LT z Jt →
      val u (q ≫ f) z JA = tf wA ℓ w f sA sT q z JP JA JG Jt ^ k * val u' q z Jt *
        (tf wA ℓ w f sA sT (q ≫ e') z JP JA JG Jt ^ k)⁻¹ := by
  have hm : f ≫ mA ≫ α = mT ≫ c ≫ β := by
    rw [← h₂, Category.assoc, ← h₁, ← Category.assoc f mA, ← h₃]
    simp only [Category.assoc]
  obtain ⟨t₁, ht₁, v₁⟩ := exists_up ((isGen_iff wA).1 hwA) hP hA (φ' := ![sA, mA]) (ε := ![k, -k]) u hu
  obtain ⟨t₂, ht₂, v₂⟩ := GlobalTheory.ArcPull.exists_down_om hℓ hP hG (φ' := ![sT ≫ c, mT ≫ c]) f (fun i => by
      fin_cases i
      · simpa using h₁.symm
      · simpa using hm.symm) t₁ ht₁
  obtain ⟨u', hu', v₃⟩ := GlobalTheory.ArcPull.exists_down_om hw hG hT (φ' := ![sT, mT]) (φ := ![sT ≫ c, mT ≫ c]) (𝟙 Y')
    (fun i => by fin_cases i <;> simp) t₂ ht₂
  refine ⟨u', hu', fun Z q z JP JA JG Jt hP' hA' hG' hT' => ?_⟩
  have e₁ : val t₁ (q ≫ f) z JP = pw wA ![sA, mA] ![k, -k] (q ≫ f) z (fun i => JP ((q ≫ f) ≫ ![sA, mA] i ≫ α))
      (fun i => JA ((q ≫ f) ≫ ![sA, mA] i)) * val u (q ≫ f) z JA :=
    v₁ Z (q ≫ f) z _ _ (hP'.mem _ _) (hA'.mem _ _)
  have e₂ := v₂ Z q z JP JG hP' hG'
  have e₃ := v₃ Z q z JG Jt hG' hT'
  rw [Category.comp_id] at e₃
  rw [e₂, e₃] at e₁
  simp only [pw, GlobalTheory.ArcPull.om, tf, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Category.assoc] at e₁ ⊢
  simp only [reassoc_of% h₁, reassoc_of% hm, reassoc_of% h₂, reassoc_of% h₃, h₁, hm, h₂, h₃] at e₁ ⊢
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e₁
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at e' ⊢
  linear_combination (norm := module) -e'

end GlobalTheory.ThetaMove
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

noncomputable section

namespace GlobalTheory.Mum.GenDesc

theorem fracMap_finite : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (hρ : Function.Injective ρ), ρ.Finite → (fracMap ρ hρ).Finite := by
  intro R R' _ _ _ _ ρ hρ hfin
  letI : Algebra R R' := ρ.toAlgebra
  haveI : Module.Finite R R' := hfin
  have hinj : Function.Injective (algebraMap R R') := hρ
  haveI : FaithfulSMul R R' := (faithfulSMul_iff_algebraMap_injective R R').mpr hinj
  letI : Algebra (FractionRing R) (FractionRing R') := FractionRing.liftAlgebra R (FractionRing R')
  haveI : IsScalarTower R (FractionRing R) (FractionRing R') :=
    FractionRing.isScalarTower_liftAlgebra R (FractionRing R')
  haveI : IsLocalization (Algebra.algebraMapSubmonoid R' (nonZeroDivisors R)) (FractionRing R') :=
    inferInstance
  haveI : Module.Finite (FractionRing R) (FractionRing R') :=
    Module.Finite.of_isLocalization R R' (nonZeroDivisors R)
  have heq : fracMap ρ hρ = algebraMap (FractionRing R) (FractionRing R') := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_)
    simp only [RingHom.comp_apply]
    rw [fracMap_algebraMap, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R R' (FractionRing R')]
    rfl
  rw [heq]
  exact RingHom.finite_algebraMap.mpr inferInstance

end GlobalTheory.Mum.GenDesc
end
end
