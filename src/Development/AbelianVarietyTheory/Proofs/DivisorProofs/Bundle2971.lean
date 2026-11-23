module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegOfSameTorusTwist
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1992
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2897
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle833
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2889
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle621
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatioGenerationModMaxIdealOfClosedFibre
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2841
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle643
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2840
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.Norm

section General

variable {X X' S : Scheme.{0}} {L : LB X} {L' : LB X'}

theorem exists_iso (hL : L.IsLB) (hL' : L'.IsLB) (p : X' ⟶ S) (e' : S ⟶ X') (he : e' ≫ p = 𝟙 S) (Φ : X' ⟶ X)
    (e : S ⟶ X) (ρ' : LB.Gen (L'.pull e')) (hρ' : ρ'.IsGen) (ρ : LB.Gen (L.pull e)) (hρ : ρ.IsGen)
    (w₀ : LB.Iso L' (L.pull Φ)) (hw₀ : w₀.IsGen) :
    ∃ w : LB.Iso L' (LB.LinComb L ![Φ, p ≫ e' ≫ Φ, p ≫ e] twε), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (j : Fin 3 → L.ι) (q : L'.ι),
        e' (r z) ∈ LB.wchart L ![Φ, p ≫ e' ≫ Φ, p ≫ e] j → e' (r z) ∈ L'.U q →
        gv w (r ≫ e') z j q = gm ((r ≫ e') ≫ Φ) z (L.U (j 0) ⊓ L.U (j 1)) (L.g (j 0) (j 1)) *
          gm r z (LB.wchart L (fun _ : PUnit => e) (fun _ => j 2)) (ρ.s (fun _ => j 2)) *
          (gm r z (LB.wchart L' (fun _ : PUnit => e') (fun _ => q)) (ρ'.s (fun _ => q)))⁻¹ := by
  have hw := (isGen_iff w₀).1 hw₀
  obtain ⟨u, hu, vu⟩ := exists_up hw hL hL' (K := PUnit) (φ' := fun _ => e') (ε := fun _ => 1) ρ' hρ'
  have l₀ : ∀ (j : Fin 3 → L.ι) (q : L'.ι), LB.wchart L ![Φ, p ≫ e' ≫ Φ, p ≫ e] j ⊓ L'.U q ≤
      (L.pull Φ).U (fun _ => j 0) ⊓ L'.U q := fun j q x hx => ⟨mem_pull.2 (Set.mem_iInter.1 hx.1 0), hx.2⟩
  have l₁ : ∀ (j : Fin 3 → L.ι) (q : L'.ι), LB.wchart L ![Φ, p ≫ e' ≫ Φ, p ≫ e] j ⊓ L'.U q ≤
      p ⁻¹ᵁ LB.wchart L (fun _ : PUnit => e' ≫ Φ) (fun _ => j 1) := fun j q x hx =>
    Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx.1 1
  have l₂ : ∀ (j : Fin 3 → L.ι) (q : L'.ι), LB.wchart L ![Φ, p ≫ e' ≫ Φ, p ≫ e] j ⊓ L'.U q ≤
      p ⁻¹ᵁ LB.wchart L (fun _ : PUnit => e) (fun _ => j 2) := fun j q x hx =>
    Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx.1 2
  let w : LB.Iso L' (LB.LinComb L ![Φ, p ≫ e' ≫ Φ, p ≫ e] twε) :=
    ⟨fun c => res (l₀ c.1 c.2) (w₀.s (fun _ => c.1 0, c.2)) *
      (res (l₁ c.1 c.2) (pullU p _ (u.s (fun _ => c.1 1))))⁻¹ * res (l₂ c.1 c.2) (pullU p _ (ρ.s (fun _ => c.1 2)))⟩
  have vw : ∀ (Z : Scheme.{0}) (f : Z ⟶ X') (z : Z) (j : Fin 3 → L.ι) (q : L'.ι),
      f z ∈ LB.wchart L ![Φ, p ≫ e' ≫ Φ, p ≫ e] j ⊓ L'.U q →
      gm f z (LB.wchart L ![Φ, p ≫ e' ≫ Φ, p ≫ e] j ⊓ L'.U q) (w.s (j, q)) = gw w₀ f z (j 0) q *
        (gm (f ≫ p) z (LB.wchart L (fun _ : PUnit => e' ≫ Φ) (fun _ => j 1)) (u.s (fun _ => j 1)))⁻¹ *
        gm (f ≫ p) z (LB.wchart L (fun _ : PUnit => e) (fun _ => j 2)) (ρ.s (fun _ => j 2)) := fun Z f z j q hz =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f z (l₀ j q) hz _)
      ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res f z (l₁ j q) hz _).trans (gm_pull f p z _ (l₁ j q hz) _))))))
      ((gm_res f z (l₂ j q) hz _).trans (gm_pull f p z _ (l₂ j q hz) _)))
  refine ⟨w, ?_, fun Z r z j q hj hq => ?_⟩
  · rintro ⟨j, q⟩ ⟨j', q'⟩
    refine unit_ext fun x hx => ?_
    refine ((gm_res (𝟙 X') x _ hx _).trans (vw _ _ x j q hx.1)).trans (Eq.symm ((map_mul _ _ _).trans
      ((congrArg₂ (· * ·) ((gm_div L' _ (𝟙 X') x (j, q) (j', q') hx).trans
        (congrArg (· * _) (gm_linComb L _ twε (𝟙 X') x j j' hx.1.1 hx.2.1)))
        ((gm_res (𝟙 X') x _ hx _).trans (vw _ _ x j' q' hx.2))).trans ?_)))
    rw [hw _ (𝟙 X') x (j 0) (j' 0) q q' (Set.mem_iInter.1 hx.1.1 0) (Set.mem_iInter.1 hx.2.1 0) hx.1.2 hx.2.2,
      gen_trans hu (𝟙 X' ≫ p) x (l₁ j q hx.1) (l₁ j' q' hx.2), gen_trans hρ (𝟙 X' ≫ p) x (l₂ j q hx.1) (l₂ j' q' hx.2),
      Fin.prod_univ_three]
    simp only [trF, Fintype.prod_unique, twε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, zpow_one,
      zpow_neg, Category.assoc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have hp : (r ≫ e') ≫ p = r := by rw [Category.assoc, he, Category.comp_id]
    have hz : p (e' (r z)) = r z := congrArg (fun g => g z) hp
    have m₀ : Φ (e' (r z)) ∈ L.U (j 0) := Set.mem_iInter.1 hj 0
    have m₁ : Φ (e' (r z)) ∈ L.U (j 1) := by
      have : Φ (e' (p (e' (r z)))) ∈ L.U (j 1) := Set.mem_iInter.1 hj 1
      rwa [hz] at this
    refine (vw Z (r ≫ e') z j q ⟨hj, hq⟩).trans ?_
    rw [hp, vu Z r z (fun _ => j 1) (fun _ => q) (Set.mem_iInter.2 fun _ => m₁) (Set.mem_iInter.2 fun _ => hq),
      pw, Fintype.prod_unique, zpow_one, hw Z (r ≫ e') z (j 0) (j 1) q q m₀ m₁ hq hq, gm_self hL' (r ≫ e') z hq]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, inv_one, ofMul_one]
    abel

theorem exists_iso_maps (hL : L.IsLB) (hL' : L'.IsLB) (p : X' ⟶ S) (e' : S ⟶ X') (he : e' ≫ p = 𝟙 S) (Φ : X' ⟶ X)
    (b e : S ⟶ X) (hb : e' ≫ Φ = b) (ρ' : LB.Gen (L'.pull e')) (hρ' : ρ'.IsGen) (ρ : LB.Gen (L.pull e)) (hρ : ρ.IsGen)
    (w₀ : LB.Iso L' (L.pull Φ)) (hw₀ : w₀.IsGen) {Y : Scheme.{0}} (r : Y ⟶ S) (x : Y ⟶ X') (hx : x = r ≫ e')
    (a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => x) (fun _ => -1)))
    (ha : ∀ (y : Y) (q : L'.ι), e' (r y) ∈ L'.U q →
      gm (𝟙 Y) y (LB.wchart L' (fun _ : PUnit => x) (fun _ => q)) (a.s (fun _ => q)) =
        (gm r y (LB.wchart L' (fun _ : PUnit => e') (fun _ => q)) (ρ'.s (fun _ => q)))⁻¹) :
    ∃ w : LB.Iso L' (LB.LinComb L ![Φ, p ≫ b, p ≫ e] twε), w.IsGen ∧
      ∃ t : LB.Gen (LB.LinComb L (fun i => x ≫ (![Φ, p ≫ b, p ≫ e] : Fin 3 → (X' ⟶ X)) i) (fun i => -1 * twε i)),
        MapsAtExp L L' ![Φ, p ≫ b, p ≫ e] twε w x (-1) a t ∧
        ∀ y J, Good L y J → val t (𝟙 Y) y J = (val ρ r y J)⁻¹ := by
  subst hb hx
  obtain ⟨w, hw, vw⟩ := exists_iso hL hL' p e' he Φ e ρ' hρ' ρ hρ w₀ hw₀
  have hp : (r ≫ e') ≫ p = r := by rw [Category.assoc, he, Category.comp_id]
  have hz : ∀ z, p (e' (r z)) = r z := fun z => congrArg (fun g => g z) hp
  have l₁ : ∀ j : Fin 3 → L.ι,
      LB.wchart L (fun i => (r ≫ e') ≫ (![Φ, p ≫ e' ≫ Φ, p ≫ e] : Fin 3 → (X' ⟶ X)) i) j ≤
        ((r ≫ e') ≫ Φ) ⁻¹ᵁ (L.U (j 0) ⊓ L.U (j 1)) := fun j y hy => ⟨Set.mem_iInter.1 hy 0, by
    have : Φ (e' (p (e' (r y)))) ∈ L.U (j 1) := Set.mem_iInter.1 hy 1
    rw [hz] at this
    exact this⟩
  have l₂ : ∀ j : Fin 3 → L.ι,
      LB.wchart L (fun i => (r ≫ e') ≫ (![Φ, p ≫ e' ≫ Φ, p ≫ e] : Fin 3 → (X' ⟶ X)) i) j ≤
        r ⁻¹ᵁ LB.wchart L (fun _ : PUnit => e) (fun _ => j 2) := fun j y hy => Set.mem_iInter.2 fun _ => by
    have : e (p (e' (r y))) ∈ L.U (j 2) := Set.mem_iInter.1 hy 2
    rw [hz] at this
    exact this
  let t : LB.Gen (LB.LinComb L (fun i => (r ≫ e') ≫ (![Φ, p ≫ e' ≫ Φ, p ≫ e] : Fin 3 → (X' ⟶ X)) i)
      (fun i => -1 * twε i)) :=
    ⟨fun j => (res (l₁ j) (pullU ((r ≫ e') ≫ Φ) (L.U (j 0) ⊓ L.U (j 1)) (L.g (j 0) (j 1))) * res (l₂ j) (pullU r _ (ρ.s (fun _ => j 2))))⁻¹⟩
  have vt : ∀ (y : Y) (j : Fin 3 → L.ι),
      y ∈ LB.wchart L (fun i => (r ≫ e') ≫ (![Φ, p ≫ e' ≫ Φ, p ≫ e] : Fin 3 → (X' ⟶ X)) i) j →
      gm (𝟙 Y) y (LB.wchart L (fun i => (r ≫ e') ≫ (![Φ, p ≫ e' ≫ Φ, p ≫ e] : Fin 3 → (X' ⟶ X)) i) j) (t.s j) =
        (gm ((r ≫ e') ≫ Φ) y (L.U (j 0) ⊓ L.U (j 1)) (L.g (j 0) (j 1)) *
          gm r y (LB.wchart L (fun _ : PUnit => e) (fun _ => j 2)) (ρ.s (fun _ => j 2)))⁻¹ := fun y j hy =>
    (map_inv _ _).trans (congrArg (·⁻¹) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res (𝟙 Y) y (l₁ j) hy _).trans ((gm_pull (𝟙 Y) ((r ≫ e') ≫ Φ) y (L.U (j 0) ⊓ L.U (j 1)) (l₁ j hy) _).trans (by rw [Category.id_comp])))
      ((gm_res (𝟙 Y) y (l₂ j) hy _).trans ((gm_pull (𝟙 Y) r y _ (l₂ j hy) _).trans (by rw [Category.id_comp]))))))
  refine ⟨w, hw, t, fun j q => unit_ext fun y hy => ?_, fun y J hJ => ?_⟩
  · refine ((gm_res (𝟙 Y) y _ hy _).trans (vt y j (mapsAtExp_le_b L L' _ twε _ j q hy))).trans
      (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·) ((map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ))
        ((gm_pull (𝟙 Y) (r ≫ e') y _ hy _).trans ((congrArg (fun f => gv w f y j q) (Category.id_comp _)).trans
          (vw Y r y j q hy.1 hy.2))))) ((gm_res (𝟙 Y) y _ hy _).trans (ha y q hy.2))).trans ?_)))
    rw [zpow_neg, zpow_one, ← mul_inv, inv_mul_cancel_right]
  · have e₁ : (r ≫ e') ≫ p ≫ e' ≫ Φ = (r ≫ e') ≫ Φ := by rw [← Category.assoc, hp, Category.assoc]
    have e₂ : (r ≫ e') ≫ p ≫ e = r ≫ e := by rw [← Category.assoc, hp]
    rw [val_of t (𝟙 Y) y J ![J ((r ≫ e') ≫ Φ), J ((r ≫ e') ≫ Φ), J (r ≫ e)] (fun k => by
      rw [Category.id_comp]
      fin_cases k
      exacts [rfl, congrArg J e₁, congrArg J e₂])]
    refine (vt y _ (Set.mem_iInter.2 fun k => ?_)).trans ?_
    · fin_cases k
      · exact hJ ((r ≫ e') ≫ Φ)
      · show ((r ≫ e') ≫ p ≫ e' ≫ Φ) y ∈ L.U (J ((r ≫ e') ≫ Φ))
        rw [e₁]; exact hJ _
      · show ((r ≫ e') ≫ p ≫ e) y ∈ L.U (J (r ≫ e))
        rw [e₂]; exact hJ _
    · exact congrArg (·⁻¹) ((congrArg (· * _) (gm_self hL ((r ≫ e') ≫ Φ) y (hJ _))).trans (_root_.one_mul _))

end General

theorem exists_rigidified : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₂ : DegData R I) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))) (β : D₂.toPre.P.A ⟶ D.toPre.P.A), IsMonHom β → ∀ w₀ : LB.Iso D₂.toPre.P.L (D.toPre.P.L.pull (padd D.toPre.P.A β (toUnit D₂.toPre.P.A ≫ g.b)).left), w₀.IsGen → ∃ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b) GlobalTheory.MumCmp.twε), w.IsGen ∧ ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK 0 ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK 0) (-1) (D₂.toPre.psi 0) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi 0) (LB.pullGen D.toPre.P.L _ _ (g.s 0) (toUnit (TK R)).left)) := by
  intro R _ _ I D D₂ g β hβ w₀ hw₀
  have hb : eSec D₂.toPre.P.A ≫ (padd D.toPre.P.A β (toUnit D₂.toPre.P.A ≫ g.b)).left = g.b.left := by
    rw [eSec, ← Over.comp_left]
    congr 1
    show η[D₂.toPre.P.A] ≫ (β * (toUnit D₂.toPre.P.A ≫ g.b)) = g.b
    have h₁ : η[D₂.toPre.P.A] ≫ β = 1 := by rw [IsMonHom.one_hom, Hom.one_def, toUnit_unit, Category.id_comp]
    have h₂ : η[D₂.toPre.P.A] ≫ toUnit D₂.toPre.P.A = 𝟙 _ := toUnit_unique _ _
    rw [MonObj.comp_mul, h₁, ← Category.assoc, h₂, Category.id_comp, _root_.one_mul]
  have he : eSec D₂.toPre.P.A ≫ (toUnit D₂.toPre.P.A).left = 𝟙 _ := by
    rw [eSec, ← Over.comp_left, toUnit_unique (η[D₂.toPre.P.A] ≫ toUnit D₂.toPre.P.A) (𝟙 _)]
    rfl
  obtain ⟨w, hw, t, h₁, h₂⟩ := exists_iso_maps D.toPre.P.isLB D₂.toPre.P.isLB (toUnit D₂.toPre.P.A).left
    (eSec D₂.toPre.P.A) he _ g.b.left (eSec D.toPre.P.A) hb D₂.toPre.rig D₂.toPre.rig_gen D.toPre.rig D.toPre.rig_gen
    w₀ hw₀ (jK R) (D₂.toPre.xK 0) (Uniq.xK_zero D₂.toPre) (D₂.toPre.psi 0)
    (fun y q hq => Uniq.gm_psi_zero D₂.tau_bimult 0 rfl y q hq)
  refine ⟨w, hw, t, h₁, corr_of_val D.toPre.P.isLB fun y J hJ => (h₂ y J hJ).trans ?_⟩
  refine Eq.symm ((val_mul hJ _ _ _).trans ?_)
  rw [PsiZero.val_psi_zero D.tau_bimult hJ, val_pull hJ, val_corr hJ g.s_zero, val_one, _root_.mul_one]

end GlobalTheory.MumCmp.Norm
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.IsoLin

variable {S : Scheme.{0}}

theorem transl_mul' {G : Over S} [GrpObj G] (x y : 𝟙_ (Over S) ⟶ G) :
    Hecke.transl (x * y) = Hecke.transl x ≫ Hecke.transl y := by
  simp only [Hecke.transl, comp_mul, Category.comp_id, Category.id_comp]
  rw [← Category.assoc _ (toUnit G) y, toUnit_unique (_ ≫ toUnit G) (toUnit G), _root_.mul_assoc]

theorem transl_comm {G : Over S} [GrpObj G] [IsCommMonObj G] (x y : 𝟙_ (Over S) ⟶ G) :
    Hecke.transl x ≫ Hecke.transl y = Hecke.transl y ≫ Hecke.transl x := by
  rw [← transl_mul', ← transl_mul', _root_.mul_comm]

theorem lift_mul_lift' {A : Over S} [GrpObj A] (a b c d : 𝟙_ (Over S) ⟶ A) :
    (lift (a * c) (b * d) : 𝟙_ (Over S) ⟶ G2 A) = lift a b * lift c d := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.mul_comp]

theorem surj_appTop {A : Over S} [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A) :
    Function.Surjective (fst A A).left.appTop.hom ∧ Function.Surjective (snd A A).left.appTop.hom := by
  have h2 := (GlobalTheory.globalFns_holds S (G2 A) (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA)).2
  have w1 : (G2 A).hom = (fst A A).left ≫ A.hom := (Over.w (fst A A)).symm
  have w2 : (G2 A).hom = (snd A A).left ≫ A.hom := (Over.w (snd A A)).symm
  refine ⟨?_, ?_⟩
  · rw [w1, Scheme.Hom.comp_appTop] at h2
    exact Function.Surjective.of_comp h2
  · rw [w2, Scheme.Hom.comp_appTop] at h2
    exact Function.Surjective.of_comp h2

theorem rig_lbPow {X Y : Scheme.{0}} (P : LB X) (hP : P.IsLB) (m : ℕ) (f : Y ⟶ X)
    (h : ∃ t : (P.pull f).Gen, t.IsGen) : ∃ t : ((Hecke.lbPow P m).pull f).Gen, t.IsGen := by
  have hQ : (Hecke.lbPow P m).IsLB := DVR.linComb_isLB P hP _ _
  have h0 := (GlobalTheory.CechPic.cls_eq_zero_iff (DVR.linComb_isLB P hP (fun _ : PUnit => f) (fun _ => 1))).2 h
  refine (GlobalTheory.CechPic.cls_eq_zero_iff (DVR.linComb_isLB _ hQ (fun _ : PUnit => f) (fun _ => 1))).1 ?_
  have e : GlobalTheory.CechPic.cls _ hQ = (m : ℤ) • GlobalTheory.CechPic.cls P hP := by
    refine (GlobalTheory.CechPic.cls_linComb hP (fun _ : Fin m => 𝟙 X) (fun _ => 1) hQ).trans ?_
    simp [GlobalTheory.CechPic.pull_id]
  rw [GlobalTheory.CechPic.cls_pull hQ f, e, map_zsmul,
    ← GlobalTheory.CechPic.cls_pull hP f (DVR.linComb_isLB P hP (fun _ : PUnit => f) (fun _ => 1)), h0, smul_zero]

end GlobalTheory.IsoLin

namespace GlobalTheory.IsoLin

theorem exists_linearisation_isotropic : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (m : ℕ) (H : Subgroup (𝟙_ (Over S) ⟶ A)), (∀ h ∈ H, ∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow P m).pull (lift (toUnit A ≫ h) (𝟙 A)).left).Gen, t.IsGen) → (∀ h ∈ H, ∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow P m).pull (lift (𝟙 A) (toUnit A ≫ h)).left).Gen, t.IsGen) → (∀ h₁ ∈ H, ∀ h₂ ∈ H, Out.WeilIs (G2 A) (GlobalTheory.UPel.HT.Hecke.lbPow P m) 1 (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 A) (lift 1 h₂) 1) → ∃ u : ∀ a : H × H, LB.Gen (LB.LinComb (GlobalTheory.UPel.HT.Hecke.lbPow P m) (K := Fin 2) ![𝟙 (G2 A).left, (GlobalTheory.UPel.HT.Hecke.transl (lift a.1.1 a.2.1 : 𝟙_ (Over S) ⟶ G2 A)).left] ![1, -1]), (∀ a, (u a).IsGen) ∧ ∀ a c, LB.Gen.Corr (GlobalTheory.UPel.HT.Hecke.lbPow P m) _ _ _ _ (u (a * c)) (LB.mulGen (GlobalTheory.UPel.HT.Hecke.lbPow P m) _ _ _ _ (u a) (LB.pullGen (GlobalTheory.UPel.HT.Hecke.lbPow P m) _ _ (u c) (GlobalTheory.UPel.HT.Hecke.transl (lift a.1.1 a.2.1 : 𝟙_ (Over S) ⟶ G2 A)).left)) := by
  intro S A _ _ hA P hP hr1 hr2 m H hH1 hH2 hW
  have hQ : (Hecke.lbPow P m).IsLB := DVR.linComb_isLB P hP _ _
  have q1 := rig_lbPow P hP m _ hr1
  have q2 := rig_lbPow P hP m _ hr2
  obtain ⟨sf, ss⟩ := surj_appTop hA
  have hm1 : ∀ a c : H, (lift ((a * c : H) : 𝟙_ (Over S) ⟶ A) 1 : 𝟙_ (Over S) ⟶ G2 A) = lift (a : 𝟙_ (Over S) ⟶ A) 1 * lift (c : 𝟙_ (Over S) ⟶ A) 1 := by
    intro a c
    rw [← lift_mul_lift', _root_.mul_one, Subgroup.coe_mul]
  have hm2 : ∀ a c : H, (lift 1 ((a * c : H) : 𝟙_ (Over S) ⟶ A) : 𝟙_ (Over S) ⟶ G2 A) = lift 1 (a : 𝟙_ (Over S) ⟶ A) * lift 1 (c : 𝟙_ (Over S) ⟶ A) := by
    intro a c
    rw [← lift_mul_lift', _root_.mul_one, Subgroup.coe_mul]
  obtain ⟨v₁, hv₁, cv₁⟩ := GlobalTheory.MumLin.exists_linearisation A.left (G2 A).left (fst A A).left
    (lift (𝟙 A) (1 : A ⟶ A)).left (by rw [← Over.comp_left, lift_fst, Over.id_left]) sf
    (Hecke.lbPow P m) hQ q2 H (fun a => (Hecke.transl (lift (a : 𝟙_ (Over S) ⟶ A) 1 : 𝟙_ (Over S) ⟶ G2 A)).left)
    (fun a => (Hecke.transl (a : 𝟙_ (Over S) ⟶ A)).left)
    (fun a c => by simp only [hm1, transl_mul', Over.comp_left])
    (fun a c => by simp only [Subgroup.coe_mul, transl_mul', Over.comp_left])
    (fun a => by
      rw [← Over.comp_left, ← Over.comp_left]
      congr 1
      apply CartesianMonoidalCategory.hom_ext <;> simp [Hecke.transl, MonObj.mul_comp, MonObj.comp_mul])
    (fun a => GlobalTheory.T.birigidified_bundle_translation_invariant_first_factor S A hA _ hQ q1 q2 a (hH1 a a.2))
  obtain ⟨v₂, hv₂, cv₂⟩ := GlobalTheory.MumLin.exists_linearisation A.left (G2 A).left (snd A A).left
    (lift (1 : A ⟶ A) (𝟙 A)).left (by rw [← Over.comp_left, lift_snd, Over.id_left]) ss
    (Hecke.lbPow P m) hQ q1 H (fun a => (Hecke.transl (lift 1 (a : 𝟙_ (Over S) ⟶ A) : 𝟙_ (Over S) ⟶ G2 A)).left)
    (fun a => (Hecke.transl (a : 𝟙_ (Over S) ⟶ A)).left)
    (fun a c => by simp only [hm2, transl_mul', Over.comp_left])
    (fun a c => by simp only [Subgroup.coe_mul, transl_mul', Over.comp_left])
    (fun a => by
      rw [← Over.comp_left, ← Over.comp_left]
      congr 1
      apply CartesianMonoidalCategory.hom_ext <;> simp [Hecke.transl, MonObj.mul_comp, MonObj.comp_mul])
    (fun a => GlobalTheory.T.birigidified_bundle_translation_invariant_second_factor S A hA _ hQ q1 q2 a (hH2 a a.2))
  exact GlobalTheory.T.exists_linearization_prod (G2 A).left (Hecke.lbPow P m) hQ H H _ _
    (fun p => (Hecke.transl (lift (p.1 : 𝟙_ (Over S) ⟶ A) (p.2 : 𝟙_ (Over S) ⟶ A) : 𝟙_ (Over S) ⟶ G2 A)).left)
    (fun p => by
      show _ = (Hecke.transl _ ≫ Hecke.transl _).left
      rw [← transl_mul', ← lift_mul_lift', _root_.mul_one, _root_.one_mul])
    (fun a b => by rw [← Over.comp_left, ← Over.comp_left, transl_comm])
    (fun a c => by simp only [hm1, transl_mul', Over.comp_left])
    (fun a c => by simp only [hm2, transl_mul', Over.comp_left])
    v₁ v₂ hv₁ hv₂ cv₁ cv₂
    (fun a b => GlobalTheory.T.translation_isos_commute_of_commutatorPairing_one S (G2 A) (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) _ hQ _ _ (v₁ a) (v₂ b) (hv₁ a) (hv₂ b) (hW a a.2 b b.2))

end GlobalTheory.IsoLin
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionCommPairing

open GlobalTheory.CechPic

theorem unitOn_inj {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) := by
  intro a b h
  ext
  have := congrArg (fun u : (Γ(Sp R, ⊤))ˣ => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom u.val) h
  simpa [unitOn] using this

theorem unitOn_surj {R : Type} [CommRing R] (c : (Γ(Sp R, ⊤))ˣ) : ∃ z : Rˣ, unitOn z = c := by
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom c, ?_⟩
  ext
  simp [unitOn]

theorem unitOn_mul {R : Type} [CommRing R] (a b : Rˣ) : unitOn (a * b) = unitOn a * unitOn b :=
  map_mul _ a b

theorem theta_lbPow {S : Scheme.{0}} {B : Over S} [GrpObj B] {L : LB B.left} (hL : L.IsLB) (k : ℕ)
    {T : Over S} (θ : Out.ThetaGrp B L (k : ℤ) T) :
    ∃ θ' : Out.ThetaGrp B (Hecke.lbPow L k) 1 T, θ'.pt = θ.pt := by
  have hQ : (Hecke.lbPow L k).IsLB := LB.isLB_linComb hL _ _
  have hcls : cls _ hQ = k • cls L hL := by
    refine (cls_linComb hL (K := Fin k) (fun _ => 𝟙 _) (fun _ => 1) hQ).trans ?_
    simp [pull_id]
  have h0 := (cls_eq_zero_iff (LB.isLB_linComb hL _ _ : (Out.thetaLB B L (k : ℤ) θ.pt).IsLB)).2 ⟨θ.φ, θ.isGen⟩
  obtain ⟨u, hu⟩ : ∃ u : LB.Gen (Out.thetaLB B (Hecke.lbPow L k) 1 θ.pt), u.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hQ _ _)).1 ?_
    rw [cls_linComb hQ, Fin.sum_univ_two, hcls]
    rw [cls_linComb hL, Fin.sum_univ_two] at h0
    simp at h0 ⊢
    exact h0
  exact ⟨⟨_, u, hu⟩, rfl⟩

theorem exists_weilIs_lbPow {S : Scheme.{0}} {B : Over S} [GrpObj B] (hB : IsAbelianScheme B) {L : LB B.left}
    (hL : L.IsLB) (k : ℕ) {T : Over S} {x y : T ⟶ B} {c : Γ(T.left, ⊤)ˣ} (h : Out.WeilIs B L (k : ℤ) x y c) :
    ∃ c' : Γ(T.left, ⊤)ˣ, Out.WeilIs B (Hecke.lbPow L k) 1 x y c' := by
  have hQ : (Hecke.lbPow L k).IsLB := LB.isLB_linComb hL _ _
  refine CommutatorPairing.exists_weilIs GlobalTheory.globalFns_holds hB hQ (fun p => ?_) (fun p => ?_)
  · obtain ⟨V, hV, ⟨θx, -, hx, -⟩, -⟩ := h p
    obtain ⟨θ, hθ⟩ := theta_lbPow hL k θx
    exact ⟨V, hV, θ, hθ.trans hx⟩
  · obtain ⟨V, hV, ⟨-, θy, -, hy⟩, -⟩ := h p
    obtain ⟨θ, hθ⟩ := theta_lbPow hL k θy
    exact ⟨V, hV, θ, hθ.trans hy⟩

theorem lift_mul_lift {S : Scheme.{0}} {A B T : Over S} [GrpObj A] [GrpObj B] (x x' : T ⟶ A) (y y' : T ⟶ B) :
    lift x y * lift x' y' = lift (x * x') (y * y') := by
  ext1 <;> simp only [MonObj.mul_comp, lift_fst, lift_snd]

theorem lift_pow {S : Scheme.{0}} {A B T : Over S} [GrpObj A] [GrpObj B] (x : T ⟶ A) (y : T ⟶ B) (m : ℕ) :
    lift x y ^ m = lift (x ^ m) (y ^ m) := by
  ext1 <;> simp only [MonObj.pow_comp, lift_fst, lift_snd]

theorem lift_one_one {S : Scheme.{0}} {A B T : Over S} [GrpObj A] [GrpObj B] :
    (1 : T ⟶ A ⊗ B) = lift (1 : T ⟶ A) (1 : T ⟶ B) := by
  ext1 <;> simp only [MonObj.one_comp, lift_fst, lift_snd]

theorem exists_pairing : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (c : ℕ), (c : κ) ≠ 0 → ∃ e : (Over.mk x ⟶ A) → (Over.mk x ⟶ A) → κˣ, (∀ g g' : Over.mk x ⟶ A, g ^ c = 1 → g' ^ c = 1 → ∀ u : Γ((Over.mk x).left, ⊤)ˣ, Out.WeilIs (G2 A) (Hecke.lbPow P c) 1 (lift g 1 : Over.mk x ⟶ G2 A) (lift 1 g') u ↔ u = unitOn (e g g')) ∧ (∀ g₁ g₂ g' : Over.mk x ⟶ A, g₁ ^ c = 1 → g₂ ^ c = 1 → g' ^ c = 1 → e (g₁ * g₂) g' = e g₁ g' * e g₂ g') ∧ (∀ g g₁ g₂ : Over.mk x ⟶ A, g ^ c = 1 → g₁ ^ c = 1 → g₂ ^ c = 1 → e g (g₁ * g₂) = e g g₁ * e g g₂) := by
  intro S A _ _ P hA hP κ _ _ x c hc
  classical
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hQ : (Hecke.lbPow P c).IsLB := LB.isLB_linComb hP _ _
  have hc0 : 0 < c := Nat.pos_of_ne_zero fun h => hc (by rw [h, Nat.cast_zero])
  have ex : ∀ g g' : Over.mk x ⟶ A, g ^ c = 1 → g' ^ c = 1 →
      ∃ z : κˣ, Out.WeilIs (G2 A) (Hecke.lbPow P c) 1 (lift g 1 : Over.mk x ⟶ G2 A) (lift 1 g') (unitOn z) := by
    intro g g' hg hg'
    have hx : (lift g 1 : Over.mk x ⟶ G2 A) ^ c = 1 := by rw [lift_pow, hg, one_pow, lift_one_one]
    have hy : (lift 1 g' : Over.mk x ⟶ G2 A) ^ c = 1 := by rw [lift_pow, hg', one_pow, lift_one_one]
    obtain ⟨u, hu⟩ := GlobalTheory.WeilGeomPt.exists_weilIs_geomPt S (G2 A) P hAA hP κ x c hc0 hc _ _ hx hy
    obtain ⟨u', hu'⟩ := exists_weilIs_lbPow hAA hP c hu
    obtain ⟨z, rfl⟩ := unitOn_surj u'
    exact ⟨z, hu'⟩
  let e : (Over.mk x ⟶ A) → (Over.mk x ⟶ A) → κˣ := fun g g' =>
    if h : g ^ c = 1 ∧ g' ^ c = 1 then (ex g g' h.1 h.2).choose else 1
  have he : ∀ g g' : Over.mk x ⟶ A, ∀ hg : g ^ c = 1, ∀ hg' : g' ^ c = 1,
      Out.WeilIs (G2 A) (Hecke.lbPow P c) 1 (lift g 1 : Over.mk x ⟶ G2 A) (lift 1 g') (unitOn (e g g')) := by
    intro g g' hg hg'
    simp only [e, dif_pos (And.intro hg hg')]
    exact (ex g g' hg hg').choose_spec
  have hmulc : ∀ g₁ g₂ : Over.mk x ⟶ A, g₁ ^ c = 1 → g₂ ^ c = 1 → (g₁ * g₂) ^ c = 1 := by
    intro g₁ g₂ h₁ h₂
    rw [mul_pow, h₁, h₂, _root_.one_mul]
  refine ⟨e, fun g g' hg hg' u => ⟨fun h => CommutatorPairing.weilIs_unique hG hAA hQ h (he g g' hg hg'),
    fun h => h ▸ he g g' hg hg'⟩, ?_, ?_⟩
  · intro g₁ g₂ g' h₁ h₂ h'
    have hm := DiagPairing.weilIs_mul_left hG hAA hQ (he g₁ g' h₁ h') (he g₂ g' h₂ h')
    rw [lift_mul_lift, _root_.mul_one] at hm
    apply unitOn_inj
    rw [unitOn_mul]
    exact CommutatorPairing.weilIs_unique hG hAA hQ (he _ _ (hmulc g₁ g₂ h₁ h₂) h') hm
  · intro g g₁ g₂ hg h₁ h₂
    have hm := CommPairing.weilIs_symm hQ (DiagPairing.weilIs_mul_left hG hAA hQ
      (CommPairing.weilIs_symm hQ (he g g₁ hg h₁)) (CommPairing.weilIs_symm hQ (he g g₂ hg h₂)))
    rw [lift_mul_lift, _root_.mul_one, mul_inv, inv_inv, inv_inv] at hm
    apply unitOn_inj
    rw [unitOn_mul]
    exact CommutatorPairing.weilIs_unique hG hAA hQ (he _ _ hg (hmulc g₁ g₂ h₁ h₂)) hm

end GlobalTheory.TorsionCommPairing
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.ratioGeneration_mod_maxIdeal_of_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) (L : LB G.left) (k : ℕ) (s₀ : H0 L k) (i : Fin 1 → L.ι), (∀ w : (thickObj R (maximalIdeal R) 0 G).left, (fstG (maximalIdeal R) 0 G).left w ∈ secChart L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) 0 G).left.Opens) (m : ℕ) (σ : Fin m → H0 L k) (r : Fin m → Γ((thickObj R (maximalIdeal R) 0 G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y s₀ i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (σ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y s₀ i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) 0 G).left, N), ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r P) → ∀ (e : ℕ) (w : (thickObj R (maximalIdeal R) e G).left), (fstG (maximalIdeal R) e G).left w ∈ secChart L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) e G).left.Opens) (m : ℕ) (σ : Fin m → H0 L k) (r : Fin m → Γ((thickObj R (maximalIdeal R) e G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y s₀ i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y (σ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y s₀ i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) e G).left, N), ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r Q - MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r P ∈ Ideal.map (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) (maximalIdeal R) := by
  first | exact @GlobalTheory.Mum.ratio_gen_mod_of_closedFibre | exact GlobalTheory.Mum.ratio_gen_mod_of_closedFibre | (intros; apply GlobalTheory.Mum.ratio_gen_mod_of_closedFibre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_veryAmple_fourthPower_polarisedAbelian_field : AmpleSt → ∀ (K : Type) [Field K] (P : PolAV (Sp K)), ∃ (m : ℕ) (b : Fin (m + 1) → H0 P.L 4), VeryAmpleAlong P.A.hom (𝟙 P.A.left) P.L b := by
  first | exact @GlobalTheory.Mum.veryAmpleAlong_field | exact GlobalTheory.Mum.veryAmpleAlong_field | (intros; apply GlobalTheory.Mum.veryAmpleAlong_field <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

theorem _root_.GlobalTheory.T.isGrpPullback_genericFibre_fractionFieldMap : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (hρ : Function.Injective ρ) (G' : Over (Sp R')) [GrpObj G'] (G : Over (Sp R)) [GrpObj G] (β : G'.left ⟶ G.left) (h : IsGrpPullback G' G (spMap ρ) β), IsGrpPullback ((Over.pullback (jK R')).obj G') ((Over.pullback (jK R)).obj G) (spMap (fracMap ρ hρ)) (genMap hρ β h.1.w) := by
  first | exact @GlobalTheory.Mum.GenDesc.isGrpPullback_genMap | exact GlobalTheory.Mum.GenDesc.isGrpPullback_genMap | (intros; apply GlobalTheory.Mum.GenDesc.isGrpPullback_genMap <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

theorem _root_.GlobalTheory.T.fractionFieldMap_finite_of_finite_injective : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (hρ : Function.Injective ρ), ρ.Finite → (fracMap ρ hρ).Finite := by
  first | exact @GlobalTheory.Mum.GenDesc.fracMap_finite | exact GlobalTheory.Mum.GenDesc.fracMap_finite | (intros; apply GlobalTheory.Mum.GenDesc.fracMap_finite <;> assumption)
end
