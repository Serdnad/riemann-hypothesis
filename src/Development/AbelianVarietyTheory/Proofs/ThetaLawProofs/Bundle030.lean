module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle023
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
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory

private lemma spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) : spMap g ≫ spMap f = spMap (g.comp f) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem morphism_descends_to_subring :
    ∀ (R : Type) [CommRing R] (R₀ : Subring R) (X X₀ Y₀ : Scheme.{0}) (f : X ⟶ Sp R) (f₀ : X₀ ⟶ Sp R₀) (q : Y₀ ⟶ Sp R₀) (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] [LocallyOfFinitePresentation q] (φ : X ⟶ Y₀), IsPullback π f f₀ (spMap R₀.subtype) → φ ≫ q = π ≫ f₀ → ∃ S : Finset R, ∀ (R₁ : Subring R) (h : R₀ ≤ R₁), (S : Set R) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion h)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ ψ : X₁ ⟶ Y₀, j ≫ ψ = φ ∧ ψ ≫ q = π₁ ≫ f₀ := by
  intro R _ R₀ X X₀ Y₀ f f₀ q π _ _ _ φ hP hφ
  let _ : Algebra R₀ R := R₀.subtype.toAlgebra
  have hP' : IsPullback π f f₀ (spMap (algebraMap R₀ R)) := hP

  let e := hP'.isoPullback
  obtain ⟨R', ψ', hfg, hψ'q, hψ'φ⟩ := Spread.exists_fg_comp_eq (pB := f₀) (pZ := q) (A := R)
    (e.inv ≫ φ) (by rw [Category.assoc, hφ, ← Category.assoc, hP'.isoPullback_inv_fst])
  obtain ⟨t, ht⟩ := hfg
  refine ⟨t, fun R₁ h hS X₁ f₁ π₁ j hP₁ hjπ hjf => ?_⟩

  have hle : ∀ x ∈ R', x ∈ R₁ := by
    let T : Subalgebra R₀ R := { R₁.toSubsemiring with algebraMap_mem' := fun r => h r.2 }
    have hT : R' ≤ T := ht ▸ Algebra.adjoin_le hS
    exact fun x hx => hT hx
  let a : R' →+* R₁ := RingHom.codRestrict R'.val.toRingHom R₁ (fun x => hle x x.2)
  have ha : spMap a ≫ spMap (algebraMap R₀ R') = spMap (Subring.inclusion h) := by
    rw [spMap_comp_moduli_spaces]
    congr 1
  have hb : spMap R₁.subtype ≫ spMap a = spMap R'.val.toRingHom := by
    rw [spMap_comp_moduli_spaces]
    congr 1
  let L : X₁ ⟶ pullback f₀ (spMap (algebraMap R₀ R')) :=
    pullback.lift π₁ (f₁ ≫ spMap a) (by rw [Category.assoc, ha]; exact hP₁.w)
  refine ⟨L ≫ ψ', ?_, ?_⟩
  · have hjL : j ≫ L = e.hom ≫ Spread.bcMap f₀ R'.val := by
      apply pullback.hom_ext
      · simp only [L, e, Category.assoc, Spread.bcMap_fst, IsPullback.isoPullback_hom_fst]
        rw [pullback.lift_fst, hjπ]
      · simp only [L, e, Category.assoc, pullback.lift_snd, Spread.bcMap_snd,
          IsPullback.isoPullback_hom_snd_assoc]
        rw [← Category.assoc, hjf, Category.assoc, hb]
    rw [← Category.assoc, hjL, Category.assoc, hψ'φ, ← Category.assoc, e.hom_inv_id,
      Category.id_comp]
  · rw [Category.assoc, hψ'q, ← Category.assoc, pullback.lift_fst]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyScaleLift

theorem exists_keyPB_scale : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (y : KeyIn R) (x : KeyIn R') (a : Rˣ) (M : Matrix (Fin x.P.g) (Fin x.P.g) R), KeyPB x y f → IsUnit M.det → ∃ y₁ : KeyIn R, ∀ (t : x.P.L.Sec) (ht : _) (v : Fin x.P.g → (epsR R' ⟶ x.P.A)) (hv : _), (∀ i, t.f i = constFn x.P.A.hom _ (f a) * x.th.f i) → (∀ i, IsLieComb (fun k => f (M i k)) x.v (v i)) → KeyPB ⟨x.P, x.g_pos, x.rig, x.rig_gen, t, ht, v, hv⟩ y₁ f := by
  intro R R' _ _ f y x a M h hM
  obtain ⟨e⟩ : Nonempty (x.P.g = y.P.g) := by
    obtain ⟨_, _, _, hg, _⟩ := h
    exact ⟨hg⟩
  haveI := y.P.isAb.comm
  let N : Matrix (Fin y.P.g) (Fin y.P.g) R := Matrix.reindex (finCongr e) (finCongr e) M
  have hN : IsUnit N.det := by rwa [Matrix.det_reindex_self]
  obtain ⟨ex, -, -, -, bas⟩ := GlobalTheory.LieComb.lieComb_algebra R y.P.A y.P.g y.v y.basis.1
  choose v₁ hv₁ using fun i => (ex (N i)).exists
  obtain ⟨s, hs, -, hle⟩ := exists_sec_div y.P.A.hom a.inv_mul y.th
  refine ⟨⟨y.P, y.g_pos, y.rig, y.rig_gen, s, fun p => (y.th_ne p).imp fun z hz => ⟨hz.1, hle hz.2⟩, v₁,
    (bas N v₁ y.basis hv₁).2 hN⟩, fun t ht v hv h₁ h₂ => ?_⟩
  exact KeyPBScale.keyPB_scale R R' f y.P y.g_pos y.rig y.rig_gen y.th y.th_ne y.v y.basis s _ v₁ _ a N x.P e
    x.g_pos x.rig x.rig_gen x.th x.th_ne x.v x.basis t ht v hv hs hv₁ h₁ h₂ h

end GlobalTheory.KeyScaleLift
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BoxPower

section Gen

variable {X X' Y Y₀ : Scheme.{0}} {M : LB X} {J K : Type} [Fintype J] [Fintype K]

theorem mem_of_box {pr : J → (X' ⟶ X)} {φ' : K → (Y ⟶ X')} {φ : J → K → (Y₀ ⟶ X)} {ρ : J → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) {y : Y} {jN : K → J → M.ι}
    (hy : y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN) (i : J) :
    ρ i y ∈ LB.wchart M (φ i) (fun a => jN a i) :=
  Out.GeneratorPullback.pullAlong_le M (pr i) (ρ i) (φ i) φ' (hψ i) (fun a _ => jN a i) (Out.GeneratorPullback.box_le M pr φ' jN i hy)

theorem gm_box {pr : J → (X' ⟶ X)} {φ' : K → (Y ⟶ X')} {φ : J → K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : J → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) (t : ∀ i, LB.Gen (LB.LinComb M (φ i) ε)) {y : Y} {jN : K → J → M.ι}
    (hy : y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN) :
    gm (𝟙 Y) y (LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN)
      ((Out.GeneratorPullback.boxGen M pr φ' ε (fun i => Out.GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i))).s jN) =
      ∏ i, gm (ρ i) y (LB.wchart M (φ i) (fun a => jN a i)) ((t i).s (fun a => jN a i)) := by
  refine (map_prod (gm (𝟙 Y) y (LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN))
    (fun i => res (Out.GeneratorPullback.box_le M pr φ' jN i)
      ((Out.GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i)).s (fun a _ => jN a i))) Finset.univ).trans
    (Finset.prod_congr rfl fun i _ => ?_)
  refine (gm_res (𝟙 Y) y (Out.GeneratorPullback.box_le M pr φ' jN i) hy _).trans ?_
  refine (gm_res (𝟙 Y) y (Out.GeneratorPullback.pullAlong_le M (pr i) (ρ i) (φ i) φ' (hψ i) (fun a _ => jN a i))
    (Out.GeneratorPullback.box_le M pr φ' jN i hy) _).trans ?_
  refine (gm_pull (𝟙 Y) (ρ i) y _ (mem_of_box hψ hy i) _).trans ?_
  rw [Category.id_comp]

theorem trF_box {pr : J → (X' ⟶ X)} {φ' : K → (Y ⟶ X')} {φ : J → K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : J → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) {y : Y} {jN jN' : K → J → M.ι}
    (hy : y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN)
    (hy' : y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN') :
    trF (L := LB.LinComb M pr (fun _ => 1)) φ' ε (𝟙 Y) y jN jN' =
      ∏ i, trF (φ i) ε (ρ i) y (fun a => jN a i) (fun a => jN' a i) := by
  unfold trF
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Finset.prod_zpow]
  refine congrArg (· ^ ε a) ?_
  refine (gm_linComb M pr (fun _ => 1) (𝟙 Y ≫ φ' a) y (jN a) (jN' a) (Set.mem_iInter.1 hy a)
    (Set.mem_iInter.1 hy' a)).trans (Finset.prod_congr rfl fun i _ => ?_)
  rw [zpow_one, Category.id_comp, hψ]

theorem box_isGen {pr : J → (X' ⟶ X)} {φ' : K → (Y ⟶ X')} {φ : J → K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : J → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) (t : ∀ i, LB.Gen (LB.LinComb M (φ i) ε)) (ht : ∀ i, (t i).IsGen) :
    (Out.GeneratorPullback.boxGen M pr φ' ε (fun i => Out.GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i))).IsGen := by
  refine isGen_of_gm _ fun y jN jN' hy hy' => ?_
  refine (gm_box hψ t hy).trans (Eq.trans ?_ (congrArg₂ (· * ·) (trF_box hψ hy hy') (gm_box hψ t hy')).symm)
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => gen_trans (ht i) (ρ i) y (mem_of_box hψ hy i) (mem_of_box hψ hy' i)

end Gen

section Grp

variable {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ}

theorem boxRig_isGen [IsCommMonObj G'] [IsCommMonObj G] (p : Out.IsPowGrp G' G j) (L : LB G.left)
    (r : LB.Gen (L.pull (eSec G))) (hr : r.IsGen) : (Out.boxRig p L r).IsGen :=
  box_isGen (M := L) (pr := fun i => (p.pr i).left) (φ' := fun _ : PUnit => eSec G') (φ := fun _ _ => eSec G)
    (ε := fun _ => 1) (ρ := fun _ => 𝟙 _)
    (fun i _ => letI := p.hom i; (CubeMap.ofHom (p.pr i)).e_comm) (fun _ => r) (fun _ => hr)

theorem sym_box (pr : Fin j → (G' ⟶ G)) [∀ i, IsMonHom (pr i)] (L : LB G.left) (hL : Out.Sym G L) :
    Out.Sym G' (Out.boxLB L pr) := by
  intro s
  obtain ⟨U, hU, t, ht⟩ := hL s
  have le : ∀ i, G'.hom ⁻¹ᵁ U ≤ (pr i).left ⁻¹ᵁ (G.hom ⁻¹ᵁ U) := fun i => by
    rw [← Scheme.Hom.comp_preimage, Over.w]
  have e : ∀ i, (G'.hom ⁻¹ᵁ U).ι ≫ (pr i).left = (pr i).left.resLE _ _ (le i) ≫ (G.hom ⁻¹ᵁ U).ι := fun i =>
    (Scheme.Hom.resLE_comp_ι _ _).symm
  refine ⟨U, hU, _, box_isGen (M := L) (pr := fun i => (pr i).left)
    (φ := fun _ => ![(G.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : G ⟶ G).left, (G.hom ⁻¹ᵁ U).ι])
    (ρ := fun i => (pr i).left.resLE _ _ (le i)) (fun i a => ?_) (fun _ => t) (fun _ => ht)⟩
  fin_cases a
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [← Category.assoc, ← e, Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, GrpObj.inv_hom]
  · exact e i

end Grp

theorem boxPower_basic : ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (j : ℕ), (Out.boxLB P.L (Out.powPr P.A (n := j))).IsLB ∧ Out.Sym (Out.powObj P.A j) (Out.boxLB P.L (Out.powPr P.A (n := j))) ∧ ∀ rig : LB.Gen (P.L.pull (eSec P.A)), rig.IsGen → (haveI := P.isAb.comm; (Out.boxRig (Out.powIsPowGrp P.A j) P.L rig).IsGen) := by
  intro R _ P j
  have := P.isAb.comm
  exact ⟨DVR.linComb_isLB _ P.isLB _ _, sym_box _ _ P.sym, fun rig h => boxRig_isGen _ _ rig h⟩

end GlobalTheory.BoxPower
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyKa

theorem exists_zpowGen {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℤ) :
    ∃ t' : LB.Gen (LB.LinComb L φ (fun k => ε k * n)), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J, val t' r z J = val t r z J ^ n := by
  refine ⟨⟨fun j => (show Γ(Y, LB.wchart L φ j)ˣ from t.s j) ^ n⟩, isGen_of_gm _ fun y j j' hj hj' => ?_,
    fun Z r z J => map_zpow _ _ _⟩
  refine (map_zpow _ _ _).trans (Eq.trans ?_ (congrArg _ (map_zpow _ _ _).symm))
  rw [gen_trans ht (𝟙 Y) y hj hj', mul_zpow]
  congr 1
  simp only [trF, zpow_mul, Finset.prod_zpow]

theorem exists_normalised_mulPull : Out.Laws → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (x : KeyIn R) (m : ℕ), ∃ mu : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] ![1, -(m : ℤ) ^ 2]), mu.IsGen ∧ ∀ (p : (𝟙_ (Over (Sp R))).left) J, Good x.P.L p J → val mu (eSec x.P.A) p J = val x.rig (𝟙 _) p J ^ (1 - (m : ℤ) ^ 2) := by
  intro laws R _ _ x m
  have hL := x.P.isLB
  obtain ⟨α, hα⟩ := laws.mulPull _ x.P m
  obtain ⟨ρ, hρ, hρv⟩ := exists_zpowGen (φ := fun _ : PUnit => eSec x.P.A) (ε := fun _ => 1) x.rig x.rig_gen
    (1 - (m : ℤ) ^ 2)
  have e₁ : eSec x.P.A ≫ (Out.mulA x.P.A m).left = eSec x.P.A := by
    have : η[x.P.A] ≫ Out.mulA x.P.A m = η[x.P.A] := by
      have h1 : η[x.P.A] = (1 : 𝟙_ (Over (Sp R)) ⟶ x.P.A) := by
        rw [Hom.one_def, toUnit_unit, Category.id_comp]
      rw [MonObj.comp_pow, Category.comp_id, h1, one_pow]
    exact congrArg (·.left) this
  have e₂ : eSec x.P.A ≫ (toUnit x.P.A).left = 𝟙 _ := by
    have : η[x.P.A] ≫ toUnit x.P.A = 𝟙 _ := toUnit_unique _ _
    exact congrArg (·.left) this
  obtain ⟨mu, hmu, hv⟩ := exists_gen hL (K' := Fin 2) (φ' := ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left])
    (ε' := ![1, -(m : ℤ) ^ 2]) (fun U _ f => by
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Sum.elim_inl, Sum.elim_inr, Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique,
        Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, e₁]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen x.P.L _ _ _ _ (LB.invGen x.P.L _ _ α) (LB.pullGen x.P.L _ _
      (LB.mulGen x.P.L _ _ _ _ (LB.pullGen x.P.L _ _ α (eSec x.P.A)) ρ) (toUnit x.P.A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ hα) (DVR.pullGen_isGen _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _) hρ) _))
  refine ⟨mu, hmu, fun p J hJ => ?_⟩
  rw [hv _ _ p J hJ, val_mul hJ, val_inv, val_pull hJ, val_mul hJ, val_pull hJ, hρv, e₂, Category.id_comp,
    inv_mul_cancel_left]

end GlobalTheory.KeyKa
end
end
