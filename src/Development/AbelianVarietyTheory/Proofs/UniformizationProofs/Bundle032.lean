module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle019
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle016
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.Bundle002

@[expose] public section

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.BiLift

section Gen
variable {X Y Y₀ : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem exists_val_lift (hL : L.IsLB) (f : Y₀ ⟶ Y) [IsClosedImmersion f] [Surjective f] [IsAffine Y]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t₀ : LB.Gen (LB.LinComb L (fun k => f ≫ φ k) ε)) (ht₀ : t₀.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y₀) (z : Z) (J), Good L z J → val t (r ≫ f) z J = val t₀ r z J := by
  have le : ∀ j : PUnit → K → L.ι, ((LB.LinComb L φ ε).pull f).U j ≤ LB.wchart L (fun k => f ≫ φ k) (j PUnit.unit) :=
    fun j y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (mem_pull.1 hy) k
  let c : LB.Gen ((LB.LinComb L φ ε).pull f) := ⟨fun j => res (le j) (t₀.s (j PUnit.unit))⟩
  have hc : c.IsGen := isGen_of_gm (M := LB.LinComb L φ ε) c fun y j j' hj hj' => by
    refine (gm_res _ y _ hj _).trans ((gen_trans ht₀ (𝟙 Y₀) y (le j hj) (le j' hj')).trans
      (congrArg₂ (· * ·) ?_ (gm_res _ y _ hj' _).symm))
    unfold trF
    symm
    rw [Fintype.prod_unique, zpow_one]
    refine (gm_linComb L φ ε (𝟙 Y₀ ≫ f) y _ _ (mem_pull.1 hj) (mem_pull.1 hj')).trans ?_
    simp only [Category.assoc]
  obtain ⟨t, ht, e⟩ := GenLift.exists_genPull_eq f (LB.isLB_linComb hL φ ε) c hc
  refine ⟨t, ht, fun Z r z J hJ => ?_⟩
  rw [val_of t (r ≫ f) z J (fun k => J (r ≫ f ≫ φ k)) (fun k => by rw [Category.assoc])]
  have hm := hJ.mem (fun k => f ≫ φ k) r
  have hm' : r z ∈ ((LB.LinComb L φ ε).pull f).U (fun _ k => J (r ≫ f ≫ φ k)) :=
    mem_pull.2 (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hm k)
  have e' := congrArg (fun q : LB.Gen ((LB.LinComb L φ ε).pull f) => gm r z _ (q.s fun _ k => J (r ≫ f ≫ φ k))) e
  refine Eq.trans ?_ (e'.trans (gm_res r z _ hm' _))
  exact ((gm_res r z _ hm' _).trans (gm_pull r f z _ (mem_pull.1 hm') _)).symm

theorem unit_eq_one {u : Γ(Y, ⊤)ˣ}
    (h : ∀ y : Y, ∃ (W : Y.Opens) (hy : y ∈ W), gm W.ι (⟨y, hy⟩ : W.toScheme) ⊤ u = 1) : u = 1 :=
  unit_ext fun y _ => by
    obtain ⟨W, hy, e⟩ := h y
    exact gm_inj W.ι (⟨y, hy⟩ : W.toScheme) (U := ⊤) (U' := ⊤) trivial trivial (e.trans (map_one _).symm)

end Gen

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)

def lam {Y : Over S} (a x : Y ⟶ G) : Fin 4 → (Y.left ⟶ G.left) := ![(a * x).left, a.left, x.left, (1 : Y ⟶ G).left]

theorem comp_lam {Y Z : Over S} (r : Z ⟶ Y) (a x : Y ⟶ G) (k : Fin 4) : r.left ≫ lam a x k = lam (r ≫ a) (r ≫ x) k := by
  fin_cases k
  · exact congrArg (·.left) (MonObj.comp_mul r a x)
  · rfl
  · rfl
  · exact congrArg (·.left) (MonObj.comp_one (M := G) r)

theorem prod_lam {Y : Over S} (a x : Y ⟶ G) {U : Type} [CommGroup U] (h : (Y.left ⟶ G.left) → U) :
    ∏ k, h (lam a x k) ^ Oε k = h (a * x).left * (h a.left)⁻¹ * (h x.left)⁻¹ * h (1 : Y ⟶ G).left := by
  simp [Fin.prod_univ_four, lam, Oε]

theorem exists_pull_lam {Y Z : Over S} (r : Z ⟶ Y) {a x : Y ⟶ G} {a' x' : Z ⟶ G} (ha : r ≫ a = a') (hx : r ≫ x = x')
    (s : LB.Gen (LB.LinComb L.L (lam a x) Oε)) (hs : s.IsGen) :
    ∃ s' : LB.Gen (LB.LinComb L.L (lam a' x') Oε), s'.IsGen ∧
      ∀ (W : Scheme.{0}) (q : W ⟶ Z.left) (z : W) (J), Good L.L z J → val s' q z J = val s (q ≫ r.left) z J := by
  subst ha hx
  obtain ⟨s', hs', e⟩ := exists_gen L.isLB (φ' := lam (r ≫ a) (r ≫ x)) (ε' := Oε)
    (fun U _ h => by simp only [comp_lam]) (LB.pullGen L.L _ _ s r.left) (DVR.pullGen_isGen _ _ _ _ hs _)
  exact ⟨s', hs', fun W q z J hJ => (e W q z J hJ).trans (val_pull hJ _ _ _)⟩

theorem exists_defect {Y : Over S} (a b x : Y ⟶ G) {φ₁ φ₂ φ₃ : Fin 4 → (Y.left ⟶ G.left)}
    (h₁ : FormEq φ₁ Oε (lam (a * b) x) Oε) (h₂ : FormEq φ₂ Oε (lam a x) Oε) (h₃ : FormEq φ₃ Oε (lam b x) Oε)
    (s₁ : LB.Gen (LB.LinComb L.L φ₁ Oε)) (s₂ : LB.Gen (LB.LinComb L.L φ₂ Oε)) (s₃ : LB.Gen (LB.LinComb L.L φ₃ Oε))
    (g₁ : s₁.IsGen) (g₂ : s₂.IsGen) (g₃ : s₃.IsGen) :
    ∃ f : Γ(Y.left, ⊤)ˣ, ∀ (Z : Over S) (r : Z ⟶ Y) (z : Z.left) (J), Good L.L z J →
      val s₁ r.left z J = gm r.left z ⊤ f * (cubV c z J (r ≫ a) (r ≫ b) (r ≫ x) * val s₂ r.left z J * val s₃ r.left z J) := by
  obtain ⟨f, hf⟩ := TorusCoord.exists_ratio L.isLB (fun U _ h => by
      refine Eq.trans ?_ (DVR.prod_sum₂ (K := thK ⊕ Fin 4) (K' := Fin 4) (U := U) _
        (DVR.prod_sum₂ (K := thK) (K' := Fin 4) (U := U) _ (prod_cub a b x h) ((h₂ U h).trans (prod_lam a x h)))
        ((h₃ U h).trans (prod_lam b x h))).symm
      rw [h₁ U h, prod_lam]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) s₁ g₁
    (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b x)).left) s₂) s₃)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ c.isGen _) g₂) g₃)
  refine ⟨f, fun Z r z J hJ => (hf _ r.left z J hJ).trans (congrArg _ ?_)⟩
  exact (val_mul hJ _ _ _).trans (congrArg (· * _) ((val_mul hJ _ _ _).trans (congrArg (· * _) (val_cub c r hJ _ _ _))))

omit [GrpObj G] [IsCommMonObj G] in
theorem formEq_refl {Y : Over S} (φ : Fin 4 → (Y.left ⟶ G.left)) : FormEq φ Oε φ Oε := fun _ _ _ => rfl

theorem formEq_symm {Y : Over S} (a x : Y ⟶ G) : FormEq (lam a x) Oε (lam x a) Oε := fun U _ h => by
  rw [prod_lam, prod_lam, mul_comm x a, mul_right_comm (h _) (h a.left)⁻¹]

variable {H Y : Over S} [GrpObj H] {i : H ⟶ G} [IsMonHom i] {x : Y ⟶ G}

theorem exists_defect₁ (s : LB.Gen (LB.LinComb L.L (lam (fst H Y ≫ i) (snd H Y ≫ x)) Oε)) (hs : s.IsGen) :
    ∃ f : Γ((H ⊗ H ⊗ Y).left, ⊤)ˣ, ∀ (Z : Over S) (t t' : Z ⟶ H) (y : Z ⟶ Y) (z : Z.left) (J), Good L.L z J →
      val s (lift (t * t') y).left z J = gm (lift t (lift t' y)).left z ⊤ f *
        (cubV c z J (t ≫ i) (t' ≫ i) (y ≫ x) * val s (lift t y).left z J * val s (lift t' y).left z J) := by
  let p : H ⊗ H ⊗ Y ⟶ H := fst _ _
  let p' : H ⊗ H ⊗ Y ⟶ H := snd _ _ ≫ fst _ _
  let q : H ⊗ H ⊗ Y ⟶ Y := snd _ _ ≫ snd _ _
  obtain ⟨s₁, g₁, e₁⟩ := exists_pull_lam (lift (p * p') q) (a' := p ≫ i * p' ≫ i) (x' := q ≫ x)
    (by rw [lift_fst_assoc, MonObj.mul_comp]) (lift_snd_assoc _ _ _) s hs
  obtain ⟨s₂, g₂, e₂⟩ := exists_pull_lam (lift p q) (lift_fst_assoc _ _ _) (lift_snd_assoc _ _ _) s hs
  obtain ⟨s₃, g₃, e₃⟩ := exists_pull_lam (lift p' q) (lift_fst_assoc _ _ _) (lift_snd_assoc _ _ _) s hs
  obtain ⟨f, hf⟩ := exists_defect c _ _ _ (formEq_refl _) (formEq_refl _) (formEq_refl _) s₁ s₂ s₃ g₁ g₂ g₃
  refine ⟨f, fun Z t t' y z J hJ => ?_⟩
  have e := hf Z (lift t (lift t' y)) z J hJ
  rw [e₁ _ _ z J hJ, e₂ _ _ z J hJ, e₃ _ _ z J hJ] at e
  simpa only [← Over.comp_left, comp_lift, MonObj.comp_mul, p, p', q, lift_fst, lift_snd, lift_fst_assoc,
    lift_snd_assoc, Category.assoc] using e


omit [IsMonHom i] [GrpObj H] in
theorem exists_defect₂ (s : LB.Gen (LB.LinComb L.L (lam (fst H G ≫ i) (snd H G)) Oε)) (hs : s.IsGen) :
    ∃ f : Γ((H ⊗ G ⊗ G).left, ⊤)ˣ, ∀ (Z : Over S) (t : Z ⟶ H) (y : Z ⟶ G ⊗ G) (z : Z.left) (J), Good L.L z J →
      val s (lift t (y ≫ fst _ _ * y ≫ snd _ _)).left z J = gm (lift t y).left z ⊤ f *
        (cubV c z J (t ≫ i) (y ≫ fst _ _) (y ≫ snd _ _) * val s (lift t (y ≫ fst _ _)).left z J *
          val s (lift t (y ≫ snd _ _)).left z J) := by
  let p : H ⊗ G ⊗ G ⟶ H := fst _ _
  let q : H ⊗ G ⊗ G ⟶ G := snd _ _ ≫ fst _ _
  let q' : H ⊗ G ⊗ G ⟶ G := snd _ _ ≫ snd _ _
  obtain ⟨s₁, g₁, e₁⟩ := exists_pull_lam (lift p (q * q')) (lift_fst_assoc _ _ _) (lift_snd _ _) s hs
  obtain ⟨s₂, g₂, e₂⟩ := exists_pull_lam (lift p q) (lift_fst_assoc _ _ _) (lift_snd _ _) s hs
  obtain ⟨s₃, g₃, e₃⟩ := exists_pull_lam (lift p q') (lift_fst_assoc _ _ _) (lift_snd _ _) s hs
  obtain ⟨f, hf⟩ := exists_defect c _ _ _ (formEq_symm _ _) (formEq_symm _ _) (formEq_symm _ _) s₁ s₂ s₃ g₁ g₂ g₃
  refine ⟨f, fun Z t y z J hJ => ?_⟩
  have e := hf Z (lift t y) z J hJ
  rw [e₁ _ _ z J hJ, e₂ _ _ z J hJ, e₃ _ _ z J hJ, (isCub_cubV c hJ).s12, (isCub_cubV c hJ).s01] at e
  simpa only [← Over.comp_left, comp_lift, MonObj.comp_mul, p, q, q', lift_fst, lift_snd, lift_fst_assoc,
    lift_snd_assoc, Category.assoc] using e

end GlobalTheory.UU.BiLift
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnifPreCompare

section General

variable {X₁ X₂ Y Y₁ Y₂ T : Scheme.{0}} {L : LB X₁} {M : LB X₂} {a : Y ⟶ X₁} {b : Y ⟶ X₂}
  {K : Type} [Fintype K]

variable {w : LB.Iso (L.pull a) (M.pull b)} {ψ : K → (T ⟶ Y)} {ε : K → ℤ}
  {φ₁ : K → (Y₁ ⟶ X₁)} {s : LB.Gen (LB.LinComb L φ₁ ε)} {f₁ : T ⟶ Y₁}
  {φ₂ : K → (Y₂ ⟶ X₂)} {t : LB.Gen (LB.LinComb M φ₂ ε)} {f₂ : T ⟶ Y₂}

end General

section Rigid

variable {X X' T Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem exists_ratio {M : LB X} (cov : ∀ x, ∃ j, x ∈ M.U j) {t t' : LB.Gen M} (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ u : Γ(X, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (j : M.ι), r z ∈ M.U j →
      gm r z _ (t.s j) = gm r z ⊤ u * gm r z _ (t'.s j) := by
  obtain ⟨u, hu⟩ := glue_unit ⊤ M.U (fun _ => le_top) (fun x _ => TopologicalSpace.Opens.mem_iSup.2 (cov x))
    (fun j => t.s j * (t'.s j)⁻¹) (fun i j x hx => by
      rw [map_mul, map_mul, map_inv, map_inv, GtCoordCompare.gm_gen ht (𝟙 X) x hx.1 hx.2,
        GtCoordCompare.gm_gen ht' (𝟙 X) x hx.1 hx.2, ← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div])
  refine ⟨u, fun Z r z j hj => ?_⟩
  rw [← gm_res r z (le_top : M.U j ≤ ⊤) hj u, hu, map_mul, map_inv, inv_mul_cancel_right]

theorem exists_rigidified (hL : L.IsLB) (hL' : L'.IsLB) (π : X' ⟶ T) (σ : T ⟶ X') (hσ : σ ≫ π = 𝟙 T)
    (w₀ : LB.Iso L' (L.pull F)) (hw₀ : w₀.IsGen) (ρ' : LB.Gen (L'.pull σ)) (hρ' : ρ'.IsGen) {φ : Y ⟶ X}
    (ρ : LB.Gen (L.pull φ)) (hρ : ρ.IsGen) (h : T ⟶ Y) (e : σ ≫ F = h ≫ φ) :
    ∃ w : LB.Iso L' (L.pull F), w.IsGen ∧ PMaps w (K := PUnit) (fun _ => σ) (fun _ => φ) (fun _ => 1) ρ' ρ h := by
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff w₀).1 hw₀) hL hL' ρ' hρ'
  have ex : ∀ g : T ⟶ X, g = h ≫ φ → ∃ t' : LB.Gen (L.pull g), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) p,
      r z ∈ (L.pull g).U p → gm r z _ (t'.s p) = gm (r ≫ h) z ((L.pull φ).U p) (ρ.s p) := by
    rintro _ rfl
    exact ⟨LB.pullGen L _ _ ρ h, DVR.pullGen_isGen _ _ _ _ hρ h, fun Z r z p hp =>
      (gm_res r z _ hp _).trans (gm_pull r h z _ (mem_pull.2 (mem_pull₂.1 hp)) _)⟩
  obtain ⟨t', ht', hv'⟩ := ex _ e
  obtain ⟨u, hu⟩ := exists_ratio (M := L.pull (σ ≫ F)) (fun x => by
    obtain ⟨j, hj⟩ := exists_chart hL (F (σ x))
    exact ⟨fun _ => j, mem_pull₂.2 hj⟩) ht' ht
  let w : LB.Iso L' (L.pull F) := ⟨fun p => res le_top (pullU π ⊤ u) * w₀.s p⟩
  have hw : ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gw w r z j k = gm (r ≫ π) z ⊤ u * gw w₀ r z j k := fun Z r z j k hj hk =>
    (map_mul _ _ _).trans (congrArg (· * _) (GtCoordCompare.gm_res_pull_top r z π
      (V := (L.pull F).U (fun _ => j) ⊓ L'.U k) ⟨mem_pull.2 hj, hk⟩ _ u))
  refine ⟨w, (isGen_iff w).2 fun Z r z j j' k k' hj hj' hk hk' => ?_, fun Z r z p q hp hq => ?_⟩
  · rw [hw Z r z j k hj hk, hw Z r z j' k' hj' hk', (isGen_iff w₀).1 hw₀ Z r z j j' k k' hj hj' hk hk']
    exact mul_left_comm _ _ _
  · have m : r z ∈ (L.pull (σ ≫ F)).U p := mem_pull₂.2 (hp _)
    refine (hv' Z r z p m).symm.trans ((hu Z r z p m).trans ?_)
    refine (congrArg _ (hv Z r z p q m (Set.mem_iInter.2 hq))).trans ?_
    rw [pw, Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one, hw Z (r ≫ σ) z _ _ (hp _) (hq _),
      Category.assoc, hσ, Category.comp_id, _root_.mul_assoc]

end Rigid

section Cube

open GlobalTheory.IndefiniteRowSideFullHecke.SeparatedSymmetricModel

variable {S S' : Scheme.{0}} (p : S' ⟶ S) {G : Over S} {H T : Over S'}

end Cube

section Clauses

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SeparatedSymmetricModel

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {e : ℕ}

variable {LG : RigLB G} {g : GtCoord I D e G} {j : CanonicalRigidImages.GtIso D I e G}
  {w : LB.Iso (LG.L.pull (fstG I e G).left) (D.P.L.pull g.pG.left)}
  {ph : LB.Iso (LG.L.pull (toG I e G).F) (D.P.L.pull (toB j).F)}

end Clauses

section Main

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SeparatedSymmetricModel

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

variable {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {rA : LB.Gen (A.L.pull (eSec A.A))}

end Main

end GlobalTheory.UnifPreCompare
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace AbelianPartIso

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

theorem isMonHom_of_comp {S : Scheme.{0}} {G B B' : Over S} [GrpObj G] [GrpObj B] [GrpObj B']
    (q' : G ⟶ B') (q : G ⟶ B) (β : B' ⟶ B) [IsMonHom q'] [IsMonHom q] [Flat q'.left]
    [Surjective q'.left] (hβ : q' ≫ β = q) : IsMonHom β := by
  refine ⟨?_, ?_⟩
  · rw [← IsMonHom.one_hom q', Category.assoc, hβ, IsMonHom.one_hom]
  · have := FlatQuotient.epi_tensorHom q' q'
    rw [← cancel_epi (q' ⊗ₘ q'), ← IsMonHom.mul_hom_assoc, hβ, tensorHom_comp_tensorHom_assoc, hβ,
      IsMonHom.mul_hom]

theorem hom_eq_of_map_eq {R : Type} [CommRing R] [IsNoetherianRing R] {I : Ideal R}
    (hI : I ≤ Ideal.jacobson ⊥) (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [Smooth H.hom]
    [GeometricallyConnected H.hom] {Y : Over (Spec (CommRingCat.of R))} [IsSeparated Y.hom]
    (f g : H ⟶ Y)
    (h : ∀ n, (Over.pullback (thick R I n)).map f = (Over.pullback (thick R I n)).map g) : f = g := by
  refine (sec_eq_zero_and_hom_eq_of_thickenings R I hI H).2 Y f g fun n => ?_
  have k : ∀ f : H ⟶ Y, ((Over.pullback (thick R I n)).map f).left ≫ pullback.fst Y.hom (thick R I n) =
      pullback.fst H.hom (thick R I n) ≫ f.left := fun f => pullback.lift_fst _ _ _
  exact (k f).symm.trans ((congrArg (fun φ => φ.left ≫ pullback.fst Y.hom (thick R I n)) (h n)).trans (k g))

theorem isMonHom_of_thickenings {R : Type} [CommRing R] [IsNoetherianRing R] {I : Ideal R}
    (hI : I ≤ Ideal.jacobson ⊥) {B B' : Over (Spec (CommRingCat.of R))} [GrpObj B] [GrpObj B']
    (hB : IsAbelianScheme B) (hB' : IsAbelianScheme B') (f : B' ⟶ B)
    (h : ∀ n, IsMonHom ((Over.pullback (thick R I n)).map f)) : IsMonHom f := by
  have := hB.proper
  have := hB'.smooth
  have := hB'.geomConnected
  refine ⟨?_, ?_⟩
  · have : Smooth (𝟙_ (Over (Spec (CommRingCat.of R)))).hom := inferInstanceAs (Smooth (𝟙 _))
    have : GeometricallyConnected (𝟙_ (Over (Spec (CommRingCat.of R)))).hom :=
      inferInstanceAs (GeometricallyConnected (𝟙 _))
    refine hom_eq_of_map_eq hI _ _ _ fun n => ?_
    have e := (h n).one_hom
    rw [Functor.obj.η_def, Functor.obj.η_def, Category.assoc, cancel_epi, ← Functor.map_comp] at e
    exact e
  · have : Smooth (B' ⊗ B').hom := inferInstanceAs (Smooth (pullback.fst B'.hom B'.hom ≫ B'.hom))
    have : GeometricallyConnected (B' ⊗ B').hom := by
      change GeometricallyConnected (pullback.fst B'.hom B'.hom ≫ B'.hom)
      exact GeometricallyConnected.comp _ _
    refine hom_eq_of_map_eq hI _ _ _ fun n => ?_
    have e := (h n).mul_hom
    rw [Functor.obj.μ_def, Functor.obj.μ_def, Category.assoc, Functor.LaxMonoidal.μ_natural_assoc,
      cancel_epi, ← Functor.map_comp, ← Functor.map_comp] at e
    exact e

theorem fn_eq_of_thickenings {R : Type} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {I : Ideal R} (hI : I ≠ ⊤)
    (W : (Spec (CommRingCat.of R)).Opens) (hW : W = ⊤) (a b : Γ(Spec (CommRingCat.of R), W))
    (h : ∀ (e : ℕ) (z), gs (thick R I e) z W a = gs (thick R I e) z W b) : a = b := by
  subst hW
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
  apply hinj
  rw [← sub_eq_zero, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing I hI, Ideal.mem_iInf]
  intro e
  refine Ideal.pow_le_pow_right (Nat.le_succ e) (Ideal.Quotient.eq.1 ?_)
  have key : ((thick R I e).app ⊤).hom a = ((thick R I e).app ⊤).hom b := by
    refine fn_ext fun z hz => ?_
    rw [gs_pull _ _ z ⊤ trivial, gs_pull _ _ z ⊤ trivial, Category.id_comp]
    exact h e z
  have nat := fun x => congrArg (fun φ => φ.hom x)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
  exact (nat a).symm.trans ((congrArg _ key).trans (nat b))

theorem pmaps_of_thickenings {R : Type} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {I : Ideal R} (hI : I ≠ ⊤) {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} (hL : L.IsLB)
    (hL' : L'.IsLB) {F : X' ⟶ X} (w : LB.Iso L' (L.pull F)) (hw : w.IsGen)
    (s' : Spec (CommRingCat.of R) ⟶ X') (s : Spec (CommRingCat.of R) ⟶ X) (hs : s' ≫ F = s)
    (a : LB.Gen (L'.pull s')) (ha : a.IsGen) (t : LB.Gen (L.pull s)) (ht : t.IsGen)
    (h : ∀ (e : ℕ) (z) (p : L.ι) (q : L'.ι), (thick R I e ≫ s) z ∈ L.U p →
      (thick R I e ≫ s') z ∈ L'.U q →
      gm (thick R I e) z ((L.pull s).U (fun _ => p)) (t.s (fun _ => p)) =
        gw w (thick R I e ≫ s') z p q *
          gm (thick R I e) z ((L'.pull s').U (fun _ => q)) (a.s (fun _ => q))) :
    PMaps w (K := PUnit) (fun _ => s') (fun _ => s) (fun _ => 1) a t (𝟙 _) := by
  subst hs
  obtain ⟨p₀, hp₀⟩ := exists_chart hL ((s' ≫ F) (IsLocalRing.closedPoint R))
  obtain ⟨q₀, hq₀⟩ := exists_chart hL' (s' (IsLocalRing.closedPoint R))
  have hp : ∀ x, (s' ≫ F) x ∈ L.U p₀ := fun x =>
    ((IsLocalRing.specializes_closedPoint (R := R) x).map (s' ≫ F).continuous).mem_open
      (L.U p₀).isOpen hp₀
  have hq : ∀ x, s' x ∈ L'.U q₀ := fun x =>
    ((IsLocalRing.specializes_closedPoint (R := R) x).map s'.continuous).mem_open
      (L'.U q₀).isOpen hq₀
  have l₁ : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (L.pull (s' ≫ F)).U (fun _ => p₀) :=
    fun x _ => mem_pull.2 (hp x)
  have l₂ : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (L'.pull s').U (fun _ => q₀) :=
    fun x _ => mem_pull.2 (hq x)
  have l₃ : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤
      s' ⁻¹ᵁ ((L.pull F).U (fun _ => p₀) ⊓ L'.U q₀) :=
    fun x _ => ⟨mem_pull.2 (hp x), hq x⟩
  have ev₁ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z),
      gm r z ⊤ (res l₁ (t.s (fun _ => p₀))) =
        gm r z ((L.pull (s' ≫ F)).U (fun _ => p₀)) (t.s (fun _ => p₀)) :=
    fun Z r z => gm_res r z l₁ trivial _
  have ev₂ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z),
      gm r z ⊤ (res l₃ (pullU s' _ (w.s (fun _ => p₀, q₀))) * res l₂ (a.s (fun _ => q₀))) =
        gw w (r ≫ s') z p₀ q₀ * gm r z ((L'.pull s').U (fun _ => q₀)) (a.s (fun _ => q₀)) :=
    fun Z r z => (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res r z l₃ trivial _).trans (gm_pull r s' z _ (l₃ (Set.mem_univ (r z))) _))
      (gm_res r z l₂ trivial _))
  have key : res l₁ (t.s (fun _ => p₀)) =
      res l₃ (pullU s' _ (w.s (fun _ => p₀, q₀))) * res l₂ (a.s (fun _ => q₀)) := by
    refine Units.ext (fn_eq_of_thickenings hI ⊤ rfl _ _ fun e z => ?_)
    rw [gs_unit _ z ⊤ trivial, gs_unit _ z ⊤ trivial, ev₁, ev₂, h e z p₀ q₀ (hp _) (hq _)]
  intro Z r z p q hpz hqz
  have E := (ev₁ Z r z).symm.trans ((congrArg (gm r z ⊤) key).trans (ev₂ Z r z))
  have a₁ := gen_trans ht r z (j := p) (j' := fun _ => p₀) (Set.mem_iInter.2 hpz) (l₁ (Set.mem_univ _))
  have a₂ := gen_trans ha r z (j := q) (j' := fun _ => q₀) (Set.mem_iInter.2 hqz) (l₂ (Set.mem_univ _))
  have a₃ := (isGen_iff w).1 hw Z (r ≫ s') z (p PUnit.unit) p₀ (q PUnit.unit) q₀ (hpz _) (hp _)
    (hqz _) (hq _)
  rw [Category.comp_id, a₁, a₂, Fintype.prod_unique, zpow_one, a₃]
  refine (congrArg _ E).trans ?_
  simp only [trF, Fintype.prod_unique, zpow_one, Category.assoc, PUnit.default_eq_unit]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end AbelianPartIso


open AbelianPartIso ReciprocityTheory.ChartRestriction.G.DVR in
theorem abelianPartIso_isMonHom_and_rigidified : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (wL : LB.Iso U'.LG.L (U.LG.L.pull (𝟙 G.left))) (he : eSec G ≫ 𝟙 G.left = 𝟙 _ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) U'.LG.rig (rigPullOf (𝟙 G.left) (𝟙 _) he U.LG.L U.LG.rig) → ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso D'.toPre.P.L (D.toPre.P.L.pull Φ.hom.left)), (w.IsGen ∧ ∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) r z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I e G).left) z jL jL')) → (IsMonHom Φ.hom ∧ Geo.Tor.PMaps w (K := PUnit) (fun _ => eSec D'.toPre.P.A) (fun _ => eSec D.toPre.P.A) (fun _ => 1) D'.toPre.rig D.toPre.rig (𝟙 _)) := by
  intro R _ _ _ I hR D D' A A' G _ _ _ U U' wL he hwL hrig Φ w ⟨hw, H⟩
  obtain ⟨_, -, -, _⟩ := hR
  have hI : I ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot I
  have hI' : I ≠ ⊤ := fun h => (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (top_le_iff.1 (h.ge.trans (hI.trans (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).le)))
  have hΦ : IsMonHom Φ.hom := by
    refine isMonHom_of_thickenings hI D.toPre.P.isAb D'.toPre.P.isAb Φ.hom fun e => ?_
    have := (U.gt e).q_hom
    have := (U'.gt e).q_hom
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    refine isMonHom_of_comp (U'.gt e).q (U.gt e).q _ (Over.OverMorphism.ext ?_)
    refine pullback.hom_ext ?_ ?_
    · have k : ((Over.pullback (thick R I e)).map Φ.hom).left ≫
          pullback.fst D.toPre.P.A.hom (thick R I e) =
          pullback.fst D'.toPre.P.A.hom (thick R I e) ≫ Φ.hom.left := pullback.lift_fst _ _ _
      exact (Category.assoc _ _ _).trans ((congrArg ((U'.gt e).q.left ≫ ·) k).trans
        ((Category.assoc _ _ _).symm.trans (H e).1))
    · exact (Over.w _).trans (Over.w (U.gt e).q).symm
  refine ⟨hΦ, pmaps_of_thickenings hI' D.toPre.P.isLB D'.toPre.P.isLB w hw _ _
    (congrArg Over.Hom.left hΦ.one_hom) _ D'.toPre.rig_gen _ D.toPre.rig_gen
    fun e z p q hp hq => ?_⟩
  obtain ⟨j, hj⟩ := Geo.Tor.exists_chart U.LG.isLB ((UnitValue.thU R I e ≫ eSec G) z)
  obtain ⟨j', hj'⟩ := Geo.Tor.exists_chart U'.LG.isLB ((UnitValue.thU R I e ≫ eSec G) z)
  have e₁ := UnitValue.wv_rig U e z p j hp hj
  have e₂ := UnitValue.wv_rig U' e z q j' hq hj'
  have e₃ := (Geo.Tor.maps_iff wL _ (fun _ => eSec G) _ U'.LG.rig U.LG.rig (𝟙 _) _
    (rigPull_le (𝟙 G.left) (𝟙 _) he U.LG.L) (fun _ => rfl)).1 hrig _ (UnitValue.thU R I e) z
    (fun _ => j) (fun _ => j') (fun _ => hj) (fun _ => hj')
  have e₄ := (H e).2 _ (eSec (thickObj R I e G)) z p q j j'
    ((congrArg (fun g => g z ∈ D.toPre.P.L.U p) (UnitValue.eSec_pGl U e)).mpr hp)
    ((congrArg (fun g => g z ∈ D'.toPre.P.L.U q) (UnitValue.eSec_pGl U' e)).mpr hq)
    ((congrArg (fun g => g z ∈ U.LG.L.U j) (UnitValue.eSec_fGl (G := G) e)).mpr hj)
    ((congrArg (fun g => g z ∈ U'.LG.L.U j') (UnitValue.eSec_fGl (G := G) e)).mpr hj')
  rw [UnitValue.eSec_pGl U' e, UnitValue.eSec_fGl (G := G) e] at e₄
  rw [Category.comp_id, Fintype.prod_unique, zpow_one] at e₃
  refine e₁.symm.trans ((congrArg _ e₃).trans ((mul_assoc _ _ _).symm.trans ?_))
  exact (congrArg (· * _) e₄.symm).trans ((mul_assoc _ _ _).trans (congrArg _ e₂))

end GlobalTheory
end
