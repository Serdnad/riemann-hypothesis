module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle125
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRingEquiv
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle013
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle059
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsStarNormLEOfIsCMField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle130

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch.FibCube
open GlobalTheory.FrameValue GlobalTheory.TorusExt

theorem vF_eq_genVal_mul {X Y Y' : Scheme.{0}} {L : LB X} {A : Over (Sp ℂ)} [GrpObj A] {L' : LB A.left} {g : ℕ}
    (u : HolUnif A L' g) (hL' : L'.IsLB) {Φ : A.left ⟶ X} {w : LB.Iso L' (L.pull Φ)} {K : Type} [Fintype K]
    {φ' : K → (Y' ⟶ A.left)} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y} (hψ : ∀ k, φ' k ≫ Φ = h ≫ φ k)
    {a : LB.Gen (LB.LinComb L' φ' ε)} (ha : a.IsGen) {t : LB.Gen (LB.LinComb L φ ε)} (H : PMaps w φ' φ ε a t h)
    {J : (Sp ℂ ⟶ X) → L.ι} (hJ : ∀ ψ : Sp ℂ ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) (fr : (Fin g → ℂ) → ℂˣ)
    (hfr : ∀ z i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U i →
      (fr z : ℂ) = valAt' (u.ex z).left _ (w.s (fun _ => J ((u.ex z).left ≫ Φ), i)).val * u.fr i z)
    {r : Sp ℂ ⟶ Y'} {z : K → Fin g → ℂ} (hz : IsLift u φ' r z) :
    vF t (r ≫ h) J = genVal u hL' a r z * ((∏ k, fr (z k) ^ ε k : ℂˣ) : ℂ) := by
  let p : Sp ℂ := (default : PrimeSpectrum ℂ)
  let J' : (Sp ℂ ⟶ A.left) → L'.ι := chartAt hL'
  have hJ' : ∀ ψ : Sp ℂ ⟶ A.left, ⊤ ≤ ψ ⁻¹ᵁ L'.U (J' ψ) := le_chartAt hL'
  have e := congrArg (fun q => (((stalkUnits p).symm q : ℂˣ) : ℂ))
    (DegPull.pmaps_val hψ H r p (J := J) (J' := J') (fun ψ => hJ ψ trivial) (fun ψ => hJ' ψ trivial))
  have e₁ : vF a r J' = genVal u hL' a r z * GlobalTheory.FrameValue.frameProd u ε z (fun k => J' (r ≫ φ' k)) :=
    valAt'_gen hL' ha hz (le_wchart_chartAt hL' φ' r)
  have e₂ : ∀ v, (((stalkUnits p).symm (gw w (u.ex v).left p (J ((u.ex v).left ≫ Φ)) (J' (u.ex v).left)) : ℂˣ) : ℂ) *
      u.fr (J' (u.ex v).left) v = fr v := fun v => by
    rw [hfr v _ (hJ' _)]
    refine congrArg (· * _) ((stalkConst p).injective ?_)
    have m : ⊤ ≤ (u.ex v).left ⁻¹ᵁ ((L.pull Φ).U (fun _ => J ((u.ex v).left ≫ Φ)) ⊓ L'.U (J' (u.ex v).left)) :=
      fun y hy => ⟨mem_pull.2 (hJ ((u.ex v).left ≫ Φ) hy), hJ' _ hy⟩
    rw [← stalkUnits_val, MulEquiv.apply_symm_apply]
    exact (gs_unit (u.ex v).left p ((L.pull Φ).U (fun _ => J ((u.ex v).left ≫ Φ)) ⊓ L'.U (J' (u.ex v).left))
      (m trivial) _).symm.trans (gs_eq_stalkConst _ p m _)
  simp only [map_mul, map_prod, map_zpow, Units.val_mul] at e
  rw [GaugeValues.vF_eq hJ, GaugeValues.vF_eq hJ', e₁] at e
  rw [e, mul_left_comm]
  congr 1
  rw [GlobalTheory.FrameValue.frameProd, Units.coe_prod, Units.coe_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, ← mul_zpow, hz k, e₂]

theorem exists_cube_down {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'} [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f F) {L : RigLB G}
    (c : CubicalStr G L) {L' : LB G'.left} (hL' : L'.IsLB) {w : LB.Iso L' (L.L.pull F)} (hw : w.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' (thφ G' (x3 G')) thε), a.IsGen ∧
      PMaps w (thφ G' (x3 G')) (thφ G (x3 G)) thε a c.t (cubeMapOf gp).F3 ∧
      LB.Gen.Corr L' _ _ (Y := (G2 G').left) _ _ (LB.pullGen L' (thφ G' (x3 G')) thε a (faceMap G' 0).left)
        (LB.oneGen L') := by
  have hψ : ∀ I : thK, thφ G' (x3 G') I ≫ F = (cubeMapOf gp).F3 ≫ thφ G (x3 G) I :=
    fun I => (cubeMapOf gp).psum_comm I.down
  obtain ⟨a, ha, H⟩ := DegPull.exists_pmaps ((isGen_iff w).1 hw) L.isLB hL' (ε := thε) (cubeMapOf gp).F3 hψ c.t c.isGen
  refine ⟨a, ha, H, corr_of_val hL' fun y J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := DegPull.exists_good' L.isLB y
  have e := DegPull.pmaps_val hψ H (lift (1 : G2 G' ⟶ G') (lift (x2 G' 0) (x2 G' 1))).left y hJ hJ'
  have q : ∀ a b c : G2 G' ⟶ G', (lift a (lift b c)).left ≫ (cubeMapOf gp).F3 =
      (lift (pushHom gp _ a) (lift (pushHom gp _ b) (pushHom gp _ c))).left := fun a b c =>
    hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3] <;> rfl
  rw [q, map_one] at e
  have p := prod_cub (1 : G2 G' ⟶ G') (x2 G' 0) (x2 G' 1) (fun q => gw w q y (J (q ≫ F)) (J' q))
  rw [_root_.one_mul, _root_.one_mul] at p
  have face : val c.t (lift (1 : Over.mk ((G2 G').hom ≫ f) ⟶ G)
      (lift (pushHom gp _ (x2 G' 0)) (pushHom gp _ (x2 G' 1)))).left y J = 1 := by
    have h := val_corr hJ (c.face 0) (lift (pushHom gp _ (x2 G' 0)) (pushHom gp _ (x2 G' 1))).left
    rw [val_one] at h
    refine Eq.trans ?_ h
    refine Eq.trans ?_ (val_cub c (lift (pushHom gp _ (x2 G' 0)) (pushHom gp _ (x2 G' 1))) hJ (pzero G _) (x2 G 0) (x2 G 1)).symm
    congr 1 <;> simp [x2, pzero, Hom.one_def]
  have e' := face.symm.trans (e.trans (congrArg (· * _) p))
  refine (val_pull hJ' _ _ _).trans (Eq.trans ?_ (val_one _).symm)
  rw [Category.id_comp]
  apply Additive.ofMul.injective
  have e'' := congrArg Additive.ofMul e'
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at e'' ⊢
  refine Eq.trans ?_ e''.symm
  abel

end GlobalTheory.Ex.Arch.FibCube

namespace GlobalTheory.Ex.Arch
open GlobalTheory.FrameValue GlobalTheory.CubeValues

theorem fibCubeSt : Laws → FibCubeSt := by
  rintro - R _ _ _ D J g Λ Hm χ ex fr ⟨hJ, P', φ, w, u, hΛ, gp, hw, hAH, -, -, -, hex, hfr⟩ x y z
  obtain ⟨a, ha, H, hf⟩ := FibCube.exists_cube_down gp D.cub P'.isLB hw
  have e := FibCube.vF_eq_genVal_mul (L := D.P.L) (Φ := φ) (w := w) u P'.isLB (fun I : thK => (cubeMapOf gp).psum_comm I.down) ha H hJ fr
    (fun v i hi => by rw [← hex v]; exact hfr v i hi) (isLift_cube u ![x, y, z])
  replace e := e.trans ((congrArg (· * _) (genVal_cube_of_face P'.isLB hAH a ha hf _)).trans (_root_.one_mul _))
  have q : (pt3 u ![x, y, z]).left ≫ (cubeMapOf gp).F3 = (lift (ex x) (lift (ex y) (ex z))).left :=
    hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3, pt3, hex] <;> rfl
  have p := prod_thK fun I => fr (∑ a ∈ I, ![x, y, z] a)
  simp only [sum_three, Finset.sum_singleton, Finset.sum_empty, Matrix.cons_val] at p
  rw [q] at e
  refine (congrArg (fun s : ℂ => s * fr (x + y) * fr (x + z) * fr (y + z) * fr 0)
    (e.trans (congrArg Units.val p))).trans ?_
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

end GlobalTheory.Ex.Arch
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RatioExt

open GlobalTheory.SecRingIso GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

theorem corresp_refl {X Z : Scheme.{0}} {L : LB X} {φ ψ : Z ⟶ X}
    (hc : ∀ N : ℕ, 4 ≤ N → ∀ x : X, ∃ s : H0 L N, x ∈ nonzeroLocus s)
    (h : ∀ n : ℕ, 1 ≤ n → ∀ (a b : H0 L n) (z : Z) (j j' : Fin 1 → L.ι), φ z ∈ ch L j → ψ z ∈ ch L j' →
      sv φ z a j * sv ψ z b j' = sv φ z b j * sv ψ z a j') :
    Corresp (L := L) (L' := L) (fun _ _ => Equiv.refl _) φ ψ := by
  intro n hn a b z
  refine ⟨?_, fun j j' _ hj hj' => h n hn a b z j j' hj hj'⟩
  have hk : 1 ≤ n * (3 + 1) := by omega
  obtain ⟨d, hd, -⟩ := presMul_refl.exists_pow hn b 3 _ hk rfl
  obtain ⟨c, hcφ⟩ := hc (n * (3 + 1)) (by omega) (φ z)
  obtain ⟨c', hcψ⟩ := hc (n * (3 + 1)) (by omega) (ψ z)
  obtain ⟨j, hj⟩ := exists_ch hcφ
  obtain ⟨j', hj'⟩ := exists_ch hcψ
  show φ z ∈ nonzeroLocus b ↔ ψ z ∈ nonzeroLocus b
  rw [mem_iff b φ z hj, mem_iff b ψ z hj']
  constructor
  · intro hb
    have e := h _ hk d c' z j j' hj hj'
    rw [sv_pow hd φ z hj, sv_pow hd ψ z hj'] at e
    have u := (hb.pow (3 + 1)).mul ((mem_iff c' ψ z hj').1 hcψ)
    rw [e] at u
    exact isUnit_pow_succ_iff.1 (isUnit_of_mul_isUnit_right u)
  · intro hb
    have e := h _ hk c d z j j' hj hj'
    rw [sv_pow hd φ z hj, sv_pow hd ψ z hj'] at e
    have u := ((mem_iff c φ z hj).1 hcφ).mul (hb.pow (3 + 1))
    rw [e] at u
    exact isUnit_pow_succ_iff.1 (isUnit_of_mul_isUnit_left u)

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G]

theorem exists_integral (U : Unif I D A G)
    {w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))} (hw : w.IsGen)
    {n : ℕ} (hn : 1 ≤ n) (a : H0 A.L n) : ∃ (r : R) (σ : H0 U.LG.L n), r ≠ 0 ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ ((Over.pullback (jK R)).obj G).left) (z : Z) (i : U.LG.L.ι) (j : A.L.ι),
        (f ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U i → (f ≫ U.gen.hom.left) z ∈ A.L.U j →
        powVal σ (f ≫ pullback.fst G.hom (jK R)) z i =
          cst ((f ≫ pullback.snd G.hom (jK R)) ≫ jK R) z r *
            ((isoVal w f z i j ^ (n : ℤ)).val * powVal a (f ≫ U.gen.hom.left) z j) := by
  obtain ⟨s, hs⟩ := exists_move A.isLB U.LG.isLB hw (𝟙 _) (n : ℤ) (g₁ := 𝟙 A.A.left) U.gen.hom.left
    ((Category.comp_id _).trans (Category.id_comp _).symm) (g₂ := pullback.fst G.hom (jK R))
    (Category.id_comp _).symm a
  obtain ⟨F, ⟨r, hr, σ, -, h₁, -⟩, -⟩ := (U.expand n hn).1 s
  refine ⟨r, σ, hr, fun Z f z i j hi hj => ?_⟩
  obtain ⟨J, hJ, e⟩ := exists_good U.LG.L U.LG.isLB z (fun _ : Unit => f ≫ pullback.fst G.hom (jK R))
    (fun _ => i) (fun _ _ _ => rfl) (fun _ => hi)
  have e₁ := ExpInt.secScal_sval h₁ f z hJ
  rw [sval_eq_powVal, sval_eq_powVal, Category.comp_id, e (), ExpInt.gs_scal, hs Z f z i j hi hj,
    Category.comp_id, ← Category.assoc] at e₁
  exact e₁

end GlobalTheory.RatioExt

namespace GlobalTheory


open GlobalTheory.SecRingIso GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.RatioExt in
theorem hom_ext_of_integral_ratios : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (P : ∀ k : ℕ, H0 U.LG.L k → Prop), (∀ k : ℕ, 1 ≤ k → ∀ σ₀ : H0 U.LG.L k, ∃ (c : R) (σ : H0 U.LG.L k), c ≠ 0 ∧ (∀ i, σ.f i = resTop _ (scal G.hom c) * σ₀.f i) ∧ P k σ) → ∀ (Z : Scheme.{0}) (f₁ f₂ : Z ⟶ ((Over.pullback (jK R)).obj G).left), f₁ ≫ pullback.snd G.hom (jK R) = f₂ ≫ pullback.snd G.hom (jK R) → (∀ z : Z, ∃ i₁ i₂ : U.LG.L.ι, (f₁ ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U i₁ ∧ (f₂ ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U i₂ ∧ ∀ k : ℕ, 1 ≤ k → ∀ σ τ : H0 U.LG.L k, P k σ → P k τ → gs (f₁ ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i₁)) (σ.f (fun _ => i₁)) * gs (f₂ ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i₂)) (τ.f (fun _ => i₂)) = gs (f₁ ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i₁)) (τ.f (fun _ => i₁)) * gs (f₂ ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i₂)) (σ.f (fun _ => i₂))) → f₁ = f₂ := by
  intro hL R _ _ I D A G _ _ U P hP Z f₁ f₂ hK h
  obtain ⟨w, hw⟩ := U.ext
  have key : ∀ n : ℕ, 1 ≤ n → ∀ a : H0 A.L n, ∃ (r : R) (σ : H0 U.LG.L n), r ≠ 0 ∧ P n σ ∧
      ∀ (f : Z ⟶ ((Over.pullback (jK R)).obj G).left) (z : Z) (i : U.LG.L.ι) (j : Fin 1 → A.L.ι),
        (f ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U i → (f ≫ U.gen.hom.left) z ∈ ch A.L j →
        powVal σ (f ≫ pullback.fst G.hom (jK R)) z i =
          cst ((f ≫ pullback.snd G.hom (jK R)) ≫ jK R) z r *
            ((isoVal w f z i (j 0) ^ (n : ℤ)).val * sv (f ≫ U.gen.hom.left) z a j) := fun n hn a => by
    obtain ⟨r, σ₀, hr, H⟩ := exists_integral U hw hn a
    obtain ⟨c, σ, hc, hσ, hPσ⟩ := hP n hn σ₀
    refine ⟨c * r, σ, mul_ne_zero hc hr, hPσ, fun f z i j hi hj => ?_⟩
    obtain ⟨j, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun t => congrArg j (Subsingleton.elim _ _)⟩
    have e₁ := H Z f z i j hi (mem_wchart.1 hj 0)
    have e₂ : powVal σ (f ≫ pullback.fst G.hom (jK R)) z i = cst ((f ≫ pullback.fst G.hom (jK R)) ≫ G.hom) z c *
        powVal σ₀ (f ≫ pullback.fst G.hom (jK R)) z i :=
      secIsMul_gs (p := G.hom) (a := c) hσ _ z _ (mem_wchart.2 fun _ => hi)
    rw [Category.assoc, pullback.condition, ← Category.assoc] at e₂
    rw [e₂, e₁, H1.cst_mul, _root_.mul_assoc]
    rfl
  have := A.isAb.proper
  have : CompactSpace A.A.left := QuasiCompact.compactSpace_of_compactSpace A.A.hom
  have : QuasiSeparatedSpace A.A.left := quasiSeparatedSpace_of_quasiSeparated A.A.hom
  have hc := fun N hN => (polAV_nonzeroLocus_cover_affine hL.ample A (N := N) hN).1
  have h₁ : Corresp (L := A.L) (L' := A.L) (fun _ _ => Equiv.refl _) (f₁ ≫ U.gen.hom.left) (f₂ ≫ U.gen.hom.left) := by
    refine corresp_refl hc fun n hn a b z j j' hj hj' => ?_
    obtain ⟨i₁, i₂, m₁, m₂, H⟩ := h z
    obtain ⟨r, σ, hr, hσ, Hσ⟩ := key n hn a
    obtain ⟨s, τ, hs, hτ, Hτ⟩ := key n hn b
    have e : powVal σ (f₁ ≫ pullback.fst G.hom (jK R)) z i₁ * powVal τ (f₂ ≫ pullback.fst G.hom (jK R)) z i₂ =
        powVal τ (f₁ ≫ pullback.fst G.hom (jK R)) z i₁ * powVal σ (f₂ ≫ pullback.fst G.hom (jK R)) z i₂ :=
      H n hn σ τ hσ hτ
    rw [Hσ f₁ z i₁ j m₁ hj, Hσ f₂ z i₂ j' m₂ hj', Hτ f₁ z i₁ j m₁ hj, Hτ f₂ z i₂ j' m₂ hj', hK] at e
    refine ((((ExpInt.isUnit_cst (f₂ ≫ pullback.snd G.hom (jK R)) z hr).mul
      (ExpInt.isUnit_cst (f₂ ≫ pullback.snd G.hom (jK R)) z hs)).mul
      (isoVal w f₁ z i₁ (j 0) ^ (n : ℤ)).isUnit).mul (isoVal w f₂ z i₂ (j' 0) ^ (n : ℤ)).isUnit).mul_left_cancel ?_
    linear_combination e
  have h₂ : Corresp (L := A.L) (L' := A.L) (fun _ _ => Equiv.refl _) (f₂ ≫ U.gen.hom.left) (f₂ ≫ U.gen.hom.left) :=
    corresp_refl hc fun n hn a b z j j' hj hj' => by
      refine (congrArg₂ (· * ·) (sec_trans a _ z hj hj') rfl).trans
        (Eq.trans ?_ (congrArg₂ (· * ·) (sec_trans b _ z hj hj') rfl).symm)
      exact (mul_right_comm _ _ _)
  have e := h₁.unique A.isLB h₂ (n := 4) (by norm_num) id
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 (hc 4 le_rfl x))
    (polAV_nonzeroLocus_cover_affine hL.ample A le_rfl).2
  have : IsIso U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.hom))
  exact (cancel_mono _).1 e

end GlobalTheory
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory.Ex.Trait

theorem eq_of_comp_schemeDominant {W X Y Z : Scheme.{0}} {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (d : W ⟶ X) [IsSchemeTheoreticallyDominant d] (hU : d ≫ f = d ≫ g) : f = g := by
  let f' : Over.mk (f ≫ s) ⟶ Over.mk s := Over.homMk f
  let g' : Over.mk (f ≫ s) ⟶ Over.mk s := Over.homMk g h.symm
  haveI : IsSeparated (Over.mk s).hom := ‹IsSeparated s›
  let d' : Over.mk (d ≫ f ≫ s) ⟶ Over.mk (f ≫ s) := Over.homMk d
  have e : d' ≫ f' = d' ≫ g' := Over.OverMorphism.ext hU
  let l := equalizer.lift d' e
  have hd : d = l.left ≫ (equalizer.ι f' g').left := by
    rw [← Over.comp_left, equalizer.lift_ι]; rfl
  have hker : (equalizer.ι f' g').left.ker = ⊥ := by
    apply le_bot_iff.1
    calc _ ≤ (l.left ≫ (equalizer.ι f' g').left).ker := Scheme.Hom.le_ker_comp _ _
      _ = ⊥ := by rw [← hd]; exact d.ker_eq_bot
  haveI : IsIso (equalizer.ι f' g').left := IsClosedImmersion.isIso_iff_ker_eq_bot.2 hker
  have h0 : IsIso ((Over.forget Z).map (equalizer.ι f' g')) := (inferInstance : IsIso (equalizer.ι f' g').left)
  have : IsIso (equalizer.ι f' g') := isIso_of_reflects_iso _ (Over.forget Z)
  exact congrArg CommaMorphism.left ((cancel_epi (equalizer.ι f' g')).1 (equalizer.condition f' g'))

theorem schemeDominant_spec_of_injective {A B : Type} [CommRing A] [CommRing B] [_root_.IsReduced A] (φ : A →+* B)
    (hφ : Function.Injective φ) : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom φ)) := by
  haveI : IsDominant (Spec.map (CommRingCat.ofHom φ)) := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap φ)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot φ).1 hφ]
    exact bot_le
  exact IsSchemeTheoreticallyDominant.of_isDominant _

theorem act_comm_of_torsion : Laws → EndDeterminedOnTorsionSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (S : Scheme.{0}) (s : Sp R ⟶ S) (B : PolAV (Sp R)) (B₀ : PolAV S) (ρ : letI := H.starRing; B.OAct (𝓞 E)) (ρ₀ : letI := H.starRing; B₀.OAct (𝓞 E)) (ψ : B.A.left ⟶ B₀.A.left), IsGrpPullback B.A B₀.A s ψ → LBIso B.L (B₀.L.pull ψ) → ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing R) C] (n : ℕ), 2 ≤ n → ∀ x : 𝓞 E, (letI := H.starRing; (∀ (j : ℕ) (y : TF (R := R) C ⟶ B.A), y ^ n ^ j = 1 → (y ≫ ρ.act x).left ≫ ψ = y.left ≫ ψ ≫ (ρ₀.act x).left) → (ρ.act x).left ≫ ψ = ψ ≫ (ρ₀.act x).left) := by
  intro hL h₂ E _ _ _ H R _ _ _ S s B B₀ ρ ρ₀ ψ hψ hw C _ _ _ _ n hn x h
  letI := H.starRing
  obtain ⟨ρ', hρ'⟩ := polOActPull _ _ s B₀ B ψ hψ hw.symm (𝓞 E) ρ₀
  obtain ⟨P, g, hg, -, hm, ht⟩ := hL.polBaseChange _ _ (TF (R := R) C).hom B
  have gp : IsGrpPullback P.A B.A (TF (R := R) C).hom g := ⟨hg, fun T a b a₀ b₀ ha hb => by
    have e₁ : a₀ = toBase hg.w a := Over.OverMorphism.ext ha
    have e₂ : b₀ = toBase hg.w b := Over.OverMorphism.ext hb
    rw [e₁, e₂, ← hm]; rfl⟩
  obtain ⟨σ, hσ⟩ := polOActPull _ _ _ B P g gp ht (𝓞 E) ρ
  obtain ⟨σ', hσ'⟩ := polOActPull _ _ _ B P g gp ht (𝓞 E) ρ'
  obtain ⟨c, hc⟩ := exists_starNormLE_of_isCMField E (fun a => H.bar_eq a) x
  set j := 4 ^ P.g * P.g.factorial * (2 * c) with hj
  have hlt : j < (n ^ j) ^ 2 := (Nat.lt_pow_self hn).trans_le (Nat.le_self_pow two_ne_zero _)
  have key := h₂ P.g c (n ^ j) hlt C (Nat.cast_ne_zero.2 (by positivity)) P P rfl rfl (Iso.refl _)
    (ThetaPtDet.isPolIso_refl P) _ σ σ' x hc fun y hy => by
      let u : TF (R := R) C ⟶ Over.mk ((baseOver (Sp C)).hom ≫ (TF (R := R) C).hom) :=
        Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))
      let z : TF (R := R) C ⟶ B.A := u ≫ pushHom gp _ y
      have hz : z.left = y.left ≫ g := Category.id_comp _
      have hz' : z ^ n ^ j = 1 := by
        rw [← MonObj.comp_pow, ← map_pow, hy, map_one, MonObj.comp_one]
      have e := h j z hz'
      rw [← hρ', ← Category.assoc, ← Over.comp_left] at e
      have e' : (z ≫ ρ.act x).left = (z ≫ ρ'.act x).left := hψ.1.hom_ext e (by rw [Over.w, Over.w])
      rw [Iso.refl_hom, Category.comp_id, Category.id_comp]
      refine Over.OverMorphism.ext (hg.hom_ext ?_ (by rw [Over.w, Over.w]))
      rw [Over.comp_left _ _ _ z, Over.comp_left _ _ _ z, hz] at e'
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hσ, hσ']
      simpa only [Category.assoc] using e'
  rw [Iso.refl_hom, Category.comp_id, Category.id_comp] at key
  haveI : IsSchemeTheoreticallyDominant (jK R) := schemeDominant_spec_of_injective _ (IsFractionRing.injective R _)
  haveI : IsSchemeTheoreticallyDominant (jFK (R := R) C) := schemeDominant_spec_of_injective _ (RingHom.injective _)
  haveI : IsSchemeTheoreticallyDominant (TF (R := R) C).hom := by
    show IsSchemeTheoreticallyDominant (_ ≫ _); infer_instance
  haveI := B.isAb.proper
  haveI := B.isAb.smooth
  haveI : QuasiCompact (TF (R := R) C).hom := by
    show QuasiCompact (spMap (algebraMap (FractionRing R) C) ≫ spMap (algebraMap R (FractionRing R))); infer_instance
  haveI : IsSchemeTheoreticallyDominant g := IsSchemeTheoreticallyDominant.of_isPullback hg.flip
  rw [← hρ', eq_of_comp_schemeDominant B.A.hom ((Over.w (ρ.act x)).trans (Over.w (ρ'.act x)).symm) g
    (by rw [← hσ, ← hσ', key])]

end GlobalTheory.Ex.Trait
end
