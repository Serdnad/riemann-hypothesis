module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsValuedFieldValuationCentreLePow
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle158
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericIsoAgreesOnCompletePoints
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsGTransport
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnramifiedExtTorsionPointsGoodReduction
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle101
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle049
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle045
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


open GlobalTheory.FormalGeneric GlobalTheory.SectionRingIso GlobalTheory.FormalPoint in
theorem GlobalTheory.GenericIso.cross_identity : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), ∀ (B : Type) [CommRing B] [Algebra R B] (g' : Spec (CommRingCat.of B) ⟶ G'.left) (g : Spec (CommRingCat.of B) ⟶ G.left) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), IsAdicComplete (I.map (algebraMap R B)) B → g' ≫ G'.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) → ⊤ ≤ g' ⁻¹ᵁ U'.LG.L.U jL' → ⊤ ≤ g ⁻¹ᵁ U.LG.L.U jL → (∀ (e : ℕ) (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ (thickObj R I e G').left), r ≫ (fstG I e G').left = ρ ≫ g' → r ≫ (j e).hom.left ≫ (fstG I e G).left = ρ ≫ g) → ∀ (k : ℕ) (σ τ : H0 U.LG.L k) (σ' τ' : H0 U'.LG.L k), GlobalTheory.GenericIso.AgreeAll U.toUnifPre U'.toUnifPre hD j k σ σ' → GlobalTheory.GenericIso.AgreeAll U.toUnifPre U'.toUnifPre hD j k τ τ' → ∀ (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (z : Z), gs (ρ ≫ g) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL)) * gs (ρ ≫ g') z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (τ'.f (fun _ => jL')) = gs (ρ ≫ g) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (τ.f (fun _ => jL)) * gs (ρ ≫ g') z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL')) := by
  intro R _ _ I _ D D' A A' G G' _ _ _ _ _ _ U U' hD j B _ _ g' g jL jL' hB hg' c' c hgg k σ τ σ' τ' hσ hτ Z ρ z
  let y : Over.mk (spMap (algebraMap R B)) ⟶ G' := Over.homMk g' hg'
  have hy : ∀ e, reduction I y e ≫ (fstG I e G').left = adicLevelι (I.map (algebraMap R B)) (e + 1) ≫ g' :=
    fun e => reduction_fstG I y e
  have ex : ∀ s : H0 U.LG.L k, ∃ a : Γ(Spec (CommRingCat.of B), ⊤),
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (z : Z),
      gs ρ z ⊤ a = vl s (ρ ≫ g) z (fun _ => jL) := fun s =>
    ⟨_, fun Z ρ z => gs_appLE g (ch U.LG.L fun _ => jL) ⊤ (fun _ _ => mem_ch.2 (c trivial)) ρ z trivial _⟩
  have ex' : ∀ s : H0 U'.LG.L k, ∃ a : Γ(Spec (CommRingCat.of B), ⊤),
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (z : Z),
      gs ρ z ⊤ a = vl s (ρ ≫ g') z (fun _ => jL') := fun s =>
    ⟨_, fun Z ρ z => gs_appLE g' (ch U'.LG.L fun _ => jL') ⊤ (fun _ _ => mem_ch.2 (c' trivial)) ρ z trivial _⟩
  choose b hb using ex
  choose b' hb' using ex'
  have pr : ∀ (s : H0 U.LG.L k) (s' : H0 U'.LG.L k) (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (z : Z),
      gs ρ z ⊤ (b s * b' s') = vl s (ρ ≫ g) z (fun _ => jL) * vl s' (ρ ≫ g') z (fun _ => jL') :=
    fun s s' Z ρ z => (gs_mul ρ z ⊤ trivial _ _).trans (congrArg₂ (· * ·) (hb s Z ρ z) (hb' s' Z ρ z))
  have key : ∀ {T : Type} [CommRing T] (u : Tˣ) (v x y x' y' : T), u.val * x = v * x' → u.val * y = v * y' →
      x * y' = y * x' := fun u v x y x' y' h₁ h₂ => by
    refine (Units.mul_right_inj u).1 ?_
    linear_combination y' * h₁ - x' * h₂
  have E : b σ * b' τ' = b τ * b' σ' := fn_ext_germs (I.map (algebraMap R B)) fun e z => by
    obtain ⟨jM, a₁⟩ := exists_chart D.toPre.P.isLB
      (GlobalTheory.FamFieldPull.prA hD ((U'.gt e).pG.left (reduction I y e z)))
    obtain ⟨jM', a₂⟩ := exists_chart D'.toPre.P.isLB ((U'.gt e).pG.left (reduction I y e z))
    have a₄ : (fstG I e G').left (reduction I y e z) ∈ U'.LG.L.U jL' :=
      (congrArg (fun q => q z ∈ U'.LG.L.U jL') (hy e)).mpr (c' trivial)
    have a₃ : (fstG I e G).left ((j e).hom.left (reduction I y e z)) ∈ U.LG.L.U jL :=
      (congrArg (fun q => q z ∈ U.LG.L.U jL) (hgg e _ _ _ (hy e))).mpr (c trivial)
    have H₁ := hσ e _ (reduction I y e) z jM jM' jL jL' a₁ a₂ a₃ a₄
    have H₂ := hτ e _ (reduction I y e) z jM jM' jL jL' a₁ a₂ a₃ a₄
    rw [pr, pr, ← hgg e _ _ _ (hy e), ← hy]
    exact key _ _ _ _ _ _ H₁ H₂
  exact (pr σ τ' Z ρ z).symm.trans ((congrArg (gs ρ z ⊤) E).trans (pr τ σ' Z ρ z))
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericIso

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.RigidSections GlobalTheory.FamFieldPull GlobalTheory.ExpGTrans

section Generic

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem cst_mul_eq {R : Type} [CommRing R] (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (a b : R) :
    cst q z (a * b) = cst q z a * cst q z b := by
  rw [cst, map_mul]
  exact gs_mul q z ⊤ trivial _ _

theorem cst_comp_eq {R F : Type} [CommRing R] [CommRing F] (q : Z ⟶ Spec (CommRingCat.of F)) (φ : R →+* F) (z : Z)
    (a : R) : cst (q ≫ Spec.map (CommRingCat.ofHom φ)) z a = cst q z (φ a) := by
  refine (gs_pull q _ z ⊤ trivial _).symm.trans (congrArg (gs q z ⊤) ?_)
  exact (congrArg (fun t => t.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))).symm

theorem sval_scale_const {R : Type} [CommRing R] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (p : Y ⟶ Spec (CommRingCat.of R))
    (c : R) (t : LB.Sec (LB.LinComb L φ ε)) (q : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval (SecOps.secScale (scal p c) t) q z J = cst (q ≫ p) z c * sval t q z J :=
  (gs_mul q z _ (hJ.mem _ q) _ _).trans (congrArg (· * _)
    ((gs_res q z le_top (hJ.mem _ q) _).trans (ExpInt.gs_scal p q z c)))

theorem secLin_rescale (hL : L.IsLB) {R F : Type} [CommRing R] [Field F] (ρ : R →+* F)
    {φ₁ : K' → (Y' ⟶ X)} {ε₁ : K' → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {n : ℕ} {s : Fin n → LB.Sec (LB.LinComb L φ ε)} {h : Y' ⟶ Y} (p : Y ⟶ Spec (CommRingCat.of R))
    {π : Y' ⟶ Spec (CommRingCat.of F)} (hp : h ≫ p = π ≫ Spec.map (CommRingCat.ofHom ρ)) {c : Fin n → F}
    (a : Fin n → R) (ha : ∀ i, ρ (a i) ≠ 0) (H : GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ ε s h (fun i => scal π (c i))) :
    GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ ε (fun i => SecOps.secScale (scal p (a i)) (s i)) h
      (fun i => scal π (c i / ρ (a i))) := by
  refine (FieldBaseChange.secLin_iff_val hL _ _ _ _).2 fun y J hJ => ?_
  rw [(FieldBaseChange.secLin_iff_val hL _ _ _ _).1 H y J hJ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sval_scale_const _ _ _ _ _ hJ, ExpInt.gs_scal, ExpInt.gs_scal, Category.assoc, hp, ← Category.assoc, cst_comp_eq,
    ← _root_.mul_assoc, ← cst_mul_eq, div_mul_cancel₀ _ (ha i)]

end Generic

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G G' : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

theorem expansion_eq (hR : AdmBase R I) (U : UnifPre I D A G) {k : ℕ} {σ : H0 U.LG.L k}
    {f g : ∀ α, D.toPre.SecB k α} (hf : ∀ e, U.ExpandsAt e k σ f) (hg : ∀ e, U.ExpandsAt e k σ g) : f = g := by
  have s : ∀ {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (W : Y.Opens) (a b : Γ(Y, W)),
      resTop W (scal p 1) * a + resTop W (scal p (-1)) * b = a - b := fun p W a b => by
    simp only [scal, map_neg, map_one, resTop]
    ring
  have h := (comb_eq_zero_iff_expansion_comb_eq_zero R I hR D A G U k 2 ![1, -1] (fun _ => σ) ![f, g]
    (fun i => by fin_cases i; exacts [hf, hg])).1 fun j => by
      rw [Fin.sum_univ_two]; exact (s _ _ _ _).trans (sub_self _)
  funext α
  refine SecOps.sec_ext fun j => sub_eq_zero.1 ((s D.toPre.P.A.hom _ _ _).symm.trans ?_)
  have := h α j
  rwa [Fin.sum_univ_two] at this

theorem LevelIso.exists_expansion (hG : GlobalFnsSt) (hR : AdmBase R I) {U : Unif I D A G} {U' : Unif I D' A' G'}
    {hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre} {j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G}
    (hj : LevelIso U.toUnifPre U'.toUnifPre hD j) {k : ℕ} (hk : 1 ≤ k) (τ : H0 U.LG.L k)
    (f : ∀ α, D.toPre.SecB k α) (hE : ∀ e, U.ExpandsAt e k τ f) :
    ∃ (a : R) (τ' : H0 U'.LG.L k) (f' : ∀ α, D'.toPre.SecB k α), a ≠ 0 ∧ (∀ e, U'.ExpandsAt e k τ' f') ∧
      AgreeAll U.toUnifPre U'.toUnifPre hD j k (SecOps.secScale (scal G.hom a) τ) τ' ∧
      ∀ x, IsSecPull hD.w (D'.toPre.famφB x) (D.toPre.famφB (hD.xe x)) (DegPre.famε k) (prA hD) (f' x)
        (SecOps.secScale (scal D.toPre.P.A.hom a) (f (hD.xe x))) := by
  obtain ⟨s, hs⟩ := exists_restrict U.toUnifPre k τ
  obtain ⟨F, ⟨r, hr, σ, f₀, h₁, h₂, h₃⟩, -⟩ := (U.expand k hk).1 s
  obtain ⟨F', hF⟩ := exists_pull hD _ hG k F
  obtain ⟨s', ⟨r', hr', σ', f', h₁', h₂', h₃'⟩, -⟩ := (U'.expand k hk).2 F'
  have e₁ : SecOps.secScale (scal G.hom r') σ = SecOps.secScale (scal G.hom (r' * r)) τ :=
    SecOps.sec_ext (scale_of_restrict _ hs h₁ r')
  have e₂ := expansion_eq hR U.toUnifPre (fun e => e₁ ▸ expandsAt_scale _ (h₃ e) r')
    (fun e => expandsAt_scale _ (hE e) (r' * r))
  have hp := fun x => congrFun e₂ (hD.xe x) ▸ integral_rel hD _ hF h₂ h₂' x
  exact ⟨r' * r, _, _, mul_ne_zero hr' hr, fun e => expandsAt_scale _ (h₃' e) r,
    hj.agreeAll (fun e => expandsAt_scale _ (hE e) _) (fun e => expandsAt_scale _ (h₃' e) _) hp, hp⟩

end GlobalTheory.GenericIso

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.RigidSections GlobalTheory.FamFieldPull GlobalTheory.ExpGTrans GlobalTheory.GenericIso in
theorem expandsG_of_genericRel : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), GlobalTheory.GenericIso.LevelIso U.toUnifPre U'.toUnifPre hD j → ∀ (Φ : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G) (w : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (Φ.hom.left ≫ pullback.fst G.hom (jK R)))), GlobalTheory.GenericIso.GenericRel U.toUnifPre U'.toUnifPre hD j Φ w → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (σ : U.SecGF F k) (σ' : U'.SecGF F k) (s : Fam D.toPre F k) (s' : Fam D'.toPre F k), (∀ (Z : Scheme.{0}) (r : Z ⟶ (UnifPre.GF (G := G') F).left) (z : Z) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (r ≫ (TFK (R := R) F ◁ Φ.hom).left ≫ UnifPre.gFK (G := G) F) z ∈ U.LG.L.U jL → (r ≫ UnifPre.gFK (G := G') F) z ∈ U'.LG.L.U jL' → gs (r ≫ (TFK (R := R) F ◁ Φ.hom).left) z (LB.wchart U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) (fun _ => jL)) (σ.f (fun _ => jL)) = (Geo.Tor.gw w (r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G')).left) z jL (fun _ => jL') ^ k).val * gs r z (LB.wchart U'.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G') F) (fun _ => jL')) (σ'.f (fun _ => jL'))) → GlobalTheory.RigidSections.FamRel hD F s'.s s.s → U.ExpandsG F k σ s → U'.ExpandsG F k σ' s' := by
  intro hGl R _ _ I hR D D' A A' G G' _ _ _ _ _ _ U U' hD j hj Φ w hw F _ _ k hk σ σ' s s' hσ hs
    ⟨n, c, τ, f, hE, hG, hB⟩
  choose a τ' f' ha hE' hA hf using fun i => hj.exists_expansion hGl hR hk (τ i) (f i) (hE i)
  let ρ : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))
  have hρ : ∀ i, ρ (a i) ≠ 0 := fun i =>
    (map_ne_zero_iff ρ ((algebraMap (FractionRing R) F).injective.comp
      (IsFractionRing.injective R (FractionRing R)))).2 (ha i)
  have hT : jFK (R := R) F ≫ jK R = Spec.map (CommRingCat.ofHom ρ) := (spMap_comp _ _).symm
  have pG : UnifPre.gFK (G := G) F ≫ G.hom =
      (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ Spec.map (CommRingCat.ofHom ρ) := by
    have e₁ := Over.w (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G))
    have e₂ := Over.w (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G))
    rw [← hT, Category.assoc, pullback.condition]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jK R) (e₁.trans e₂.symm)).trans (Category.assoc _ _ _))
  have pB : (DegPre.prB D.toPre F).left ≫ D.toPre.P.A.hom =
      (fst (TF (R := R) F) D.toPre.P.A).left ≫ Spec.map (CommRingCat.ofHom ρ) := by
    rw [Over.w, ← hT]
    exact (Over.w (fst (TF (R := R) F) D.toPre.P.A)).symm
  refine ⟨n, fun i => c i / ρ (a i), τ', f', hE', ?_, fun x => ?_⟩
  · refine (FieldBaseChange.secLin_iff_val U'.LG.isLB _ _ _ _).2 fun y J' hJ' => ?_
    obtain ⟨J, hJ⟩ := BoxFamily.exists_good_at (Z := (UnifPre.GF (G := G') F).left) U.LG.isLB y
    have a₁ : (𝟙 _ ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G')).left) ≫ Φ.hom.left ≫
        pullback.fst G.hom (jK R) = (𝟙 _ ≫ (TFK (R := R) F ◁ Φ.hom).left) ≫ UnifPre.gFK (G := G) F := by
      have e := congrArg (fun q => q.left) (whiskerLeft_snd (TFK (R := R) F) Φ.hom)
      simp only [Over.comp_left] at e
      rw [Category.id_comp, Category.id_comp, ← Category.assoc, ← e, Category.assoc]
    have a₂ : (𝟙 _ ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G')).left) ≫ pullback.fst G'.hom (jK R) =
        𝟙 _ ≫ UnifPre.gFK (G := G') F := Category.assoc _ _ _
    have a₃ : (𝟙 _ ≫ (TFK (R := R) F ◁ Φ.hom).left) ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
        𝟙 _ ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G')).left :=
      (Category.assoc _ _ _).trans
        (congrArg (𝟙 _ ≫ ·) (congrArg (fun q => q.left) (whiskerLeft_fst (TFK (R := R) F) Φ.hom)))
    have e₁ := hσ _ (𝟙 _) y _ _ (hJ ((𝟙 _ ≫ (TFK (R := R) F ◁ Φ.hom).left) ≫ UnifPre.gFK (G := G) F))
      (hJ' (𝟙 _ ≫ UnifPre.gFK (G := G') F))
    have e₃ := secLin_val (secLin_rescale U.LG.isLB ρ G.hom pG a hρ hG) (𝟙 _ ≫ (TFK (R := R) F ◁ Φ.hom).left) y hJ
    refine (Units.mul_right_inj _).1 (e₁.symm.trans (e₃.trans ?_))
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e₂ := hw.2 k hk _ _ (hA i) _ (𝟙 _ ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G')).left) y
      (J ((𝟙 _ ≫ (TFK (R := R) F ◁ Φ.hom).left) ≫ UnifPre.gFK (G := G) F)) (J' (𝟙 _ ≫ UnifPre.gFK (G := G') F))
      (by rw [a₁]; exact hJ _) (by rw [a₂]; exact hJ' _)
    rw [a₁, a₂] at e₂
    rw [ExpInt.gs_scal, ExpInt.gs_scal, a₃, mul_left_comm]
    refine congrArg (_ * ·) ?_
    refine (sval_of _ _ y J _ fun _ => ?_).trans (e₂.trans (congrArg (_ * ·) (sval_of _ _ y J' _ fun _ => ?_).symm))
    · rw [Category.comp_id]
    · rw [Category.comp_id]
  · refine secLin_transport D.toPre.P.isLB D'.toPre.P.isLB hD.w _ _ _ _ _ _ _ (prF hD F) _
      (famφ_eq D.toPre F (hD.xe x)) (famφ_eq D'.toPre F x) (famφB_pull hD x) (prF_snd hD F) _ _ (fun i y => ?_)
      _ _ _ _ (hs x) (fun i => hf i x) (secLin_rescale D.toPre.P.isLB ρ D.toPre.P.A.hom pB a hρ (hB (hD.xe x)))
    rw [ExpInt.gs_scal, ExpInt.gs_scal, Category.assoc, prF_fst]

end GlobalTheory
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_group_law_smooth_proper_model_of_generic : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (X : Scheme.{0}) (f : X ⟶ Sp R) (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ X), IsPullback φ A.hom f (spMap (algebraMap R K)) → Smooth f → IsProper f → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (ψ : R' →+* K), Function.Injective ψ → ψ.comp g = algebraMap R K → ∀ (G' : Over (Sp R')) (π : G'.left ⟶ X) (φ' : A.left ⟶ G'.left), IsPullback π G'.hom f (spMap g) → φ' ≫ π = φ → φ' ≫ G'.hom = A.hom ≫ spMap ψ → ∃ _ : GrpObj G', IsCommMonObj G' ∧ IsGrpPullback A G' (spMap ψ) φ' := by
  first | exact @GlobalTheory.GenSpread.exists_grpObj | exact GlobalTheory.GenSpread.exists_grpObj | (intros; apply GlobalTheory.GenSpread.exists_grpObj <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_valuedField_valuationCentre_le_pow : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] [Field K] [Algebra R K] [FaithfulSMul R K] [Algebra.IsAlgebraic R K] (u : R), u ∈ IsLocalRing.maximalIdeal R → u ≠ 0 → ∀ R₁ : Subalgebra R K, Module.Finite R R₁ → ∀ S : ValuationSubring K, (∀ r, algebraMap R K r ∈ S) → ∀ e : ℕ, ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (gam : K →+* C), (∀ r, ‖gam (algebraMap R K r)‖ ≤ 1) ∧ ‖gam (algebraMap R K u)‖ < 1 ∧ ∀ f ∈ R₁, S.valuation f < 1 → ‖gam f‖ < 1 ∧ (S.valuation (algebraMap R K u) = 1 → ‖gam f‖ ≤ ‖gam (algebraMap R K u)‖ ^ e) := by
  first | exact @GlobalTheory.exists_valuedField_centre_le_pow | exact GlobalTheory.exists_valuedField_centre_le_pow | (intros; apply GlobalTheory.exists_valuedField_centre_le_pow <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_unramified_ext_torsion_points_good_reduction : Laws → Laws2 → ∀ (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → abLocus G = Set.univ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra T F], Function.Injective (algebraMap T F) → ∀ k : ℕ, IsUnit (k : T) → ∃ (T' : Subalgebra T F) (_ : IsDiscreteValuationRing T'), (∀ π : T, Irreducible π → Irreducible (algebraMap T T' π)) ∧ ∀ x : Over.mk (spMap (algebraMap T F)) ⟶ G, x ^ k = 1 → ∃ x' : Sp T' ⟶ G.left, spMap (T'.val.toRingHom) ≫ x' = x.left := by
  first | exact @GlobalTheory.exists_unramified_torsion_points | exact GlobalTheory.exists_unramified_torsion_points | (intros; apply GlobalTheory.exists_unramified_torsion_points <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KTrivLocal

open GlobalTheory.AbLaw GlobalTheory.UU

theorem ring_retraction {A C : Type} [CommRing A] [IsLocalRing A] [CommRing C] (φ : A →+* C) (hφ : φ.Finite)
    (ε : C →+* A) (he : ∀ a, ε (φ a) = a)
    (h : ∀ c, c - φ (ε c) ∈ (IsLocalRing.maximalIdeal A).map φ) (c : C) : φ (ε c) = c := by
  algebraize [φ]
  have hle : (⊤ : Submodule A C) ≤ LinearMap.range (Algebra.linearMap A C) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
      (IsLocalRing.maximalIdeal_le_jacobson _) fun x _ => ?_
    refine Submodule.mem_sup.2 ⟨φ (ε x), ⟨ε x, rfl⟩, x - φ (ε x), ?_, by ring⟩
    rw [Ideal.smul_top_eq_map]
    exact h x
  obtain ⟨a, rfl⟩ := hle (Submodule.mem_top (x := c))
  exact congrArg φ (he a)

theorem comp_section_eq_id_spec {A : Type} [CommRing A] [IsLocalRing A] {C : CommRingCat.{0}}
    (f : Spec C ⟶ Spec (CommRingCat.of A)) [hf : IsFinite f] (e : Spec (CommRingCat.of A) ⟶ Spec C)
    (he : e ≫ f = 𝟙 _)
    (h : ∀ (T : Scheme.{0}) (t : T ⟶ Sp (IsLocalRing.ResidueField A)) (y : T ⟶ Spec C),
      y ≫ f = t ≫ spMap (IsLocalRing.residue A) → y ≫ f ≫ e = y) : f ≫ e = 𝟙 _ := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  obtain ⟨ε, rfl⟩ := Spec.map_surjective e
  have hφ : φ.hom.Finite := (IsFinite.SpecMap_iff φ).1 hf
  have he' : φ ≫ ε = 𝟙 _ := Spec.map_injective (by rw [Spec.map_comp, he, Spec.map_id])
  let I : Ideal C := (IsLocalRing.maximalIdeal A).map φ.hom
  let τ : IsLocalRing.ResidueField A →+* C ⧸ I :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk I).comp φ.hom) fun a ha =>
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha)
  have k := h _ (spMap τ) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) (by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl)
  rw [← Spec.map_comp, ← Spec.map_comp] at k
  have k' := Spec.map_injective k
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext c
  refine ring_retraction φ.hom hφ ε.hom (fun a => congrArg (fun q => q.hom a) he') (fun x => ?_) c
  exact Ideal.Quotient.eq.1 (congrArg (fun q => q.hom x) k').symm

theorem comp_section_eq_id {A : Type} [CommRing A] [IsLocalRing A] {H : Scheme.{0}}
    (f : H ⟶ Spec (CommRingCat.of A)) [IsFinite f] (e : Spec (CommRingCat.of A) ⟶ H) (he : e ≫ f = 𝟙 _)
    (h : ∀ (T : Scheme.{0}) (t : T ⟶ Sp (IsLocalRing.ResidueField A)) (y : T ⟶ H),
      y ≫ f = t ≫ spMap (IsLocalRing.residue A) → y ≫ f ≫ e = y) : f ≫ e = 𝟙 _ := by
  have : IsAffine H := isAffine_of_isAffineHom f
  have k := comp_section_eq_id_spec (H.isoSpec.inv ≫ f) (e ≫ H.isoSpec.hom) (by simpa using he)
    fun T t y hy => by
      have := h T t (y ≫ H.isoSpec.inv) (by simpa using hy)
      simp only [Category.assoc] at this ⊢
      rw [reassoc_of% this]
      simp
  rw [← cancel_epi H.isoSpec.inv, ← cancel_mono H.isoSpec.hom]
  simpa using k

theorem kTriv_of_closed_fibre : Laws → Laws2 → ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ N : LB B.left, N.IsLB → RelAmple B N → KTriv ((Over.pullback (spMap (IsLocalRing.residue A))).obj B) (N.pull (pullback.fst B.hom (spMap (IsLocalRing.residue A)))) → KTriv B N := by
  intro hLaws _ A _ _ _ B _ _ hB L hLB hL hk
  have hG := hLaws.globalFns
  obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy A B L hLB).1 hL
  have hP : IsProjBy B.hom := ⟨_, isLB_pw hLB _, n, s, hs⟩
  obtain ⟨hO, -, hK⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ B L hLB
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.UU.TwistKer.exists_closed_twist_kernel hG A B hB hP L (pw L 0) hLB hO
  have hfin : IsFinite H.hom :=
    GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hG A B hB L (pw L 0) hLB hO hL H j hj hH
  have hrep : ∀ (T : Over (Spec (CommRingCat.of A))) (x : T ⟶ B), InK B L x ↔ ∃ y : T ⟶ H, y ≫ j = x :=
    fun T x => (hK _ rfl T x).trans (hH T x)
  have hm : Mono j := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))
  obtain ⟨e, he⟩ := (hrep _ _).1 (inK_one hLB (𝟙_ _))
  have h := isGrpPullback_pullback B (spMap (IsLocalRing.residue A))
  have hL' : (L.pull (pullback.fst B.hom (spMap (IsLocalRing.residue A)))).IsLB := DVR.linComb_isLB _ hLB _ _
  have key : H.hom ≫ e.left = 𝟙 _ := by
    refine comp_section_eq_id H.hom e.left (Over.w e) fun T t y hy => ?_
    have hdi : (y ≫ j.left) ≫ B.hom = t ≫ spMap (IsLocalRing.residue A) := by
      rw [Category.assoc, Over.w j, hy]
    let x : Over.mk t ⟶ (Over.pullback (spMap (IsLocalRing.residue A))).obj B :=
      Over.homMk (h.1.lift _ _ hdi) (h.1.lift_snd _ _ _)
    let z : Over.mk (t ≫ spMap (IsLocalRing.residue A)) ⟶ H := Over.homMk y hy
    have hz : z ≫ j = pushPt h.1.w x := Over.OverMorphism.ext (h.1.lift_fst _ _ hdi).symm
    have hx : x = 1 := InK.eq_one hk (inK_of_push h hLB hL' (lbIso_self hL') x ((hrep _ _).2 ⟨z, hz⟩))
    have hx' : pushPt h.1.w x = 1 := (congrArg (pushHom h (Over.mk t)) hx).trans (map_one _)
    have h1 : z ≫ toUnit H ≫ e = z := by
      rw [← cancel_mono j, hz, hx', Category.assoc, Category.assoc, he, MonObj.comp_one, MonObj.comp_one]
    have h2 : (toUnit H).left = H.hom := (Category.comp_id _).symm.trans (Over.w (toUnit H))
    exact (congrArg (fun q => y ≫ q ≫ e.left) h2).symm.trans (congrArg (fun q => q.left) h1)
  have hj1 : j = 1 := by
    have h2 : (toUnit H).left = H.hom := (Category.comp_id _).symm.trans (Over.w (toUnit H))
    have h1 : toUnit H ≫ e = 𝟙 H :=
      Over.OverMorphism.ext ((congrArg (fun q => q ≫ e.left) h2).trans key)
    rw [← Category.id_comp j, ← h1, Category.assoc, he, MonObj.comp_one]
  refine kTriv_iff_forall.2 fun T x hxK => ?_
  obtain ⟨y, rfl⟩ := (hrep T x).1 hxK
  rw [hj1, MonObj.comp_one]

end GlobalTheory.KTrivLocal
end
