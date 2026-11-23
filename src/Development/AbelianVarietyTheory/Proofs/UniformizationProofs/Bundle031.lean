module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoOfIsClosedImmersionOfThickenings
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle013
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle027
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.TorusWeight

theorem gs_map {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (f : Γ(X, U)) :
    gs r z U f = (r.stalkMap z).hom (gs (𝟙 X) (r z) U f) := by
  rw [gs_eq r z U h, gs_eq (𝟙 X) (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r U z h f).symm

theorem val_const {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (a : Γ(Y, ⊤))
    (h : ∀ y J, Good L y J → (val t (𝟙 _) y J).val = gs (𝟙 _) y ⊤ a) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    (val t r z J).val = gs r z ⊤ a := by
  have hJ' : Good L (r z) (fun ψ => J (r ≫ ψ)) := fun ψ => hJ (r ≫ ψ)
  have e := h (r z) _ hJ'
  rw [val_of t (𝟙 _) (r z) _ (fun k => J (r ≫ φ k)) (fun k => by rw [Category.id_comp])] at e
  have hm := hJ.mem φ r
  refine (gs_unit r z _ hm _).symm.trans ((gs_map r z _ hm _).trans (Eq.trans ?_ (gs_map r z ⊤ trivial a).symm))
  exact congrArg _ ((gs_unit (𝟙 Y) (r z) _ hm _).trans e)

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem normd_one {K : Type} [Fintype K] {φ : K → (D.P.A.left ⟶ D.P.A.left)} {ε : K → ℤ}
    {u : LB.Gen (LB.LinComb D.P.L φ ε)} (hu : Normd u) (z : (TF (R := R) F).left) {J} (hJ : Good D.P.L z J) :
    val u (1 : TF (R := R) F ⟶ D.P.A).left z J = 1 :=
  (val_pull hJ u (eSec D.P.A) (toUnit (TF (R := R) F)).left).symm.trans ((val_corr hJ hu.2 _).trans (val_one _))

theorem psi_zero (hB : D.TauBimult) (z : (TF (R := R) F).left) {J} (hJ : Good D.P.L z J) :
    @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi 0) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J = 1 := by
  have C : IsCub (th D z J) := isCub_cubV D.cub hJ
  have z0 : (0 : D.X) + 0 = 0 := add_zero 0
  have hpt : ∀ a b c : D.X, a = b → ∀ (r : (TF (R := R) F).left ⟶ _),
      val (D.tau a c) r z J = val (D.tau b c) r z J := by rintro a b c rfl r; rfl
  have hpp : ∀ a b : D.X, a = b → ∀ (r : (TF (R := R) F).left ⟶ _), val (D.psi a) r z J = val (D.psi b) r z J := by
    rintro a b rfl r; rfl
  have hτ0 := tau_mul (𝟙 (TF (R := R) F)) hJ hB 0 0 0
  rw [hpt _ _ _ z0, cPoint_zero, C.face] at hτ0
  have t00 := (mul_left_cancel hτ0).symm
  have hψ := UUA.psi_add (𝟙 (TF (R := R) F)) hJ (0 : D.X) 0
  rw [hpp _ _ z0, t00, _root_.one_mul, _root_.mul_assoc] at hψ
  have h1 := left_eq_mul.1 hψ
  rw [Over.id_left, Category.id_comp] at h1
  refine Eq.trans (congrArg₂ (· * ·) rfl ?_) h1
  exact (val_pull hJ (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (toUnit (TK R)).left (jFK (R := R) F)).symm

theorem txFrame_of_one (hB : D.TauBimult) {N : ℕ} (p : QkPt D F N) {τ : Multiplicative D.X →* Fˣ} (hy : p.y = 0)
    (hτ : IsTor τ p.g) {w : Frm D F N p.g.b} (hw : FrmOne w) : TXFrame N p w := by
  refine ⟨hw.1, fun ν hν z J hJ => ?_, fun κ hκ z J hJ => ?_⟩
  · have e : val (p.g.s p.y) (𝟙 _) z J = 1 := Units.ext (by
      rw [hτ.2 _ z J hJ, hy, ofAdd_zero, map_one, CoefBasic.cst_eq]; exact map_one _)
    rw [hw.2 z J hJ, e, hτ.1, normd_one hν z hJ, one_pow, _root_.one_mul]
  · rw [hw.2 z J hJ, hτ.1, normd_one hκ z hJ, one_pow, _root_.one_mul, hy, psi_zero hB z hJ]

theorem sval_const {k : ℕ} (α : D.X) (ζ : F) (s s' : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))) :
    (∀ j, s'.f j = DegPre.constBF D F ζ _ * s.f j) ↔
      ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J), Good D.P.L z J →
        sval s' ρ.left z J = sval s ρ.left z J *
          gs (ρ ≫ fst _ _).left z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) := by
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) j, r z ∈ LB.wchart D.P.L (DegPre.famφ D F α) j →
      gs r z (LB.wchart D.P.L (DegPre.famφ D F α) j) (DegPre.constBF D F ζ _ * s.f j) =
        gs r z (LB.wchart D.P.L (DegPre.famφ D F α) j) (s.f j) *
          gs (r ≫ (fst (TF (R := R) F) D.P.A).left) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) :=
    fun Z r z j hm => (gs_mul r z _ hm _ _).trans ((mul_comm _ _).trans (congrArg₂ (· * ·) rfl
      ((gs_res r z le_top hm _).trans (gs_pull r (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _))))
  constructor
  · intro h T ρ z J hJ
    exact (congrArg (gs ρ.left z _) (h _)).trans (key _ ρ.left z _ (hJ.mem _ _))
  · intro h j
    refine fn_ext fun y hy => ?_
    obtain ⟨J, hJ⟩ := CoefBasic.exists_good' D.P.isLB y
    have e := h _ (𝟙 _) y J hJ
    refine Eq.trans ?_ (key _ (𝟙 _) y j hy).symm
    refine (sec_trans s' (𝟙 _) y hy (hJ.mem _ (𝟙 _))).trans ?_
    rw [sec_trans s (𝟙 _) y hy (hJ.mem _ (𝟙 _)), _root_.mul_assoc]
    exact congrArg _ e

theorem phiRel_tor (hG : GlobalFnsSt) {N : ℕ} (p : QkPt D F N) {τ : Multiplicative D.X →* Fˣ} (hy : p.y = 0)
    (hτ : IsTor τ p.g) {w : Frm D F N p.g.b} (hw : FrmOne w) (s s' : Fam D F N) :
    PhiRel D F N p w s s' ↔
      ∀ α j, (s'.s α).f j = DegPre.constBF D F (τ (Multiplicative.ofAdd α)).val _ * (s.s α).f j := by
  have tr : DegPre.trPt D F p.g.b = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.id_comp]; exact tr_fst D F _
    · rw [Category.id_comp]
      refine (tr_pr D F _).trans ?_
      rw [hτ.1, MonObj.comp_one, _root_.mul_one]
  have v : ∀ (α : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J), Good D.P.L z J →
      (uVal D F N α p.g.b ρ z J * val (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w) (ρ ≫ fst _ _).left z J).val =
        gs (ρ ≫ fst _ _).left z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (τ (Multiplicative.ofAdd α)).val) := by
    intro α T ρ z J hJ
    have C : IsCub (th D z J) := isCub_cubV D.cub hJ
    have hu : uVal D F N α p.g.b ρ z J = 1 := by
      rw [uVal, hτ.1]
      simp only [MonObj.comp_one]
      unfold cubN
      simp only [C.face₃, C.face₂, Finset.prod_const_one, inv_one, _root_.mul_one]
    have h₁ := val_const (p.g.s α) _ (hτ.2 α) (ρ ≫ fst _ _).left z hJ
    have h₂ := val_const w 1 (fun y J hJ => by
      rw [hw.2 y J hJ, gs_eq _ _ ⊤ trivial, map_one, map_one]; rfl) (ρ ≫ fst _ _).left z hJ
    rw [gs_eq _ _ ⊤ trivial, map_one, map_one] at h₂
    rw [hu, _root_.one_mul, val_mul hJ, Units.val_mul, h₁, h₂, _root_.mul_one]
  rw [phiRel_iff hG p w hw.1]
  constructor
  · intro H α
    refine (sval_const α _ _ _).2 fun T ρ z J hJ => ?_
    have := H α α (by rw [hy, add_zero]) T ρ z J hJ
    rwa [v α T ρ z J hJ, tr, Category.comp_id] at this
  · intro H α β h T ρ z J hJ
    obtain rfl : α = β := by rw [← h, hy, add_zero]
    rw [v α T ρ z J hJ, tr, Category.comp_id]
    exact (sval_const α _ _ _).1 (H α) T ρ z J hJ

theorem torus_weight : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), Odd N → ∀ (p : QkPt D.toPre F N) τ, p.y = 0 → IsTor τ p.g → ∀ w, TXFrame N p w → FrmOne w ∧ ∀ s s' : Fam D.toPre F N, PhiRel D.toPre F N p w s s' ↔ ∀ α j, (s'.s α).f j = DegPre.constBF D.toPre F (τ (Multiplicative.ofAdd α)).val _ * (s.s α).f j := by
  intro hL R _ _ _ I hI D A G _ _ _ U F _ _ _ N hN p τ hy hτ w hw
  obtain ⟨w₀, hw₀⟩ := (CoefBasic.coef_basic R D.toPre F N p.g).2.1 hτ.1
  have h₁ : FrmOne w := ⟨hw.1, fun z J hJ =>
    ((GlobalTheory.UT.SymFrame.main hL R I hI D F N hN p).2 w w₀ hw (txFrame_of_one D.tau_bimult p hy hτ hw₀) z J hJ).trans (hw₀.2 z J hJ)⟩
  exact ⟨h₁, phiRel_tor hL.1.globalFns p hy hτ h₁⟩

end GlobalTheory.UT.TorusWeight
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.IotaInj

open GlobalTheory.TorusExt

variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem mem_of_nonempty (y : Spec (CommRingCat.of F)) {V : (Spec (CommRingCat.of R)).Opens}
    {p : Spec (CommRingCat.of R)} (hp : p ∈ V) : (jFK (R := R) F ≫ jK R) y ∈ V := by
  have h : IsDominant (jFK (R := R) F ≫ jK R) := GC.isDominant_jFR (V := R) F
  obtain ⟨y', hy'⟩ := (jFK (R := R) F ≫ jK R).denseRange.exists_mem_open V.isOpen ⟨p, hp⟩
  have : Subsingleton (Spec (CommRingCat.of F)) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  rwa [Subsingleton.elim y y']

theorem eq_zero_of_gs (y : Spec (CommRingCat.of F)) {V : (Spec (CommRingCat.of R)).Opens}
    {p : Spec (CommRingCat.of R)} (hp : p ∈ V) (a : Γ(Spec (CommRingCat.of R), V))
    (h : gs (jFK (R := R) F ≫ jK R) y V a = 0) : a = 0 := by
  by_contra ha
  have : Nonempty V := ⟨⟨p, hp⟩⟩
  have hne : (Spec (CommRingCat.of R)).basicOpen a ≠ ⊥ := fun e => ha ((basicOpen_eq_bot_iff a).1 e)
  obtain ⟨p', hp'⟩ : ∃ p', p' ∈ (Spec (CommRingCat.of R)).basicOpen a := by
    by_contra hc
    exact hne (eq_bot_iff.2 fun z hz => (hc ⟨z, hz⟩).elim)
  have hm : y ∈ (jFK (R := R) F ≫ jK R) ⁻¹ᵁ (Spec (CommRingCat.of R)).basicOpen a := mem_of_nonempty y hp'
  rw [Scheme.preimage_basicOpen, Scheme.mem_basicOpen _ _ y (mem_of_nonempty y hp)] at hm
  rw [gs_eq _ y V (mem_of_nonempty y hp)] at h
  exact hm.ne_zero h

theorem not_isUnit_germ {I : Ideal R} {V : (Spec (CommRingCat.of R)).Opens} {p : Spec (CommRingCat.of R)} (hp : p ∈ V)
    (hI : I ≤ p.asIdeal) {r : Γ(Spec (CommRingCat.of R), V)} (hr : r ∈ I.map (DegPre.toOpen V)) :
    ¬ IsUnit (((Spec (CommRingCat.of R)).presheaf.germ V p hp).hom r) := by
  have key : I.map (DegPre.toOpen V) ≤ (maximalIdeal ((Spec (CommRingCat.of R)).presheaf.stalk p)).comap
      ((Spec (CommRingCat.of R)).presheaf.germ V p hp).hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha hu
    have e : ((Spec (CommRingCat.of R)).presheaf.germ V p hp).hom (DegPre.toOpen V a) =
        ((Spec (CommRingCat.of R)).presheaf.germ ⊤ p trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) :=
      TopCat.Presheaf.germ_res_apply _ _ p hp _
    have hu' : IsUnit (((Spec (CommRingCat.of R)).presheaf.germ V p hp).hom (DegPre.toOpen V a)) := hu
    rw [e] at hu'
    have hm := (Scheme.mem_basicOpen (Spec (CommRingCat.of R)) (U := ⊤) _ p trivial).2 hu'
    rw [show (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) = _ from
      basicOpen_eq_of_affine (R := CommRingCat.of R) a] at hm
    exact hm (hI ha)
  exact key hr

theorem exists_val_psi (D : DegPre R) {I : Ideal R} {χ : D.X} (hχ : D.PsiIn χ I) (hc : (D.c χ).left = eSec D.P.A)
    (j : D.P.L.ι) {V : (Spec (CommRingCat.of R)).Opens} (hV : IsAffineOpen V) (hle : V ≤ eSec D.P.A ⁻¹ᵁ D.P.L.U j)
    (y : Spec (CommRingCat.of F)) (hy : (jFK (R := R) F ≫ jK R) y ∈ V)
    (J : (Spec (CommRingCat.of F) ⟶ D.P.A.left) → D.P.L.ι) (hj : J ((jFK (R := R) F ≫ jK R) ≫ eSec D.P.A) = j) :
    ∃ r ∈ I.map (DegPre.toOpen V), (val (D.psi χ) (jFK (R := R) F) y J).val = gs (jFK (R := R) F ≫ jK R) y V r := by
  have hx : D.xK χ = jK R ≫ eSec D.P.A := by
    rw [← hc]; simp [DegPre.xK, ptK]
  have le' : jK R ⁻¹ᵁ V ≤ LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => j) := fun x hxV =>
    Set.mem_iInter.2 fun k => by
      rw [hx]; exact hle hxV
  obtain ⟨r, hr, hψ⟩ := hχ (fun _ => j) V hV (by rw [hc]; exact hle) le'
  refine ⟨r, hr, ?_⟩
  have e := val_of (D.psi χ) (jFK (R := R) F) y J (fun _ => j) (fun _ => by
    rw [← hj]; exact congrArg J ((congrArg (jFK (R := R) F ≫ ·) hx).trans (Category.assoc _ _ _).symm))
  refine (congrArg Units.val e).trans ?_
  refine (gs_unit _ y _ (le' hy) _).symm.trans ((gs_res _ y le' hy _).symm.trans ?_)
  exact (congrArg (gs (jFK (R := R) F) y _) hψ.symm).trans (gs_pull _ (jK R) y V hy _)

theorem val_tau (D : DegPre R) (a b : D.X) {y : Spec (CommRingCat.of F)} {J} (hJ : Good D.P.L y J) :
    val (D.tau a b) (jFK (R := R) F) y J = val (D.psi (a + b)) (jFK (R := R) F) y J *
      (val (D.psi a) (jFK (R := R) F) y J)⁻¹ * (val (D.psi b) (jFK (R := R) F) y J)⁻¹ *
      (val D.rigK (jFK (R := R) F) y J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem c_left_eq (D : DegPre R) {χ : D.X} (h : cP D (TF (R := R) F) χ = 1) : (D.c χ).left = eSec D.P.A :=
  GC.vpt_ext F D.P (Over.w (D.c χ)) (Over.w η[D.P.A]) (congrArg CommaMorphism.left h)

attribute [local instance] gtGroup

theorem eq_zero_of_iota {I : Ideal R} (hI : I ≠ ⊤) (D : DegData R I) (z : D.toPre.X)
    (h : iota D.tau_bimult F z = 0) : z = 0 := by
  by_contra hz
  have hL := D.toPre.P.isLB
  have c₁ : (D.toPre.c z).left = eSec D.toPre.P.A := c_left_eq (F := F) _ (by rw [← iota_b D.tau_bimult, h, zero_b])
  have c₂ : (D.toPre.c (-z)).left = eSec D.toPre.P.A :=
    c_left_eq (F := F) _ (by rw [← iota_b D.tau_bimult, map_neg, h, neg_zero, zero_b])
  obtain ⟨m, hm, hIm⟩ := I.exists_le_maximal hI
  let p : Spec (CommRingCat.of R) := (⟨m, hm.isPrime⟩ : PrimeSpectrum R)
  obtain ⟨j, hj⟩ := exists_chart hL (eSec D.toPre.P.A p)
  obtain ⟨V, hV, hp, hle⟩ : ∃ V : (Spec (CommRingCat.of R)).Opens, IsAffineOpen V ∧ p ∈ V ∧
      V ≤ eSec D.toPre.P.A ⁻¹ᵁ D.toPre.P.L.U j := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hp, hle⟩ := (Spec (CommRingCat.of R)).isBasis_affineOpens.exists_subset_of_mem_open
      (show p ∈ ((eSec D.toPre.P.A ⁻¹ᵁ D.toPre.P.L.U j : (Spec (CommRingCat.of R)).Opens) : Set _) from hj)
      (eSec D.toPre.P.A ⁻¹ᵁ D.toPre.P.L.U j).isOpen
    exact ⟨V, hV, hp, hle⟩
  let y : Spec (CommRingCat.of F) := (⊥ : PrimeSpectrum F)
  have hy := mem_of_nonempty (R := R) y hp
  obtain ⟨J, hJ, hJj⟩ := exists_good D.toPre.P.L hL y (K := PUnit)
    (fun _ => (jFK (R := R) F ≫ jK R) ≫ eSec D.toPre.P.A) (fun _ => j) (fun _ _ _ => rfl) (fun _ => hle hy)
  obtain ⟨r, hr, e₁⟩ := exists_val_psi D.toPre (D.psi_pos z hz) c₁ j hV hle y hy J (hJj PUnit.unit)
  obtain ⟨r', -, e₂⟩ := exists_val_psi D.toPre (D.psi_pos (-z) (neg_ne_zero.2 hz)) c₂ j hV hle y hy J (hJj PUnit.unit)
  have τ : ∀ χ, val (D.toPre.tau z χ) (jFK (R := R) F) y J = 1 := fun χ => by
    have e := iota_val (F := F) D.tau_bimult z χ (y := y) hJ
    rw [h, zero_val χ hJ] at e
    exact e.symm
  have hle' : V ≤ LB.wchart D.toPre.P.L (K := PUnit) (fun _ => eSec D.toPre.P.A) (fun _ => j) := fun x hx =>
    Set.mem_iInter.2 fun _ => hle hx
  obtain ⟨u, e₃⟩ : ∃ u : Γ(Spec (CommRingCat.of R), V),
      (val D.toPre.rigK (jFK (R := R) F) y J).val = gs (jFK (R := R) F ≫ jK R) y V u := by
    refine ⟨((Spec (CommRingCat.of R)).presheaf.map (homOfLE hle').op).hom (D.toPre.rig.s (fun _ => j)).val, ?_⟩
    have a₁ : val D.toPre.rigK (jFK (R := R) F) y J = val (L := D.toPre.P.L) (φ := fun _ : PUnit => eSec D.toPre.P.A)
        (ε := fun _ => 1) D.toPre.rig (jFK (R := R) F ≫ jK R) y J := val_pull hJ _ _ _
    rw [a₁, val_of _ _ y J (fun _ => j) (fun _ => hJj PUnit.unit)]
    exact (gs_unit _ y _ (hle' hy) _).symm.trans (gs_res _ y hle' hy _).symm
  have t₀ := τ 0
  have t₁ := τ (-z)
  rw [val_tau _ _ _ hJ, add_zero] at t₀
  rw [val_tau _ _ _ hJ, add_neg_cancel] at t₁
  have t : val (D.toPre.psi z) (jFK (R := R) F) y J * (val (D.toPre.psi (-z)) (jFK (R := R) F) y J *
      (val D.toPre.rigK (jFK (R := R) F) y J * val D.toPre.rigK (jFK (R := R) F) y J)) = 1 := by
    have a₀ := congrArg Additive.ofMul t₀
    have a₁ := congrArg Additive.ofMul t₁
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one] at a₀ a₁ ⊢
    linear_combination (norm := abel) -a₀ - a₁
  have t' := congrArg Units.val t
  rw [Units.val_mul, Units.val_mul, Units.val_mul, e₁, e₂, e₃, ← gs_mul _ y V hy, ← gs_mul _ y V hy, ← gs_mul _ y V hy,
    Units.val_one] at t'
  have one : r * (r' * (u * u)) - 1 = 0 := eq_zero_of_gs y hp _ (by
    rw [gs_eq _ y V hy] at t' ⊢
    rw [map_sub, map_sub, map_one, map_one, t', sub_self])
  exact not_isUnit_germ hp hIm hr ((IsUnit.of_mul_eq_one _ (sub_eq_zero.1 one)).map _)

theorem main : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (y y' : D.toPre.X) (g : GtPtF D.toPre F), GtPtF.IsIota y g → GtPtF.IsIota y' g → y = y' := by
  intro _ R _ _ _ I hA D F _ _ _ y y' g h h'
  have hI : I ≠ ⊤ := by
    rintro rfl
    have := hA.2.2.2
    exact not_subsingleton R (IsHausdorff.subsingleton (R := R) (M := R) inferInstance)
  rw [isIota_iff_eq D.tau_bimult] at h h'
  exact sub_eq_zero.1 (eq_zero_of_iota (F := F) hI D _ (by rw [map_sub, ← h, ← h', sub_self]))

end GlobalTheory.IotaInj

end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT

theorem expBijF_and_expandsF_lin : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ExpBijF U.toUnifPre ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (w₀ : W0 U.toUnifPre) (t t' t'' : SecA A F k) (s s' : Fam D.toPre F k) (c : F), U.ExpandsF F k w₀ t s → U.ExpandsF F k w₀ t' s' → (∀ j, t''.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * t.f j + t'.f j) → U.ExpandsF F k w₀ t'' (c • s + s') := by
  intro hL R _ _ _ I _ D A G _ _ _ U
  refine ⟨GlobalTheory.expansion_bijective_over_fields hL.1.globalFns R I D A G U, ?_⟩
  intro F _ _ k w₀ t t' t'' s s' c h h' e
  have key := GlobalTheory.FieldBaseChange.expandsF_lin U.toUnifPre F c h h'
  have ext : ∀ a b : SecA A F k, (∀ j, a.f j = b.f j) → a = b := by
    rintro ⟨a, _⟩ ⟨b, _⟩ hab
    obtain rfl : a = b := funext hab
    rfl
  exact (congrArg (fun x : SecA A F k => U.ExpandsF F k w₀ x (c • s + s')) (ext t'' _ fun j => (e j).trans rfl)).mpr key

end GlobalTheory.UT
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem app_comp_eq_zero_of_germ_dvd {R : Type} [CommRing R] {X Y Z : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of R)) (a : Y ⟶ X) (b : Z ⟶ Y) (r : R)
    (hr : ∀ z, cst (b ≫ a ≫ p) z r = 0) (U : X.Opens) (f : Γ(X, U))
    (h : ∀ y, a y ∈ U → cst (a ≫ p) y r ∣ gs a y U f) : ((b ≫ a).app U).hom f = 0 := by
  refine fn_ext fun z hz ↦ ?_
  have hz' : b z ∈ a ⁻¹ᵁ U := hz
  have key : ∀ {W : Scheme.{0}} (c : Y ⟶ W) (V : W.Opens) (g : Γ(W, V)), c (b z) ∈ V →
      gs (b ≫ c) z V g = (b.stalkMap z).hom (gs c (b z) V g) := fun c V g hV ↦ by
    rw [← gs_pull b c z V hV, gs_stalkMap b z _ hV, gs_pull (𝟙 Y) c (b z) V hV, Category.id_comp]
  obtain ⟨t, ht⟩ := h (b z) hz'
  have h0 : (b.stalkMap z).hom (cst (a ≫ p) (b z) r) = 0 :=
    (key (a ≫ p) ⊤ _ trivial).symm.trans (hr z)
  rw [gs_pull (𝟙 Z) (b ≫ a) z U hz, Category.id_comp, key a U f hz', ht, map_mul, h0, zero_mul,
    ThickeningDivisible.gs_zero]


open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Cartier EffCartierData ThickeningDetermines
  ThickeningDivisible in
theorem sec_div_of_germ_dvd (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R)
    (hI : I ≤ Ideal.jacobson ⊥) (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [Smooth H.hom]
    [GeometricallyConnected H.hom] (N : LB H.left) (hN : N.IsLB) (s : LB.Sec N) (r : R) (hr : r ≠ 0)
    (hs : ∀ (n : ℕ) (j : N.ι) (y : (thickObj R I n H).left), (fstG I n H).left y ∈ N.U j →
      cst (Z := (thickObj R I n H).left) ((fstG I n H).left ≫ H.hom) y r ∣
        gs (Y := (thickObj R I n H).left) (fstG I n H).left y (N.U j) (s.f j)) :
    ∃ s' : LB.Sec N, ∀ j, s.f j = resTop _ (scal H.hom r) * s'.f j := by
  let φ : R →+* R ⧸ Ideal.span {r} := Ideal.Quotient.mk _
  let q := Spec.map (CommRingCat.ofHom φ)
  let H₀ : Over (Spec (CommRingCat.of (R ⧸ Ideal.span {r}))) := (Over.pullback q).obj H
  let π : H₀.left ⟶ H.left := pullback.fst H.hom q
  have : IsClosedImmersion q := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : Smooth H₀.hom := inferInstanceAs (Smooth (pullback.snd H.hom q))
  have : GeometricallyConnected H₀.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd H.hom q))
  have := grpObj_geometricallyIntegral_of_smooth _ H₀
  have key := isIso_of_isClosedImmersion_of_thickenings _ (I.map φ)
    (map_le_jacobson φ Ideal.Quotient.mk_surjective hI) H₀ η[H₀] (fun p ↦ inferInstance)
    _ (pullback.snd (secIdeal hN s).subschemeι π) fun n ↦ by
      have : IsClosedImmersion (thick _ (I.map φ) n) :=
        IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
      have : QuasiCompact (fstG (I.map φ) n H₀).left :=
        inferInstanceAs (QuasiCompact (pullback.fst H₀.hom (thick _ (I.map φ) n)))
      have : QuasiCompact π := inferInstanceAs (QuasiCompact (pullback.fst H.hom q))
      have hπ : π ≫ H.hom = H₀.hom ≫ q := pullback.condition
      let b : (thickObj _ (I.map φ) n H₀).left ⟶ (thickObj R I n H).left :=
        pullback.lift ((fstG (I.map φ) n H₀).left ≫ π)
          (pullback.snd H₀.hom (thick _ (I.map φ) n) ≫
            Spec.map (CommRingCat.ofHom (Ideal.quotientMap ((I.map φ) ^ (n + 1)) φ
            (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map))))
          (by
            rw [Category.assoc, hπ, Category.assoc, ← Spec.map_comp, ← Category.assoc]
            erw [pullback.condition]
            rw [Category.assoc, ← Spec.map_comp]
            rfl)
      have hb : b ≫ (fstG I n H).left = (fstG (I.map φ) n H₀).left ≫ π := pullback.lift_fst _ _ _
      have h0 : ∀ j, (((fstG (I.map φ) n H₀).left ≫ π).app _).hom (s.f j) = 0 := fun j ↦ by
        rw [← hb]
        refine app_comp_eq_zero_of_germ_dvd H.hom _ b r (fun z ↦ ?_) _ _ (hs n j)
        rw [← Category.assoc, hb, Category.assoc, hπ, ← Category.assoc]
        exact cst_comp_eq_zero φ
          (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self r)) _ z
      exact ⟨pullback.lift (IsClosedImmersion.lift _ ((fstG (I.map φ) n H₀).left ≫ π) (by
        rw [Scheme.IdealSheafData.ker_subschemeι]
        exact secIdeal_le_ker hN s _ h0)) _ (IsClosedImmersion.lift_fac _ _ _),
        pullback.lift_snd _ _ _⟩
  refine exists_div_sec H.hom hr s fun j x hx ↦ ?_
  obtain ⟨W, hxW, hW⟩ := exists_affine_le (V := N.U j) hx
  have h1 := constFn_dvd_of_mem_ker H.hom r (secIdeal hN s).subschemeι
    (inv (pullback.snd (secIdeal hN s).subschemeι π) ≫ pullback.fst _ _)
    (by rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]) W.2
    (a := resG _ hW (s.f j)) (by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact (ideal_locIdeal _ _ (exists_mem_chart hN) (associated_germ_sec s) W j hW).ge
        (Ideal.mem_span_singleton_self _))
  obtain ⟨c, hc⟩ := h1
  refine ⟨gs (𝟙 _) x W.1 c, ?_⟩
  have h2 := congrArg (gs (𝟙 _) x W.1) hc
  rw [gs_mul _ _ _ hxW, gs_constFn _ _ _ _ hxW, Category.id_comp] at h2
  exact (gs_res _ x hW hxW _).symm.trans h2


open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR in
theorem sec_div_of_expandsAt : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ) (r : R), r ≠ 0 → ∀ (σ₀ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (f₀ f : ∀ α, D.toPre.SecB k α), (∀ α, (∀ j, (f₀ α).f j = resTop _ (scal D.toPre.P.A.hom r) * (f α).f j)) → (∀ e, U.ExpandsAt e k σ₀ f₀) → ∃ σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))), (∀ j, (σ₀).f j = resTop _ (scal G.hom r) * (σ).f j) := by
  intro R _ _ I hR D A G _ _ _ U k r hr σ₀ f₀ f hf hE
  have : IsNoetherianRing R := hR.1
  have hI : I ≤ Ideal.jacobson ⊥ := have := hR.2.2.2; IsAdicComplete.le_jacobson_bot I
  have := U.smooth
  refine sec_div_of_germ_dvd R I hI G _ (linComb_isLB _ U.LG.isLB _ _) σ₀ r hr fun e j y hy ↦ ?_
  obtain ⟨S, H⟩ := (expandsAt_iff_stalks U e k σ₀ f₀).1 (hE e)
  choose J hJ using fun ψ : (thickObj R I e G).left ⟶ D.toPre.P.A.left ↦
    exists_chart D.toPre.P.isLB (ψ y)
  have hJ : Good D.toPre.P.L y J := hJ
  have hc : pGl U e ≫ D.toPre.P.A.hom = fGl I G e ≫ G.hom :=
    (Over.w (U.gt e).pG).trans (Over.w (fstG I e G)).symm
  obtain ⟨jL, rfl⟩ : ∃ jL : U.LG.L.ι, j = fun _ ↦ jL :=
    ⟨j 0, funext fun i ↦ congrArg j (Subsingleton.elim i 0)⟩
  have h := (H y J hJ).2 jL (Set.mem_iInter.1 hy 0)
  refine (Units.dvd_mul_left (u := wv U e (𝟙 _) y (J (pGl U e)) jL ^ k)).1 (h.symm ▸ ?_)
  refine Finset.dvd_sum fun α _ ↦ Dvd.dvd.mul_right ⟨sval (f α) (pGl U e) y J, ?_⟩ _
  rw [← hc]
  have := gs_of_eq_sum_scal (n := 1) D.toPre.P.A.hom (pGl U e) y _ (hJ.mem (D.toPre.famφB α) _)
    (fun _ ↦ r) (a := (f₀ α).f _) (b := fun _ ↦ (f α).f _) (by rw [Fin.sum_univ_one]; exact hf α _)
  rw [Fin.sum_univ_one] at this
  exact this

end GlobalTheory
end
end
