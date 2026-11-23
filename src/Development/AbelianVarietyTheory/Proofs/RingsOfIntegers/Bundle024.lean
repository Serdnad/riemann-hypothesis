module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle007
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxSec
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle017
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGenOfSection
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle007
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle020
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace ExpansionValueZero

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem cst_comp {A C : Type} [CommRing A] [CommRing C] {Z : Scheme.{0}} (q : Z ⟶ Sp C) (φ : A →+* C) (z : Z) (a : A) :
    cst (q ≫ spMap φ) z a = cst q z (φ a) := by
  rw [← H1.cst_stalkMap, H1.gs_spec, H1.cst_stalkMap, Category.comp_id]

theorem cst_sum {A : Type} [CommRing A] {Z : Scheme.{0}} (q : Z ⟶ Sp A) (z : Z) {K : Type} (S : Finset K) (a : K → A) :
    cst q z (∑ i ∈ S, a i) = ∑ i ∈ S, cst q z (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cst, gs_eq q z ⊤ trivial, map_sum]

theorem exists_coeff {A : Type} [CommRing A] {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K]
    [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Sp A ⟶ X)} {ε' : K' → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (e : Sp A ⟶ Y) (t : LB.Gen (LB.LinComb L φ' ε')) (ht : t.IsGen)
    (h : FormEq (fun k => e ≫ φ k) ε φ' ε') :
    ∃ a : A, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp A) (z : Z) (J), Good L z J →
      sval s (r ≫ e) z J = cst r z a * (val t r z J).val := by
  obtain ⟨s', hv⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ f => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [h U f, mul_inv_cancel])
    (pullMulSec s e (LB.invGen L _ _ t) (DVR.invGen_isGen _ _ _ _ ht))
  have le : (⊤ : (Sp A).Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Sp A ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2
    (((Sp A).presheaf.map (homOfLE le).op).hom (s'.f PEmpty.elim))
  refine ⟨a, fun Z r z J hJ => ?_⟩
  have e₁ := hv Z r z J hJ
  rw [sval_pullMulSec _ _ _ _ _ _ hJ, val_inv, sval_of s' r z J PEmpty.elim (fun k => k.elim)] at e₁
  have e₂ : cst r z a = sval s (r ≫ e) z J * ((val t r z J)⁻¹).val :=
    (congrArg (gs r z ⊤) ha).trans ((gs_res r z le trivial _).trans e₁)
  rw [e₂, Units.inv_mul_cancel_right]

section Geometry

variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R)

omit [IsDomain R] in
theorem eSec_fstG (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] :
    eSec (thickObj R I e G) ≫ (fstG I e G).left = thick R I e ≫ eSec G := by
  show eSec (thickObj R I e G) ≫ pullback.fst G.hom (thick R I e) = _
  simp [eSec]

theorem eSec_pG {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (g : GtCoord I D e G) :
    eSec (thickObj R I e G) ≫ g.pG.left = thick R I e ≫ eSec D.P.A := by
  have := g.q_hom
  have h : eSec (thickObj R I e G) ≫ g.q.left = eSec (thickObj R I e D.P.A) :=
    congrArg (·.left) (IsMonHom.one_hom g.q)
  rw [← eSec_fstG I e D.P.A, ← h, Category.assoc]
  rfl

theorem formEq_zero (D : DegPre R) (k : ℕ) (α : D.X) :
    FormEq (fun i => eSec D.P.A ≫ D.famφB α i) (DegPre.famε k) (fun _ : PUnit => eSec D.P.A)
      (fun _ => (k : ℤ) * 1) := by
  intro U _ f
  have a₀ : eSec D.P.A ≫ D.famφB α 0 = eSec D.P.A := Category.comp_id _
  have a₁ : eSec D.P.A ≫ D.famφB α 1 = eSec D.P.A ≫ D.famφB α 2 := by
    have : η[D.P.A] ≫ ((𝟙 D.P.A) * (toUnit _ ≫ D.c α)) = η[D.P.A] ≫ (toUnit _ ≫ D.c α) := by
      rw [MonObj.comp_mul, Category.comp_id]
      have : η[D.P.A] = (1 : 𝟙_ _ ⟶ D.P.A) := by simp [Hom.one_def]
      rw [this, _root_.one_mul]
    exact congrArg (fun z => z.left) this
  have a₃ : eSec D.P.A ≫ D.famφB α 3 = eSec D.P.A := by
    have : η[D.P.A] ≫ (toUnit D.P.A ≫ η[D.P.A]) = η[D.P.A] := by
      rw [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]
    exact congrArg (fun z => z.left) this
  rw [Fin.prod_univ_four, Fintype.prod_unique]
  simp only [a₀, a₁, a₃]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, DegPre.famε, Matrix.cons_val]
  module

theorem exists_value (D : DegPre R) (k : ℕ) (α : D.X) (g : D.SecB k α) :
    ∃ a : R, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J), Good D.P.L z J →
      sval g (r ≫ eSec D.P.A) z J = cst r z a * (val (L := D.P.L) D.rig r z J ^ k).val := by
  obtain ⟨a, ha⟩ := exists_coeff (A := R) D.P.isLB g (eSec D.P.A) (GeneratorPullback.powGen D.P.L _ _ D.rig k)
    (powGen_isGen _ _ _ _ D.rig_gen k) (formEq_zero D k α)
  exact ⟨a, fun Z r z J hJ => (ha Z r z J hJ).trans (by rw [val_pow])⟩

end Geometry

section Congruence

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)


variable (I G) in
omit [IsDomain R] in
abbrev unitE (e : ℕ) : Sp (R ⧸ I ^ (e + 1)) ⟶ (thickObj R I e G).left := eSec (thickObj R I e G)

theorem wv_rig (e : ℕ) (z : Sp (R ⧸ I ^ (e + 1))) {J J'} (hJ : Good D.toPre.P.L z J) (hJ' : Good U.LG.L z J') :
    wv U e (unitE I G e) z (J (unitE I G e ≫ pGl U e)) (J' (thick R I e ≫ eSec G)) *
      val (L := U.LG.L) U.LG.rig (thick R I e) z J' = val (L := D.toPre.P.L) D.toPre.rig (thick R I e) z J := by
  have hp : unitE I G e ≫ pGl U e = thick R I e ≫ eSec D.toPre.P.A := eSec_pG I (U.gt e)
  have hf : unitE I G e ≫ fGl I G e = thick R I e ≫ eSec G := eSec_fstG I e G
  rw [hp]
  have m₁ : z ∈ unitE I G e ⁻¹ᵁ
      ((D.toPre.P.L.pull (U.gt e).pG.left).U (fun _ => J (thick R I e ≫ eSec D.toPre.P.A)) ⊓
        (U.LG.L.pull (fstG I e G).left).U (fun _ => J' (thick R I e ≫ eSec G))) :=
    ⟨mem_pull.2 ((congrArg (fun q => q z ∈ D.toPre.P.L.U (J (thick R I e ≫ eSec D.toPre.P.A))) hp).mpr (hJ _)),
      mem_pull.2 ((congrArg (fun q => q z ∈ U.LG.L.U (J' (thick R I e ≫ eSec G))) hf).mpr (hJ' _))⟩
  have m₂ : z ∈ thick R I e ⁻¹ᵁ (U.LG.L.pull (eSec G)).U (fun _ => J' (thick R I e ≫ eSec G)) :=
    mem_pull.2 (hJ' (thick R I e ≫ eSec G))
  have m₃ : z ∈ thick R I e ⁻¹ᵁ (D.toPre.P.L.pull (eSec D.toPre.P.A)).U
      (fun _ => J (thick R I e ≫ eSec D.toPre.P.A)) := mem_pull.2 (hJ (thick R I e ≫ eSec D.toPre.P.A))
  have W := congrArg (gm (𝟙 _) z _) (U.w_rig e (fun _ => J (thick R I e ≫ eSec D.toPre.P.A),
    fun _ => J' (thick R I e ≫ eSec G)) (_ ⊓ _ ⊓ _) (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
    inf_le_right)
  exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_rp₁ _ z _ _ _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _)
    (gm_rp₁ _ z _ _ _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _))).symm.trans (W.trans (gm_rp₁ _ z _ _ _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _))

theorem value_sub_sum_mem (e k : ℕ) (σ : H0 U.LG.L k) (g : ∀ α : D.toPre.X, D.toPre.SecB k α)
    (hE : U.ExpandsAt e k σ g) (x : R)
    (hx : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J), Good U.LG.L z J →
      sval σ (r ≫ eSec G) z J = cst r z x * (val (L := U.LG.L) U.LG.rig r z J ^ k).val)
    (a : D.toPre.X → R)
    (ha : ∀ α (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J), Good D.toPre.P.L z J →
      sval (g α) (r ≫ eSec D.toPre.P.A) z J = cst r z (a α) * (val (L := D.toPre.P.L) D.toPre.rig r z J ^ k).val) :
    ∃ S : Finset D.toPre.X, ∀ T : Finset D.toPre.X, S ⊆ T → x - ∑ α ∈ T, a α ∈ I ^ (e + 1) := by
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ g hE
  have hp : unitE I G e ≫ pGl U e = thick R I e ≫ eSec D.toPre.P.A := eSec_pG I (U.gt e)
  have hf : unitE I G e ≫ fGl I G e = thick R I e ≫ eSec G := eSec_fstG I e G
  have hc : ∀ (z : Sp (R ⧸ I ^ (e + 1))) (c : R),
      cst (thick R I e) z c = cst (𝟙 _) z (Ideal.Quotient.mk (I ^ (e + 1)) c) := fun z c => H1.gs_spec _ z c
  refine ⟨S, fun T hT => ?_⟩
  rw [← Ideal.Quotient.eq]
  refine H1.cst_ext fun z => ?_
  rw [← hc, ← hc, cst_sum]
  choose J hJ using fun ψ : Sp (R ⧸ I ^ (e + 1)) ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ z)
  choose J' hJ' using fun ψ : Sp (R ⧸ I ^ (e + 1)) ⟶ G.left => exists_chart U.LG.isLB (ψ z)
  have hJ : Good D.toPre.P.L z J := hJ
  have hJ' : Good U.LG.L z J' := hJ'
  obtain ⟨h₀, h₁⟩ := hS _ (unitE I G e) z J hJ
  have h₂ := h₁ (J' (thick R I e ≫ eSec G))
    ((congrArg (fun q => q z ∈ U.LG.L.U (J' (thick R I e ≫ eSec G))) hf).mpr (hJ' _))
  have hs : sv U k σ (unitE I G e ≫ fGl I G e) z (J' (thick R I e ≫ eSec G)) =
      cst (thick R I e) z x * (val (L := U.LG.L) U.LG.rig (thick R I e) z J' ^ k).val := by
    rw [hf]
    exact (sval_of σ _ z J' (fun _ => J' (thick R I e ≫ eSec G)) (fun _ => by rw [Category.comp_id])).symm.trans
      (hx _ _ z J' hJ')
  have ht : ∀ α, val (tG U e α) (unitE I G e) z J = 1 := fun α => by
    have := (val_pull hJ (tG U e α) (unitE I G e) (𝟙 _)).symm.trans
      ((val_corr hJ ((U.gt e).t_unit α) _).trans (val_one _))
    rwa [Category.id_comp] at this
  have hg : ∀ α, sval (g α) (unitE I G e ≫ pGl U e) z J =
      cst (thick R I e) z (a α) * (val (L := D.toPre.P.L) D.toPre.rig (thick R I e) z J ^ k).val := fun α => by
    rw [hp]; exact ha α _ _ z J hJ
  have hw := wv_rig U e z hJ hJ'
  refine (val (L := D.toPre.P.L) D.toPre.rig (thick R I e) z J ^ k).mul_left_inj.1 ?_
  rw [Finset.sum_mul, ← Finset.sum_subset hT (fun α _ hα => (hg α).symm.trans (h₀ α hα))]
  rw [hs, mul_left_comm, ← Units.val_mul, ← mul_pow] at h₂
  refine Eq.trans (by rw [← hw]) (h₂.trans (Finset.sum_congr rfl fun α _ => ?_))
  rw [ht, hg, Units.val_one, _root_.mul_one]

end Congruence

section Value

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]

variable {F} in
theorem le_val_of_mem_pow {ϖ : V} (hϖ : Irreducible ϖ) {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)
    (n : ℕ) {c : V} (hc : c ∈ maximalIdeal V ^ n) :
    (((n : ℕ) : ℚ) : WithTop ℚ) ≤ v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) c)) := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow] at hc
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hc
  have h : HasVal ϖ (algebraMap V (FractionRing V) (ϖ ^ n)) (n : ℤ) := ⟨1, by simp⟩
  rw [map_mul, map_mul, AddValuation.map_mul, hv _ _ h]
  simpa using le_add_of_nonneg_left (GC.v_alg_nonneg hϖ hv b)

end Value

end ExpansionValueZero

end GlobalTheory
end
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ProdTorsion


open Geo.Tor in
theorem val_scale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (c : Γ(Y, ⊤)ˣ) (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) :
    val (scaleGen c t) r z J = gm r z ⊤ c * val t r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) c) rfl)


open Geo.Tor in
theorem exists_phiRel_smul (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}
    {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ} (p : QkPt D F k)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) (hw : w.IsGen)
    (ζ : F) (hζ : ζ ≠ 0) :
    ∃ w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)), w'.IsGen ∧
      ∀ s t : Fam D F k, PhiRel D F k p w s t → PhiRel D F k p w' s (ζ • t) := by
  let u : Γ((TF (R := R) F).left, ⊤)ˣ :=
    ((Ne.isUnit hζ).map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom).unit
  have hw' := scaleGen_isGen u w hw
  refine ⟨scaleGen u w, hw', fun s t h => (phiRel_iff hG p _ hw' s _).2 ?_⟩
  intro a' β hβ T ρ z' J hJ
  have h1 := (phiRel_iff hG p w hw s t).1 h a' β hβ T ρ z' J hJ
  have hu : gs (ρ.left ≫ (fst (TF (R := R) F) D.P.A).left) z' ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) =
      (gm (ρ ≫ fst (TF (R := R) F) D.P.A).left z' ⊤ u).val :=
    gs_unit _ z' ⊤ trivial u
  rw [sval_smul ζ t β ρ.left z' hJ, h1, val_mul hJ, val_mul hJ, val_scale hJ, hu]
  simp only [Units.val_mul]
  ring

theorem pow_eq_one_of_pr {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ} (p : IsPowGrp G' G j)
    {T : Over S} (x : T ⟶ G') (k : ℕ) (h : ∀ i, (x ≫ p.pr i) ^ k = 1) : x ^ k = 1 :=
  Fan.IsLimit.hom_ext p.lim _ _ fun i => by
    haveI := p.hom i
    show (x ^ k) ≫ p.pr i = 1 ≫ p.pr i
    rw [MonObj.pow_comp, MonObj.one_comp, h]

theorem equiv_comb {B M : Type} [CommRing B] [AddCommGroup M] [Module B M] (f : M ≃ₗ[B] M) {I : Type} [Fintype I]
    (a : I → B) (v : I → M) : f (∑ l, a l • v l) = ∑ l, a l • f (v l) := by

  simp only [map_sum, map_smul]

theorem act_comb (hG : GlobalFnsSt) {S : Scheme.{0}} (P : PolAV S) (k : ℤ) (T : Over S) (θ : ThetaGrp P.A P.L k T)
    {I : Type} [Fintype I] (a : I → Γ(T.left, ⊤)) (c : Γ(T.left, ⊤)) (t u : I → LB.Sec (LPow P.A P.L k T))
    (t₀ t₁ : LB.Sec (LPow P.A P.L k T)) (h₀ : ∀ jj, t₀.f jj = ∑ l, liftFun P.A _ (a l) * (t l).f jj)
    (hu : ∀ l t', IsActOf P.A P.L k θ (t l) t' → ∀ jj, t'.f jj = liftFun P.A _ c * (u l).f jj)
    (ha : IsActOf P.A P.L k θ t₀ t₁) (jj) : t₁.f jj = ∑ l, liftFun P.A _ (a l * c) * (u l).f jj := by
  obtain ⟨ρ, hρ, -⟩ := thetaGrp_acts_linearly hG _ P k T
  have h0 : SecM.ofSec P.A t₀ = ∑ l, a l • SecM.ofSec P.A (t l) :=
    Subtype.ext (funext fun jj => (h₀ jj).trans
      (BoxSpan.comb_apply P.A P.L k _ _ (fun l => SecM.ofSec P.A (t l)) jj).symm)
  have h1 := (equiv_comb (ρ θ) _ _).symm.trans ((congrArg (ρ θ) h0).symm.trans ((hρ _ _ _).1 ha))
  refine ((congrFun (congrArg Subtype.val h1) jj).symm.trans (BoxSpan.comb_apply P.A P.L k _ _ _ jj)).trans
    (Finset.sum_congr rfl fun l _ => ?_)
  have e := hu l (SecM.toSec P.A (ρ θ (SecM.ofSec P.A (t l)))) ((hρ _ _ _).2 rfl) jj
  refine (congrArg (liftFun P.A _ (a l) * ·) e).trans ((_root_.mul_assoc _ _ _).symm.trans
    (congrArg (· * (u l).f jj) ?_))
  exact (map_mul (liftHom P.A _) _ _).symm

theorem qkToAk_box : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U' : Unif I D' A' G') (U : Unif I D A G) (P : UnifPowOf3 pD pA pG U' U), Geo.Tor.ExpBijF U.toUnifPre → Geo.Tor.ExpBijF U'.toUnifPre → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (p' : QkPt D'.toPre F k) (p : Fin j → QkPt D.toPre F k), IsBoxQk pD F k p' p → ∀ (x' : TFK (R := R) F ⟶ A'.A) (x : Fin j → (TFK (R := R) F ⟶ A.A)), (∀ i, x' ≫ pA.pr i = x i) → (∀ i, QkToAkU U.toUnifPre F k (p i) (x i)) → QkToAkU U'.toUnifPre F k p' x' := by
  intro hL R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U' U P hB hB' F _ _ k hk p' p hp x' x hx h w' hw'
  have hG := hL.globalFns
  obtain ⟨w, hw⟩ := U.ext
  have hk1 : x' ^ k = 1 := pow_eq_one_of_pr pA.toIsPowGrp x' k fun i => by
    rw [hx i]; exact (h i w hw).1
  refine ⟨hk1, fun θ' hθ' => ?_⟩
  obtain ⟨θ, c, hc, hθ, hact⟩ := BoxTheta.box_theta_act hL R j A A' pA F k hk θ' (hθ' ▸ hk1)
  choose v hv hΦ using fun i => (h i w hw).2 (θ i) ((hθ i).trans (hθ' ▸ hx i))
  obtain ⟨V, hV, hVΦ⟩ := BoxPhi.phiRel_box hG R j D.toPre D'.toPre pD F k p' p hp v hv
  obtain ⟨Φ, hΦl⟩ := phiFun_of_globalFns hG R I D' F k hk p' V hV
  obtain ⟨V', hV', hV'Φ⟩ := exists_phiRel_smul hG p' V hV c hc
  obtain ⟨c₀, -, hexp⟩ := BoxExpansion.main hG R I j D D' A A' G G' pD pA pG U' U P w hw w' hw' F k
  obtain ⟨ρ, hρ, -⟩ := thetaGrp_acts_linearly hG _ A k (TFK (R := R) F)
  refine ⟨V', hV', fun t₀ t₁ s₀ s₁ e₀ e₁ ha => ?_⟩
  obtain ⟨n, a, t, t', hbox, hsum⟩ := boxProduct_span hL R j A A' pA F k hk t₀
  let u : Fin n → Fin j → LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) :=
    fun l i => SecM.toSec A.A (ρ (θ i) (SecM.ofSec A.A (t l i)))
  have hu : ∀ l i, IsActOf A.A A.L (k : ℤ) (θ i) (t l i) (u l i) := fun l i => (hρ _ _ _).2 rfl
  choose u' hu' using fun l => exists_boxSec_pow_ext R j A A' pA F k (u l)
  choose s hs using fun l i => ((hB F k hk w hw).1 (t l i)).exists
  choose r hr using fun l i => ((hB F k hk w hw).1 (u l i)).exists
  choose S hS using fun l => BoxFamily.exists_isBoxFam hG R j D.toPre D'.toPre pD F k (s l)
  choose S₁ hS₁ using fun l => BoxFamily.exists_isBoxFam hG R j D.toPre D'.toPre pD F k (r l)
  have hSS : ∀ l, S₁ l = Φ (S l) := fun l => (hΦl _ _).1
    (hVΦ (s l) (r l) _ _ (fun i => hΦ i _ _ _ _ (hs l i) (hr l i) (hu l i)) (hS l) (hS₁ l))
  have E₀ := ExpansionLinear.expandsF_sum R I D' A' G' U'.toUnifPre F k w' hw' n a t' (fun l => c₀ • S l) t₀
    (fun l => hexp (t l) (s l) (t' l) (S l) (hs l) (hbox l) (hS l)) hsum
  have hsum₁ := act_comb hG A' k (TFK (R := R) F) θ' (fun l => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (a l))
    ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) t' u' t₀ t₁ hsum
    (fun l t'' h'' => hact (t l) (u l) (t' l) (u' l) t'' (hbox l) (hu' l) (hu l) h'') ha
  have E₁ := ExpansionLinear.expandsF_sum R I D' A' G' U'.toUnifPre F k w' hw' n (fun l => a l * c) u'
    (fun l => c₀ • S₁ l) t₁ (fun l => hexp (u l) (r l) (u' l) (S₁ l) (hr l) (hu' l) (hS₁ l))
    (fun jj => (hsum₁ jj).trans (Finset.sum_congr rfl fun l _ => by rw [map_mul]; rfl))
  have q₀ := ((hB' F k hk w' hw').1 t₀).unique e₀ E₀
  have q₁ := ((hB' F k hk w' hw').1 t₁).unique e₁ E₁
  have q : s₁ = c • Φ s₀ := by

    rw [q₁, q₀, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hSS, map_smul, map_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  rw [q]
  exact hV'Φ _ _ ((hΦl _ _).2 rfl)

end GlobalTheory.ProdTorsion
end
end
