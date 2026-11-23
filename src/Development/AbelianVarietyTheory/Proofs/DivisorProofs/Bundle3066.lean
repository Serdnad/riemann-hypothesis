module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2964
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2979
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2927
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2895
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoefficientsDescendFiniteFreeAffineOpen
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.OrigValExists

theorem mem_of_closed {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (f : Sp R ⟶ X) (U : X.Opens)
    (h : f (closedPoint R) ∈ U) (z : Sp R) : f z ∈ U := by
  have : f ⁻¹ᵁ U = ⊤ := (closedPoint_mem_iff (f ⁻¹ᵁ U)).1 h
  show z ∈ f ⁻¹ᵁ U
  rw [this]; trivial

theorem exists_stalkOf {R : Type} [CommRing R] {X : Scheme.{0}} (f : Sp R ⟶ X) (U : X.Opens)
    (h : ∀ z, f z ∈ U) (a : Γ(X, U)) : ∃ r : R, ∀ z, gs f z U a = stalkOf z r := by
  have hle : (⊤ : (Sp R).Opens) ≤ f ⁻¹ᵁ U := fun z _ => h z
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
    (((Sp R).presheaf.map (homOfLE hle).op).hom ((f.app U).hom a)), fun z => ?_⟩
  rw [gs_eq f z U (h z)]
  have e : ∀ x, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) = x :=
    fun x => (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply x
  refine Eq.trans ?_ (congrArg ((Sp R).presheaf.germ ⊤ z trivial).hom (e _)).symm
  exact (TopCat.Presheaf.germ_res_apply (Sp R).presheaf (homOfLE hle) z trivial _).symm

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (α : D.X)

theorem unit_fam_zero : unitW D.P.A ≫ D.famφB α 0 = idW R ≫ eSec D.P.A :=
  (Category.comp_id _).trans (Category.id_comp _).symm

theorem unit_fam_one : unitW D.P.A ≫ D.famφB α 1 = unitW D.P.A ≫ D.famφB α 2 := by
  change η[D.P.A].left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left = η[D.P.A].left ≫ (toUnit D.P.A ≫ D.c α).left
  rw [← Over.comp_left, ← Over.comp_left]; congr 1
  simp only [padd, comp_lift_assoc, Category.comp_id]
  have := MonObj.lift_comp_one_left (𝟙 (𝟙_ (Over (Sp R)))) (η[D.P.A] ≫ toUnit D.P.A ≫ D.c α)
  rwa [Category.id_comp] at this

theorem unit_fam_three : unitW D.P.A ≫ D.famφB α 3 = idW R ≫ eSec D.P.A := by
  refine Eq.trans ?_ (Category.id_comp _).symm
  change η[D.P.A].left ≫ (toUnit D.P.A ≫ η[D.P.A]).left = η[D.P.A].left
  rw [← Over.comp_left]; congr 1
  rw [← Category.assoc, Subsingleton.elim (η[D.P.A] ≫ toUnit D.P.A) (𝟙 _), Category.id_comp]

theorem trF_unit (k : ℕ) (z : Sp R) (J I : (Sp R ⟶ D.P.A.left) → D.P.L.ι) :
    trF (L := D.P.L) (D.famφB α) (DegPre.famε k) (unitW D.P.A) z (fun i => J (unitW D.P.A ≫ D.famφB α i))
      (fun i => I (unitW D.P.A ≫ D.famφB α i)) =
    trF (L := D.P.L) (K := PUnit) (fun _ => eSec D.P.A) (fun _ => 1) (idW R) z (fun _ => J (idW R ≫ eSec D.P.A))
      (fun _ => I (idW R ≫ eSec D.P.A)) ^ k := by
  let h : (Sp R ⟶ D.P.A.left) → ((Sp R).presheaf.stalk z)ˣ :=
    fun ψ => gm ψ z (D.P.L.U (J ψ) ⊓ D.P.L.U (I ψ)) (D.P.L.g (J ψ) (I ψ))
  show ∏ i, h (unitW D.P.A ≫ D.famφB α i) ^ DegPre.famε k i = (∏ _i : PUnit, h (idW R ≫ eSec D.P.A) ^ (1 : ℤ)) ^ k
  rw [Fin.prod_univ_four, unit_fam_zero, unit_fam_one, unit_fam_three, Fintype.prod_unique]
  generalize h (idW R ≫ eSec D.P.A) = A
  generalize h (unitW D.P.A ≫ D.famφB α 2) = B
  show A ^ ((k : ℤ) - 1) * B ^ (1 : ℤ) * B ^ (-1 : ℤ) * A ^ (1 : ℤ) = (A ^ (1 : ℤ)) ^ k
  rw [zpow_sub_one, zpow_natCast, zpow_neg, zpow_one, zpow_one, mul_inv_cancel_right, inv_mul_cancel_right]

end GlobalTheory.Mum.OrigValExists

namespace GlobalTheory.Mum
open OrigValExists

theorem exists_origVal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (k : ℕ) (α : D.X) (b : D.SecB k α), ∃ v : R, OrigVal D b v := by
  intro R _ _ _ D k α b
  obtain ⟨I, hI₀, -⟩ := exists_good D.P.L D.P.isLB (Z := Sp R) (closedPoint R) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim
    (fun a => a.elim) (fun a => a.elim)
  have hI : ∀ z, Good D.P.L z I := fun z ψ => mem_of_closed ψ _ (hI₀ ψ) z
  obtain ⟨a, ha⟩ := exists_stalkOf (unitW D.P.A) _ (fun z => (hI z).mem (D.famφB α) (unitW D.P.A))
    (b.f (fun i => I (unitW D.P.A ≫ D.famφB α i)))
  obtain ⟨u, hu⟩ := exists_stalkOf (idW R) _ (fun z => (hI z).mem (K := PUnit) (fun _ => eSec D.P.A) (idW R))
    ((D.rig.s (fun _ => I (idW R ≫ eSec D.P.A)))⁻¹).val
  refine ⟨a * u ^ k, fun z J hJ => ?_⟩
  have e₁ : sval b (unitW D.P.A) z J = _ * sval b (unitW D.P.A) z I :=
    sec_trans b (unitW D.P.A) z (hJ.mem _ _) ((hI z).mem _ _)
  have e₂ : val D.rig (idW R) z J = _ * val D.rig (idW R) z I :=
    gen_trans D.rig_gen (idW R) z (hJ.mem _ _) ((hI z).mem _ _)
  have e₃ : sval b (unitW D.P.A) z I = stalkOf z a := ha z
  have e₄ : stalkOf z u = ((val D.rig (idW R) z I)⁻¹).val :=
    (hu z).symm.trans ((gs_unit (idW R) z _ ((hI z).mem (K := PUnit) (fun _ => eSec D.P.A) (idW R)) _).trans
      (congrArg Units.val (map_inv _ _)))
  rw [e₁, e₂, e₃, trF_unit, map_mul, map_pow, e₄]
  generalize trF (K := PUnit) _ _ _ _ _ _ = A
  generalize val D.rig (idW R) z I = B
  rw [_root_.mul_assoc, ← mul_pow, ← Units.val_mul, _root_.mul_comm A B, inv_mul_cancel_left, Units.val_pow_eq_pow_val, _root_.mul_comm]

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem cst_id_eq_stalkOf {W : Type} [CommRing W] (z : Sp W) (a : W) : cst (𝟙 (Sp W)) z a = stalkOf z a :=
  gs_eq (𝟙 _) z ⊤ trivial _


open GlobalTheory.ExpansionValueZero in
theorem expandsAt_origVal : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (D' : DegData W (maximalIdeal W)) (A : PolAV (Sp (FractionRing W))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal W) D' A G) (k e : ℕ) (σ' : H0 U.LG.L k) (f' : ∀ x, D'.toPre.SecB k x) (w : D'.toPre.X → W), (∀ x, OrigVal D'.toPre (f' x) (w x)) → U.ExpandsAt e k σ' f' → ∃ S : Finset D'.toPre.X, (∀ x ∉ S, w x ∈ maximalIdeal W ^ (e + 1)) ∧ ∀ J', Good U.LG.L (cpt W) J' → ∃ c ∈ maximalIdeal W ^ (e + 1), sval σ' (unitW G) (cpt W) J' = stalkOf (cpt W) (∑ x ∈ S, w x + c) * (val U.LG.rig (idW W) (cpt W) J').val ^ k := by
  intro W _ _ _ D' A G _ _ U k e σ' f' w hw hE
  classical
  choose a ha using fun α => exists_value D'.toPre k α (f' α)
  obtain rfl : w = a := funext fun α => stalkOf_injective (cpt W) (by
    choose J hJ using fun ψ : Sp W ⟶ D'.toPre.P.A.left => exists_chart D'.toPre.P.isLB (ψ (cpt W))
    have h₁ := ha α _ (𝟙 (Sp W)) (cpt W) J hJ
    have h₂ := hw α (cpt W) J hJ
    rw [cst_id_eq_stalkOf] at h₁
    rw [← Units.val_pow_eq_pow_val] at h₂
    have h₃ : sval (f' α) (𝟙 (Sp W) ≫ eSec D'.toPre.P.A) (cpt W) J = sval (f' α) (unitW D'.toPre.P.A) (cpt W) J :=
      congrArg (fun q => sval (f' α) q (cpt W) J) (Category.id_comp (unitW D'.toPre.P.A))
    exact (Units.mul_left_inj _).1 (h₂.symm.trans (h₃.symm.trans h₁)))
  obtain ⟨x, hx⟩ := exists_coeff (A := W) U.LG.isLB σ' (eSec G) (GeneratorPullback.powGen U.LG.L _ _ U.LG.rig k)
    (DVR.powGen_isGen _ _ _ _ U.LG.rigGen k) (fun W _ f => by simp)
  have hx' : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (J), Good U.LG.L z J →
      sval σ' (r ≫ eSec G) z J = cst r z x * (val (L := U.LG.L) U.LG.rig r z J ^ k).val :=
    fun Z r z J hJ => (hx Z r z J hJ).trans (by rw [DVR.val_pow])
  obtain ⟨S, hS⟩ := value_sub_sum_mem U e k σ' f' hE x hx' w ha
  refine ⟨S, fun y hy => ?_, fun J' hJ' => ⟨x - ∑ α ∈ S, w α, hS S le_rfl, ?_⟩⟩
  · have h := Ideal.sub_mem _ (hS S le_rfl) (hS (insert y S) (Finset.subset_insert _ _))
    rw [Finset.sum_insert hy] at h
    convert h using 1
    ring
  · have h₁ := hx' _ (𝟙 (Sp W)) (cpt W) J' hJ'
    rw [cst_id_eq_stalkOf, Units.val_pow_eq_pow_val] at h₁
    rw [add_sub_cancel]
    exact (congrArg (fun q => sval σ' q (cpt W) J') (Category.id_comp (unitW G))).symm.trans h₁

end GlobalTheory.Mum
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.Conj.FamBij

open GlobalTheory.FieldBaseChange

variable {R : Type} [CommRing R] [IsDomain R]

def famMapTw (D : DegPre R) (σ : Kb R →ₐ[FractionRing R] Kb R) : DegPre.BF D (Kb R) ⟶ DegPre.BF D (Kb R) :=
  (famMap D (Kb R) (TwF σ) : DegPre.BF D (TwF σ) ⟶ DegPre.BF D (Kb R))

theorem famMapTw_eq (D : DegPre R) (σ : Kb R →ₐ[FractionRing R] Kb R) :
    famMapTw D σ = lift (fst (TF (R := R) (Kb R)) D.P.A ≫ twF σ) (snd (TF (R := R) (Kb R)) D.P.A) := rfl

theorem twF_comp_eq_id {σ τ : Kb R →ₐ[FractionRing R] Kb R} (h : ∀ x, τ (σ x) = x) :
    twF τ ≫ twF σ = 𝟙 _ := by
  apply Over.OverMorphism.ext
  show spMap τ.toRingHom ≫ spMap σ.toRingHom = 𝟙 _
  have e : τ.toRingHom.comp σ.toRingHom = RingHom.id _ := RingHom.ext h
  rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e, CommRingCat.ofHom_id, Spec.map_id]

theorem famMapTw_comp_eq_id (D : DegPre R) {σ τ : Kb R →ₐ[FractionRing R] Kb R} (h : ∀ x, τ (σ x) = x) :
    famMapTw D τ ≫ famMapTw D σ = 𝟙 _ := by
  have : lift (fst (TF (R := R) (Kb R)) D.P.A ≫ twF τ) (snd (TF (R := R) (Kb R)) D.P.A) ≫
      lift (fst (TF (R := R) (Kb R)) D.P.A ≫ twF σ) (snd (TF (R := R) (Kb R)) D.P.A) = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, lift_fst_assoc, Category.assoc, twF_comp_eq_id h, Category.comp_id,
        Category.id_comp]
    · rw [Category.assoc, lift_snd, lift_snd, Category.id_comp]
  exact this

theorem sval_famTw (D : DegPre R) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (s : Fam D (Kb R) N) (α : D.X)
    {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D (Kb R)).left) {z : Z} {J : (Z ⟶ D.P.A.left) → D.P.L.ι}
    (hJ : Good D.P.L z J) :
    sval ((famTw D N σ s).s α) r z J = sval (s.s α) (r ≫ (famMapTw D σ).left) z J :=
  sval_pullOver (isPullback_famMap D (Kb R) (TwF σ)).w (famφ_famMap D (Kb R) (TwF σ) α) (s.s α) r hJ

theorem famTw_famTw_eq (D : DegPre R) (N : ℕ) {σ τ : Kb R →ₐ[FractionRing R] Kb R} (h : ∀ x, τ (σ x) = x)
    (s : Fam D (Kb R) N) : famTw D N τ (famTw D N σ s) = s := by
  refine ReciprocityTheory.ChartRestriction.G.DVR.fam_ext fun α j => congrArg (fun q => LB.Sec.f q j) ?_
  refine sec_ext' D.P.isLB fun y J hJ => ?_
  rw [sval_famTw D N τ _ α _ hJ, sval_famTw D N σ _ α _ hJ, Category.assoc, ← Over.comp_left,
    famMapTw_comp_eq_id D h, Over.id_left, Category.comp_id]

theorem famTw_bijective (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ)
    (σ : Kb R →ₐ[FractionRing R] Kb R) : Function.Bijective (famTw D N σ) := by
  let e : Kb R ≃ₐ[FractionRing R] Kb R := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  refine Function.bijective_iff_has_inverse.2 ⟨famTw D N (e.symm : Kb R →ₐ[FractionRing R] Kb R), ?_, ?_⟩
  · exact famTw_famTw_eq D N fun x => e.symm_apply_apply x
  · exact famTw_famTw_eq D N fun x => e.apply_symm_apply x

end GlobalTheory.Mum.Conj.FamBij
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

variable {R : Type} [CommRing R] [IsDomain R]

theorem twK_comp_eq_id {σ τ : Kb R →ₐ[FractionRing R] Kb R} (h : σ.comp τ = AlgHom.id _ _) :
    twK σ ≫ twK τ = 𝟙 _ := by
  apply Over.OverMorphism.ext
  show spMap σ.toRingHom ≫ spMap τ.toRingHom = 𝟙 _
  rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have e : σ.toRingHom.comp τ.toRingHom = RingHom.id _ := congrArg AlgHom.toRingHom h
  rw [e]
  exact Spec.map_id _

theorem mTw_comp_eq_id (A : PolAV (Sp (FractionRing R))) {σ τ : Kb R →ₐ[FractionRing R] Kb R}
    (h : σ.comp τ = AlgHom.id _ _) : mTw A σ ≫ mTw A τ = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, mTw_fst, ← Category.assoc, mTw_fst, Category.assoc, twK_comp_eq_id h, Category.comp_id,
      Category.id_comp]
  · rw [Category.assoc, mTw_snd, mTw_snd, Category.id_comp]

theorem mTw_translT (A : PolAV (Sp (FractionRing R))) {σ τ : Kb R →ₐ[FractionRing R] Kb R}
    (h : σ.comp τ = AlgHom.id _ _) (x : TFK (R := R) (Kb R) ⟶ A.A) :
    mTw A σ ≫ translT A.A (twK τ ≫ x) = translT A.A x ≫ mTw A σ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [translT]
    rw [Category.assoc, Category.assoc, lift_fst, mTw_fst, ← Category.assoc, lift_fst]
  · simp only [translT]
    rw [Category.assoc, Category.assoc, lift_snd, mTw_snd, lift_snd]
    simp only [translPt]
    rw [← Category.assoc, comp_lift, ← Category.assoc (mTw A σ), mTw_fst, mTw_snd, Category.assoc,
      ← Category.assoc (twK σ), twK_comp_eq_id h, Category.id_comp]

theorem isActOf_secTw : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ τ : Kb R →ₐ[FractionRing R] Kb R), σ.comp τ = AlgHom.id _ _ → ∀ (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R))) (a b : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), IsActOf A.A A.L N (thTw A N τ θ) a b → IsActOf A.A A.L N θ (secTw A N σ a) (secTw A N σ b) := by
  intro R _ _ A N σ τ hστ θ a b H
  refine twist_of_val A.isLB θ.isGen fun z J hJ => ?_
  have e1 : (𝟙 _ ≫ (mTw A σ).left) ≫ (mTw A τ).left = 𝟙 _ := by
    rw [Category.id_comp, ← Over.comp_left, mTw_comp_eq_id A hστ, Over.id_left]
  have e2 : (𝟙 _ ≫ (mTw A σ).left) ≫ (translT A.A (twK τ ≫ θ.pt)).left =
      (𝟙 _ ≫ (translT A.A θ.pt).left) ≫ (mTw A σ).left := by
    simp only [Category.id_comp, ← Over.comp_left, mTw_translT A hστ]
  have hv : val (thTw A N τ θ).φ (𝟙 _ ≫ (mTw A σ).left) z J = val θ.φ (𝟙 _) z J :=
    (val_genCast _ _ _ z J).trans ((val_pull hJ _ _ _).trans (congrArg (fun r => val θ.φ r z J) e1))
  have H' := twist_val H (𝟙 _ ≫ (mTw A σ).left) z hJ
  rw [hv] at H'
  have hb : sval (secTw A N σ b) (𝟙 _) z J = sval b (𝟙 _ ≫ (mTw A σ).left) z J :=
    GlobalTheory.FieldBaseChange.sval_pullOver _ _ b _ hJ
  have ha : sval (secTw A N σ a) (𝟙 _ ≫ (translT A.A θ.pt).left) z J =
      sval a ((𝟙 _ ≫ (translT A.A θ.pt).left) ≫ (mTw A σ).left) z J :=
    GlobalTheory.FieldBaseChange.sval_pullOver _ _ a _ hJ
  refine hb.trans (H'.trans ?_)
  rw [ha]
  exact congrArg (fun r => (val θ.φ (𝟙 _) z J).val * sval a r z J) e2

end GlobalTheory.Mum.Conj
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

noncomputable section

namespace GlobalTheory.Mum.Conj

variable {R : Type} [CommRing R] [IsDomain R]

theorem twK_comp_twK (σ τ : Kb R →ₐ[FractionRing R] Kb R) (h : τ.comp σ = AlgHom.id _ _) :
    twK τ ≫ twK σ = 𝟙 _ := by
  ext1
  rw [Over.comp_left, twK_left, twK_left, Over.id_left, spMap, spMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  have : τ.toRingHom.comp σ.toRingHom = RingHom.id _ := congrArg AlgHom.toRingHom h
  rw [this]
  exact Spec.map_id _

theorem mTw_comp_mTw_left (A : PolAV (Sp (FractionRing R))) (σ τ : Kb R →ₐ[FractionRing R] Kb R)
    (h : τ.comp σ = AlgHom.id _ _) : (mTw A τ).left ≫ (mTw A σ).left = 𝟙 _ := by
  rw [← Over.comp_left]
  have : mTw A τ ≫ mTw A σ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, mTw_fst, ← Category.assoc, mTw_fst, Category.assoc, twK_comp_twK σ τ h,
        Category.comp_id, Category.id_comp]
    · rw [Category.assoc, mTw_snd, mTw_snd, Category.id_comp]
  rw [this]; rfl

theorem secTw_secTw (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ τ : Kb R →ₐ[FractionRing R] Kb R)
    (h : τ.comp σ = AlgHom.id _ _) (t : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N) :
    secTw A N τ (secTw A N σ t) = t := by
  refine GlobalTheory.FieldBaseChange.sec_ext' A.isLB fun y J hJ => ?_
  refine (GlobalTheory.FieldBaseChange.sval_pullOver _ _ _ _ hJ).trans
    ((GlobalTheory.FieldBaseChange.sval_pullOver _ _ _ _ hJ).trans ?_)
  rw [Category.assoc, mTw_comp_mTw_left A σ τ h, Category.comp_id]

theorem secTw_bijective (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ)
    (σ : Kb R →ₐ[FractionRing R] Kb R) : Function.Bijective (secTw A N σ) := by
  have hσ : Function.Bijective σ := Algebra.IsAlgebraic.algHom_bijective σ
  let e := AlgEquiv.ofBijective σ hσ
  let τ : Kb R →ₐ[FractionRing R] Kb R := e.symm.toAlgHom
  have h1 : τ.comp σ = AlgHom.id _ _ := by
    ext x; exact e.symm_apply_apply x
  have h2 : σ.comp τ = AlgHom.id _ _ := by
    ext x; exact e.apply_symm_apply x
  exact ⟨Function.LeftInverse.injective (g := secTw A N τ) (secTw_secTw A N σ τ h1),
    Function.RightInverse.surjective (g := secTw A N τ) (secTw_secTw A N τ σ h2)⟩

end GlobalTheory.Mum.Conj
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem gm_comp_stalkMap {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U)
    (a : Γ(X, U)ˣ) : gm (f ≫ g) z U a = Units.map (f.stalkMap z).hom.toMonoidHom (gm g (f z) U a) := by
  apply Units.ext
  rw [gm_val (f ≫ g) z U h, Units.coe_map, gm_val g (f z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply f (g ⁻¹ᵁ U) z h ((g.app U).hom a.val)).symm

theorem val_comp_stalkMap {X Y Z W : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (f : Z ⟶ W) (r : W ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) :
    val t (f ≫ r) z J = Units.map (f.stalkMap z).hom.toMonoidHom (val t r (f z) (fun ψ => J (f ≫ ψ))) := by
  rw [val_of t (f ≫ r) z J (fun k => J (f ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gm_comp_stalkMap f r z _ (Set.mem_iInter.2 fun k => hJ (f ≫ r ≫ φ k)) _

theorem good_comp {X Z W : Scheme.{0}} {L : LB X} (f : Z ⟶ W) {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Good L (f z) (fun ψ => J (f ≫ ψ)) := fun ψ => hJ (f ≫ ψ)

end GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem txFrame_frTw (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ)
    (τ : Kb R →ₐ[FractionRing R] Kb R) (p p₀ : QkPt D (Kb R) N) (h : QkExt τ.toRingHom p p₀)
    (w : GlobalTheory.UT.Frm D (Kb R) N p.g.b) : GlobalTheory.UT.TXFrame N p w → GlobalTheory.UT.TXFrame N p₀ (frTw D τ h w) := by
  rintro ⟨hg, h2, hN⟩
  set f : (TF (R := R) (Kb R)).left ⟶ (TF (R := R) (Kb R)).left := spMap τ.toRingHom with hf
  have hfr : ∀ (z : (TF (R := R) (Kb R)).left) (J), Good D.P.L z J →
      val (frTw D τ h w) (𝟙 _) z J = Units.map (f.stalkMap z).hom.toMonoidHom (val w (𝟙 _) (f z) (fun ψ => J (f ≫ ψ))) := by
    intro z J hJ
    rw [frTw, val_genCast, val_pull hJ, Category.id_comp, ← Category.comp_id f]
    exact val_comp_stalkMap w f (𝟙 _) z J hJ
  have hsy : ∀ (z : (TF (R := R) (Kb R)).left) (J), Good D.P.L z J →
      val (p₀.g.s p₀.y) (𝟙 _) z J = Units.map (f.stalkMap z).hom.toMonoidHom (val (p.g.s p.y) (𝟙 _) (f z) (fun ψ => J (f ≫ ψ))) := by
    intro z J hJ
    rw [h.1, val_corr hJ (h.2.2 p.y), val_pull hJ, Category.id_comp, ← Category.comp_id f]
    exact val_comp_stalkMap _ f (𝟙 _) z J hJ
  refine ⟨genCast_isGen _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen D.P.L _ _ w hg _), ?_, ?_⟩
  · intro ν hν z J hJ
    rw [hfr z J hJ, hsy z J hJ, h.2.1, val_comp_stalkMap ν f _ z J hJ, ← map_pow, ← map_mul,
      h2 ν hν (f z) _ (good_comp f hJ)]
  · intro κ hκ z J hJ
    have hpsi : val (D.psi p₀.y) (jFK (R := R) (Kb R)) z J =
        Units.map (f.stalkMap z).hom.toMonoidHom (val (D.psi p.y) (jFK (R := R) (Kb R)) (f z) (fun ψ => J (f ≫ ψ))) := by
      have e := val_comp_stalkMap (D.psi p.y) f (jFK (R := R) (Kb R)) z J hJ
      rw [h.1]
      refine Eq.trans ?_ e
      exact congrArg (fun r => val (D.psi p.y) r z J) (spMap_jFK τ).symm
    have hrig : GlobalTheory.UT.rigV D (TF (R := R) (Kb R)).hom z J =
        Units.map (f.stalkMap z).hom.toMonoidHom (GlobalTheory.UT.rigV D (TF (R := R) (Kb R)).hom (f z) (fun ψ => J (f ≫ ψ))) := by
      unfold GlobalTheory.UT.rigV
      rw [← val_comp_stalkMap _ f _ z J hJ]
      exact congrArg (fun r => val D.rig r z J) (spMap_jFKR τ).symm
    rw [id_eq, hfr z J hJ, hpsi, hrig, h.2.1, val_comp_stalkMap κ f _ z J hJ, ← map_pow,
      ← map_mul, ← map_mul]
    exact congrArg _ (hN κ hκ (f z) _ (good_comp f hJ))

end GlobalTheory.Mum.Conj

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem comp_mTw_left_eq {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R)))
    (σ : Kb R →ₐ[FractionRing R] Kb R) {Z : Scheme.{0}} {p p' : Z ⟶ (TFK (R := R) (Kb R) ⊗ A.A).left}
    (h₂ : p' ≫ (snd (TFK (R := R) (Kb R)) A.A).left = p ≫ (snd (TFK (R := R) (Kb R)) A.A).left)
    (h₁ : p' ≫ (fst (TFK (R := R) (Kb R)) A.A).left =
      p ≫ (fst (TFK (R := R) (Kb R)) A.A).left ≫ spMap σ.toRingHom) :
    p ≫ (mTw A σ).left = p' := by
  refine pullback.hom_ext (f := (TFK (R := R) (Kb R)).hom) (g := A.A.hom) ?_ ?_
  · change (p ≫ (mTw A σ).left) ≫ (fst (TFK (R := R) (Kb R)) A.A).left = p' ≫ (fst (TFK (R := R) (Kb R)) A.A).left
    rw [Category.assoc, mTw_fst_left, h₁]
  · change (p ≫ (mTw A σ).left) ≫ (snd (TFK (R := R) (Kb R)) A.A).left = p' ≫ (snd (TFK (R := R) (Kb R)) A.A).left
    rw [Category.assoc, mTw_snd_left, h₂]

theorem secTw_isTwist (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ)
    (σ : Kb R →ₐ[FractionRing R] Kb R) (t : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N) :
    SecTw σ t (secTw A N σ t) := by
  intro Z p p' h₂ h₁ z J hJ
  rw [← comp_mTw_left_eq A σ h₂ h₁]
  exact GlobalTheory.FieldBaseChange.sval_pullOver (mTw_fst_left A σ) (fun _ => (mTw_snd_left A σ).symm) t p hJ

end GlobalTheory.Mum.Conj
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.frame_coefficients_descend_finiteFree_affineOpen : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁), (∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l) → ∀ (X : Scheme.{0}) (f : X ⟶ Sp R) (L : LB X), L.IsLB → ∀ (W O : X.Opens), O ≤ W → IsAffineOpen O → ∀ (τ : ∀ k : L.ι, Γ((pullback f (spMap ρ₁)), (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k)ˣ), FrameAlong L (pullback.fst f (spMap ρ₁)) ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W) τ → ∃ s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k), (∀ l, IsSecOver L O (s l)) ∧ ∀ (z : (pullback f (spMap ρ₁) : Scheme.{0})) (k : L.ι), (pullback.fst f (spMap ρ₁)) z ∈ O → (pullback.fst f (spMap ρ₁)) z ∈ L.U k → gs (𝟙 (pullback f (spMap ρ₁))) z ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k) (τ k).val = ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z (O ⊓ L.U k) (s l k) := by
  first | exact @GlobalTheory.FrameCoeff.frame_coeff | exact GlobalTheory.FrameCoeff.frame_coeff | (intros; apply GlobalTheory.FrameCoeff.frame_coeff <;> assumption)
end
