module

public import ReciprocityTheory.DualLattices.UpBrChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxSec
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle005
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import ReciprocityTheory.DualLattices.ProdDvdOfIso
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
open ReciprocityTheory.PGsh.Up

namespace GlobalTheory.CharDepth

theorem det_dvd_det_of_trunc_mem_span {R : Type} [CommRing R] {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (B : Matrix (Fin n) (Fin n) R)
    (h : ∀ j, (fun a : Fin n => A a.castSucc j) ∈ Submodule.span R (Set.range fun i => fun a => B a i)) :
    B.det ∣ A.det := by
  choose X hX using fun j => (Submodule.mem_span_range_iff_exists_fun R).1 (h j)
  rw [Matrix.det_succ_row A (Fin.last n)]
  refine Finset.dvd_sum fun j _ => Dvd.dvd.mul_left ?_ _
  have e : A.submatrix (Fin.last n).succAbove j.succAbove = B * Matrix.of (fun i k => X (j.succAbove k) i) := by
    ext a k
    have := congrFun (hX (j.succAbove k)) a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_apply, Matrix.submatrix_apply, Fin.succAbove_last, ← this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e, Matrix.det_mul]
  exact Dvd.intro _ rfl

theorem minor_dvd_minor {R : Type} [CommRing R] {g N : ℕ} (M : Matrix (Fin g) (Fin N) R) (ι : Fin g → Fin N)
    (hι : ∀ s (hs : s ≤ g), Submodule.span R (Set.range fun b : Fin s => fun a : Fin s =>
      M (Fin.castLE hs a) (ι (Fin.castLE hs b))) = omTr M s hs)
    (n m : ℕ) (hnm : n ≤ m) (hm : m ≤ g) :
    (Matrix.of fun a b : Fin n => M (Fin.castLE (hnm.trans hm) a) (ι (Fin.castLE (hnm.trans hm) b))).det ∣
      (Matrix.of fun a b : Fin m => M (Fin.castLE hm a) (ι (Fin.castLE hm b))).det := by
  induction m, hnm using Nat.le_induction with
  | base => exact dvd_rfl
  | succ m hnm ih =>
    refine (ih (Nat.le_of_succ_le hm)).trans (det_dvd_det_of_trunc_mem_span _ _ fun j => ?_)
    have h := hι m (Nat.le_of_succ_le hm)
    have h2 : (fun a : Fin m => M (Fin.castLE (Nat.le_of_succ_le hm) a) (ι (Fin.castLE hm j))) ∈
        omTr M m (Nat.le_of_succ_le hm) := Submodule.subset_span ⟨_, rfl⟩
    rw [← h] at h2
    exact h2

theorem exists_smul_eq_zero_of_hasLen {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R) {M : Type} [AddCommGroup M] [Module R M] {x : NNReal}
    (h : HasLen v R M x) (hx : x ≠ 0) : x ≤ 1 ∧ ∃ c : R, c ≠ 0 ∧ ∀ m : M, c • m = 0 := by
  obtain ⟨m, c, ⟨e⟩, hc⟩ := h
  have hc' : v (algebraMap R C (∏ i, c i)) = x := by rw [map_prod, map_prod, hc]
  refine ⟨hc' ▸ hv.map_le_one _, ∏ i, c i, ?_, fun z => ?_⟩
  · intro h0
    rw [h0, map_zero, map_zero] at hc'
    exact hx hc'.symm
  · apply e.injective
    rw [map_smul, map_zero]
    funext i
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (e z i)
    rw [Pi.smul_apply, ← hy, Pi.zero_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton.2 ((Finset.dvd_prod_of_mem c (Finset.mem_univ i)).mul_right y)

theorem exists_flag_characters (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    (hv : v.Integers O) (d s : ℕ) (F : Fin d → PS O 2 d) (w : Fin s → Fin d → O) (x : NNReal)
    (h : HasAF v F w x) (hx : x ≠ 0) :
    x ≤ 1 ∧ ∃ χ : Fin s → PS O 1 d, (∀ b, IsCh F (χ b)) ∧ ∀ i : Fin s, x ≤ v (algebraMap O C
      (Matrix.of fun a b : Fin (i.val + 1) =>
        ∑ j, w (Fin.castLE i.isLt a) j * dl (χ (Fin.castLE i.isLt b)) j).det) := by
  obtain ⟨N, u, hu, hlen⟩ := h
  obtain ⟨hx1, c, hc, hkill⟩ := exists_smul_eq_zero_of_hasLen hv hlen hx
  refine ⟨hx1, ?_⟩
  let M : Matrix (Fin s) (Fin N) O := fun a k => res w (dl (u k)) a
  have hom : omTr M s le_rfl = Submodule.span O (Set.range fun k => res w (dl (u k))) := rfl
  have hspan : ∀ n (hn : n ≤ s), ∀ y : Fin n → O, c • y ∈ omTr M n hn := by
    intro n hn y
    let y' : Fin s → O := Function.extend (Fin.castLE hn) y 0
    have h1 : c • y' ∈ Submodule.span O (Set.range fun k => res w (dl (u k))) := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
      exact hkill _
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 h1
    refine (Submodule.mem_span_range_iff_exists_fun O).2 ⟨r, ?_⟩
    funext a
    have h2 := congrFun hr (Fin.castLE hn a)
    have h3 : y' (Fin.castLE hn a) = y a := (Fin.castLE_injective hn).extend_apply y 0 a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h3] at h2 ⊢
    exact h2
  obtain ⟨ι, -, hι⟩ := charThm C v O hv s N M c hc hspan
  haveI : IsDomain O := Function.Injective.isDomain _ hv.hom_inj
  have hfull := char_len hv M ι s le_rfl (hι s le_rfl)
  rw [hom] at hfull
  have hxe := hasLen_unique hv hlen hfull
  refine ⟨fun b => u (ι b), fun b => hu _, fun i => ?_⟩
  have hd := hv.le_of_dvd (minor_dvd_minor M ι hι (i.val + 1) s i.isLt le_rfl)
  rw [← hxe] at hd
  exact hd

end GlobalTheory.CharDepth
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.BoxPull

open GlobalTheory.BoxPhi

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {F : Type} [Field F] [Algebra (FractionRing V) F] {O : Type} [CommRing O] [StarRing O]

theorem gs_zero' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  by_cases h : f y ∈ U
  · rw [gs_eq f y U h, map_zero, map_zero]
  · exact dif_neg h

theorem prod_pull_zero (D : DegData V (maximalIdeal V)) [Module O D.toPre.X] (oa : D.toPre.OAct O) (a : O) (k N : ℕ)
    (hN : 1 ≤ N) (χ : D.toPre.X) {U : Type} [CommGroup U] (h : ((TF (R := V) F).left ⟶ D.toPre.P.A.left) → U) :
    ∏ i, h ((DegPre.zF D.toPre F).left ≫ pullφ D F oa a χ i) ^ pullε k N i =
      h (1 : TF (R := V) F ⟶ D.toPre.P.A).left ^ (k * (N - 1)) := by
  have := oa.onB.hom a
  have p₃ := prod_fam D.toPre F (DegPre.zF D.toPre F) (star a • χ) (k * N) h
  have p₄ := prod_fam D.toPre F (DegPre.zF D.toPre F ≫ aF D F oa a) χ k h
  have z₂ : DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F = 1 := lift_snd _ _
  have z₃ : (DegPre.zF D.toPre F ≫ aF D F oa a) ≫ DegPre.prB D.toPre F = 1 := by
    rw [Category.assoc, aF, lift_snd, ← Category.assoc, z₂, MonObj.one_comp]
  rw [z₂, _root_.mul_one] at p₃
  rw [z₃, _root_.mul_one] at p₄
  simp only [Over.comp_left, Category.assoc] at p₄
  refine (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₃ (prod_neg _ _ p₄)).trans ?_
  rw [← zpow_natCast, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hN]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem aF_pr {j : ℕ} {D D' : DegData V (maximalIdeal V)} (pD : IsPowDeg D'.toPre D.toPre j)
    [Module O D.toPre.X] [Module O D'.toPre.X] (oa : D.toPre.OAct O) (oa' : D'.toPre.OAct O) (a : O) (i : Fin j)
    (hact : oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a) :
    (aF D' F oa' a).left ≫ prB pD F i = prB pD F i ≫ (aF D F oa a).left := by
  refine congrArg (fun q => q.left) (?_ : aF D' F oa' a ≫ (TF (R := V) F ◁ pD.pw.pr i) =
    (TF (R := V) F ◁ pD.pw.pr i) ≫ aF D F oa a)
  apply CartesianMonoidalCategory.hom_ext
  · simp [aF]
  · simp [aF, hact]

theorem pullAl_box {j : ℕ} {D D' : DegData V (maximalIdeal V)} (pD : IsPowDeg D'.toPre D.toPre j)
    [Module O D.toPre.X] [Module O D'.toPre.X]
    (hx : ∀ (a : O) (x : D'.toPre.X) (i : Fin j), pD.xe (a • x) i = a • pD.xe x i)
    (oa : D.toPre.OAct O) (oa' : D'.toPre.OAct O)
    (hact : ∀ a i, oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a) (a : O) (N k : ℕ) (hN : 1 ≤ N)
    (s : Fin j → Fam D.toPre F k) (s' : Fin j → Fam D.toPre F (k * N)) (S : Fam D'.toPre F k)
    (S' : Fam D'.toPre F (k * N)) (hs : ∀ i, PullAl D F oa a k N (s i) (s' i)) (hS : IsBoxFam pD F k S s)
    (hS' : IsBoxFam pD F (k * N) S' s') : PullAl D' F oa' a k N S S' := by
  have ht := fun i => aF_pr (F := F) pD oa oa' a i (hact a i)
  refine ⟨fun χ' => ?_, fun β' hβ' => ?_⟩
  · choose u hu hc hr using fun i => (hs i).1 (pD.xe χ' i)
    have hφ : ∀ i b, pullφ D' F oa' a χ' b ≫ (pD.pw.pr i).left =
        prB pD F i ≫ pullφ D F oa a (pD.xe χ' i) b := by
      rintro i (b | b)
      · exact ((hS' (star a • χ')).choose i b).trans (by rw [hx]; rfl)
      · show ((aF D' F oa' a).left ≫ DegPre.famφ D'.toPre F χ' b) ≫ _ =
          _ ≫ (aF D F oa a).left ≫ DegPre.famφ D.toPre F (pD.xe χ' i) b
        rw [Category.assoc, (hS χ').choose i b, ← Category.assoc, ht, Category.assoc]
    obtain ⟨v, hv, vv⟩ := exists_box_gen D.toPre.P.isLB D'.toPre.P.isLB pD.w pD.w_gen hφ u hu
    refine ⟨v, hv, corr_of_val D'.toPre.P.isLB fun y J' hJ' => ?_,
      (secRel_iff D'.toPre.P.isLB _ _ _ _ _ _ _ _ _ v).2 fun y J' hJ' => ?_⟩
    · obtain ⟨J, hJ⟩ := BoxFamily.exists_good_at D.toPre.P.isLB y
      have e₂ := vv _ (DegPre.zF D'.toPre F).left y J J' hJ hJ'
      let r : (TF (R := V) F).left ⟶ (TK V).left := 𝟙 (TF (R := V) F).left ≫ jFK (R := V) F
      have e₃ : om pD.w y J J' (1 : TF (R := V) F ⟶ D'.toPre.P.A).left * val D'.toPre.rigK r y J' =
          ∏ _i : Fin j, val D.toPre.rigK r y J := by
        have z : (1 : TF (R := V) F ⟶ D'.toPre.P.A).left = r ≫ (toUnit (TK V)).left ≫ eSec D'.toPre.P.A :=
          (show (1 : TF (R := V) F ⟶ D'.toPre.P.A).left =
              jFK (R := V) F ≫ (toUnit (TK V)).left ≫ eSec D'.toPre.P.A by
            show (toUnit _ ≫ η[D'.toPre.P.A]).left = _
            rw [Over.comp_left]
            rfl).trans (congrArg (· ≫ (toUnit (TK V)).left ≫ eSec D'.toPre.P.A)
            (Category.id_comp (jFK (R := V) F)).symm)
        rw [z]
        exact BoxFamily.rig_val pD hJ hJ' r
      have e₅ : ∀ i, val (u i) ((DegPre.zF D'.toPre F).left ≫ prB pD F i) y J =
          val D.toPre.rigK r y J ^ (k * (N - 1)) := fun i => by
        have := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (hc i) (𝟙 _)).trans
          ((val_pull hJ _ _ _).trans (BoxFamily.val_powGen _ _ _ _ _ _ _)))
        rw [Category.id_comp] at this
        rw [BoxFamily.zF_pr]
        exact this
      rw [prod_pull_zero D' oa' a k N hN χ', Finset.prod_congr rfl (fun i _ => e₅ i), Finset.prod_pow, ← e₃,
        mul_pow] at e₂
      refine (val_pull hJ' _ _ _).trans (Eq.trans ?_
        ((val_pull hJ' _ _ _).trans (BoxFamily.val_powGen _ _ _ _ _ _ _)).symm)
      rw [Category.id_comp]
      exact mul_left_cancel e₂
    · obtain ⟨J, hJ⟩ := BoxFamily.exists_good_at D.toPre.P.isLB y
      have e₁ := fam_val pD hS' (star a • χ') (𝟙 _) y hJ hJ'
      have e₂ := fam_val pD hS χ' (𝟙 _ ≫ (aF D' F oa' a).left) y hJ hJ'
      have e₃ := vv _ (𝟙 _) y J J' hJ hJ'
      have e₄ : ∀ i, sval ((s' i).s (pD.xe (star a • χ') i)) (𝟙 _ ≫ prB pD F i) y J =
          sval ((s i).s (pD.xe χ' i)) ((𝟙 _ ≫ (aF D' F oa' a).left) ≫ prB pD F i) y J *
            (val (u i) (𝟙 _ ≫ prB pD F i) y J).val := fun i => by
        rw [hx, Category.assoc, ht, ← Category.assoc]
        exact (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ (u i)).1 (hr i) _ _ y J hJ
      have e₅ : ∏ b, om pD.w y J J' (𝟙 _ ≫ pullφ D' F oa' a χ' b) ^ pullε k N b =
          (∏ b, om pD.w y J J' (𝟙 _ ≫ DegPre.famφ D'.toPre F (star a • χ') b) ^ DegPre.famε (k * N) b) *
          (∏ b, om pD.w y J J' ((𝟙 _ ≫ (aF D' F oa' a).left) ≫ DegPre.famφ D'.toPre F χ' b) ^
            DegPre.famε k b)⁻¹ := by
        simp only [Category.assoc]
        exact prod_sum₂ (K := Fin 4) (K' := Fin 4) _ rfl (prod_neg _ _ rfl)
      rw [Finset.prod_congr rfl (fun i _ => e₄ i), Finset.prod_mul_distrib, ← e₂, ← Units.coe_prod, ← e₃, e₅] at e₁
      exact alg_fin e₁
  · obtain ⟨i, hi⟩ : ∃ i, ∀ χ, pD.xe β' i ≠ star a • χ := by
      by_contra hne
      push Not at hne
      choose χ hχ using hne
      refine hβ' (pD.xe.symm χ) (pD.xe.injective (funext fun i => ?_))
      rw [hx, AddEquiv.apply_symm_apply, hχ]
    have hz := (hs i).2 _ hi
    intro jj
    refine fn_ext fun y hy => ?_
    obtain ⟨J', hJ', e⟩ := sval_trans D'.toPre.P.isLB (S'.s β') y jj hy
    obtain ⟨J, hJ⟩ := BoxFamily.exists_good_at D.toPre.P.isLB y
    have e₁ := fam_val pD hS' β' (𝟙 _) y hJ hJ'
    have z₀ : sval ((s' i).s (pD.xe β' i)) (𝟙 _ ≫ prB pD F i) y J = 0 := by
      exact (congrArg (gs _ y _) (hz _)).trans (gs_zero' _ y _)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) z₀, Units.mul_right_eq_zero] at e₁
    rw [e₁, mul_zero] at e
    refine e.trans ?_
    exact (gs_zero' _ y _).symm

theorem main : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (j : ℕ) (D D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre D.toPre j) (F : Type) [Field F] [Algebra (FractionRing V) F] (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X], (∀ (a : O) (x : D'.toPre.X) (i : Fin j), pD.xe (a • x) i = a • pD.xe x i) → ∀ (oa : D.toPre.OAct O) (oa' : D'.toPre.OAct O), (∀ a i, oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a) → ∀ (a : O) (N k : ℕ), 1 ≤ N → 1 ≤ k → a * star a = (N : O) → ∀ (s : Fin j → Fam D.toPre F k) (s' : Fin j → Fam D.toPre F (k * N)) (S : Fam D'.toPre F k) (S' : Fam D'.toPre F (k * N)), (∀ i, PullAl D F oa a k N (s i) (s' i)) → IsBoxFam pD F k S s → IsBoxFam pD F (k * N) S' s' → PullAl D' F oa' a k N S S' :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ pD _ _ _ _ _ _ _ _ hx oa oa' hact a N k hN _ _ s s' S S' hs hS hS' =>
    pullAl_box pD hx oa oa' hact a N k hN s s' S S' hs hS hS'

end GlobalTheory.BoxPull
end
end

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigBaseChange

theorem piScalarRight_lTensor_mulVec {R O : Type} [CommRing R] [CommRing O] [Algebra R O]
    {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (A : Matrix m n R)
    (x : O ⊗[R] (n → R)) :
    TensorProduct.piScalarRight R O O m (LinearMap.lTensor O A.mulVecLin x) =
      (A.map (algebraMap R O)).mulVec (TensorProduct.piScalarRight R O O n x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, Matrix.mulVec_add]
  | tmul o v =>
    ext i
    simp [Matrix.mulVec, dotProduct, Algebra.smul_def, Finset.sum_mul, mul_assoc]

theorem exact_mulVec_map {R O : Type} [CommRing R] [CommRing O] [Algebra R O] [Module.Flat R O]
    {k m n : Type} [Fintype k] [Fintype m] [Fintype n] (A : Matrix m n R) (B : Matrix k m R)
    (h : Function.Exact A.mulVec B.mulVec) :
    Function.Exact (A.map (algebraMap R O)).mulVec (B.map (algebraMap R O)).mulVec := by
  classical
  have h' : Function.Exact A.mulVecLin B.mulVecLin := h
  have h2 := Module.Flat.lTensor_exact O h'
  intro y
  obtain ⟨y, rfl⟩ := (TensorProduct.piScalarRight R O O m).surjective y
  rw [← piScalarRight_lTensor_mulVec, LinearEquiv.map_eq_zero_iff, h2 y]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, (piScalarRight_lTensor_mulVec A x).symm⟩
  · rintro ⟨x, hx⟩
    obtain ⟨x, rfl⟩ := (TensorProduct.piScalarRight R O O n).surjective x
    rw [← piScalarRight_lTensor_mulVec] at hx
    exact ⟨x, (TensorProduct.piScalarRight R O O m).injective hx⟩

theorem transpose_mulVec {R : Type} [CommRing R] {d s : ℕ} (w : Fin s → Fin d → R) (c : Fin s → R) :
    (Matrix.of w).transpose.mulVec c = ∑ i, c i • w i := by
  ext j
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

def eigMat {R : Type} [CommRing R] {d N : ℕ} (L : Fin N → Matrix (Fin d) (Fin d) R)
    (t : Fin N → R) : Matrix (Fin N × Fin d) (Fin d) R :=
  Matrix.of fun p j => (L p.1 - t p.1 • (1 : Matrix (Fin d) (Fin d) R)) p.2 j

theorem eigMat_mulVec_eq_zero {R : Type} [CommRing R] {d N : ℕ}
    (L : Fin N → Matrix (Fin d) (Fin d) R) (t : Fin N → R) (v : Fin d → R) :
    (eigMat L t).mulVec v = 0 ↔ ∀ k, (L k).mulVec v = t k • v := by
  have key : ∀ k i, (eigMat L t).mulVec v (k, i) = ((L k).mulVec v - t k • v) i := by
    intro k i
    have : (eigMat L t).mulVec v (k, i) =
        (L k - t k • (1 : Matrix (Fin d) (Fin d) R)).mulVec v i := rfl
    rw [this, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  constructor
  · intro h k
    rw [← sub_eq_zero]
    ext i
    rw [← key, h]; rfl
  · intro h
    ext ⟨k, i⟩
    rw [key, h k, sub_self]; rfl

theorem eigMat_map {R O : Type} [CommRing R] [CommRing O] (f : R →+* O) {d N : ℕ}
    (L : Fin N → Matrix (Fin d) (Fin d) R) (t : Fin N → R) :
    (eigMat L t).map f = eigMat (fun k => (L k).map f) (fun k => f (t k)) := by
  ext ⟨k, i⟩ j
  by_cases h : i = j <;> simp [eigMat, Matrix.one_apply, h]

theorem eig_of_span {R OE : Type} [CommRing R] [CommRing OE] {d N : ℕ}
    (L : OE → Matrix (Fin d) (Fin d) R) (hL : ∀ a b, L (a + b) = L a + L b) (τ : OE →+* R)
    (g : Fin N → OE) (hg : Submodule.span ℤ (Set.range g) = ⊤) (v : Fin d → R)
    (hv : ∀ k, (L (g k)).mulVec v = τ (g k) • v) (a : OE) : (L a).mulVec v = τ a • v := by
  let L' : OE →+ Matrix (Fin d) (Fin d) R := AddMonoidHom.mk' L hL
  change (L' a).mulVec v = _
  have ha : a ∈ Submodule.span ℤ (Set.range g) := hg ▸ Submodule.mem_top
  induction ha using Submodule.span_induction with
  | mem x hx => obtain ⟨k, rfl⟩ := hx; exact hv k
  | zero => simp
  | add x y _ _ hx hy => simp [Matrix.add_mulVec, hx, hy, add_smul]
  | smul z x _ hx => rw [map_zsmul, map_zsmul, Matrix.smul_mulVec, hx, smul_assoc]

theorem linPart_map {R O : Type} [CommRing R] [CommRing O] (f : R →+* O) {d : ℕ}
    (φ : Fin d → PS R 1 d) :
    linPart (fun i => MvPowerSeries.map f (φ i)) = (linPart φ).map f := by
  ext i j
  simp [linPart, MvPowerSeries.coeff_map]

theorem isEigBasis_map : ∀ (R O : Type) [CommRing R] [CommRing O] [Algebra R O] [Module.Flat R O] (OE : Type) [CommRing OE] [Module.Finite ℤ OE] (d s : ℕ) (act : OE → Fin d → PS R 1 d), (∀ a b, linPart (act (a + b)) = linPart (act a) + linPart (act b)) → ∀ (τ : OE →+* R) (w : Fin s → Fin d → R), IsEigBasis act τ w → IsEigBasis (fun a i => MvPowerSeries.map (algebraMap R O) (act a i)) ((algebraMap R O).comp τ) (fun i j => algebraMap R O (w i j)) := by
  intro R O _ _ _ _ OE _ _ d s act hadd τ w hw
  obtain ⟨N, g, hg⟩ := Module.Finite.exists_fin (R := ℤ) (M := OE)
  have hadd' : ∀ a b, (linPart (act (a + b))).map (algebraMap R O) =
      (linPart (act a)).map (algebraMap R O) + (linPart (act b)).map (algebraMap R O) := by
    intro a b
    rw [hadd, Matrix.map_add _ (map_add _)]
  have hlin : ∀ (c : Fin s → R) a, (linPart (act a)).mulVec (∑ i, c i • w i) = τ a • ∑ i, c i • w i := by
    intro c a
    rw [Matrix.mulVec_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul, hw.1, smul_comm]
  have ex1 : Function.Exact (Matrix.of w).transpose.mulVec
      (eigMat (fun k => linPart (act (g k))) (fun k => τ (g k))).mulVec := by
    intro v
    rw [eigMat_mulVec_eq_zero]
    constructor
    · intro h
      obtain ⟨c, hc, -⟩ := hw.2 v (eig_of_span (fun a => linPart (act a)) hadd τ g hg v h)
      exact ⟨c, by rw [transpose_mulVec, hc]⟩
    · rintro ⟨c, rfl⟩ k
      rw [transpose_mulVec]; exact hlin c _
  have ex0 : Function.Exact (0 : Matrix (Fin s) (Fin 0) R).mulVec (Matrix.of w).transpose.mulVec := by
    intro c
    rw [transpose_mulVec]
    constructor
    · intro h
      obtain ⟨c0, -, hu⟩ := hw.2 0 (by simp)
      exact ⟨0, by rw [hu c h, ← hu 0 (by simp)]; simp⟩
    · rintro ⟨x, rfl⟩
      simp
  have ex1' := exact_mulVec_map (O := O) _ _ ex1
  have ex0' := exact_mulVec_map (O := O) _ _ ex0
  have hT : ((Matrix.of w).transpose.map (algebraMap R O)) =
      (Matrix.of fun i j => algebraMap R O (w i j)).transpose := rfl
  rw [hT] at ex1' ex0'
  rw [eigMat_map] at ex1'
  constructor
  · intro i a
    rw [linPart_map]
    ext j
    have := congrArg (algebraMap R O) (congrFun (hw.1 i a) j)
    simpa [Matrix.mulVec, dotProduct] using this
  · intro v hv
    simp only [linPart_map] at hv
    obtain ⟨c, hc⟩ := (ex1' v).1 ((eigMat_mulVec_eq_zero _ _ _).2 fun k => hv (g k))
    rw [transpose_mulVec] at hc
    refine ⟨c, hc, fun c' hc' => ?_⟩
    obtain ⟨x, hx⟩ := (ex0' (c' - c)).1 (by
      rw [Matrix.mulVec_sub, transpose_mulVec, transpose_mulVec]
      exact sub_eq_zero.2 (hc'.trans hc.symm))
    rw [← sub_eq_zero, ← hx]
    simp

end GlobalTheory.EigBaseChange
end

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem exists_chars_leading_minors_ge :
    ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (d s N : ℕ) (F : Fin d → PS O 2 d) (w : Fin s → Fin d → O), Function.Surjective (res w) → ∀ (u : Fin N → PS O 1 d), (∀ k, IsCh F (u k)) → ∀ c : O, c ≠ 0 → (∀ f : Fin d → O, c • f ∈ Submodule.span O (Set.range fun k => dl (u k))) → ∃ χ : Fin s → PS O 1 d, (∀ b, IsCh F (χ b)) ∧ ∀ i : Fin s, v (algebraMap O C c) ^ s ≤ v (algebraMap O C (Matrix.of fun a b : Fin (i.val + 1) => ∑ j, w (Fin.castLE i.isLt a) j * dl (χ (Fin.castLE i.isLt b)) j).det) := by
  intro C _ v O _ _ hv d s N F w hw u hu c hc hspan
  have hA : ∀ y : Fin s → O,
      c • y ∈ Submodule.span O (Set.range fun k => res w (dl (u k))) := by
    intro y
    obtain ⟨f, rfl⟩ := hw y
    have h1 : (Set.range fun k => res w (dl (u k))) = res w '' (Set.range fun k => dl (u k)) := by
      rw [← Set.range_comp]
      rfl
    rw [h1, ← Submodule.map_span, ← map_smul]
    exact Submodule.mem_map_of_mem (hspan f)
  obtain ⟨t, ht, hmin⟩ := GlobalTheory.exists_leading_minors_ge C v O hv s _ c hc hA
  choose k hk using ht
  refine ⟨fun b => u (k b), fun b => hu _, fun i => ?_⟩
  have hm : (Matrix.of fun a b : Fin (i.val + 1) =>
      ∑ j, w (Fin.castLE i.isLt a) j * dl (u (k (Fin.castLE i.isLt b))) j) =
      Matrix.of fun a b : Fin (i.val + 1) => t (Fin.castLE i.isLt b) (Fin.castLE i.isLt a) := by
    ext a b
    rw [Matrix.of_apply, Matrix.of_apply, ← hk]
    simp [res, Matrix.mulVec, dotProduct]
  rw [hm]
  exact (pow_le_pow_right_of_le_one' (hv.map_le_one c) i.isLt).trans (hmin i)

end GlobalTheory.CharDepth
end
