module

import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfEq
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle013
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle019
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
public import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle007
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPowSt

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.NuBox

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Generic

variable {X Y Y' Z : Scheme.{0}}

theorem lin_of_sval {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {s : LB.Sec (LB.LinComb L φ ε)} {n : ℕ} (b : Fin n → Γ(Y, ⊤)) (t : Fin n → LB.Sec (LB.LinComb L φ ε))
    (H : ∀ (y : Y) J, Good L y J → sval s (𝟙 Y) y J = ∑ i, gs (𝟙 Y) y ⊤ (b i) * sval (t i) (𝟙 Y) y J)
    (j : K → L.ι) :
    s.f j = ∑ i, resTop (LB.wchart L φ j) (b i) * (show Γ(Y, LB.wchart L φ j) from (t i).f j) := by
  apply GlobalTheory.IntegralCoord.lin_of_sval <;> assumption

theorem gs_one (r : Z ⟶ Y) (z : Z) : gs r z ⊤ (1 : Γ(Y, ⊤)) = 1 := by
  rw [gs_eq r z ⊤ trivial, map_one, map_one]

end Generic

theorem le_val_prod {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {T : Type} (S : Finset T)
    (a : T → F) (q : T → ℚ) (h : ∀ i, ((q i : ℚ) : WithTop ℚ) ≤ v (a i)) :
    ((∑ i ∈ S, q i : ℚ) : WithTop ℚ) ≤ v (∏ i ∈ S, a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert x S hx ih =>
    rw [Finset.sum_insert hx, Finset.prod_insert hx, v.map_mul, WithTop.coe_add]
    exact add_le_add (h x) ih



theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (j : ℕ) (D D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre D.toPre j) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (k : ℕ) (Fs : Fin j → Fam D.toPre F k) (F' : Fam D'.toPre F k), IsBoxFam pD F k F' Fs → ∀ r : Fin j → ℚ, (∀ i, NuGe D Q F v k (Fs i) (r i)) → NuGe D' (fun x => ∑ i, Q (pD.xe x i)) F v k F' (∑ i, r i) := by
  intro V _ _ _ ϖ hϖ j D D' pD Q hQ F _ _ v k Fs F' hB r hr
  unfold IsBoxFam at hB
  unfold NuGe at hr ⊢
  intro α'
  have hBα := hB α'
  clear hB
  obtain ⟨hφ, hB⟩ := hBα
  unfold VGe at hr ⊢
  choose n a σ σF hsc hv he using fun i => hr i (pD.xe α' i)
  clear hr
  have hM := D.toPre.P.isLB
  have hM' := D'.toPre.P.isLB

  choose σB hσB using fun m : (∀ i, Fin (n i)) =>
    exists_boxSec_val hM hM' pD.w pD.w_gen (D'.toPre.famφB α') (DegPre.famε k)
      (fun i => (pD.pw.pr i).left) (fun i => D.toPre.famφB (pD.xe α' i)) (famφB_pr pD α')
      (fun i => σ i (m i))

  choose σFB hσFB using fun m : (∀ i, Fin (n i)) =>
    exists_boxSec_val hM hM' pD.w pD.w_gen (D'.toPre.famφ F α') (DegPre.famε k)
      (prB pD F) (fun i => D.toPre.famφ F (pD.xe α' i)) hφ (fun i => σF i (m i))
  have hpr : ∀ i, (DegPre.prB D'.toPre F).left ≫ (pD.pw.pr i).left =
      prB pD F i ≫ (DegPre.prB D.toPre F).left := by
    intro i
    unfold prB
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    unfold DegPre.prB
    simp
  have hsc' : ∀ m : (∀ i, Fin (n i)), GeneratorPullback.SecScal D'.toPre.P.L (D'.toPre.famφ F α') (DegPre.famε k) (σFB m)
      (D'.toPre.famφB α') (DegPre.famε k) (σB m) (DegPre.prB D'.toPre F).left 1 := fun m =>
    BoxFamScalar.secScal_box hM hM' pD.w (GC.famφ_eq D'.toPre F α') hpr (σFB m) (fun i => σF i (m i)) (σB m)
      (fun i => σ i (m i))
      (fun y J J' hJ hJ' => hσFB m _ (𝟙 _) y J J' hJ hJ')
      (fun y J J' hJ hJ' => hσB m _ (DegPre.prB D'.toPre F).left y J J' hJ hJ')
      (fun _ => 1) 1 (fun y => by rw [Finset.prod_eq_one fun i _ => gs_one _ _, gs_one])
      (fun i => hsc i (m i))
  let e := Fintype.equivFin (∀ i, Fin (n i))
  refine ⟨Fintype.card (∀ i, Fin (n i)), fun l => ∏ i, a i (e.symm l i), fun l => σB (e.symm l),
    fun l => σFB (e.symm l), fun l => hsc' _, fun l => ?_, fun jM => ?_⟩
  · refine le_trans (le_of_eq ?_) (le_val_prod v Finset.univ _ _ fun i => hv i (e.symm l i))
    congr 1
    simp only [Finset.sum_add_distrib, Finset.sum_div, Int.cast_sum]
  ·
    have H : ∀ (y : (D'.toPre.BF F).left) (J' : ((D'.toPre.BF F).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι),
        Good D'.toPre.P.L y J' → sval (F'.s α') (𝟙 _) y J' =
          ∑ l, gs (𝟙 _) y ⊤ (((fst (TF (R := V) F) D'.toPre.P.A).left.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (∏ i, a i (e.symm l i)))) * sval (σFB (e.symm l)) (𝟙 _) y J' := by
      intro y J' hJ'
      obtain ⟨J, hJ, -⟩ := exists_good _ hM y (K := Empty) Empty.elim Empty.elim (fun x => x.elim)
        (fun x => x.elim)
      have hle : ∀ (jN : Fin 4 → Fin j → D.toPre.P.L.ι) (jM : Fin 4 → D'.toPre.P.L.ι) (i : Fin j),
          LB.wchart (LB.LinComb D.toPre.P.L (fun i => (pD.pw.pr i).left) (fun _ => 1)) (D'.toPre.famφ F α') jN ⊓
            LB.wchart D'.toPre.P.L (D'.toPre.famφ F α') jM ≤
              prB pD F i ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφ F (pD.xe α' i)) (fun a => jN a i) :=
        fun jN jM i => inf_le_left.trans (box_le_of_comp D.toPre.P.L (fun i => (pD.pw.pr i).left)
          (D'.toPre.famφ F α') (D.toPre.famφ F (pD.xe α' i)) (prB pD F i) i (hφ i) jN)
      have hF := BoxFamScalar.box_sval pD.w hφ (F'.s α') (fun i => (Fs i).s (pD.xe α' i)) hle hB (𝟙 _) y hJ hJ'
      have hfac : ∀ i, sval ((Fs i).s (pD.xe α' i)) (𝟙 _ ≫ prB pD F i) y J =
          ∑ l, gs (𝟙 _ ≫ prB pD F i) y ⊤ (((fst (TF (R := V) F) D.toPre.P.A).left.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (a i l))) * sval (σF i l) (𝟙 _ ≫ prB pD F i) y J := by
        intro i
        have hm := hJ.mem (D.toPre.famφ F (pD.xe α' i)) (𝟙 _ ≫ prB pD F i)
        unfold sval
        refine (congrArg (gs (𝟙 _ ≫ prB pD F i) y _) (he i _)).trans ?_
        refine (gs_fsum _ y _ hm _ _).trans (Finset.sum_congr rfl fun l _ => ?_)
        refine (gs_mul _ y _ hm _ _).trans ?_
        unfold DegPre.constBF
        exact congrArg (· * _) (gs_res _ y le_top hm _)
      have hcst : ∀ m : (∀ i, Fin (n i)), ∏ i, gs (𝟙 _ ≫ prB pD F i) y ⊤ (((fst (TF (R := V) F) D.toPre.P.A).left.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (a i (m i)))) =
          gs (𝟙 _) y ⊤ (((fst (TF (R := V) F) D'.toPre.P.A).left.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (∏ i, a i (m i)))) := by
        intro m
        refine BoxFamScalar.gs_scal_prod (fst (TF (R := V) F) D.toPre.P.A).left
          (fst (TF (R := V) F) D'.toPre.P.A).left (prB pD F) (fun i => ?_) y (fun i => a i (m i))
        unfold prB
        rw [← Over.comp_left]
        simp
      refine (Units.mul_right_inj (∏ a, bw pD.w (𝟙 _ ≫ D'.toPre.famφ F α' a) y (fun i => J ((𝟙 _ ≫ D'.toPre.famφ F α' a) ≫ (pD.pw.pr i).left)) (J' (𝟙 _ ≫ D'.toPre.famφ F α' a)) ^ DegPre.famε k a)).1 ?_
      refine hF.trans ?_
      rw [Finset.mul_sum]
      simp only [hfac]
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
      rw [Equiv.sum_comp e.symm (fun m => ((∏ a, bw pD.w (𝟙 _ ≫ D'.toPre.famφ F α' a) y (fun i => J ((𝟙 _ ≫ D'.toPre.famφ F α' a) ≫ (pD.pw.pr i).left)) (J' (𝟙 _ ≫ D'.toPre.famφ F α' a)) ^ DegPre.famε k a) : _) * (gs (𝟙 _) y ⊤ (((fst (TF (R := V) F) D'.toPre.P.A).left.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (∏ i, a i (m i)))) * sval (σFB m) (𝟙 _) y J'))]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.prod_mul_distrib, hcst m, ← hσFB m _ (𝟙 _) y J J' hJ hJ']
      ring
    have key := lin_of_sval hM' _ (fun l => σFB (e.symm l)) H jM
    unfold resTop at key
    unfold DegPre.constBF
    exact key

end GlobalTheory.NuBox
end
end

section

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PlaceInt.LocBasis
open NumberField Module
open scoped nonZeroDivisors

theorem exists_basis_up_to {O A E : Type} [CommRing O] [CommRing A] [IsDomain A] [Field E] [Algebra O A] [Algebra A E]
    [Algebra O E] [IsScalarTower O A E] (S : Submonoid O) [IsLocalization S A] [IsFractionRing A E]
    [IsPrincipalIdealRing A] {n : ℕ} (L : Submodule O (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ (s : S) (b : Fin n → Fin n → E), LinearIndependent E b ∧ (∀ i, b i ∈ L) ∧
      ∀ w ∈ L, (s : O) • w ∈ Submodule.span O (Set.range b) := by
  classical
  set M : Submodule A (Fin n → E) := Submodule.span A (L : Set (Fin n → E)) with hM
  have : Submodule.IsFullLattice E M :=
    { toIsLattice := Submodule.IsLattice.of_fg E <| by
        obtain ⟨s, hs⟩ := hfg
        refine ⟨s, ?_⟩
        rw [hM, ← hs, Submodule.span_span_of_tower]
      span_eq_top := by rw [hM, Submodule.span_span_of_tower, hsp] }
  have hrk : Module.finrank A M = n := by
    simpa using ((Submodule.IsFullLattice.finrank_eq E M).trans (Module.finrank_fintype_fun_eq_card E))
  haveI : Module.Finite A M := Submodule.IsLattice.finite E M
  let c : Basis (Fin n) A M := Module.finBasisOfFinrankEq A M hrk
  have hc : ∀ i, ∃ t : S, (t : O) • (c i : Fin n → E) ∈ L := fun i => by
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span S A (L : Set (Fin n → E)) _ (c i).2
    rw [Submodule.span_eq] at ht
    exact ⟨t, ht⟩
  choose t ht using hc
  let u : Fin n → Aˣ := fun i => (IsLocalization.map_units A (t i)).unit
  let c' : Basis (Fin n) A M := c.unitsSMul u
  have hc' : ∀ i, (c' i : Fin n → E) = (t i : O) • (c i : Fin n → E) := fun i => by
    simp only [c', Basis.unitsSMul_apply, u, Units.smul_def, IsUnit.unit_spec, algebraMap_smul,
      Submodule.coe_smul_of_tower]
  let b : Fin n → Fin n → E := fun i => (c' i : Fin n → E)
  have hli : LinearIndependent E b := by
    have h : b = c'.extendOfIsFullLattice E := funext fun i => by simp [b]
    rw [h]
    exact (c'.extendOfIsFullLattice E).linearIndependent
  have hspanA : Submodule.span A (Set.range b) = M := by
    have : Set.range b = M.subtype '' Set.range c' := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, c'.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hw : ∀ w ∈ L, ∃ r : S, (r : O) • w ∈ Submodule.span O (Set.range b) := fun w hw => by
    obtain ⟨r, hr⟩ := multiple_mem_span_of_mem_localization_span S A (Set.range b) w
      (hspanA ▸ Submodule.subset_span hw)
    exact ⟨r, hr⟩
  obtain ⟨G, hG⟩ := hfg
  choose! r hr using hw
  refine ⟨∏ x ∈ G, r x, b, hli, fun i => by simpa only [b, hc'] using ht i, fun w hw => ?_⟩
  rw [← hG] at hw
  induction hw using Submodule.span_induction with
  | mem y hy =>
    have hy' : y ∈ G := hy
    rw [← Finset.prod_erase_mul G r hy', Submonoid.coe_mul, mul_smul]
    exact Submodule.smul_mem _ _ (hr y (hG ▸ Submodule.subset_span hy))
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ _ hy

def primeTo (R : Type) [CommRing R] (m : ℕ) : Submonoid R where
  carrier := {x | ∃ k : ℕ, k ≠ 0 ∧ Nat.Coprime k m ∧ x = (k : R)}
  one_mem' := ⟨1, one_ne_zero, Nat.coprime_one_left m, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha0, ha, rfl⟩ ⟨b, hb0, hb, rfl⟩
    exact ⟨a * b, mul_ne_zero ha0 hb0, Nat.Coprime.mul_left ha hb, by simp⟩

theorem exists_prime_mem {R : Type} [CommRing R] (Q : Ideal R) (hQ : Q.IsPrime) (a : ℕ) (ha : a ≠ 0)
    (h : (a : R) ∈ Q) : ∃ p : ℕ, p.Prime ∧ (p : R) ∈ Q := by
  induction a using induction_on_primes with
  | zero => exact absurd rfl ha
  | one => exact absurd ((Ideal.eq_top_iff_one Q).2 (by simpa using h)) hQ.ne_top
  | prime_mul p a hp ih =>
    rw [Nat.cast_mul] at h
    rcases hQ.mem_or_mem h with h | h
    · exact ⟨p, hp, h⟩
    · exact ih (by rintro rfl; simp at ha) h

theorem isPrincipalIdealRing_loc (E : Type) [Field E] [NumberField E] (m : ℕ) (hm : 0 < m)
    (hS : primeTo (𝓞 E) m ≤ (𝓞 E)⁰) (A : Type) [CommRing A] [IsDomain A] [Algebra (𝓞 E) A]
    [IsLocalization (primeTo (𝓞 E) m) A] : IsPrincipalIdealRing A := by
  have : IsDedekindDomain A := IsLocalization.isDedekindDomain (𝓞 E) hS A
  have hinj : Function.Injective (algebraMap (𝓞 E) A) := IsLocalization.injective A hS
  have hm0 : (m : A) ≠ 0 := by
    rw [← map_natCast (algebraMap (𝓞 E) A), map_ne_zero_iff _ hinj]
    exact_mod_cast hm.ne'
  have hI : (Ideal.span {(m : A)}) ≠ 0 := by simpa using hm0
  apply IsPrincipalIdealRing.of_finite_primes
  apply (((Ideal.finite_factors hI).image (fun v => v.asIdeal)).insert ⊥).subset
  intro P hP
  have hP' : P.IsPrime := hP
  by_cases hb : P = ⊥
  · exact Or.inl hb
  refine Or.inr ⟨⟨P, hP', hb⟩, ?_, rfl⟩
  set Q := P.comap (algebraMap (𝓞 E) A) with hQ
  have hQb : Q ≠ ⊥ := by
    intro h
    apply hb
    rw [← IsLocalization.map_under (primeTo (𝓞 E) m) A P]
    change Q.map _ = ⊥
    rw [h, Ideal.map_bot]
  have h1 : ((Ideal.absNorm Q : ℕ) : A) ∈ P := by
    have := Ideal.absNorm_mem Q
    rw [hQ, Ideal.mem_comap, map_natCast] at this
    exact this
  obtain ⟨p, hp, hpP⟩ := exists_prime_mem P hP' _ (by rwa [Ne, Ideal.absNorm_eq_zero_iff]) h1
  have hpm : p ∣ m := by
    by_contra hn
    have hu := IsLocalization.map_units A (⟨(p : 𝓞 E), p, hp.ne_zero, (Nat.Prime.coprime_iff_not_dvd hp).2 hn,
      rfl⟩ : primeTo (𝓞 E) m)
    simp only [map_natCast] at hu
    exact hP'.ne_top (Ideal.eq_top_of_isUnit_mem _ hpP hu)
  obtain ⟨c, rfl⟩ := hpm
  simp only [Set.mem_setOf_eq, Ideal.dvd_span_singleton, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hpP

end GlobalTheory.PlaceInt.LocBasis

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt.LocBasis

theorem exists_matrix_primeTo : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (N : ℕ), 0 < N → L ≤ stdLat E n → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ L → ∀ m : ℕ, 0 < m → ∃ (k₁ : ℕ) (g : Matrix (Fin n) (Fin n) (𝓞 E)), Nat.Coprime k₁ m ∧ g.det ≠ 0 ∧ (∀ v ∈ stdLat E n, (g.map (algebraMap (𝓞 E) E)).mulVec v ∈ L) ∧ ∀ w ∈ L, ∃ v ∈ stdLat E n, (k₁ : E) • w = (g.map (algebraMap (𝓞 E) E)).mulVec v := by
  intro E _ _ n L N hN hle hNL m hm
  classical
  have hmem : ∀ v : Fin n → E, v ∈ stdLat E n ↔ ∃ u : Fin n → 𝓞 E, v = fun i => algebraMap (𝓞 E) E (u i) := fun v => by
    simp only [stdLat, Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]
    constructor
    · intro h
      choose u hu using h
      exact ⟨u, funext fun i => (hu i).symm⟩
    · rintro ⟨u, rfl⟩ i
      exact ⟨u i, rfl⟩
  have hS : primeTo (𝓞 E) m ≤ nonZeroDivisors (𝓞 E) := by
    rintro _ ⟨k, hk, -, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk)
  let A := Localization.subalgebra E (primeTo (𝓞 E) m) hS
  have : IsPrincipalIdealRing A := isPrincipalIdealRing_loc E m hm hS A
  have hstd : (stdLat E n).FG := Submodule.fg_pi fun _ => by
    rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  have hfg : L.FG := hstd.of_le hle
  have hN0 : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h1 : (Pi.basisFun E (Fin n) i) ∈ stdLat E n :=
      (hmem _).2 ⟨Pi.single i 1, funext fun j => by by_cases h : j = i <;> simp [h, Pi.single_apply]⟩
    have h2 := hNL (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (N : 𝓞 E)) h1)
    have h3 := Submodule.smul_mem (Submodule.span E (L : Set (Fin n → E))) (N : E)⁻¹ (Submodule.subset_span h2)
    rwa [← algebraMap_smul E (N : 𝓞 E), smul_smul, map_natCast, inv_mul_cancel₀ hN0, one_smul] at h3
  obtain ⟨⟨_, k, hk0, hk, rfl⟩, b, hli, hb, hw⟩ := exists_basis_up_to (A := A) (primeTo (𝓞 E) m) L hfg hsp
  choose u hu using fun j => (hmem (b j)).1 (hle (hb j))
  let g : Matrix (Fin n) (Fin n) (𝓞 E) := Matrix.of fun i j => u j i
  have hg : ∀ a : Fin n → 𝓞 E, (g.map (algebraMap (𝓞 E) E)).mulVec (fun i => algebraMap (𝓞 E) E (a i)) =
      ∑ j, a j • b j := fun a => by
    funext i
    simp only [Matrix.mulVec, dotProduct, g, Matrix.map_apply, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hu j, Algebra.smul_def, mul_comm]
  refine ⟨k, g, hk, ?_, ?_, ?_⟩
  · have hcol : (g.map (algebraMap (𝓞 E) E)).col = b := by
      funext j i
      rw [hu j]; rfl
    have hunit : IsUnit (g.map (algebraMap (𝓞 E) E)) :=
      Matrix.linearIndependent_cols_iff_isUnit.1 (hcol ▸ hli)
    intro h0
    have := ((Matrix.isUnit_iff_isUnit_det _).1 hunit).ne_zero
    apply this
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  · intro v hv
    obtain ⟨a, rfl⟩ := (hmem v).1 hv
    rw [hg]
    exact Submodule.sum_mem _ fun j _ => L.smul_mem _ (hb j)
  · intro w hwL
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hw w hwL)
    refine ⟨_, (hmem _).2 ⟨a, rfl⟩, ?_⟩
    rw [hg, ha]
    change _ = (k : 𝓞 E) • w
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
end GlobalTheory.PlaceInt.LocBasis
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.expansion_of_integral_section_is_integral : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (k : ℕ) (σ : H0 U.LG.L k) (s : U.SecK k), GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => ((k : ℕ) : ℤ)) s (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((k : ℕ) : ℤ)) σ (pullback.fst G.hom (jK V)) 1 → ∀ E : Fam D.toPre (FractionRing V) k, U.Expands k s E → ∃ g : ∀ α : D.toPre.X, D.toPre.SecB k α, (∀ e, U.ExpandsAt e k σ g) ∧ ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) (E.s α) (D.toPre.famφB α) (DegPre.famε k) (g α) (DegPre.prB D.toPre (FractionRing V)).left 1 := by
  first | exact @GlobalTheory.ExpInt.main | exact GlobalTheory.ExpInt.main | (intros; apply GlobalTheory.ExpInt.main <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.value_at_unitSection_genericFibre : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (k : ℕ) (s : P.U.SecK k) (F : Fam P.D.toPre (FractionRing V) k) (u : P.U.SecK (k * N)) (F' : Fam P.D.toPre (FractionRing V) (k * N)), P.U.Expands k s F → P.U.Expands (k * N) u F' → PullAl P.D (FractionRing V) P.oD a k N F F' → ∀ (y : Spec (CommRingCat.of (FractionRing V))) (J), Geo.Tor.Good P.U.LG.L y J → Geo.Tor.sval u unitK y J = (Geo.Tor.val (L := P.U.LG.L) P.U.LG.rig (jK V) y J ^ (k * (N - 1))).val * Geo.Tor.sval s unitK y J := by
  first | exact @GlobalTheory.GenericUnitValue.value_at_generic_unit | exact GlobalTheory.GenericUnitValue.value_at_generic_unit | (intros; apply GlobalTheory.GenericUnitValue.value_at_generic_unit <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ExpFun

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.ExpInt

theorem cross_eq {V : Type} [CommRing V] [IsDomain V] (G : Over (Spec (CommRingCat.of V))) [Flat G.hom]
    {L : LB G.left} (hL : L.IsLB) (k : ℕ) (σ σ' ρ ρ' : H0 L k)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ)))) (r r' : V)
    (h : GeneratorPullback.SecScal L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ)) s (fun _ : Fin 1 => 𝟙 G.left)
      (fun _ => (k : ℤ)) σ (pullback.fst G.hom (jK V)) (scal (pullback.snd G.hom (jK V) ≫ jK V) r))
    (h' : GeneratorPullback.SecScal L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ)) s (fun _ : Fin 1 => 𝟙 G.left)
      (fun _ => (k : ℤ)) σ' (pullback.fst G.hom (jK V)) (scal (pullback.snd G.hom (jK V) ≫ jK V) r'))
    (hρ : SecIsMul G.hom r' ρ σ) (hρ' : SecIsMul G.hom r ρ' σ') : ρ = ρ' := by
  refine SecOps.sec_ext fun j => generic_app_injective G _ (fn_ext fun y hy => ?_)
  obtain ⟨J, hJ, e⟩ := exists_good L hL y (fun _ : Unit => (𝟙 _ ≫ pullback.fst G.hom (jK V)) ≫ 𝟙 G.left)
    (fun _ => j 0) (fun _ _ _ => rfl) (fun _ => Set.mem_iInter.1 hy 0)
  have ej : ∀ a : Fin 1, J ((𝟙 _ ≫ pullback.fst G.hom (jK V)) ≫ 𝟙 G.left) = j a := fun a => by
    rw [Subsingleton.elim a 0]; exact e ()
  have e₁ := secScal_sval h (𝟙 _) y hJ
  have e₂ := secScal_sval h' (𝟙 _) y hJ
  rw [sval_of σ _ y J j ej, gs_scal, ← pullback.condition, ← Category.assoc] at e₁
  rw [sval_of σ' _ y J j ej, gs_scal, ← pullback.condition, ← Category.assoc] at e₂
  refine (gs_pull (𝟙 _) _ y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 _) _ y _ hy _).symm)
  refine (secIsMul_gs hρ _ y j hy).trans (Eq.trans ?_ (secIsMul_gs hρ' _ y j hy).symm)
  exact (congrArg _ e₁).trans ((mul_left_comm _ _ _).trans (congrArg _ e₂).symm)

theorem main : lemmaBSt.{0} → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (k : ℕ) (s : U.SecK k) (E E' : Fam D.toPre (FractionRing V) k), U.Expands k s E → U.Expands k s E' → E = E' := by
  intro hB V _ _ _ D A G _ _ U k s E E' hE hE'
  obtain ⟨r, hr, σ, f, h, hf, hx⟩ := hE
  obtain ⟨r', hr', σ', f', h', hf', hx'⟩ := hE'
  have := U.smooth
  have : Flat G.hom := inferInstance
  obtain ⟨ρ, hρ⟩ := exists_secIsMul (p := G.hom) r' σ
  obtain ⟨ρ', hρ'⟩ := exists_secIsMul (p := G.hom) r σ'
  choose g hg using fun α => exists_secIsMul (p := D.toPre.P.A.hom) r' (f α)
  choose g' hg' using fun α => exists_secIsMul (p := D.toPre.P.A.hom) r (f' α)
  obtain rfl : ρ = ρ' := cross_eq G U.LG.isLB k σ σ' ρ ρ' s r r' h h' hρ hρ'
  obtain rfl : g = g' := GlobalTheory.ExpUniq.main hB V D A G U k ρ g g'
    (fun e => expandsAt_secIsMul V _ D A G U e k _ σ ρ f g hρ hg (hx e))
    (fun e => expandsAt_secIsMul V _ D A G U e k _ σ' ρ f' g' hρ' hg' (hx' e))
  refine fam_ext fun α j => sec_ext_val D.toPre.P.isLB (fun y J hJ => ?_) j
  have e₁ := secScal_sval (hf α) (𝟙 _) y hJ
  have e₁' := secScal_sval (hf' α) (𝟙 _) y hJ
  have e₂ : sval (g α) (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) y J = _ *
      sval (f α) (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) y J :=
    secIsMul_gs (hg α) _ y _ (hJ.mem _ _)
  have e₂' : sval (g α) (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) y J = _ *
      sval (f' α) (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) y J :=
    secIsMul_gs (hg' α) _ y _ (hJ.mem _ _)
  rw [Category.assoc, Over.w] at e₂ e₂'
  rw [gs_scal] at e₁ e₁'
  rw [e₁] at e₂
  rw [e₁', e₂, mul_left_comm] at e₂'
  have e₃ : 𝟙 _ ≫ (DegPre.BF D.toPre (FractionRing V)).hom =
      ((fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left ≫ jFK (R := V) (FractionRing V)) ≫ jK V := by
    rw [Category.id_comp, Category.assoc]
    exact (Over.w (fst (TF (R := V) (FractionRing V)) D.toPre.P.A)).symm
  rw [e₃] at e₂'
  exact (IsUnit.mul_right_inj (isUnit_cst _ y hr')).1 ((IsUnit.mul_right_inj (isUnit_cst _ y hr)).1 e₂')

end GlobalTheory.ExpFun
end
