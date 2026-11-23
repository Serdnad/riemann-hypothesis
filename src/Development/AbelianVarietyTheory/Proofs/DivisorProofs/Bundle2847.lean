module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle777
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle048
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PrimitiveCocycle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle071
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle984
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2748
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2667

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two

open GlobalTheory.PullPair LBGerm GlobalTheory.AbLaw

def chartPullTwJ {X₁ X₂ : Scheme.{0}} (M₁ : LB X₁) (M₂ : LB X₂) (f : X₁ ⟶ X₂) (e : ℤ) (n t : ℕ) :
    ChartPull (LB.LinComb (join M₁ M₂) (K := Fin 2) ![f ≫ coprod.inr, coprod.inl] ![e, ((n * t : ℕ) : ℤ)])
      (tw (LB.LinComb (join M₁ M₂) (fun _ : PUnit => f ≫ coprod.inr) (fun _ => e)) (lbPow M₁ n) t) (𝟙 X₁) where
  idx J := (fun _ => J 0, fun _ => (J 1).1)
  le J y hy := ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0,
    Set.mem_iInter.2 fun _ => ((isPart_inl M₁ M₂).mem _ _).1 (Set.mem_iInter.1 hy 1)⟩
  g y J J' hJ hJ' := by
    have P := isPart_inl M₁ M₂
    have a₀ : (𝟙 X₁ : X₁ ⟶ X₁) y ∈ LB.wchart (join M₁ M₂) (fun _ : PUnit => f ≫ coprod.inr) (fun _ => J 0) :=
      Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hJ 0
    have a₁ : (𝟙 X₁ : X₁ ⟶ X₁) y ∈ powChart M₁ (fun _ => (J 1).1) :=
      Set.mem_iInter.2 fun _ => (P.mem _ _).1 (Set.mem_iInter.1 hJ 1)
    have b₀ : (𝟙 X₁ : X₁ ⟶ X₁) y ∈ LB.wchart (join M₁ M₂) (fun _ : PUnit => f ≫ coprod.inr) (fun _ => J' 0) :=
      Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hJ' 0
    have b₁ : (𝟙 X₁ : X₁ ⟶ X₁) y ∈ powChart M₁ (fun _ => (J' 1).1) :=
      Set.mem_iInter.2 fun _ => (P.mem _ _).1 (Set.mem_iInter.1 hJ' 1)
    have hg := P.g _ (𝟙 X₁) y (J 1) (J' 1) ((P.mem _ _).1 (Set.mem_iInter.1 hJ 1)) ((P.mem _ _).1 (Set.mem_iInter.1 hJ' 1))
    refine (gm_linComb (join M₁ M₂) _ _ (𝟙 X₁) y J J' hJ hJ').trans (Units.ext (Eq.symm ?_))
    refine (TwistGen.gm_tw_g (LB.LinComb (join M₁ M₂) (fun _ : PUnit => f ≫ coprod.inr) (fun _ => e)) (lbPow M₁ n) t y
      (fun _ => J 0, fun _ => (J 1).1) (fun _ => J' 0, fun _ => (J' 1).1) ⟨a₀, a₁⟩ ⟨b₀, b₁⟩).trans ?_
    rw [gm_lbPow_g n (𝟙 X₁) y _ _ a₁ b₁, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
    refine congrArg Units.val ((congrArg (· * _) (gm_linComb _ _ _ (𝟙 X₁) y _ _ a₀ b₀)).trans ?_)
    rw [Fintype.prod_unique, Fin.prod_univ_two, ← pow_mul, ← zpow_natCast]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.id_comp] at hg ⊢
    rw [hg]

theorem exists_sec_twist_join {X₁ X₂ : Scheme.{0}} {M₁ : LB X₁} {M₂ : LB X₂} (h : IsAmpleLB M₁) (h₂ : M₂.IsLB)
    [Nonempty X₁] [Nonempty X₂] (f : X₁ ⟶ X₂) (e : ℤ) (k : ℕ) (hk : 1 ≤ k) (y : X₁) :
    ∃ n, 1 ≤ n ∧ ∃ u : LB.Sec (LB.LinComb (join M₁ M₂) (K := Fin 2) ![f ≫ coprod.inr, coprod.inl] ![e, ((k * n : ℕ) : ℤ)]),
      y ∈ nonzeroLocus u := by
  have := h.compactSpace
  have := h.quasiSeparatedSpace
  have hL := h.isLB
  have hN := join_isLB hL h₂
  obtain ⟨m, hm, s, hs, -, ha⟩ := h.exists_affine_le (x := y) (U := ⊤) trivial
  obtain ⟨V, N, hV, H⟩ := TwistGen.exists_nhds
    (M := LB.LinComb (join M₁ M₂) (fun _ : PUnit => f ≫ coprod.inr) (fun _ => e))
    (LB.isLB_linComb hN _ _) (isLB_lbPow hL m) s ha y hs
  obtain ⟨d, hd⟩ : ∃ d, k * (N + 1) = N + d := Nat.exists_eq_add_of_le (by nlinarith)
  obtain ⟨u, hu⟩ := H d
  refine ⟨m * (N + 1), Nat.mul_pos hm (Nat.succ_pos N), ?_⟩
  rw [show k * (m * (N + 1)) = m * (N + d) by rw [← hd]; ring]
  refine ⟨chartSec (chartPullTwJ M₁ M₂ f e m (N + d)) u, ?_⟩
  rw [nonzeroLocus_chartSec_id _ u fun x _ _ => exists_chart (LB.isLB_linComb hN _ _) x]
  exact hu hV

theorem exists_crossH : ∀ (R : Type) [CommRing R] [IsDomain R] (A₁ A₂ : PolAV (Sp (FractionRing R))) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (c : A₁.A ⟶ A₂.A), IsMonHom c → ∀ (j k : ℕ), 1 ≤ k → ∃ n, 1 ≤ n ∧
      ∀ t₁ t₂ : SecA A₂ F j, ∃ t₁' t₂' : SecA A₁ F (k * n), CrossH c t₁ t₂ t₁' t₂' ∧
        ((∀ z J, Good A₂.L z J → sA t₂ (ptSecT A₂.A 1).left z J ≠ 0) →
          (∀ z J, Good A₁.L z J → sA t₂' (ptSecT A₁.A 1).left z J ≠ 0)) := by
  intro R _ _ A₁ A₂ F _ _ c hc j k hk
  have hL₁ := A₁.isLB
  have hL₂ := A₂.isLB
  let T : Over (Sp (FractionRing R)) := TFK (R := R) F
  have hsub : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  let z₀ : T.left := (⊥ : PrimeSpectrum F)
  have P₁ := isPart_inl A₁.L A₂.L
  have P₂ := isPart_inr A₁.L A₂.L
  have hN := join_isLB hL₁ hL₂
  obtain ⟨n, hn, u, hu⟩ := exists_sec_twist_join (isAmpleLB_of_relAmple_of_isAffine A₁.A hL₁ A₁.ample) hL₂ c.left
    (-(j : ℤ)) k hk (((ptSecT A₁.A (1 : T ⟶ A₁.A)).left ≫ (snd T A₁.A).left) z₀)
  have key : ∀ t : SecA A₂ F j, ∃ t' : SecA A₁ F (k * n), ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A₁.A).left) (z : Z) (J),
      Good (join A₁.L A₂.L) z J →
        sA t' r z (rl J) = sA t (r ≫ (T ◁ c).left) z (rr J) * sval u (r ≫ (snd T A₁.A).left) z J := by
    intro t
    have e : (T ◁ c).left ≫ (snd T A₂.A).left ≫ (coprod.inr : A₂.A.left ⟶ A₁.A.left ⨿ A₂.A.left) =
        (snd T A₁.A).left ≫ c.left ≫ (coprod.inr : A₂.A.left ⟶ A₁.A.left ⨿ A₂.A.left) := by
      rw [← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
    let tN := P₂.sec (φ := fun _ : Fin 1 => (snd T A₂.A).left) (ε := fun _ => (j : ℤ)) t
    obtain ⟨s, hs⟩ := exists_sec hN (φ' := fun _ : Fin 1 => (snd T A₁.A).left ≫ coprod.inl)
      (ε' := fun _ => ((k * n : ℕ) : ℤ))
      (fun U _ h => by
        simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
          Matrix.cons_val_zero, Matrix.cons_val_one, e, zpow_neg, mul_inv_cancel_left])
      (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.pullSec tN (T ◁ c).left) (H1.SectionArithmetic.pullSec u (snd T A₁.A).left))
    obtain ⟨t', ht'⟩ := P₁.exists_sec (φ := fun _ : Fin 1 => (snd T A₁.A).left) (ε := fun _ => ((k * n : ℕ) : ℤ)) hL₁
      (fst_surjective hL₂) s
    refine ⟨t', fun Z r z J hJ => (ht' Z r z J hJ).trans ((hs Z r z J hJ).trans ?_)⟩
    refine (H1.SectionArithmetic.sval_mulSec _ _ r z hJ).trans (congrArg₂ (· * ·) ?_ (H1.SectionArithmetic.sval_pullSec _ _ r z hJ))
    exact (H1.SectionArithmetic.sval_pullSec _ _ r z hJ).trans (P₂.sval_sec _ _ z hJ)
  refine ⟨n, hn, fun t₁ t₂ => ?_⟩
  obtain ⟨t₁', h₁⟩ := key t₁
  obtain ⟨t₂', h₂⟩ := key t₂
  refine ⟨t₁', t₂', fun z J₁ J₂ g₁ g₂ => ?_, fun h z J₁ g₁ => ?_⟩
  · obtain ⟨J, hJ, rfl, rfl⟩ := exists_good_join hL₁ hL₂ g₁ g₂
    rw [h₁ _ _ z J hJ, h₂ _ _ z J hJ, Category.id_comp]
    ring
  · choose d hd using fun ψ : T.left ⟶ A₂.A.left => exists_chart hL₂ (ψ z)
    obtain ⟨J, hJ, rfl, hr⟩ := exists_good_join hL₁ hL₂ g₁ (J₂ := d) hd
    have e : (ptSecT A₁.A (1 : T ⟶ A₁.A)).left ≫ (T ◁ c).left = (ptSecT A₂.A (1 : T ⟶ A₂.A)).left := by
      rw [← Over.comp_left, ptSecT, ptSecT, lift_whiskerLeft, MonObj.one_comp]
    rw [h₂ _ _ z J hJ, e]
    obtain rfl : z₀ = z := Subsingleton.elim _ _
    have hU : IsUnit (sval u ((ptSecT A₁.A (1 : T ⟶ A₁.A)).left ≫ (snd T A₁.A).left) z₀ J) :=
      (mem_nonzeroLocus_iff_pull u _ z₀ (hJ.mem _ _)).1 hu
    have g₂ : Good A₂.L z₀ (rr J) := hr ▸ hd
    exact fun h0 => h z₀ (rr J) g₂ (hU.mul_left_eq_zero.1 h0)

end GlobalTheory.Mum.Two
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two

theorem lam_eq_ros_mul_cmp : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ D' : DegPre R) (inc : D₀.P.A ⟶ D'.P.A) (pr : D'.P.A ⟶ D₀.P.A) [IsMonHom inc] [IsMonHom pr] (ea fa ea' : D'.P.A ⟶ D'.P.A) [IsMonHom ea] [IsMonHom fa] [IsMonHom ea'], pr ≫ inc = ea → ∀ (w : LB.Iso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ D'.P.A D'.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ inc) (snd D₀.P.A D₀.P.A ≫ inc ≫ fa) : G2 D₀.P.A ⟶ G2 D'.P.A).left)), w.IsGen → (∀ (T : Over (Sp R)) (y : T ⟶ D₀.P.A) (z : T.left) (J : (T.left ⟶ D'.P.A.left) → D'.P.L.ι) (J' : (T.left ⟶ D₀.P.A.left) → D₀.P.L.ι), Good D'.P.L z J → Good D₀.P.L z J' → GlobalTheory.PolDeg.lamVal w (lift (1 : T ⟶ D₀.P.A) y).left z J J' = 1) → ∀ (ur : LB.Gen (LB.LinComb D'.P.L (rosatiφ D'.P.A ea ea') rosatiε)), ur.IsGen → (∀ (T : Over (Sp R)) (y : T ⟶ D'.P.A) (z : T.left) (J : (T.left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val ur (lift (1 : T ⟶ D'.P.A) y).left z J = 1) → ∀ (χ' : D'.X) (χ : D₀.X) (q : 𝟙_ (Over (Sp R)) ⟶ D'.P.A), D₀.c χ ≫ inc ≫ fa = q → D'.c χ' = q ≫ ea' → ∀ (u : LB.Gen (CmpLB D' D₀ pr χ' χ)), Nrm u → ∀ (T : Over (Sp R)) (x : T ⟶ D'.P.A) (z : T.left) (J : (T.left ⟶ (D'.P.A.left ⨿ D₀.P.A.left : Scheme.{0})) → (JN D' D₀).ι), Good (JN D' D₀) z J → GlobalTheory.PolDeg.lamVal w (lift (x ≫ pr) (toUnit T ≫ D₀.c χ)).left z (rl J) (rr J) = val ur (lift x (toUnit T ≫ q)).left z (rl J) * val u x.left z J := by
  intro R _ _ D₀ D' inc pr _ _ ea fa ea' _ _ _ hea w hw hw1 ur hur hur1 χ' χ q hq hq' u hu T x z J hJ
  have hN : (JN D' D₀).IsLB := jn_isLB D' D₀
  have h₁ := isPart_inl D'.P.L D₀.P.L
  have h₂ := isPart_inr D'.P.L D₀.P.L
  obtain ⟨t, ht, htv⟩ := exists_gen_of_iso h₁ h₂ w hw
  let m : D'.P.A.left ⟶ (G2 D₀.P.A).left := (lift pr (toUnit _ ≫ D₀.c χ)).left
  let n : D'.P.A.left ⟶ (G2 D'.P.A).left := (lift (𝟙 _) (toUnit _ ≫ q)).left
  let t₁ := LB.pullGen _ _ _ t m
  let t₂ := LB.mulGen _ _ _ _ _ (h₁.gen (LB.pullGen _ _ _ ur n)) u
  have hG := GlobalTheory.globalFns_holds
  have key := gen_unique' hN (u := t₁) (u' := t₂) ?fe D'.P.A.hom (eSec D'.P.A) (Over.w η[D'.P.A]) (hG _ _ D'.P.isAb).2
    (DVR.pullGen_isGen _ _ _ _ ht m) (DVR.mulGen_isGen _ _ _ _ _ _ _ (h₁.gen_isGen (DVR.pullGen_isGen _ _ _ _ hur n)) hu.1)
    ?ev T.left x.left z J hJ
  · have e₁ : x.left ≫ m = (lift (x ≫ pr) (toUnit T ≫ D₀.c χ)).left := by
      rw [← Over.comp_left, comp_lift, ← Category.assoc, toUnit_unique (x ≫ toUnit _) (toUnit T)]
    have e₂ : x.left ≫ n = (lift x (toUnit T ≫ q)).left := by
      rw [← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc, toUnit_unique (x ≫ toUnit _) (toUnit T)]
    rw [val_pull hJ, htv _ _ z J hJ, val_mul hJ, h₁.val_gen _ _ z hJ, val_pull (h₁.good hJ), e₁, e₂] at key
    exact key
  case fe =>
    intro U _ h
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    have mβ : m ≫ (lift (fst D₀.P.A D₀.P.A ≫ inc) (snd D₀.P.A D₀.P.A ≫ inc ≫ fa)).left =
        (lift ea (toUnit _ ≫ q)).left := by
      rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, hea, Category.assoc, hq]
    have A1 : ∏ a₁ : ULift (Finset (Fin 2)), h (m ≫ (lift (fst D₀.P.A D₀.P.A ≫ inc) (snd D₀.P.A D₀.P.A ≫ inc ≫ fa)).left ≫
        (psum D'.P.A (x2 D'.P.A) a₁.down).left ≫ coprod.inl) ^ ((-1 : ℤ) ^ (2 - a₁.down.card)) =
        h ((ea * (toUnit _ ≫ q)).left ≫ coprod.inl) * (h (ea.left ≫ coprod.inl))⁻¹ *
          (h ((toUnit _ ≫ q).left ≫ coprod.inl))⁻¹ * h ((1 : D'.P.A ⟶ D'.P.A).left ≫ coprod.inl) := by
      refine (Finset.prod_congr rfl fun k _ => ?_).trans
        (GlobalTheory.PrimCocycle.prod_lam ea (toUnit _ ≫ q) (fun g => h (g ≫ coprod.inl)))
      rw [← Category.assoc, ← Category.assoc, mβ]
    have A2 : ∏ a₂ : ULift (Finset (Fin 2)), h (m ≫ (psum D₀.P.A (x2 D₀.P.A) a₂.down).left ≫ coprod.inr) ^
        (-(-1 : ℤ) ^ (2 - a₂.down.card)) =
        (h ((pr * (toUnit _ ≫ D₀.c χ)).left ≫ coprod.inr) * (h (pr.left ≫ coprod.inr))⁻¹ *
          (h ((toUnit _ ≫ D₀.c χ).left ≫ coprod.inr))⁻¹ * h ((1 : D'.P.A ⟶ D₀.P.A).left ≫ coprod.inr))⁻¹ := by
      rw [← GlobalTheory.PrimCocycle.prod_lam pr (toUnit _ ≫ D₀.c χ) (fun g => h (g ≫ coprod.inr)), ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [zpow_neg, ← Category.assoc]
    have A3 := prod_ros ea ea' (𝟙 D'.P.A) (toUnit _ ≫ q) (fun g => h (g ≫ coprod.inl))
    beta_reduce at A3
    rw [A1, A2, A3, Fin.prod_univ_four, Fin.prod_univ_four]
    clear * - h hq'
    have pm : ∀ {X Y : Over (Sp R)} [GrpObj Y] (a b : X ⟶ Y), padd Y a b = a * b := fun _ _ => rfl
    simp only [DegPre.Oφ, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, pm, ← Hom.one_def, hq', Category.id_comp,
      Category.assoc]
    simp only [zpow_one, zpow_neg]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  case ev =>
    intro y I hI
    have o₀ : (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) = η[D₀.P.A] := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have o' : (1 : 𝟙_ (Over (Sp R)) ⟶ D'.P.A) = η[D'.P.A] := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have e₁ : eSec D'.P.A ≫ m = (lift (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) (toUnit _ ≫ D₀.c χ)).left := by
      rw [eSec, ← Over.comp_left, comp_lift, IsMonHom.one_hom, ← Category.assoc,
        toUnit_unique (η[D'.P.A] ≫ toUnit _) (toUnit _), o₀]
    have e₂ : eSec D'.P.A ≫ n = (lift (1 : 𝟙_ (Over (Sp R)) ⟶ D'.P.A) (toUnit _ ≫ q)).left := by
      rw [eSec, ← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc,
        toUnit_unique (η[D'.P.A] ≫ toUnit _) (toUnit _), o']
    rw [val_pull hI, htv _ _ y I hI, val_mul hI, h₁.val_gen _ _ y hI, val_pull (h₁.good hI), e₁, e₂]
    have a := hw1 (𝟙_ _) (toUnit _ ≫ D₀.c χ) y (rl I) (rr I) (h₁.good hI) (h₂.good hI)
    have b := hur1 (𝟙_ _) (toUnit _ ≫ q) y (rl I) (h₁.good hI)
    have c := hu.2 _ (𝟙 _) y I hI
    rw [Category.id_comp] at c
    rw [show isoVal w (lift (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) (toUnit _ ≫ D₀.c χ)).left y (rl I) (rr I) = 1 from a, b, c,
      _root_.one_mul]

end GlobalTheory.Mum.Two
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic

namespace GlobalTheory.Mum.PowData

def AdjCls {S : Scheme.{0}} {G G₀ : Over S} [GrpObj G] [GrpObj G₀] (c : Pic G.left) (c₀ : Pic G₀.left) (q : G ⟶ G₀)
    (j : G₀ ⟶ G) : Prop :=
  ∀ (T : Over S) (x : T ⟶ G) (z : T ⟶ G₀), lam c x (z ≫ j) = lam c₀ (x ≫ q) z

variable {R : Type} [CommRing R] [IsDomain R]

def PrimVal (D : DegPre R) (f : D.P.A ⟶ D.P.A) (m : D.X → D.X) : Prop :=
  ∃ u : LB.Gen (LB.LinComb D.P.L (K := Fin 4)
      ![(padd D.P.A (𝟙 _) f).left, 𝟙 D.P.A.left, f.left, (toUnit D.P.A ≫ η[D.P.A]).left] ![1, -2, -1, 2]),
    u.IsGen ∧ ∀ y, LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (D.tau y (m y)) (LB.pullGen D.P.L _ _ u (D.xK y))) (LB.mulGen D.P.L _ _ _ _ (D.psi y) D.rigK)

theorem isPrimitiveValue_of_ringElement_psiRelation {O : Type} [CommRing O] [StarRing O] {D : DegPre R} [Module O D.X] {o : D.OAct O} {w : O}
    (h : TraceFormTwistIso D o w) : PrimVal D (o.onB.act w) (fun y => w • y) :=
  h.imp fun _ h => ⟨h.1, h.2.2⟩

def Expand (D : DegPre R) {K : Type} [Fintype K] (n : K → ℤ) {T : Over (Sp R)} (x : T ⟶ D.P.A) (y : K → (T ⟶ D.P.A)) : Prop :=
  ∃ κ : LB.Gen (LB.LinComb D.P.L (Sum.elim (lamPts x (∏ i, y i ^ n i)) (fun k : K × Fin 4 => lamPts x (y k.1) k.2))
      (Sum.elim Oε (fun k : K × Fin 4 => -(n k.1 * Oε k.2)))),
    κ.IsGen ∧ ∀ (p : TK R ⟶ T) (a : D.X) (b : K → D.X), p ≫ x = toUnit _ ≫ D.c a → (∀ i, p ≫ y i = toUnit _ ≫ D.c (b i)) →
      ∀ z J, Good D.P.L z J →
        val (D.tau a (∑ i, n i • b i)) (𝟙 _) z J * val κ p.left z J = ∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ n i

def CmpTwo (D D₀ : DegPre R) (q : D.P.A ⟶ D₀.P.A) (j : D₀.P.A ⟶ D.P.A) : Prop :=
  ∃ Γ : LB.Gen (LB.LinComb (JN D D₀)
      (Sum.elim (fun k => lamPts (fst D.P.A D₀.P.A) (snd D.P.A D₀.P.A ≫ j) k ≫ coprod.inl)
        (fun k => lamPts (fst D.P.A D₀.P.A ≫ q) (snd D.P.A D₀.P.A) k ≫ coprod.inr)) (Sum.elim Oε Oinvε)),
    Γ.IsGen ∧ ∀ (χ' : D.X) (χ : D₀.X), D.c χ' = D₀.c χ ≫ j → ∀ u : LB.Gen (CmpLB D D₀ q χ' χ), Nrm u →
      ∀ (T : Over (Sp R)) (x : T ⟶ D.P.A) (z : T.left) (J), Good (JN D D₀) z J →
        val u x.left z J = val Γ (lift x (toUnit T ≫ D₀.c χ)).left z J

def PeriodRel (D D₀ : DegPre R) (q : D.P.A ⟶ D₀.P.A) (h : D₀.X → D.X) (k : D.X → D₀.X) : Prop :=
  ∀ χ, ∃ u : LB.Gen (CmpLB D D₀ q (h χ) χ), Nrm u ∧ ∀ y z J, Good (JN D D₀) z J →
    val (D₀.tau (k y) χ) (𝟙 _) z (rr J) = val (D.tau y (h χ)) (𝟙 _) z (rl J) * val u (ptK (D.c y)) z J

section Points

variable {S : Scheme.{0}} {T T' G G' : Over S} [GrpObj G] [IsCommMonObj G] {K : Type} [Fintype K]

theorem comp_prod_zpow (p : T' ⟶ T) (y : K → (T ⟶ G)) (n : K → ℤ) : p ≫ ∏ i, y i ^ n i = ∏ i, (p ≫ y i) ^ n i := by
  let f : (T ⟶ G) →* (T' ⟶ G) := MonoidHom.mk' (fun a => p ≫ a) fun a b => MonObj.comp_mul p a b
  exact (map_prod f _ _).trans (Finset.prod_congr rfl fun i _ => map_zpow f _ _)

theorem prod_zpow_comp [GrpObj G'] [IsCommMonObj G'] (y : K → (T ⟶ G)) (n : K → ℤ) (g : G ⟶ G') [IsMonHom g] :
    (∏ i, y i ^ n i) ≫ g = ∏ i, (y i ≫ g) ^ n i := by
  let f : (T ⟶ G) →* (T ⟶ G') := MonoidHom.mk' (fun a => a ≫ g) fun a b => MonObj.mul_comp a b g
  exact (map_prod f _ _).trans (Finset.prod_congr rfl fun i _ => map_zpow f _ _)

end Points

end GlobalTheory.Mum.PowData
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section
namespace GlobalTheory.Mum.Two
open GlobalTheory.CechPic GlobalTheory.ZH.EndoExtend

theorem lbIso_cubeLB_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (f g : G₁ ⟶ G₂) (f' g' : G₁ ⟶ G₁) (fA gA : A₁.A ⟶ A₂.A) (fA' gA' : A₁.A ⟶ A₁.A), Gen₀ U₁ U₂ f fA → Gen₀ U₁ U₂ g gA → Gen₀ U₁ U₁ f' fA' → Gen₀ U₁ U₁ g' gA' → LBIso (cubeLB G₂ ![fst G₁ G₁ ≫ f, snd G₁ G₁ ≫ g] U₂.LG.L) (cubeLB G₁ ![fst G₁ G₁ ≫ f', snd G₁ G₁ ≫ g'] U₁.LG.L) → LBIso (cubeLB A₂.A ![fst A₁.A A₁.A ≫ fA, snd A₁.A A₁.A ≫ gA] A₂.L) (cubeLB A₁.A ![fst A₁.A A₁.A ≫ fA', snd A₁.A A₁.A ≫ gA'] A₁.L) := by
  intro R _ _ I D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ f g f' g' fA gA fA' gA' hf hg hf' hg' H
  let δ := CartesianMonoidalCategory.prodComparison (Over.pullback (jK R)) G₁ G₁
  let u := lift (fst ((Over.pullback (jK R)).obj G₁) ((Over.pullback (jK R)).obj G₁) ≫ U₁.gen.hom)
    (snd ((Over.pullback (jK R)).obj G₁) ((Over.pullback (jK R)).obj G₁) ≫ U₁.gen.hom)
  have key : ∀ {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
      (U : UnifPre I D A G) (x y : G₁ ⟶ G) (cx cy : A₁.A ⟶ A.A), Gen₀ U₁ U x cx → Gen₀ U₁ U y cy →
      CechPic.pull (pullback.fst (G₁ ⊗ G₁).hom (jK R)) (cubeCls G ![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] (cls U.LG.L U.LG.isLB)) =
        CechPic.pull δ.left (CechPic.pull u.left
          (cubeCls A.A ![fst A₁.A A₁.A ≫ cx, snd A₁.A A₁.A ≫ cy] (cls A.L A.isLB))) := by
    intro D A G _ _ U x y cx cy hx hy
    have hL := U.LG.isLB
    have hA := A.isLB
    have hgen := U.gen_hom
    have hc' : CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL) =
        CechPic.pull U.gen.hom.left (cls A.L hA) := by
      obtain ⟨w, hw⟩ := U.ext
      rw [← cls_pull hL _ (pull_isLB hL _), ← cls_pull hA _ (pull_isLB hA _)]
      exact ((cls_eq_iff _ _).2 ⟨w, hw⟩).symm
    have Aw : ∀ {Y Z : Over (Sp R)} (q : Y ⟶ Z),
        ((Over.pullback (jK R)).map q).left ≫ pullback.fst Z.hom (jK R) = pullback.fst Y.hom (jK R) ≫ q.left :=
      fun q => pullback.lift_fst _ _ _
    have hu : u.left ≫ (A₁.A ⊗ A₁.A).hom =
        ((Over.pullback (jK R)).obj G₁ ⊗ (Over.pullback (jK R)).obj G₁).hom ≫ 𝟙 _ := by
      rw [Category.comp_id]; exact Over.w u
    have e' := push_cubeCls (isGrpPullback_pullback G (jK R)) (T' := (Over.pullback (jK R)).obj (G₁ ⊗ G₁))
      (T := G₁ ⊗ G₁) (fun i => (Over.pullback (jK R)).map (![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] i))
      ![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] (pullback.fst (G₁ ⊗ G₁).hom (jK R)) pullback.condition
      (fun i => Aw _) (cls U.LG.L hL)
    refine e'.trans ((pull_cubeCls _ ![fst _ _ ≫ (Over.pullback (jK R)).map x,
      snd _ _ ≫ (Over.pullback (jK R)).map y] _ δ (fun i => ?_) _).symm.trans ?_)
    · fin_cases i <;> simp [δ]
    rw [hc']
    refine congrArg (CechPic.pull δ.left) (push_cubeCls (isGrpPullback_of_iso U.gen) _ _ u.left hu (fun i => ?_) _).symm
    fin_cases i
    · show ((fst _ _ ≫ (Over.pullback (jK R)).map x) ≫ U.gen.hom).left = (u ≫ fst A₁.A A₁.A ≫ cx).left
      congr 1
      simp only [u, Category.assoc, lift_fst_assoc]
      rw [hx]
    · show ((snd _ _ ≫ (Over.pullback (jK R)).map y) ≫ U.gen.hom).left = (u ≫ snd A₁.A A₁.A ≫ cy).left
      congr 1
      simp only [u, Category.assoc, lift_snd_assoc]
      rw [hy]
  have eG := (cls_cubeLB G₂ _ U₂.LG.isLB).symm.trans (((cls_eq_iff (LB.isLB_linComb U₂.LG.isLB _ _)
    (LB.isLB_linComb U₁.LG.isLB _ _)).2 H).trans (cls_cubeLB G₁ _ U₁.LG.isLB))
  have e := (key U₂ f g fA gA hf hg).symm.trans ((congrArg _ eG).trans (key U₁ f' g' fA' gA' hf' hg'))
  let v := lift (fst A₁.A A₁.A ≫ U₁.gen.inv) (snd A₁.A A₁.A ≫ U₁.gen.inv)
  have hv : v ≫ u = 𝟙 _ := by ext <;> simp [u, v]
  have canc : ∀ c : Pic (A₁.A ⊗ A₁.A).left,
      CechPic.pull v.left (CechPic.pull (inv δ).left (CechPic.pull δ.left (CechPic.pull u.left c))) = c := by
    intro c
    rw [← pull_comp (inv δ).left δ.left, ← Over.comp_left, IsIso.inv_hom_id, Over.id_left, pull_id,
      ← pull_comp v.left u.left, ← Over.comp_left, hv, Over.id_left, pull_id]
  have eA := (canc _).symm.trans ((congrArg (fun c => CechPic.pull v.left (CechPic.pull (inv δ).left c)) e).trans (canc _))
  exact (cls_eq_iff (LB.isLB_linComb A₂.isLB _ _) (LB.isLB_linComb A₁.isLB _ _)).1
    ((cls_cubeLB A₂.A _ A₂.isLB).trans (eA.trans (cls_cubeLB A₁.A _ A₁.isLB).symm))

end GlobalTheory.Mum.Two
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

theorem _root_.GlobalTheory.T.uniformisedGroupHom_characterMap_constant : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂), IsMonHom a → ∃ h : D₂.toPre.X →+ D₁.toPre.X, OnTorus U₁ U₂ a h := by
  first | exact @GlobalTheory.Mum.Two.unifPre_hom_character_const | exact GlobalTheory.Mum.Two.unifPre_hom_character_const | (intros; apply GlobalTheory.Mum.Two.unifPre_hom_character_const <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange

noncomputable section
namespace GlobalTheory.Mum.Two

theorem whisker_comm₂ {C : Type*} [Category C] [CartesianMonoidalCategory C] (T : C) {X₁ X₂ Y₁ Y₂ : C}
    (g₁ : X₁ ⟶ Y₁) (g₂ : X₂ ⟶ Y₂) (a : X₁ ⟶ X₂) (b : Y₁ ⟶ Y₂) (h : a ≫ g₂ = g₁ ≫ b) :
    T ◁ a ≫ lift (fst _ _) (snd _ _ ≫ g₂) = lift (fst _ _) (snd _ _ ≫ g₁) ≫ T ◁ b := by
  ext <;> simp [h]

theorem crossH_at {R : Type} [CommRing R] [IsDomain R] {A₁ A₂ : PolAV (Sp (FractionRing R))} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {c : A₁.A ⟶ A₂.A} {j j' : ℕ} {t₁ t₂ : SecA A₂ F j} {t₁' t₂' : SecA A₁ F j'}
    (h : CrossH c t₁ t₂ t₁' t₂') {Z : Scheme.{0}} (r : Z ⟶ (TFK (R := R) F ⊗ A₁.A).left) (z : Z) {J₁ J₂}
    (hJ₁ : Good A₁.L z J₁) (hJ₂ : Good A₂.L z J₂) :
    sA t₁ (r ≫ (TFK (R := R) F ◁ c).left) z J₂ * sA t₂' r z J₁ =
      sA t₂ (r ≫ (TFK (R := R) F ◁ c).left) z J₂ * sA t₁' r z J₁ := by
  have e : ∀ t : SecA A₁ F j', sA t r z J₁ = (r.stalkMap z).hom (sA t (𝟙 _) (r z) (fun ψ => J₁ (r ≫ ψ))) :=
    fun t => by
      have := GlobalTheory.UU.IntExp.sval_comp (L := A₁.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A₁.A).left)
        (ε := fun _ => ((j' : ℕ) : ℤ)) t (𝟙 _) r z J₁ hJ₁
      rw [Category.comp_id] at this
      exact this
  have e' : ∀ t : SecA A₂ F j, sA t (r ≫ (TFK (R := R) F ◁ c).left) z J₂ =
      (r.stalkMap z).hom (sA t (TFK (R := R) F ◁ c).left (r z) (fun ψ => J₂ (r ≫ ψ))) :=
    fun t => GlobalTheory.UU.IntExp.sval_comp (L := A₂.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A₂.A).left)
        (ε := fun _ => ((j : ℕ) : ℤ)) t _ r z J₂ hJ₂
  rw [e, e, e', e', ← map_mul, ← map_mul, h (r z) _ _ (fun ψ => hJ₁ (r ≫ ψ)) (fun ψ => hJ₂ (r ≫ ψ))]

theorem carried_cross_of_hom : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A), Gen₀ U₁ U₂ a c → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (w₁ : W0 U₁) (w₂ : W0 U₂), w₁.IsGen → w₂.IsGen → ∀ (j j' : ℕ) (t₁ t₂ : SecA A₂ F j) (t₁' t₂' : SecA A₁ F j') (σ₁ σ₂ : U₂.SecGF F j) (σ₁' σ₂' : U₁.SecGF F j'), MixedConv.Carried w₂ j t₁ σ₁ → MixedConv.Carried w₂ j t₂ σ₂ → MixedConv.Carried w₁ j' t₁' σ₁' → MixedConv.Carried w₁ j' t₂' σ₂' → CrossH c t₁ t₂ t₁' t₂' → ∀ (y : (UnifPre.GF (G := G₁) F).left) (J₁ J₂), Good U₁.LG.L y J₁ → Good U₂.LG.L y J₂ → sval σ₁ (TFK (R := R) F ◁ (Over.pullback (jK R)).map a).left y J₂ * sval σ₂' (𝟙 _) y J₁ = sval σ₂ (TFK (R := R) F ◁ (Over.pullback (jK R)).map a).left y J₂ * sval σ₁' (𝟙 _) y J₁ := by
  intro R _ _ I D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a c hc F _ _ w₁ w₂ _ _ j j' t₁ t₂ t₁' t₂' σ₁ σ₂ σ₁' σ₂'
    h₁ h₂ h₁' h₂' h y J₁ J₂ hJ₁ hJ₂
  have hm : (TFK (R := R) F ◁ (Over.pullback (jK R)).map a).left ≫ (U₂.genF F).left =
      (U₁.genF F).left ≫ (TFK (R := R) F ◁ c).left :=
    congrArg (fun q => q.left) (whisker_comm₂ (TFK (R := R) F) U₁.gen.hom U₂.gen.hom _ _ hc)
  obtain ⟨J'₁, hJ'₁⟩ := GlobalTheory.UT.CoefBasic.exists_good' A₁.isLB y
  obtain ⟨J'₂, hJ'₂⟩ := GlobalTheory.UT.CoefBasic.exists_good' A₂.isLB y
  have a₁ := GlobalTheory.BoxExpansion.isoRel_val h₁ (TFK (R := R) F ◁ (Over.pullback (jK R)).map a).left y hJ'₂ hJ₂
  have a₂ := GlobalTheory.BoxExpansion.isoRel_val h₂ (TFK (R := R) F ◁ (Over.pullback (jK R)).map a).left y hJ'₂ hJ₂
  have a₃ := GlobalTheory.BoxExpansion.isoRel_val h₁' (𝟙 _) y hJ'₁ hJ₁
  have a₄ := GlobalTheory.BoxExpansion.isoRel_val h₂' (𝟙 _) y hJ'₁ hJ₁
  have a₅ := crossH_at h (U₁.genF F).left y hJ'₁ hJ'₂
  rw [Category.comp_id, hm] at a₁ a₂
  rw [Category.comp_id, Category.id_comp (U₁.genF F).left] at a₃ a₄
  rw [a₁, a₂, a₃, a₄]
  exact (_root_.mul_mul_mul_comm _ _ _ _).trans ((congrArg (_ * ·) a₅).trans (_root_.mul_mul_mul_comm _ _ _ _))

end GlobalTheory.Mum.Two
end
end

section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt

theorem _root_.GlobalTheory.T.uniformisationLaws_centralMovedReadings : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → G), (∀ i σ, w i σ ∈ Subgroup.center G) → R.LUnif → (moveR R w).LUnif := by
  first | exact @GlobalTheory.Unframe.lUnif_moveR | exact GlobalTheory.Unframe.lUnif_moveR | (intros; apply GlobalTheory.Unframe.lUnif_moveR <;> assumption)
end
