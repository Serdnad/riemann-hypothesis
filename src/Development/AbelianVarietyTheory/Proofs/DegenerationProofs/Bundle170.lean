module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle110
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle009
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle102
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle087
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsInvertibleAdaptedBasisLinkMatrix
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle118
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdaptedBasisFourierTermSizesTorusPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle076
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle043
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle130
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartValuesTorsionPairingSeparationIntegra
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowerSectionOfChartFunctions
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle139
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle116
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCommonField
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LinearIndependentOfIsExtension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGeneratorNeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle128
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ConstBFMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

namespace GlobalTheory

theorem psiRel_field_ne_zero_iff {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (s : Raw D F 1) (h : PsiRel D (TF (R := R) F) s) (χ : D.X) :
    (∃ j, (s χ).f j ≠ 0) ↔ ∃ j, (s 0).f j ≠ 0 := by
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsIntegral (TF (R := R) F).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  have : IsIntegral (DegPre.BF D F).left := isIntegral_tensor_left_of_smooth_grpObj _ D.P.A (TF (R := R) F)
  obtain ⟨J, hJ⟩ := exists_good_pt (Z := (DegPre.BF D F).left) D.P.isLB (genericPoint _)
  have := PsiExists.isIso_trF D F χ
  have : IsIso (DegPre.trF D F χ).left := inferInstanceAs (IsIso ((Over.forget _).map (DegPre.trF D F χ)))
  let κ : DegPre.BF D F ⟶ TK R := Over.homMk ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F)
    ((Category.assoc _ _ _).trans (Over.w (fst (TF (R := R) F) D.P.A)))
  have e := h χ (DegPre.BF D F) (fst _ _) κ (snd _ _) _ J hJ
  have e₁ : (lift (fst (TF (R := R) F) D.P.A) (snd _ _)).left = 𝟙 (DegPre.BF D F).left :=
    congrArg (fun q : DegPre.BF D F ⟶ DegPre.BF D F => q.left) lift_fst_snd
  have e₂ : sval (s χ) (𝟙 (DegPre.BF D F).left) (genericPoint _) J =
      (val (D.psi χ) κ.left (genericPoint _) J * rigV D (T := DegPre.BF D F) (genericPoint _) J).val *
        sval (s 0) (DegPre.trF D F χ).left (genericPoint _) J :=
    (congrArg (fun q => sval (s χ) q (genericPoint _) J) e₁).symm.trans e
  rw [exists_ne_zero_iff_sval_ne_zero _ hJ, e₂]
  constructor
  · intro h0
    by_contra hn
    simp only [not_exists, not_not] at hn
    exact h0 (by rw [sval_eq_zero_of_local_eq_zero (s 0) hn _ _ J hJ, MulZeroClass.mul_zero])
  · intro h0
    exact mul_ne_zero (Units.ne_zero _) (sval_ne_zero_of_isIso _ _ D.P.L D.P.isLB _ _ _ (s 0) h0 _ _ _ J hJ)

theorem forall_ne_zero_of_psiRel : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (f : ∀ α, SecBT D (𝟙_ _) 1 α), PsiRel D (𝟙_ _) f → (∃ α j, (f α).f j ≠ 0) → ∀ α, ∃ j, (f α).f j ≠ 0 := by
  rintro R _ _ D f h ⟨α, hα⟩ β
  obtain ⟨s, hs⟩ := PsiExists.exists_pullB D (FractionRing R) (toUnit _) 1 f
  have h' := psiRel_of_pullB R D _ f s hs h
  have i := pullB_ne_zero_iff R D _ 1 f s hs
  exact (i β).1 ((psiRel_field_ne_zero_iff D _ s h' β).2 ((psiRel_field_ne_zero_iff D _ s h' α).1 ((i α).2 hα)))

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight

noncomputable section
namespace GlobalTheory.ZH.FibreIndep

open GlobalTheory.VVRank GlobalTheory.UnivBasisMove

theorem linearIndependent_pullM (hS : SecBaseChangeAnySt) {S : Scheme.{0}} (P : PolAV S) (n : ℕ) (hn : 1 ≤ n)
    {T T' : Over S} [IsAffine T.left] [IsAffine T'.left] (p : T'.left) (hp : ∀ q, q = p) (h : T' ⟶ T)
    {J : Type} [Fintype J] (hJ : Fintype.card J = n ^ P.g) (s : J → SecM P.A P.L n T)
    (hs : ∀ x, ∃ c : J → Γ(T.left, ⊤), x = ∑ i, c i • s i) :
    LinearIndependent Γ(T'.left, ⊤) (fun i => pullM P.A P.L n h (s i)) := by
  have hne : Nonempty (⊤ : T'.left.Opens) := ⟨⟨p, trivial⟩⟩
  have hnt : Nontrivial Γ(T'.left, ⊤) := Scheme.component_nontrivial T'.left ⊤
  obtain ⟨V, hV, b, hb⟩ := hS S P n hn (T'.hom p)
  let l : T' ⟶ overRes (T := baseOver S) V := Over.homMk
    (IsOpenImmersion.lift V.ι T'.hom (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      rw [hp y]
      exact hV)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
  obtain ⟨c, -⟩ := exists_basis P n b hb T' l
  have := Module.Free.of_basis c
  have := Module.Finite.of_basis c
  refine linearIndependent_of_top_le_span_of_card_eq_finrank (fun x _ => ?_)
    (by rw [Module.finrank_eq_card_basis c, Fintype.card_fin, hJ])
  refine Submodule.span_le.2 ?_ (LinkMatrix.mem_span_pullM hS P n hn p hp h x)
  rintro _ ⟨u, rfl⟩
  obtain ⟨a, rfl⟩ := hs u

  rw [map_sum]
  exact Submodule.sum_mem _ fun i _ => by
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem linearIndependent_moved : LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (w : LB.Iso u.A.L (ρ.P.L.pull u.φ)), w.IsGen → ∀ t : S.J → SecA u.A (PadicAlgCl p) S.N, (∀ i, Moved u w (t i) (ρ.s i)) → LinearIndependent Γ((TFK (R := u.V) (PadicAlgCl p)).left, ⊤) (fun i => SecM.ofSec u.A.A (t i)) := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u w hw t ht
  have hN : 1 ≤ S.N := by
    rw [ρ.N_eq]
    exact Nat.one_le_pow _ _ (pow_pos ρ.n_prime.pos _)
  let T := TFK (R := u.V) (PadicAlgCl p)
  let T' : Over (Sp S.R) := Over.mk (T.hom ≫ spMap u.yK)
  have : IsAffine T'.left := inferInstanceAs (IsAffine (Sp (PadicAlgCl p)))
  have : IsAffine (baseOver (Sp S.R)).left := inferInstanceAs (IsAffine (Sp S.R))
  let h₀ : T' ⟶ baseOver (Sp S.R) := Over.homMk (spMap y₀) (base_eq u)
  have li := linearIndependent_pullM hL.2.1.secBaseChangeAny ρ.P S.N hN (T' := T')
    (IsLocalRing.closedPoint (PadicAlgCl p))
    (fun q => Subsingleton.elim (α := PrimeSpectrum (PadicAlgCl p)) _ _) h₀ (J := S.J)
    (by rw [ρ.g_eq]; exact ρ.card) (fun i => SecM.ofSec ρ.P.A (ρ.s i)) (fun x => by
      obtain ⟨c, hc⟩ := (ρ.s_basis (SecM.toSec ρ.P.A x)).exists
      refine ⟨c, Subtype.ext (funext fun j => ?_)⟩
      rw [Submodule.coe_sum, Finset.sum_apply]
      exact hc j)
  obtain ⟨E, hE⟩ := exists_linearEquiv u.cart hw ρ.P.isLB u.A.isLB (S.N : ℤ) T
  have e : ∀ i, E (pullM ρ.P.A ρ.P.L S.N h₀ (SecM.ofSec ρ.P.A (ρ.s i))) = SecM.ofSec u.A.A (t i) := fun i => by
    have r : Rel u.cart (T := T) (T₀ := baseOver (Sp S.R)) (spMap y₀) (base_eq u) w (SecM.ofSec u.A.A (t i))
      (SecM.ofSec ρ.P.A (ρ.s i)) := ht i
    have r' := r.pull (T' := T) (T₀' := T') (𝟙 T.left) (Category.id_comp _) (𝟙 T) h₀ rfl
    rw [pullM_id _ u.A.isLB] at r'
    exact (hE _).unique_down ρ.P.isLB u.A.isLB r'
  have li' := LinearIndependent.map' (R := Γ(T.left, ⊤)) li E.toLinearMap E.ker
  exact (funext e : _ = fun i => SecM.ofSec u.A.A (t i)) ▸ li'

end GlobalTheory.ZH.FibreIndep
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.NormsPf
open GlobalTheory.ZH

section
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem sum_smul_f {I : Type} (A : Finset I) (a : I → F) (s : I → Fam D F k) (α : D.X) (j) :
    ((∑ i ∈ A, a i • s i).s α).f j = ∑ i ∈ A, resTop _ (gF D F (a i)) * ((s i).s α).f j := by
  classical
  induction A using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | insert i A hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, DVR.add_f, DVR.smul_f, ih]

theorem sum_smul_subtype {I : Type} [Fintype I] (p : I → Prop) [Fintype {i // p i}] (a : I → F) (s : I → Fam D F k)
    (α : D.X) (h : ∀ i, ¬ p i → ∀ j, ((s i).s α).f j = 0) :
    (∑ i, a i • s i).s α = (∑ i : {i // p i}, a i • s i).s α := by
  classical
  refine SecOps.sec_ext fun j => ?_
  rw [sum_smul_f, sum_smul_f, ← Finset.sum_subtype (Finset.univ.filter p) (by simp)
    (fun i => resTop _ (gF D F (a i)) * ((s i).s α).f j), Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · rfl
  · rw [h i hi j, mul_zero]

theorem zero_of_famOf {s : Fam D F k} {f : ∀ α, D.SecB k α} (hs : FamOf D F f s) {α : D.X}
    (h : ∀ j, (f α).f j = 0) (j) : (s.s α).f j = 0 := by
  refine sec_ext_val (s' := SecOps.secZero) D.P.isLB (fun y J hJ => ?_) j
  rw [← SectionScalarValuation.secScal_sval (hs α) _ y hJ, UUA.sval_zero_of h _ y J (hJ.mem _ _),
    UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _)]

theorem basis_of_eq (hT : TwistBaseChangeStatement) [IsLocalRing R] [IsNoetherianRing R] (hk : 1 ≤ k) {α : D.X}
    {R' : Type} [CommRing R'] (φ : R →+* R') {B : Scheme.{0}} {pB : B ⟶ Sp R'} {π : B ⟶ D.P.A.left}
    (H : IsPullback π pB D.P.A.hom (spMap φ)) {I : Type} [Fintype I] {β : I → D.SecB k α} (hβ : IsBasisB D β)
    (ψ : Fin 4 → (B ⟶ D.P.A.left)) (hψ : ψ = fun i => π ≫ D.famφB α i)
    (t : I → LB.Sec (LB.LinComb D.P.L ψ (DegPre.famε k)))
    (ht : ∀ i, GeneratorPullback.SecScal D.P.L ψ (DegPre.famε k) (t i) (D.famφB α) (DegPre.famε k) (β i) π 1)
    (b : LB.Sec (LB.LinComb D.P.L ψ (DegPre.famε k))) : ∃! a : I → R', IsLin pB t a b := by
  subst hψ
  have e : t = fun i => DVR.pullSec D.P.L (D.famφB α) (DegPre.famε k) (β i) π := funext fun i =>
    SecOps.sec_ext fun j => sec_ext_val D.P.isLB (fun y J hJ =>
      (SectionScalarValuation.secScal_sval (ht i) _ y hJ).symm.trans (SectionScalarValuation.sval_pullSec _ _ _ _ _ y hJ).symm) j
  rw [e]
  exact BasisBaseChange.basis_pullback hT R D k hk α R' φ B pB π H I β hβ b

theorem component_basis (hT : TwistBaseChangeStatement) [IsLocalRing R] [IsNoetherianRing R] (hk : 1 ≤ k) {α : D.X}
    {I : Type} [Fintype I] {β : I → D.SecB k α} (hβ : IsBasisB D β) (s : I → Fam D F k)
    (hs : ∀ i, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) ((s i).s α)
      (D.famφB α) (DegPre.famε k) (β i) (DegPre.prB D F).left 1)
    (b : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))) :
    ∃! a : I → F, b = (∑ i, a i • s i).s α := by
  let f : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))
  have hTF : jFK (R := R) F ≫ jK R = spMap f := by
    show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have H : IsPullback (DegPre.prB D F).left (fst (TF (R := R) F) D.P.A).left D.P.A.hom (spMap f) := by
    rw [← hTF]
    exact (IsPullback.of_hasPullback (jFK (R := R) F ≫ jK R) D.P.A.hom).flip
  have h := basis_of_eq hT hk f H hβ (DegPre.famφ D F α) (funext fun i => GC.famφ_eq D F α i)
    (fun i => (s i).s α) hs b
  refine (existsUnique_congr fun a => ?_).1 h
  exact ⟨fun h => SecOps.sec_ext fun j => (h j).trans (sum_smul_f _ a s α j).symm,
    fun h j => (congrArg (fun x => x.f j) h).trans (sum_smul_f _ a s α j)⟩

end

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}
  {k : ℕ}

theorem vge_comb_iff (hT : TwistBaseChangeStatement) (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) (hk : 1 ≤ k)
    {α : D.toPre.X} {I : Type} [Fintype I] {β : I → D.toPre.SecB k α} (hβ : IsBasisB D.toPre β)
    (s : I → Fam D.toPre F k)
    (hs : ∀ i, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) ((s i).s α)
      (D.toPre.famφB α) (DegPre.famε k) (β i) (DegPre.prB D.toPre F).left 1) (a : I → F) (q : ℚ) :
    VGe D F v k α ((∑ i, a i • s i).s α) q ↔ ∀ i, (q : WithTop ℚ) ≤ v (a i) := by
  constructor
  · intro h
    obtain ⟨b, hb, e⟩ := GlobalTheory.TermSize.exists_comb hϖ hv hβ s hs h
    rw [(component_basis hT hk hβ s hs _).unique rfl e]
    exact hb
  · intro h
    let e := (Fintype.equivFin I).symm
    refine ⟨_, fun i => a (e i), fun i => β (e i), fun i => (s (e i)).s α, fun i => hs _, fun i => h _, fun j => ?_⟩
    rw [sum_smul_f]
    exact (Equiv.sum_comp e _).symm

end

theorem norms_of_adapted : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ k : ℕ, 1 ≤ k → ∀ (r : ℕ) (cls : Fin r → D.toPre.X) (mu : ℕ) (f : Fin r → ∀ α, D.toPre.SecB k α) (s : Fin r → Fam D.toPre F k), AdFam D Q k cls mu f → (∀ i, GlobalTheory.ZH.FamOf D.toPre F (f i) (s i)) → Norms D Q v k cls s := by
  intro hLL _ _ _ _ V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv k hk r cls mu f s hA hs
  classical
  obtain ⟨⟨hshort, hcls, hcov, -⟩, -, hzero, hbas⟩ := hA
  have hG := hLL.1.globalFns
  have hT : TwistBaseChangeStatement := GlobalTheory.twistBaseChange_of_finrank_sections_one fun K _ _ P =>
    (hLL.1.globalSectionsRank K P 1 le_rfl).trans (one_pow _)
  have hsub : ∀ (a : Fin r → F) i₀, (∑ i, a i • s i).s (cls i₀) =
      (∑ i : {i // cls i = cls i₀}, a i • s i).s (cls i₀) := fun a i₀ =>
    sum_smul_subtype (fun i => cls i = cls i₀) a s _ fun i hi =>
      zero_of_famOf (hs i) (hzero i _ fun z hz => hi (hcls i₀ i ⟨z, hz⟩).symm)
  have hB := fun i₀ => component_basis (F := F) hT hk (hbas i₀) (fun i => s i) (fun i => hs i _)
  have hV : ∀ (a : Fin r → F) (q : ℚ) i₀, VGe D F v k (cls i₀) ((∑ i, a i • s i).s (cls i₀)) q ↔
      ∀ i : {i // cls i = cls i₀}, (q : WithTop ℚ) ≤ v (a i) := fun a q i₀ => by
    rw [hsub]
    exact vge_comb_iff hT hϖ hv hk (hbas i₀) (fun i => s i) (fun i => hs i _) (fun i => a i) q
  refine ⟨fun s' => ?_, fun a q => ⟨?_, ⟨fun h i => (hV a q i).1 (h _) ⟨i, rfl⟩, fun h α => ?_⟩,
    fun i h => (hV a q i).1 h ⟨i, rfl⟩⟩⟩
  · have ex : ∀ α, ∃ c : {i // cls i = α} → F, (∃ i₀, cls i₀ = α) →
        s'.s α = (∑ i : {i // cls i = α}, c i • s i).s α := fun α => by
      by_cases h : ∃ i₀, cls i₀ = α
      · obtain ⟨i₀, rfl⟩ := h
        obtain ⟨c, hc⟩ := (hB i₀ (s'.s (cls i₀))).exists
        exact ⟨c, fun _ => by convert hc⟩
      · exact ⟨0, fun h' => absurd h' h⟩
    choose c hc using ex
    refine existsUnique_of_exists_of_unique ⟨fun i => c (cls i) ⟨i, rfl⟩, fam_ext fun α j => ?_⟩ fun a a' ha ha' => ?_
    · obtain ⟨i₀, z, rfl⟩ := hcov α
      refine congrArg (fun x => x.f j) (GlobalTheory.FamFree.eq_of_eq_add_nsmul hG _ _ ⟨z, rfl⟩ ?_)
      rw [hsub, hc _ ⟨i₀, rfl⟩]
      have e : ∀ α (i : {i // cls i = α}), c α i = c (cls i) ⟨i, rfl⟩ := by rintro _ ⟨i, rfl⟩; rfl
      simp only [← e]
    · funext i
      have h := (hB i (s'.s (cls i))).unique (y₁ := fun i' => a i') (y₂ := fun i' => a' i')
        (by rw [ha, hsub]) (by rw [ha', hsub])
      exact congrFun h ⟨i, rfl⟩
  · rw [n1a V ϖ hϖ D Q hQ F v hv k hk (Finset.univ.image cls) (fun χ => by
      obtain ⟨i, hi⟩ := hcov χ
      exact ⟨cls i, Finset.mem_image_of_mem _ (Finset.mem_univ i), hi⟩) _ q]
    simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index, forall_apply_eq_imp_iff, hV]
    exact ⟨fun h i => h i ⟨i, rfl⟩, fun h i₀ i => by have := h i; rwa [i.2] at this⟩
  · obtain ⟨i₀, z, rfl⟩ := hcov α
    refine (SectionScalarValuation.fe_move hϖ hQ hv k z (cls i₀) _ ((hV a q i₀).2 fun i => h i)).mono ?_
    have h1 := hshort i₀ z
    rw [q_shift hϖ hQ] at h1
    have h2 : (0 : ℤ) ≤ k * Q z + QForm.bOf D.toPre Q z (cls i₀) :=
      nonneg_of_mul_nonneg_right (a := (k : ℤ)) (by linarith) (by omega)
    have h3 : (0 : ℚ) ≤ ((k * Q z + QForm.bOf D.toPre Q z (cls i₀) : ℤ) : ℚ) := by exact_mod_cast h2
    linarith

end GlobalTheory.OneBasis.NormsPf
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

noncomputable section
namespace GlobalTheory.IsoValCocycle
open GlobalTheory.TorusExt GlobalTheory.IsoValConst

theorem exists_th_ne_zero (hL : Laws) (hL₂ : Laws2) {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type}
    [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] {N : NumD F} (ν : NumOf D F N) {n : ℕ} (hn : 2 ≤ n)
    (hF : (n : F) ≠ 0) (a : N.A) : ∃ t, t ^ n = 1 ∧ N.th (a * t) ≠ 0 := by
  let y : (TF (R := R) F).left := IsLocalRing.closedPoint F
  obtain ⟨th, ρ, hth, hv⟩ := ThetaInValues.exists_th ν y
  obtain ⟨x, hx, hu⟩ := UT.ExactTerm.exists_good_point hL.goodPt hL.polBaseChange D.P (jFK (R := R) F ≫ jK R) hn hF th
    (ThetaCoset.ne_zero_of_isGenSec hL₂.secBaseChangeAny D.P _ hth) (ν.eA a)
  obtain ⟨t, rfl⟩ := ν.eA.surjective x
  refine ⟨t, ν.eA.injective (by rw [map_pow, map_one]; exact hx), fun h => ?_⟩
  have q := hu y ν.J (ThetaInValues.good ν y)
  have e := hv (a * t)
  rw [h, MulZeroClass.zero_mul, map_zero, map_mul] at e
  exact not_isUnit_zero ((congrArg IsUnit e).mp q)

theorem cocycle_eq_val : Laws → Laws2 → ∀ (R O' : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing O'] [IsDomain O'] [IsNoetherianRing O'] (f : O' →+* R) (P : DegPre R) (D₀ : DegPre O') (C : Type) [Field C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing R) C] [Algebra (FractionRing O') C], Along f C → ∀ (N' N : NumD C) (ν' : NumOf P C N') (ν : NumOf D₀ C N) (ψ : P.P.A.left ⟶ D₀.P.A.left) (w : LB.Iso P.P.L (D₀.P.L.pull ψ)) (I : NumB.Iso N.toNumB N'.toNumB), IsGrpPullback P.P.A D₀.P.A (spMap f) ψ → w.IsGen → (∀ x : N.A, (ν'.eA (I.φ x)).left ≫ ψ = (ν.eA x).left) → (∀ x, wVal ν' ν w x ≠ 0) ∧ ∀ x : N.A, (I.h x : C) * wVal ν' ν w (I.φ x) = wVal ν' ν w 1 := by
  intro hL hL₂ R O' _ _ _ _ _ _ f P D₀ C _ _ _ _ _ hf N' N ν' ν ψ w I gp hw he
  let z : Sp C := IsLocalRing.closedPoint C
  have hJ := good ν z
  have hJ' := good ν' z
  have hT : (TF (R := R) C).hom ≫ spMap f = (TF (R := O') C).hom := ArcTransport.base_comm fun r => (hf r).symm
  have hp : ∀ x : N.A, ArcTransport.pushF gp hT (ν'.eA (I.φ x)) = ν.eA x := fun x => Over.OverMorphism.ext (he x)
  have hW : ∀ x : N'.A, stalkConst z (wVal ν' ν w x) = (ArcTransport.wVal w z ν.J ν'.J (ν'.eA x)).val := fun x =>
    toStk_valF (ν'.eA x).left ((D₀.P.L.pull ψ).U (fun _ => ν.J ((ν'.eA x).left ≫ ψ)) ⊓ P.P.L.U (ν'.J (ν'.eA x).left)) z
      ⟨mem_pull.2 (hJ ((ν'.eA x).left ≫ ψ)), hJ' _⟩ _
  refine ⟨fun x h => ?_, ?_⟩
  · have := hW x
    rw [h, map_zero] at this
    exact Units.ne_zero _ this.symm
  let Ω : N.A → ((Sp C).presheaf.stalk z)ˣ := fun x => ArcTransport.wVal w z ν.J ν'.J (ν'.eA (I.φ x))
  have hΩ : ∀ x, stalkUnits z (I.h x) * Ω x = stalkUnits z (I.h 1) * Ω 1 := by
    refine const_of_cube (fun x => stalkUnits z (I.h x) * Ω x) (fun a b c => ?_) (fun a => N.th a ≠ 0) ?_ 2
      (fun x => ?_) (exists_th_ne_zero hL hL₂ ν le_rfl (Nat.cast_ne_zero.2 two_ne_zero))
    · have e := ArcTransport.thS_push gp hT ((isGen_iff _).1 hw) hL.globalFns hJ hJ' (ν'.eA (I.φ a)) (ν'.eA (I.φ b))
        (ν'.eA (I.φ c))
      rw [hp, hp, hp, ← map_one ν'.eA, ← map_one I.φ, ← stalk_θ, ← stalk_θ] at e
      simp only [← map_mul ν'.eA, ← map_mul I.φ] at e
      have e₁ : stalkUnits z (N.θ a b c) = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b *
        Ω c * (Ω 1)⁻¹ * stalkUnits z (N'.θ (I.φ a) (I.φ b) (I.φ c)) := e
      have e₂ := congrArg (stalkUnits z) (I.θ_eq a b c)
      rw [I.h_one, map_one]
      clear_value Ω
      apply Additive.ofMul.injective
      replace e₁ := congrArg Additive.ofMul e₁
      replace e₂ := congrArg Additive.ofMul e₂
      simp only [map_mul, ofMul_mul, ofMul_inv, ofMul_one] at e₁ e₂ ⊢
      linear_combination (norm := abel) -e₁ - e₂
    · obtain ⟨s, hs⟩ := ConstFam.exists_secThrough (φ' := fun _ : Fin 1 => 𝟙 P.P.A.left)
        (φ := fun _ : Fin 1 => 𝟙 D₀.P.A.left) (h := ψ) hw D₀.P.isLB P.P.isLB
        (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm) ν.th
      obtain ⟨κ, hκ⟩ := sval_eq ν' z s
      obtain ⟨ρ, hρ⟩ := stalk_th ν z
      obtain ⟨ρ', hρ'⟩ := stalk_th ν' z
      have key : ∀ a : N.A, N.th a ≠ 0 →
          ρ.val = (stalkUnits z (I.h a) * Ω a).val * (κ * stalkConst z I.lam * ρ'.val) := fun a ha => by
        have e := hs.sval (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm)
          (show Sp C ⟶ _ from (ν'.eA (I.φ a)).left) hJ hJ'
        rw [Fin.prod_univ_one, Category.comp_id] at e
        replace e := e.trans (congrArg (fun q : ((Sp C).presheaf.stalk z)ˣ => q.val * _) (zpow_one _))
        have e' : stalkConst z (N.th a) * ρ.val = (Ω a).val * (κ * (stalkConst z (N'.th (I.φ a)) * ρ'.val)) :=
          (hρ a).trans ((congrArg (fun q => sval (Z := Sp C) ν.th q z ν.J) (he a).symm).trans (e.trans
            (congrArg _ ((hκ _).trans (congrArg _ (hρ' _).symm)))))
        refine ((IsUnit.mk0 _ ha).map (stalkConst z)).mul_left_cancel (e'.trans ?_)
        rw [I.th_eq, Units.val_mul, Units.val_mul, stalkUnits_val, map_mul, map_mul]
        ring
      intro a b ha hb
      have hu : IsUnit (κ * stalkConst z I.lam * ρ'.val) := isUnit_of_mul_isUnit_right (key a ha ▸ ρ.isUnit)
      exact Units.ext (hu.mul_right_cancel ((key a ha).symm.trans (key b hb)))
    · obtain ⟨y, hy⟩ := ValuesTorsion.exists_pow_eq hL D₀.P (jFK (R := O') C ≫ jK O') (ν.eA x) one_le_two
      exact ⟨ν.eA.symm y, by rw [← map_pow, hy, MulEquiv.symm_apply_apply]⟩
  intro x
  apply (stalkConst z).injective
  have e := congrArg Units.val (hΩ x)
  rw [I.h_one, map_one, _root_.one_mul, Units.val_mul, stalkUnits_val] at e
  rw [map_mul, hW, hW, ← map_one I.φ]
  exact e

end GlobalTheory.IsoValCocycle
end
end
