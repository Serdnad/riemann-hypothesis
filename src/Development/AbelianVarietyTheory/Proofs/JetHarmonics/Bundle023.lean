module

public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmThetaOperatorInvariantOfLiftCongrOne
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsImEqLattice
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle020
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle003
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Mathlib.Topology.UniformSpace.Uniformizable
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle001
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle002
public import Mathlib.RingTheory.MvPolynomial.Basic

@[expose] public section

section

open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators

theorem _root_.GlobalTheory.T.cmThetaOperator_invariant_of_lift_congr_one : ∀ (q : ℕ) [Fact q.Prime] (lam : Qbar →+* ℂ_[q]) (g : ℕ) (S : Setup g) (r : ℕ) (b : Fin r → Fin g → ℂ) (e : (Fin g → ℂ) → ℂ) (t : Fin g → ℂ) (n m s : ℕ) (eps : ℂ) (y : Fin r → Fin (q ^ n)), S.Ok → (∀ i, b i ∈ S.La) → S.IsTheta e → IsIdem lam S.d m eps → 2 * n ≤ m → (∀ i, ∃ z : ℤ, (hf S.Hm (eps • b i) t).im = z) → s ≡ 1 [MOD q ^ n] → opW S.d S.Hm ((s : ℂ) • liftY q n eps b y) (opU S.Hm t e) = opW S.d S.Hm (liftY q n eps b y) (opU S.Hm t e) ∧ ∀ v ∈ S.La, kap S.Hm v ((s : ℂ) • liftY q n eps b y) = kap S.Hm v (liftY q n eps b y) := by
  first | exact @GlobalTheory.MomOne.lift_change | exact GlobalTheory.MomOne.lift_change | (intros; apply GlobalTheory.MomOne.lift_change <;> assumption)
end

section

open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators ComplexOrder
open Matrix

namespace GlobalTheory.MomOne.ThetaLine

variable {g : ℕ}

theorem dot_transpose_eq_hf (Hm : Matrix (Fin g) (Fin g) ℂ) (z a : Fin g → ℂ) :
    star a ⬝ᵥ Hmᵀ.mulVec z = hf Hm z a := by
  simp only [dotProduct, mulVec, transpose_apply, hf, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def]
  ring

theorem im_hf_int {d : ℕ} (hd : 0 < d) (Hm : Matrix (Fin g) (Fin g) ℂ) (x y : Fin g → ℂ)
    (h : beta d Hm x y ∈ OK d) : ∃ k : ℤ, (hf Hm x y).im = k := by
  obtain ⟨u, v, huv⟩ := h
  refine ⟨v, ?_⟩
  have hs : Real.sqrt d / 2 ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    positivity
  have key : (beta d Hm x y).im = Real.sqrt d / 2 * (hf Hm x y).im := by
    rw [beta, Complex.im_ofReal_mul]
  have hv : (beta d Hm x y).im = Real.sqrt d / 2 * v := by
    rw [huv]
    simp [w0, rtd]
    ring
  exact mul_left_cancel₀ hs (key.symm.trans hv)

theorem transl_of_fixed {d : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} {x : Fin g → ℂ}
    {G : (Fin g → ℂ) → ℂ} (h : opW d Hm x G = G) (z : Fin g → ℂ) :
    G (z + x) = Complex.exp (-((Real.pi : ℂ) * Complex.I * ((beta d Hm x x).re : ℂ))) *
      Complex.exp (Real.pi * hf Hm z x + Real.pi / 2 * hf Hm x x) * G z := by
  have hz := congrFun h z
  simp only [opW, opU] at hz
  have e1 : Complex.exp (-((Real.pi : ℂ) * Complex.I * ((beta d Hm x x).re : ℂ))) *
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((beta d Hm x x).re : ℂ)) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have e2 : Complex.exp (Real.pi * hf Hm z x + Real.pi / 2 * hf Hm x x) *
      Complex.exp (-(Real.pi : ℂ) * hf Hm z x - (Real.pi : ℂ) / 2 * hf Hm x x) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 2
    ring
  rw [← hz]
  linear_combination (-(G (z + x) * Complex.exp (Real.pi * hf Hm z x + Real.pi / 2 * hf Hm x x) *
      Complex.exp (-(Real.pi : ℂ) * hf Hm z x - (Real.pi : ℂ) / 2 * hf Hm x x))) * e1 - G (z + x) * e2

theorem exists_eq_smul : ∀ (g : ℕ) (S : Setup g) (e F : (Fin g → ℂ) → ℂ), S.Ok → S.IsTheta e → S.IsTheta F → F ≠ 0 → ∃ c : ℂ, e = c • F := by
  intro g S e F hS he hF hF0
  obtain ⟨hp, -, hH, hdisc, -, -, hβ, hdual⟩ := hS
  have : DiscreteTopology S.La.toAddSubgroup := hdisc
  have hlaw : ∀ G : (Fin g → ℂ) → ℂ, S.IsTheta G → ∀ a ∈ S.La.toAddSubgroup, ∀ z,
      G (z + a) = Complex.exp (-((Real.pi : ℂ) * Complex.I * ((beta S.d S.Hm a a).re : ℂ))) *
        Complex.exp (Real.pi * (star a ⬝ᵥ S.Hmᵀ.mulVec z) + Real.pi / 2 * (star a ⬝ᵥ S.Hmᵀ.mulVec a)) * G z := by
    intro G hG a ha z
    rw [dot_transpose_eq_hf, dot_transpose_eq_hf]
    exact transl_of_fixed (hG.2 a ha) z
  refine GlobalTheory.ThetaTranslSpan.exists_eq_smul hH.transpose S.La.toAddSubgroup ?_
    (fun a => Complex.exp (-((Real.pi : ℂ) * Complex.I * ((beta S.d S.Hm a a).re : ℂ)))) F e ?_
    (hF.1.differentiable (by simp)) hF0 (hlaw F hF) (he.1.differentiable (by simp)) (hlaw e he)
  · intro v
    simp only [dot_transpose_eq_hf]
    exact ⟨hdual v, fun hv a ha => im_hf_int hp.pos S.Hm a v (hβ a ha v hv)⟩
  · intro a _
    simp [Complex.norm_exp]

end GlobalTheory.MomOne.ThetaLine
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open Cardinal Topology

namespace GlobalTheory.GenFrame

theorem subset_closure_forall_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U)
    {J : Type*} [Countable J] (f : J → E → ℂ) (hf : ∀ j, DifferentiableOn ℂ (f j) U)
    (hne : ∀ j, ∃ x ∈ U, f j x ≠ 0) : U ⊆ closure {x | x ∈ U ∧ ∀ j, f j x ≠ 0} := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  set W : J → Set E := fun j => (U ∩ f j ⁻¹' {0}ᶜ) ∪ (closure U)ᶜ with hW
  have hWo : ∀ j, IsOpen (W j) := fun j =>
    ((hf j).continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton).union
      isClosed_closure.isOpen_compl
  have hWd : ∀ j, Dense (W j) := by
    intro j
    rw [dense_iff_inter_open]
    intro O hO hOne
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hnot : ∀ y ∈ O, y ∉ W j := fun y hy hyW => by
      have : y ∈ O ∩ W j := ⟨hy, hyW⟩
      rw [hemp] at this
      exact this
    obtain ⟨y, hy⟩ := hOne
    have hyc : y ∈ closure U := by
      by_contra h
      exact hnot y hy (Or.inr h)
    obtain ⟨z, hzO, hzU⟩ := mem_closure_iff.mp hyc O hO hy
    have hz := GlobalTheory.SCV.eqOn_of_eqOn_open (g := fun _ => (0 : ℂ)) hU hc (hf j)
      (differentiableOn_const 0) (hO.inter hU) ⟨z, hzO, hzU⟩ Set.inter_subset_right
      (fun w hw => by
        by_contra h
        exact hnot w hw.1 (Or.inl ⟨hw.2, h⟩))
    obtain ⟨x, hx, hx0⟩ := hne j
    exact hx0 (hz hx)
  have hD := dense_iInter_of_isOpen hWo hWd
  refine (hD.open_subset_closure_inter hU).trans (closure_mono ?_)
  rintro x ⟨hxU, hx⟩
  refine ⟨hxU, fun j => ?_⟩
  rcases Set.mem_iInter.mp hx j with h | h
  · exact h.2
  · exact absurd (subset_closure hxU) h

end GlobalTheory.GenFrame
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AlphaPair

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']


set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] in
omit [IsCommMonObj G] [IsCommMonObj G'] in
theorem _root_.GlobalTheory.AlphaPair.exists_ptEquiv {f : S' ⟶ S} {F : G'.left ⟶ G.left}
    (gp : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G f F) {Z : Scheme.{0}}
    (a : Z ⟶ S') (b : Z ⟶ S) (hb : b = a ≫ f) :
    ∃ ρ : (Over.mk a ⟶ G') ≃* (Over.mk b ⟶ G), ∀ x, (ρ x).left = x.left ≫ F := by
  subst hb
  have hpb : IsPullback F G'.hom G.hom f := gp.1
  let φ : (Over.mk a ⟶ G') → (Over.mk (a ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ F) (by
      rw [Category.assoc, hpb.w, ← Category.assoc, Over.w x]
      rfl)
  let ψ : (Over.mk (a ≫ f) ⟶ G) → (Over.mk a ⟶ G') := fun y =>
    Over.homMk (hpb.lift y.left a (by simpa using Over.w y)) (by simp)
  refine ⟨{ toFun := φ, invFun := ψ, left_inv := ?_, right_inv := ?_, map_mul' := ?_ },
    fun x => rfl⟩
  · intro x
    apply Over.OverMorphism.ext
    apply hpb.hom_ext
    · simp [φ, ψ]
    · simp [φ, ψ]
  · intro y
    apply Over.OverMorphism.ext
    simp [φ, ψ]
  · intro x y
    apply Over.OverMorphism.ext
    exact (gp.2 (Over.mk a) x y (φ x) (φ y) rfl rfl).symm

end GlobalTheory.AlphaPair
end
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.ExpCong

section Abstract

variable {A k ι : Type} [CommRing A] [CommRing k] (D : ι → A → A) (c : A →+* k)

def along (w : List ι) (f : A) : A := w.foldl (fun g a => D a g) f

theorem along_nil (f : A) : along D [] f = f := rfl

theorem along_cons (a : ι) (w : List ι) (f : A) : along D (a :: w) f = along D w (D a f) := rfl

theorem along_add (hadd : ∀ a f g, D a (f + g) = D a f + D a g) (w : List ι) (f g : A) :
    along D w (f + g) = along D w f + along D w g := by
  induction w generalizing f g with
  | nil => rfl
  | cons a w ih => rw [along_cons, along_cons, along_cons, hadd, ih]

theorem along_mul_mem (hadd : ∀ a f g, D a (f + g) = D a f + D a g)
    (hmul : ∀ a f g, D a (f * g) = f * D a g + g * D a f) (S : Set k) (J : AddSubgroup k)
    (hSJ : ∀ s ∈ S, ∀ j ∈ J, s * j ∈ J) (w : List ι) (f g : A)
    (hf : ∀ v, v.Sublist w → c (along D v f) ∈ S) (hg : ∀ v, v.Sublist w → c (along D v g) ∈ J) :
    c (along D w (f * g)) ∈ J := by
  induction w generalizing f g with
  | nil =>
    rw [along_nil, map_mul]
    exact hSJ _ (hf [] (List.Sublist.refl _)) _ (hg [] (List.Sublist.refl _))
  | cons a w ih =>
    rw [along_cons, hmul, along_add D hadd, map_add (f := _), mul_comm g]
    refine J.add_mem (ih _ _ ?_ ?_) (ih _ _ ?_ ?_)
    · exact fun v hv => hf v (hv.cons a)
    · exact fun v hv => hg (a :: v) (hv.cons_cons a)
    · exact fun v hv => hf (a :: v) (hv.cons_cons a)
    · exact fun v hv => hg v (hv.cons a)

theorem along_mul_exp (hadd : ∀ a f g, D a (f + g) = D a f + D a g)
    (hmul : ∀ a f g, D a (f * g) = f * D a g + g * D a f) (S : Set k) (J : AddSubgroup k)
    (hSJ : ∀ s ∈ S, ∀ j ∈ J, s * j ∈ J) (hJS : ∀ j ∈ J, j ∈ S) (E φ : A) (hE : ∀ a, D a E = E * D a φ)
    (hE1 : c E = 1) (w : List ι) (f : A)
    (hf : ∀ v, v.Sublist w → c (along D v f) ∈ S) (hφ : ∀ v, v.Sublist w → c (along D v φ) ∈ J) :
    c (along D w (f * E)) - c (along D w f) ∈ J := by
  induction w generalizing f with
  | nil =>
    rw [along_nil, along_nil, map_mul, hE1, mul_one, sub_self]
    exact J.zero_mem
  | cons a w ih =>
    have hφ' : ∀ v, v.Sublist w → c (along D v φ) ∈ J := fun v hv => hφ v (hv.cons a)
    have h1 : ∀ v, v.Sublist w → c (along D v (f * D a φ)) ∈ J := fun v hv =>
      along_mul_mem D c hadd hmul S J hSJ v f (D a φ)
        (fun v' hv' => hf v' ((hv'.trans hv).cons a))
        (fun v' hv' => hφ (a :: v') ((hv'.trans hv).cons_cons a))
    have h2 := ih (f * D a φ) (fun v hv => hJS _ (h1 v hv)) hφ'
    have h3 := ih (D a f) (fun v hv => hf (a :: v) (hv.cons_cons a)) hφ'
    have h4 := J.add_mem (J.add_mem h2 (h1 w (List.Sublist.refl _))) h3
    rw [along_cons, along_cons, hmul, hE, along_add D hadd, map_add (f := _),
      show f * (E * D a φ) = f * D a φ * E by ring, mul_comm E]
    convert h4 using 1
    ring

def grouped (L : List ι) (m : ι → ℕ) : List ι := L.flatMap fun l => List.replicate (m l) l

theorem grouped_cons (a : ι) (L : List ι) (m : ι → ℕ) :
    grouped (a :: L) m = List.replicate (m a) a ++ grouped L m := by
  simp [grouped]

theorem exists_grouped_of_sublist {L : List ι} (hL : L.Nodup) (m : ι → ℕ) (v : List ι)
    (hv : v.Sublist (grouped L m)) : ∃ m' : ι → ℕ, v = grouped L m' := by
  classical
  induction L generalizing v with
  | nil => exact ⟨m, by simpa [grouped] using hv⟩
  | cons a L ih =>
    rw [grouped_cons, List.sublist_append_iff] at hv
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := hv
    obtain ⟨n, -, rfl⟩ := List.sublist_replicate_iff.1 h₁
    rw [List.nodup_cons] at hL
    obtain ⟨m', rfl⟩ := ih hL.2 v₂ h₂
    refine ⟨Function.update m' a n, ?_⟩
    rw [grouped_cons, Function.update_self]
    congr 1
    unfold grouped
    refine List.flatMap_congr fun l hl => ?_
    rw [Function.update_of_ne]
    rintro rfl
    exact hL.1 hl

theorem foldr_replicate (a : ι) (n : ℕ) (g : A) :
    (List.replicate n a).foldr (fun a g => D a g) g = (D a)^[n] g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.foldr_cons, ih, Function.iterate_succ_apply']

theorem along_reverse_grouped (L : List ι) (m : ι → ℕ) (f : A) :
    along D (grouped L m).reverse f = L.foldr (fun l g => (D l)^[m l] g) f := by
  unfold along
  rw [List.foldl_reverse]
  induction L with
  | nil => rfl
  | cons a L ih => rw [grouped_cons, List.foldr_append, ih, foldr_replicate, List.foldr_cons]

end Abstract

variable {k : Type} [CommRing k] {d : ℕ} (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)

theorem dmonOf_eq_along (m : ι →₀ ℕ) (f : PS k 1 d) :
    DmonOf F u m f =
      along (fun l => Dof F (u l)) (grouped (Finset.univ : Finset ι).toList m).reverse f :=
  (along_reverse_grouped _ _ _ _).symm

theorem exists_along_eq_dmonOf (m : ι →₀ ℕ) (v : List ι)
    (hv : v.Sublist (grouped (Finset.univ : Finset ι).toList m).reverse) :
    ∃ m' : ι →₀ ℕ, ∀ f : PS k 1 d, along (fun l => Dof F (u l)) v f = DmonOf F u m' f := by
  obtain ⟨m', hm'⟩ := exists_grouped_of_sublist (Finset.nodup_toList _) m v.reverse
    (by simpa using hv.reverse)
  refine ⟨Finsupp.equivFunOnFinite.symm m', fun f => ?_⟩
  rw [dmonOf_eq_along, Finsupp.coe_equivFunOnFinite_symm, ← hm', List.reverse_reverse]

end GlobalTheory.ExpCong

namespace GlobalTheory

theorem dmonOf_mul_expS_congr : ∀ (R : Type) [CommRing R] (d : ℕ) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (F : Fin d → PS R 2 d) (I : Ideal R) (ι : Type) [Fintype ι] (u : ι → Fin d → R) (φ : PS k 1 d), constantCoeff φ = 0 → (∀ m : ι →₀ ℕ, ∃ r ∈ I, constantCoeff (DmonOf (fun i => MvPowerSeries.map (algebraMap R k) (F i)) (fun l i => algebraMap R k (u l i)) m φ) = algebraMap R k r) → ∀ (f : PS R 1 d) (m : ι →₀ ℕ), ∃ r ∈ I, constantCoeff (DmonOf (fun i => MvPowerSeries.map (algebraMap R k) (F i)) (fun l i => algebraMap R k (u l i)) m (FB.toK k f * FB.expS k φ)) = algebraMap R k (constantCoeff (DmonOf F u m f) + r) := by
  intro R _ d k _ _ _ F I ι _ u φ hφ0 hφ f m
  set F' : Fin d → PS k 2 d := fun i => MvPowerSeries.map (algebraMap R k) (F i) with hF'
  set u' : ι → Fin d → k := fun l i => algebraMap R k (u l i) with hu'
  have hmap : ∀ m' : ι →₀ ℕ, constantCoeff (DmonOf F' u' m' (FB.toK k f)) =
      algebraMap R k (constantCoeff (DmonOf F u m' f)) := fun m' => by
    rw [hF', hu', FB.toK, ← map_dmonOf, constantCoeff_map]
  have key := ExpCong.along_mul_exp (fun l => Dof F' (u' l)) (constantCoeff : PS k 1 d →+* k)
    (fun a => GE.dof_add F' (u' a)) (fun a => GE.dof_mul F' (u' a)) (Set.range (algebraMap R k))
    (I.toAddSubgroup.map (algebraMap R k).toAddMonoidHom)
    (by
      rintro _ ⟨s, rfl⟩ _ ⟨j, hj, rfl⟩
      exact ⟨s * j, I.mul_mem_left s hj, map_mul (algebraMap R k) s j⟩)
    (by
      rintro _ ⟨j, -, rfl⟩
      exact ⟨j, rfl⟩)
    (FB.expS k φ) φ (fun a => NablaExpConj.Dof_expS k F' (u' a) hφ0) (WickVanishing.constantCoeff_exp hφ0)
    (ExpCong.grouped (Finset.univ : Finset ι).toList m).reverse (FB.toK k f)
    (fun v hv => by
      obtain ⟨m', hm'⟩ := ExpCong.exists_along_eq_dmonOf F' u' m v hv
      exact ⟨_, by rw [hm', hmap]⟩)
    (fun v hv => by
      obtain ⟨m', hm'⟩ := ExpCong.exists_along_eq_dmonOf F' u' m v hv
      obtain ⟨r, hr, e⟩ := hφ m'
      exact ⟨r, hr, by rw [hm', e]; rfl⟩)
  rw [← ExpCong.dmonOf_eq_along, ← ExpCong.dmonOf_eq_along, hmap] at key
  obtain ⟨r, hr, e⟩ := key
  refine ⟨r, hr, ?_⟩
  have e' : algebraMap R k r = _ := e
  rw [map_add (f := _), e']
  ring

end GlobalTheory
end
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem sum_coeff_mul_weight {k σ : Type} [CommRing k] (w : (σ →₀ ℕ) → k) (P₁ P₂ : MvPolynomial σ k) :
    ∑ mo ∈ (P₁ * P₂).support, (P₁ * P₂).coeff mo * w mo =
      ∑ m₁ ∈ P₁.support, ∑ m₂ ∈ P₂.support, P₁.coeff m₁ * P₂.coeff m₂ * w (m₁ + m₂) := by
  let L : MvPolynomial σ k →ₗ[k] k := (MvPolynomial.basisMonomials σ k).constr k w
  have hL : ∀ (m : σ →₀ ℕ) (a : k), L (MvPolynomial.monomial m a) = a * w m := by
    intro m a
    have h1 : (MvPolynomial.monomial m a : MvPolynomial σ k) =
        a • MvPolynomial.basisMonomials σ k m := by
      rw [MvPolynomial.coe_basisMonomials]
      simp [MvPolynomial.smul_monomial]
    rw [h1, map_smul, Module.Basis.constr_basis, smul_eq_mul]
  have hP : ∀ P : MvPolynomial σ k, L P = ∑ mo ∈ P.support, P.coeff mo * w mo := by
    intro P
    conv_lhs => rw [P.as_sum]

    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => hL m _
  rw [← hP]
  conv_lhs => rw [P₁.as_sum, P₂.as_sum]

  rw [Finset.sum_mul_sum, map_sum]
  refine Finset.sum_congr rfl fun m₁ _ => ?_

  rw [map_sum]
  refine Finset.sum_congr rfl fun m₂ _ => ?_
  rw [MvPolynomial.monomial_mul, hL]

theorem colValue_mul_of_disjoint_columns :
    ∀ (k : Type) [CommRing k] (ι : Type) [Fintype ι] (n : ℕ) (mu : Fin n → (ι →₀ ℕ) → k) (T : Finset (Fin n)) (P₁ P₂ : MvPolynomial (ι × Fin n) k), (∀ mo ∈ P₁.support, ∀ l b, mo (l, b) ≠ 0 → b ∈ T) → (∀ mo ∈ P₂.support, ∀ l b, mo (l, b) ≠ 0 → b ∉ T) → ∑ mo ∈ (P₁ * P₂).support, (P₁ * P₂).coeff mo * ∏ b, mu b (colM mo b) = (∑ mo ∈ P₁.support, P₁.coeff mo * ∏ b ∈ T, mu b (colM mo b)) * ∑ mo ∈ P₂.support, P₂.coeff mo * ∏ b ∈ Tᶜ, mu b (colM mo b) := by
  intro k _ ι _ n mu T P₁ P₂ h₁ h₂
  rw [sum_coeff_mul_weight (fun mo => ∏ b, mu b (colM mo b)) P₁ P₂, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m₁ hm₁ => Finset.sum_congr rfl fun m₂ hm₂ => ?_
  have e₁ : ∏ b ∈ T, mu b (colM (m₁ + m₂) b) = ∏ b ∈ T, mu b (colM m₁ b) := by
    refine Finset.prod_congr rfl fun b hb => ?_
    congr 1
    ext l
    have : m₂ (l, b) = 0 := by
      by_contra h
      exact h₂ m₂ hm₂ l b h hb
    simp [colM, this]
  have e₂ : ∏ b ∈ Tᶜ, mu b (colM (m₁ + m₂) b) = ∏ b ∈ Tᶜ, mu b (colM m₂ b) := by
    refine Finset.prod_congr rfl fun b hb => ?_
    congr 1
    ext l
    have : m₁ (l, b) = 0 := by
      by_contra h
      exact (Finset.mem_compl.1 hb) (h₁ m₁ hm₁ l b h)
    simp [colM, this]
  rw [← Finset.prod_mul_prod_compl T, e₁, e₂]
  ring

end GlobalTheory
end
end
