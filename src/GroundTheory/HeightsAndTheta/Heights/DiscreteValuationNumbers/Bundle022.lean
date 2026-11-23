module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle008
import Mathlib.Algebra.Module.StablyFree.Basic
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagIndependenceAlgebra
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dual.Lemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def FlagBundleSectionForms.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (e : ℕ),
    IsMultiProjPrime (pointIdeal F y) →
    ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B : ChartBundle F (segreVec y) N E) (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ),
      IsFlagFrame y B w b →
    ∀ (M : ℕ) (a : K → ℤ) (φ : Fin M → Module.Dual Ω E), IsTwistedDualGens y B a φ →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ i : Fin N,
      ∃ (bf bg : Option K → ℕ) (f g : MRing (bundleIdx ι M) F),
        IsMultiHomog f bf ∧ IsMultiHomog g bg ∧
        (fun o => (bf o : ℤ) - bg o) = zetaDeg + liftDeg (b i - a) ∧
        f ∉ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) ∧
        g ∉ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) ∧
        eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) f =
          t i * eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
            (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) g

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem FlagBundleDim.proof (hspan : TwistedDualGensSpan.Statement)
    (hdim : SpanBundleDim.Statement) : FlagBundleDim.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hV hdimV N E _ _ B w b hflag M a φ hφ Φ _ _ t ht i hi1 hiN

  have hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0 := fun k => by
    obtain ⟨j, hj⟩ := hV.relevant k
    refine ⟨j, fun h0 => hj ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    simp [pointConeMap, h0]
  choose c hc using hne
  have hyc : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hsp := hspan F Ω K ι y N E B a M φ hφ c hyc

  have hv : ∀ m : Fin N, ∃ v ∈ B.lat c, (∀ j, m < j → w.repr v j = 0) ∧
      w.repr v m = ∏ k, y ⟨k, c k⟩ ^ b m k := by
    intro m
    have hmem : (∏ k, y ⟨k, c k⟩ ^ b m k) ∈ degLat F y (b m) c := ⟨1, one_mem _, (one_mul _).symm⟩
    rw [← hflag.graded c hyc m] at hmem
    exact hmem
  choose v hvl hvz hvd using hv
  obtain ⟨ι', hι'⟩ : ∃ ι' : Fin i → Fin N, ι' = Fin.castLE hiN := ⟨_, rfl⟩
  have hsum : ∀ {β : Type} [AddCommMonoid β] (f : Fin N → β), (∀ j : Fin N, i ≤ (j : ℕ) → f j = 0) →
      ∑ j, f j = ∑ j : Fin i, f (ι' j) := by
    intro β _ f hf
    have hm : ∑ j : Fin i, f (ι' j) = ∑ j ∈ Finset.univ.map (Fin.castLEEmb hiN), f j := by
      rw [Finset.sum_map, hι']
      rfl
    rw [hm]
    refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => hf j ?_).symm
    by_contra h
    exact hj (Finset.mem_map.mpr ⟨⟨j, by omega⟩, Finset.mem_univ _, rfl⟩)
  obtain ⟨G, hG⟩ : ∃ G : Fin M → Fin i → Ω, G = fun l j => φ l (w (ι' j)) := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : Matrix (Fin i) (Fin i) Ω, H = Matrix.of fun j m => w.repr (v (ι' m)) (ι' j) :=
    ⟨_, rfl⟩
  have hinj : Function.Injective ι' := by
    rw [hι']
    exact Fin.castLE_injective hiN
  have hval : ∀ m : Fin i, ((ι' m : Fin N) : ℕ) = m := fun m => by
    rw [hι', Fin.val_castLE]
  have hlt : ∀ m j : Fin i, m < j → ι' m < ι' j := fun m j h => by
    rw [Fin.lt_def, hval, hval]
    exact Fin.lt_def.mp h
  have hGH : ∀ l m, (Matrix.of G * H) l m = φ l (v (ι' m)) := by
    intro l m
    conv_rhs => rw [← w.sum_repr (v (ι' m))]

    rw [map_sum, hsum]
    · simp [Matrix.mul_apply, hG, hH, mul_comm]
    · intro j hj
      have hm := m.isLt
      rw [map_smul, hvz _ j (by rw [Fin.lt_def, hval]; omega), zero_smul]
  have hdet : IsUnit H.det := by
    rw [Matrix.det_of_isUpperTriangular (M := H) fun j m hjm => by
      rw [hH, Matrix.of_apply]
      exact hvz _ _ (hlt m j hjm)]
    refine isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun m _ => ?_)
    simp only [hH, Matrix.of_apply, hvd]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  have hlin : LinearIndependent Ω (fun j l => G l j) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hall : ∀ ψ ∈ Submodule.span Ω (Set.range φ), ψ (∑ j, g j • w (ι' j)) = 0 := by
      intro ψ hψ
      induction hψ using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨l, rfl⟩ := hx
        have := congrFun hg l

        simpa [hG, map_sum, Finset.sum_apply, mul_comm] using this
      | zero => simp
      | add x z _ _ hx hz => rw [LinearMap.add_apply, hx, hz, add_zero]
      | smul r x _ hx => rw [LinearMap.smul_apply, hx, smul_zero]
    rw [hsp] at hall
    have hw := (Module.forall_dual_apply_eq_zero_iff Ω _).mp fun ψ => hall ψ Submodule.mem_top
    exact Fintype.linearIndependent_iff.mp (w.linearIndependent.comp ι' hinj) g hw
  have hcoord : projCoord y w φ (truncCoord t i) =
      projCoord y (Pi.basisFun Ω (Fin i)) (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) (t ∘ ι') := by
    funext p
    rcases p with ⟨_ | k, l⟩
    · show ∑ j, truncCoord t i j * _ = ∑ j, _
      rw [hsum]
      · refine Finset.sum_congr rfl fun j _ => ?_
        have hj : ((ι' j : Fin N) : ℕ) < i := by rw [hval]; exact j.isLt
        simp only [truncCoord, hj, if_true, hG, Function.comp_apply, Pi.basisFun_apply]
        rw [LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
        rfl
      · intro j hj
        simp [truncCoord, not_lt.mpr hj]
    · rfl
  have hproj : projIdeal F y w φ (truncCoord t i) = projIdeal F y (Pi.basisFun Ω (Fin i))
      (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) (t ∘ ι') := by
    unfold projIdeal
    rw [hcoord]
  rw [hproj]
  exact hdim F Ω K ι y e hV hdimV M i G (by omega) hlin c a H hyc hdet
    (fun l m => by rw [hGH]; exact hφ.sections c hyc l _ (hvl _)) Φ (t ∘ ι')
    (ht.comp ι' hinj)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

theorem isHomogeneous_multiset_prod_map {σ : Type*} (φ : ℕ → MvPolynomial σ ℤ)
    (hφ : ∀ b, (φ b).IsHomogeneous b) (t : Multiset ℕ) : ((t.map φ).prod).IsHomogeneous t.sum := by
  induction t using Multiset.induction_on with
  | empty => simpa using isHomogeneous_one σ ℤ
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    exact (hφ a).mul ih

theorem isHomogeneous_hsymm (N a : ℕ) : (hsymm (Fin N) ℤ a).IsHomogeneous a := by
  have h : ∀ t : Multiset (Fin N),
      ((t.map X).prod : MvPolynomial (Fin N) ℤ).IsHomogeneous (Multiset.card t) := by
    intro t
    induction t using Multiset.induction_on with
    | empty => simpa using isHomogeneous_one (Fin N) ℤ
    | cons b t ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, add_comm]
      exact (isHomogeneous_X ℤ b).mul ih
  unfold hsymm
  refine IsHomogeneous.sum _ _ _ fun s _ => ?_
  simpa [s.2] using h s.1

theorem FlagIndependence.proof (hExp : PairNumberExpansionIndependence.Statement)
    (hSeg : HsymmPairFlagIndependence.Statement) (hSym : SymmetricSpanHsymm.Statement) :
    FlagIndependence.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hBB' w w' v v' x x' u u' f g f₂ g₂
    hF1 hF2 m G hGm hGsym Gs Hs hGs hHs Q hQ
  classical

  have hvert : ∀ i, IsVerticalDivisor (pointIdeal O y) ϖ (Fin.append x u i - Fin.append x' u' i)
      (Fin.append f f₂ i) (Fin.append g g₂ i) := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]
      exact hF1.vertical i
    · simp only [Fin.append_right]
      exact hF2.vertical i
  have hind : ∀ (A : MvPolynomial (Fin (N + N)) ℤ) As Bs, A.IsHomogeneous m →
      IsPairExpansion m A As → IsPairExpansion m A Bs →
      pairNum (pointIdeal O y) (Fin.append x u) (Fin.append x' u') (Fin.append f f₂)
          (Fin.append g g₂) As Q =
        pairNum (pointIdeal O y) (Fin.append x u) (Fin.append x' u') (Fin.append f f₂)
          (Fin.append g g₂) Bs Q :=
    fun A As Bs hA h1 h2 => hExp O ϖ hϖ K ι _ d hV (N + N) _ _ _ _ hvert m A hA As Bs h1 h2 Q hQ

  let ex : MvPolynomial (Fin (N + N)) ℤ → Fin (N + N) → MvPolynomial (Fin (N + N) ⊕ Fin (N + N)) ℤ :=
    fun A => Classical.choose (exists_isPairExpansion (homogeneousComponent_isHomogeneous m A))
  have hex : ∀ A, IsPairExpansion m (homogeneousComponent m A) (ex A) :=
    fun A => Classical.choose_spec (exists_isPairExpansion (homogeneousComponent_isHomogeneous m A))
  let pn : MvPolynomial (Fin (N + N)) ℤ →+ ℤ := AddMonoidHom.mk'
    (fun A => pairNum (pointIdeal O y) (Fin.append x u) (Fin.append x' u') (Fin.append f f₂)
      (Fin.append g g₂) (ex A) Q)
    (by
      intro A B'
      have h2 : IsPairExpansion m (homogeneousComponent m (A + B')) (ex A + ex B') := by
        rw [map_add (f := _)]
        exact isPairExpansion_add (hex A) (hex B')
      rw [hind _ _ _ (homogeneousComponent_isHomogeneous m _) (hex (A + B')) h2]
      exact map_add (pairNumHom (pointIdeal O y) (Fin.append x u) (Fin.append x' u')
        (Fin.append f f₂) (Fin.append g g₂) Q) (ex A) (ex B'))
  have pn_eq : ∀ (A : MvPolynomial (Fin (N + N)) ℤ) As, A.IsHomogeneous m →
      IsPairExpansion m A As →
      pn A = pairNum (pointIdeal O y) (Fin.append x u) (Fin.append x' u') (Fin.append f f₂)
        (Fin.append g g₂) As Q := by
    intro A As hA h
    have h1 := hex A
    rw [homogeneousComponent_eq_self hA] at h1
    exact hind A _ _ hA h1 h

  have seg : ∀ (a r : ℕ) (R : MvPolynomial (Fin (N + N)) ℤ), R.IsHomogeneous r → a + r = m →
      pn (rename (Fin.castAdd N) (hsymm (Fin N) ℤ a) * R) =
        pn (rename (Fin.natAdd N) (hsymm (Fin N) ℤ a) * R) := by
    intro a r R hR har
    have hH : (hsymmTimes N (N + N) a R).IsHomogeneous (a + r) :=
      (isHomogeneous_hsymm N a).rename_isHomogeneous.mul hR.rename_isHomogeneous
    obtain ⟨As, hAs⟩ := exists_isPairExpansion hH
    have key := hSeg O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' v v' x x' u u' f g f₂ g₂ hF1 hF2
      (N + N) _ _ _ _ hvert a r R hR As As hAs hAs Q (by rw [har]; exact hQ)
    let σx : Fin (N + (N + N)) → Fin (N + N) := Fin.append (Fin.castAdd N) id
    let σu : Fin (N + (N + N)) → Fin (N + N) := Fin.append (Fin.natAdd N) id
    have cx : ∀ {α : Type} (a₁ a₂ : Fin N → α),
        Fin.append a₁ a₂ ∘ σx = Fin.append a₁ (Fin.append a₁ a₂) := by
      intro α a₁ a₂
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
        simp only [σx, Function.comp_apply, Fin.append_left, Fin.append_right, id_eq]
    have cu : ∀ {α : Type} (a₁ a₂ : Fin N → α),
        Fin.append a₁ a₂ ∘ σu = Fin.append a₂ (Fin.append a₁ a₂) := by
      intro α a₁ a₂
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
        simp only [σu, Function.comp_apply, Fin.append_left, Fin.append_right, id_eq]
    have rx : rename σx (hsymmTimes N (N + N) a R) =
        rename (Fin.castAdd N) (hsymm (Fin N) ℤ a) * R := by
      have e1 : σx ∘ Fin.castAdd (N + N) = Fin.castAdd N := by
        funext i
        simp only [σx, Function.comp_apply, Fin.append_left]
      have e2 : σx ∘ Fin.natAdd N = id := by
        funext i
        simp only [σx, Function.comp_apply, Fin.append_right, id_eq]
      simp only [hsymmTimes, map_mul, rename_rename, e1, e2, rename_id, AlgHom.id_apply]
    have ru : rename σu (hsymmTimes N (N + N) a R) =
        rename (Fin.natAdd N) (hsymm (Fin N) ℤ a) * R := by
      have e1 : σu ∘ Fin.castAdd (N + N) = Fin.natAdd N := by
        funext i
        simp only [σu, Function.comp_apply, Fin.append_left]
      have e2 : σu ∘ Fin.natAdd N = id := by
        funext i
        simp only [σu, Function.comp_apply, Fin.append_right, id_eq]
      simp only [hsymmTimes, map_mul, rename_rename, e1, e2, rename_id, AlgHom.id_apply]
    have hpx := isPairExpansion_push σx hAs
    have hpu := isPairExpansion_push σu hAs
    rw [rx, har] at hpx
    rw [ru, har] at hpu
    rw [pn_eq _ _ (har ▸ ((isHomogeneous_hsymm N a).rename_isHomogeneous.mul hR)) hpx,
      pn_eq _ _ (har ▸ ((isHomogeneous_hsymm N a).rename_isHomogeneous.mul hR)) hpu,
      pairNum_pushExpansion, pairNum_pushExpansion, cx, cx, cx, cx, cu, cu, cu, cu]
    exact key

  have hX : ∀ b, (rename (Fin.castAdd N) (hsymm (Fin N) ℤ b) :
      MvPolynomial (Fin (N + N)) ℤ).IsHomogeneous b :=
    fun b => (isHomogeneous_hsymm N b).rename_isHomogeneous
  have hU : ∀ b, (rename (Fin.natAdd N) (hsymm (Fin N) ℤ b) :
      MvPolynomial (Fin (N + N)) ℤ).IsHomogeneous b :=
    fun b => (isHomogeneous_hsymm N b).rename_isHomogeneous
  have tele : ∀ (t : Multiset ℕ) (s : ℕ) (S : MvPolynomial (Fin (N + N)) ℤ), S.IsHomogeneous s →
      s + t.sum = m →
      pn (S * (t.map fun b => rename (Fin.castAdd N) (hsymm (Fin N) ℤ b)).prod) =
        pn (S * (t.map fun b => rename (Fin.natAdd N) (hsymm (Fin N) ℤ b)).prod) := by
    intro t
    induction t using Multiset.induction_on with
    | empty => intros; rfl
    | cons a t ih =>
      intro s S hS hst
      rw [Multiset.sum_cons] at hst
      simp only [Multiset.map_cons, Multiset.prod_cons]
      have hpX := isHomogeneous_multiset_prod_map _ hX t
      calc pn (S * (rename (Fin.castAdd N) (hsymm (Fin N) ℤ a) *
              (t.map fun b => rename (Fin.castAdd N) (hsymm (Fin N) ℤ b)).prod))
          = pn (rename (Fin.castAdd N) (hsymm (Fin N) ℤ a) *
              (S * (t.map fun b => rename (Fin.castAdd N) (hsymm (Fin N) ℤ b)).prod)) := by
            rw [mul_left_comm]
        _ = pn (rename (Fin.natAdd N) (hsymm (Fin N) ℤ a) *
              (S * (t.map fun b => rename (Fin.castAdd N) (hsymm (Fin N) ℤ b)).prod)) :=
            seg a (s + t.sum) _ (hS.mul hpX) (by omega)
        _ = pn ((S * rename (Fin.natAdd N) (hsymm (Fin N) ℤ a)) *
              (t.map fun b => rename (Fin.castAdd N) (hsymm (Fin N) ℤ b)).prod) := by
            congr 1
            ring
        _ = pn ((S * rename (Fin.natAdd N) (hsymm (Fin N) ℤ a)) *
              (t.map fun b => rename (Fin.natAdd N) (hsymm (Fin N) ℤ b)).prod) :=
            ih (s + a) _ (hS.mul (hU a)) (by omega)
        _ = pn (S * (rename (Fin.natAdd N) (hsymm (Fin N) ℤ a) *
              (t.map fun b => rename (Fin.natAdd N) (hsymm (Fin N) ℤ b)).prod)) := by
            rw [mul_assoc]

  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hSym N m G hGm hGsym)
  have hren : ∀ (φ : Fin N → Fin (N + N)), rename φ G =
      ∑ μ, c μ • (μ.parts.map fun b => rename φ (hsymm (Fin N) ℤ b)).prod := by
    intro φ

    rw [← hc, map_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [map_zsmul, hsymmPart, map_multiset_prod, Multiset.map_map]
    rfl
  have hLHS : pairNum (pointIdeal O y) x x' f g Gs Q = pn (rename (Fin.castAdd N) G) := by
    rw [pn_eq _ _ hGm.rename_isHomogeneous (isPairExpansion_push (Fin.castAdd N) hGs),
      pairNum_pushExpansion]
    simp only [Function.comp_def, Fin.append_left]
  have hRHS : pairNum (pointIdeal O y) u u' f₂ g₂ Hs Q = pn (rename (Fin.natAdd N) G) := by
    rw [pn_eq _ _ hGm.rename_isHomogeneous (isPairExpansion_push (Fin.natAdd N) hHs),
      pairNum_pushExpansion]
    simp only [Function.comp_def, Fin.append_right]

  rw [hLHS, hRHS, hren, hren, map_sum, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_zsmul, map_zsmul]
  congr 1
  have h := tele μ.parts 0 1 (isHomogeneous_one _ _) (by rw [μ.parts_sum, zero_add])
  simpa only [one_mul] using h

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

def VocabMultiHomog.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (s : MRing ι R) (a : K → ℕ),
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a ↔ IsMultiHomog s a

def VocabMultiHomogIdeal.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι R)),
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal P ↔ IsMultiHomogIdeal P

def VocabDivCycle.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι R)) (s : MRing ι R) (W : Ideal (MRing ι R)),
    ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W : ℕ) : ℤ) = divCycle P s W

def IntNumPoint.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (V : Ideal (MRing ι F)) (i : ∀ k, ι k), IsMultiProjPrime V →
    ringKrullDim (MRing ι F ⧸ V) = ((0 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    (∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ V) →
    intNum F V (![] : Fin 0 → K → ℤ) = ReciprocityTheory.ChartRestriction.G.AI.I1.ptDeg V i

def IntNumRatSection.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (n : ℕ) (V : Ideal (MRing ι F)), IsMultiProjPrime V →
    ringKrullDim (MRing ι F ⧸ V) = ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (L : Fin n → K → ℤ) (A : K → ℤ) (f g : MRing ι F) (α β : K → ℕ),
      IsMultiHomog f α → IsMultiHomog g β → f ∉ V → g ∉ V → (∀ k, (α k : ℤ) - β k = A k) →
      intNum F V (Fin.snoc (α := fun _ => K → ℤ) L A) =
        cycEval (fun W => intNum F W L) (ratDiv V f g)

def IntNumIsFieldIntersection.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)],
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection (F := F) (ι := ι) (fun V _ L => intNum F V L)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
