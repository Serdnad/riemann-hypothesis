module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle380
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle346
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle192
public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle156
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisNormOfNonzero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle297
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle367
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX

noncomputable section

namespace GlobalTheory.Pass.LocDual.OneX

section VecGen
variable {K L : Type} [Field K] [Field L] (φ : K →+* L) (a n : ℕ)

def vecS : (Fin a → Fin n → K) →ₛₗ[φ] (Fin a → Fin n → L) where
  toFun v := fun b j => φ (v b j)
  map_add' u v := by funext b j; simp
  map_smul' c v := by funext b j; simp

variable {φ a n}

theorem vecS_apply (v : Fin a → Fin n → K) (b : Fin a) (j : Fin n) : vecS φ a n v b j = φ (v b j) := rfl

theorem span_vecS_span (S : Set (Fin a → Fin n → K)) :
    Submodule.span L (vecS φ a n '' (Submodule.span K S : Set (Fin a → Fin n → K))) =
      Submodule.span L (vecS φ a n '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    induction hv using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem finrank_span_vecS_le (W : Submodule K (Fin a → Fin n → K)) :
    finrank L (Submodule.span L (vecS φ a n '' (W : Set (Fin a → Fin n → K)))) ≤ finrank K W := by
  let b := Module.finBasis K W
  let g : Fin (Module.finrank K W) → (Fin a → Fin n → L) := fun i => vecS φ a n (b i)
  have hle : Submodule.span L (vecS φ a n '' (W : Set (Fin a → Fin n → K))) ≤ Submodule.span L (Set.range g) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    have h : w = ∑ i, b.repr ⟨w, hw⟩ i • (b i : Fin a → Fin n → K) := by
      have := congrArg W.subtype (b.sum_repr ⟨w, hw⟩)

      rw [map_sum] at this
      exact this.symm

    rw [h, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have h1 := Submodule.finrank_mono hle
  have h2 : Module.finrank L (Submodule.span L (Set.range g)) ≤ Module.finrank K W := by
    have := finrank_range_le_card (R := L) g
    simpa [Set.finrank] using this
  exact h1.trans h2

theorem span_vecS_top : Submodule.span L (Set.range (vecS φ a n)) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  have e : u = ∑ b, ∑ j, u b j • vecS φ a n (fun b'' j'' => if b'' = b ∧ j'' = j then 1 else 0) := by
    funext b' j'
    simp only [Finset.sum_apply, Pi.smul_apply, vecS_apply, smul_eq_mul, apply_ite φ, map_one, map_zero, mul_ite,
      mul_one, mul_zero, ite_and]
    simp [Finset.sum_ite_eq]
  rw [e]
  exact Submodule.sum_mem _ fun b _ => Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem isCompl_span_vecS {W W' : Submodule K (Fin a → Fin n → K)} (h : IsCompl W W') :
    IsCompl (Submodule.span L (vecS φ a n '' (W : Set (Fin a → Fin n → K))))
      (Submodule.span L (vecS φ a n '' (W' : Set (Fin a → Fin n → K)))) := by
  set A := Submodule.span L (vecS φ a n '' (W : Set (Fin a → Fin n → K)))
  set B := Submodule.span L (vecS φ a n '' (W' : Set (Fin a → Fin n → K)))
  have hsup : A ⊔ B = ⊤ := by
    rw [eq_top_iff, ← span_vecS_top (φ := φ), Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ W ⊔ W' := by rw [h.sup_eq_top]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add (f := _)]
    exact add_mem (Submodule.mem_sup_left (Submodule.subset_span ⟨y, hy, rfl⟩))
      (Submodule.mem_sup_right (Submodule.subset_span ⟨z, hz, rfl⟩))
  have h1 : finrank L A ≤ finrank K W := finrank_span_vecS_le W
  have h2 : finrank L B ≤ finrank K W' := finrank_span_vecS_le W'
  have h3 := Submodule.finrank_add_eq_of_isCompl h
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hsup, finrank_top] at h4
  have hK : finrank K (Fin a → Fin n → K) = a * n := by
    rw [Module.finrank_pi_fintype]; simp
  have hL : finrank L (Fin a → Fin n → L) = a * n := by
    rw [Module.finrank_pi_fintype]; simp
  have hinf : A ⊓ B = ⊥ := by
    rw [← Submodule.finrank_eq_zero]; omega
  exact ⟨disjoint_iff.2 hinf, codisjoint_iff.2 hsup⟩

end VecGen




theorem isSummandTw_XG : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)) (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y),
    (∃ C : Submodule (KK D.nd i) (Fin a → Fin D.R.nV → KK D.nd i),
    (∀ γ : GE D.nd, ∀ v ∈ C, actK i r Xs x γ v ∈ C) ∧
    IsCompl (Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i))) C) →
    IsSummandTw i w hw r Xs (XG i w hw r Xs hr x Y hst) := by
  intro D i w hw r Xs hr a x Y hst ⟨C, hC, hYC⟩
  have hspan : spanL i w hw Y = Submodule.span _ (vecS (Br.toLLK (D.nbr i w hw)) a D.R.nV ''
      (Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i)) : Set (Fin a → Fin D.R.nV → KK D.nd i))) := by
    rw [span_vecS_span]; rfl
  refine ⟨a, x, (spanL i w hw Y).subtype, Subtype.val_injective, fun g v => rfl,
    Submodule.span _ (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i))), ?_, ?_⟩
  · intro g u hu
    have hle : Submodule.span (Br.LL D.nbr i w hw) (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i))) ≤
        (Submodule.span (Br.LL D.nbr i w hw) (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i)))).comap
          ((sumG i w hw r Xs hr x).ρ g) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨v, hv, rfl⟩
      show (sumG i w hw r Xs hr x).ρ g (vecL i w hw v) ∈
        Submodule.span (Br.LL D.nbr i w hw) (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i)))
      rw [sumG_vecL]
      exact Submodule.subset_span ⟨_, hC _ v hv, rfl⟩
    exact hle hu
  · have key : IsCompl (spanL i w hw Y)
        (Submodule.span (Br.LL D.nbr i w hw) (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i)))) := by
      rw [hspan]
      exact isCompl_span_vecS hYC
    convert key using 1
    exact Submodule.range_subtype _

end GlobalTheory.Pass.LocDual.OneX

end
end

section

open NumberField Matrix GlobalTheory.CuspRep

noncomputable section

open MeasureTheory GroundTheory.Automorphic.FourierWhittaker

namespace GlobalTheory.CuspGeneric.WhitEq

theorem avg_eq_setIntegral {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [m : MeasurableSpace G] [hB : BorelSpace G]
    (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G) [μ.IsAddHaarMeasure] (D : Set G)
    (hD : IsAddFundamentalDomain Γ D μ) (h1 : μ D = 1) (Φ : G → ℂ)
    (hΦ : ∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) :
    avg Γ Φ = ∫ x in D, Φ x ∂μ := by
  obtain ⟨rfl⟩ := hB
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  have hex : ∃ p : Measure G × Set G, p.1.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ p.2 p.1 ∧ p.1 p.2 = 1 :=
    ⟨(μ, D), inferInstance, hD, h1⟩
  unfold avg
  rw [dite_eq_left hex]
  obtain ⟨hH, hD', h1'⟩ := hex.choose_spec
  set ν := hex.choose.1
  set D' := hex.choose.2
  have hν : ν = Measure.addHaarScalarFactor ν μ • μ := Measure.isAddLeftInvariant_eq_smul ν μ
  have hc0 : Measure.addHaarScalarFactor ν μ ≠ 0 := by
    intro h0
    have : ν = 0 := by rw [hν, h0, zero_smul]
    have hpos : 0 < ν Set.univ := IsOpen.measure_pos ν isOpen_univ ⟨0, trivial⟩
    rw [this] at hpos
    simp at hpos
  have hac : μ ≪ ν := by
    rw [hν]
    exact Measure.absolutelyContinuous_smul (by exact_mod_cast hc0)
  have hDμ : IsAddFundamentalDomain Γ D' μ := hD'.mono hac
  have hμD' : μ D' = 1 := by rw [hDμ.measure_eq hD, h1]
  have hc1 : Measure.addHaarScalarFactor ν μ = 1 := by
    have := h1'
    rw [hν, Measure.smul_apply, hμD', ENNReal.smul_def, smul_eq_mul, mul_one] at this
    exact_mod_cast this
  have hνμ : ν = μ := by rw [hν, hc1, one_smul]
  rw [hνμ]
  exact hDμ.setIntegral_eq hD fun g x => hΦ g g.2 x

def colIx {a k : ℕ} (hk : k < a) : UnipotentBlockColumnIndex a k k ≃ Fin k where
  toFun t := ⟨t.1.1.val, t.2.1⟩
  invFun i := ⟨(⟨i.val, by omega⟩, ⟨k, hk⟩), i.2, le_rfl, le_rfl⟩
  left_inv t := by
    obtain ⟨⟨i, j⟩, h1, h2, h3⟩ := t
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      show k = (j : ℕ)
      simp only at h2 h3
      omega
  right_inv i := rfl

theorem blkU_eq_colGL {R : Type} [CommRing R] {a k : ℕ} (hk : k < a) (x : UnipotentBlockColumnIndex a k k → R) :
    (blkU x : GL (Fin a) R) = colGL (n := a) k (fun i => x ((colIx hk).symm i)) := by
  apply Units.ext
  ext i j
  change (1 + posM Subtype.val x : Matrix (Fin a) (Fin a) R) i j = uMat (colX (n := a) k _) i j
  rw [uMat_apply, Matrix.add_apply, posM, Matrix.sum_apply, Matrix.one_apply]
  by_cases hij : (i : ℕ) < k ∧ (j : ℕ) = k
  · have hne : i ≠ j := fun h => by rw [h] at hij; omega
    have hlt : i < j := by rw [Fin.lt_def]; omega
    rw [Finset.sum_eq_single (⟨(i, j), hij.1, hij.2.ge, hij.2.le⟩ : UnipotentBlockColumnIndex a k k)]
    · rw [if_neg hne, if_neg hne, dite_eq_left hlt, colX_apply, dite_eq_left hij.2, Matrix.single_apply_same, zero_add]
      congr 1
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Fin.ext
        show (j : ℕ) = k
        exact hij.2
    · intro t _ ht
      rw [Matrix.single_apply_of_ne]
      rintro ⟨h1, h2⟩
      exact ht (Subtype.ext (Prod.ext h1 h2))
    · simp
  · rw [Finset.sum_eq_zero]
    · rw [add_zero]
      split_ifs with h1 h2
      · rfl
      · rw [colX_apply, dite_eq_right]
        intro h3
        exact hij ⟨by rw [← h3]; exact h2, h3⟩
      · rfl
    · intro t _
      rw [Matrix.single_apply_of_ne]
      rintro ⟨h1, h2⟩
      apply hij
      have := t.2
      rw [← h1, ← h2]
      omega

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem dot_eLast {k : ℕ} (hk : k < a) (x : UnipotentBlockColumnIndex a k k → Ad E) :
    dot (eLast a k) x = pair (lastVec k) (fun i => x ((colIx hk).symm i)) := by
  unfold dot pair
  refine Fintype.sum_equiv (colIx hk) _ _ fun t => ?_
  dsimp only
  rw [Equiv.symm_apply_apply]
  rfl

theorem colT_eq_stepCoeff {k : ℕ} (hk : k < a) (f : GA E a → ℂ)
    (hf : ∀ (ξ : Fin k → E) g, f (ratGL E a (colGL k ξ) * g) = f g) (g : GA E a) :
    colT (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) k f g = stepCoeff k f g := by
  set ψ₀ : AddChar (Ad E) ℂ := Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)
  have hψ : ∀ y, ψ₀ y = (GroundTheory.Global.adelicChar E y : ℂ) := fun y => rfl
  set Φ : (UnipotentBlockColumnIndex a k k → Ad E) → ℂ := fun x => ψ₀ (-dot (eLast a k) x) * f (blkU x * g) with hΦdef
  have hΦ : ∀ γ ∈ ratV E (UnipotentBlockColumnIndex a k k), ∀ x, Φ (γ + x) = Φ x := by
    rintro _ ⟨c, rfl⟩ x
    have e1 : (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (UnipotentBlockColumnIndex a k k)) c =
        fun t => algebraMap E (Ad E) (c t) := rfl
    rw [e1]
    have hU : f (blkU ((fun t => algebraMap E (Ad E) (c t)) + x) * g) = f (blkU x * g) := by
      change f (posU _ _ * g) = _
      rw [posU_add, mul_assoc]
      change f (blkU _ * _) = _
      rw [← ratGL_blkU, blkU_eq_colGL hk, hf]
      rfl
    have hD : dot (eLast a k) ((fun t => algebraMap E (Ad E) (c t)) + x) =
        algebraMap E (Ad E) (∑ t, eLast a k t * c t) + dot (eLast a k) x := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_sum, map_mul]
    simp only [Φ]
    rw [hU, hD, neg_add, AddChar.map_add_eq_mul, hψ (-(algebraMap E (Ad E) _)), ← map_neg,
      GroundTheory.Global.adelicChar_algebraMap, Circle.coe_one, one_mul]
  haveI : Countable (ratV E (UnipotentBlockColumnIndex a k k)) := countable_vecLattice
  have hA : avg (ratV E (UnipotentBlockColumnIndex a k k)) Φ = ∫ x in vecDomain E (UnipotentBlockColumnIndex a k k), Φ x ∂vecMeasure E (UnipotentBlockColumnIndex a k k) :=
    avg_eq_setIntegral (ratV E (UnipotentBlockColumnIndex a k k)) (vecMeasure E (UnipotentBlockColumnIndex a k k)) (vecDomain E (UnipotentBlockColumnIndex a k k))
      isAddFundamentalDomain_vecDomain vecMeasure_vecDomain Φ hΦ
  change avg (ratV E (UnipotentBlockColumnIndex a k k)) Φ = _
  rw [hA]
  let Em := MeasurableEquiv.piCongrLeft (fun _ : Fin k => Ad E) (colIx hk)
  have hE : MeasurePreserving Em (vecMeasure E (UnipotentBlockColumnIndex a k k)) (vecMeasure E (Fin k)) :=
    measurePreserving_piCongrLeft (fun _ : Fin k => GroundTheory.Global.adeleMeasure E) (colIx hk)
  have hEx : ∀ x : UnipotentBlockColumnIndex a k k → Ad E, Em x = fun i => x ((colIx hk).symm i) := by
    intro x
    funext i
    simp [Em, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  have hpre : Em ⁻¹' vecDomain E (Fin k) = vecDomain E (UnipotentBlockColumnIndex a k k) := by
    ext x
    simp only [Set.mem_preimage, hEx, vecDomain, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h t
      have := h (colIx hk t)
      rwa [Equiv.symm_apply_apply] at this
    · intro h i
      exact h _
  rw [stepCoeff, vecCoeff, ← hE.setIntegral_preimage_emb Em.measurableEmbedding, hpre]
  refine setIntegral_congr_fun measurableSet_vecDomain fun x _ => ?_
  simp only [Φ, hEx, hψ]
  rw [blkU_eq_colGL hk, dot_eLast hk, mul_comm]

theorem whit_partialCoeff (F : GA E a → ℂ) (hl : ∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g) :
    ∀ m, m + 1 ≤ a → whit (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) m (partialCoeff F (m + 1)) =
      partialCoeff F 1 := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    have hk : m + 1 < a := by omega
    rw [whit_succ]
    have hcol : colT (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) (m + 1) (partialCoeff F (m + 1 + 1)) =
        partialCoeff F (m + 1) := by
      funext g
      rw [colT_eq_stepCoeff hk _ (fun ξ g => partialCoeff_succ_diagonal_colGL (K := E) (n := a) hl hk ξ g),
        partialCoeff_of_lt F hk]
    rw [hcol]
    exact ih (by omega)

theorem whit_eq_whittaker : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (F : GA E a → ℂ), 0 < a → Continuous F →
    (∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g) →
    GlobalTheory.CuspGeneric.whit (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) (a - 1) F = GlobalTheory.JSW.whit F := by
  intro E _ _ a F ha hc hl
  have h := whit_partialCoeff F hl (a - 1) (by omega)
  rw [Nat.sub_add_cancel ha, partialCoeff_self] at h
  rw [h]
  funext g
  exact (whittaker_eq_partialCoeff hc ha g).symm

end GlobalTheory.CuspGeneric.WhitEq
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory

theorem sum_inv_eq_zero_of_unramified_cocycle_pow : PoitouTateTotallyComplex → ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (ζ : Ω), 0 < n → IsPrimitiveRoot ζ (l ^ n) → ∃ inv : InvFam F Ω l n, IsLocalInvariants ζ inv ∧ ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ContainsAbove S l → ∀ Av : HeightOneSpectrum (𝓞 F) → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v) → ∀ w : Z2 (muRep F Ω l n), (∀ g h : G F Ω, ∀ u ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))), ∀ u' ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))), w.1 (g * u, h * u') = w.1 (g, h)) → ∀ wl : ∀ v, Z2 (muLoc F l n (Av v)), (∀ v (g h : Dec (F := F) (Av v)), (wl v).1 (g, h) = w.1 ((g : G F Ω), (h : G F Ω))) → ∑ v ∈ S, inv (Av v) (Submodule.Quotient.mk (wl v)) = 0 := by
  intro hPT F Ω _ _ _ _ _ _ l _ n ζ hn hζ
  obtain ⟨inv, hinv, H⟩ := hPT.annihilators F Ω l n hn ζ hζ
  refine ⟨inv, hinv, fun S hS Av hA w hw wl hwl => ?_⟩
  obtain ⟨μ, hμ⟩ := exists_lift_cycMod (Ω := Ω) (r := n) hS
  obtain ⟨W, hWc, hW⟩ := exists_descend_pair_quotient _ w.1 w.2.1 hw
  have hmem : W ∈ Z2 (charRep μ) := by
    refine ⟨hWc, fun g h k => ?_⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective h
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective k
    have e := w.2.2 g h k
    have e2 : μ (g : G F Ω ⧸ _) = cycMod F Ω l n g := DFunLike.congr_fun hμ g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hW, hW, hW, hW, charRep_apply, e2]
    exact e
  have e := (H S hS (fun v => Av v.1) (fun v => hA v.1) μ hμ).1
    (Submodule.Quotient.mk ⟨W, hmem⟩)
  rw [← Finset.sum_coe_sort]
  refine Eq.trans (Finset.sum_congr rfl fun v _ => ?_) e
  refine congrArg (inv (Av v.1)) ?_
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun p => ?_))
  exact (hwl v.1 p.1 p.2).trans (hW _ _).symm

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.CoefField

theorem entries_mem_of_finset : ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ) (ρ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)), Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l))) → ∃ S : Finset (Qbar l), ∀ K : IntermediateField ℚ_[l] (Qbar l), (∀ z ∈ S, z ∈ K) → ∀ g s t, ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) s t ∈ K := by
  intro l _ E Ω _ _ _ _ _ a ρ hρ
  obtain ⟨L, -, hL⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (Formalism.ConjugateSelfDual.G E Ω) a ρ hρ
    ⟨⊥, inferInstance⟩
  haveI := L.2
  let B := Module.finBasis ℚ_[l] ↥L.1
  classical
  refine ⟨Finset.univ.image (fun i => ((B i : ↥L.1) : Qbar l)), fun K hK g s t => ?_⟩
  have key : ∀ x : ↥L.1, (x : Qbar l) ∈ K := by
    intro x
    have hx : x ∈ Submodule.span ℚ_[l] (Set.range B) := B.mem_span x
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hK _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    | zero => simpa using K.zero_mem
    | add y z _ _ hy hz => simpa using K.add_mem hy hz
    | smul c y _ hy => simpa using K.smul_mem hy (x := c)
  exact key ⟨_, hL g s t⟩

end GlobalTheory.CoefField
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.acris_norm_of_nonzero : ∀ (l : ℕ) [Fact l.Prime] (N : ℝ → Per.Acris l → ℝ), (∀ r : ℝ, (l : ℝ)⁻¹ ≤ r → r < 1 → (∀ x, 0 ≤ N r x ∧ N r x ≤ 1) ∧ (∀ x y, N r (x + y) ≤ max (N r x) (N r y)) ∧ (∀ x, N r (-x) = N r x) ∧ (∀ x y, N r (x * y) = N r x * N r y) ∧ ∀ a : Per.Ainf l, N r (algebraMap (Per.Ainf l) (Per.Acris l) a) = ⨆ n : ℕ, ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) → ∀ b : Per.Acris l, b ≠ 0 → N (l : ℝ)⁻¹ b ≠ 0 := by
  first | exact @GlobalTheory.MemLoc.gauss_ne_zero | exact GlobalTheory.MemLoc.gauss_ne_zero | (intros; apply GlobalTheory.MemLoc.gauss_ne_zero <;> assumption)
end
