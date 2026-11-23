module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle048
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle030
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle050
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

variable {n : ℕ}

theorem leadForm_ne_zero {f : MvPolynomial (Fin n) ℂ} (hf : f ≠ 0) : leadForm f ≠ 0 := by
  obtain ⟨d, hd, hdeg⟩ := Finset.exists_mem_eq_sup f.support (support_nonempty.mpr hf)
    (fun m => m.sum fun _ e => e)
  intro h0
  have hc := congrArg (AddMonoidAlgebra.coeff · d) h0
  rw [leadForm, coeff_homogeneousComponent] at hc
  rw [if_pos (by rw [totalDegree, hdeg]; rfl)] at hc
  apply (mem_support_iff.mp hd)
  simpa [AddMonoidAlgebra.coeff] using hc

theorem vars_leadForm_subset (f : MvPolynomial (Fin n) ℂ) : (leadForm f).vars ⊆ f.vars := by
  intro i hi
  rw [mem_vars_iff_mem_support] at hi ⊢
  obtain ⟨d, hd, hid⟩ := hi
  refine ⟨d, ?_, hid⟩
  rw [mem_support_iff, leadForm, coeff_homogeneousComponent] at hd
  rw [mem_support_iff]
  split_ifs at hd
  · exact hd
  · exact absurd rfl hd

theorem aeval_mk_X (I : Ideal (MvPolynomial (Fin n) ℂ)) (u : Set (Fin n))
    (q : MvPolynomial u ℂ) :
    aeval (fun i : u => Ideal.Quotient.mk I (X (i : Fin n))) q =
      Ideal.Quotient.mk I (rename Subtype.val q) := by
  induction q using MvPolynomial.induction_on with
  | C a => rw [aeval_C, rename_C]; rfl
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem algebraicIndependent_mk_X_iff (I : Ideal (MvPolynomial (Fin n) ℂ)) (u : Set (Fin n)) :
    AlgebraicIndependent ℂ (fun i : u => Ideal.Quotient.mk I (X (i : Fin n))) ↔
      ∀ q : MvPolynomial u ℂ, rename Subtype.val q ∈ I → q = 0 := by
  rw [algebraicIndependent_iff]
  simp only [aeval_mk_X, Ideal.Quotient.eq_zero_iff_mem]

theorem rename_mem_of_leadIdeal (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Set (Fin n))
    (h : ∀ q : MvPolynomial u ℂ, rename Subtype.val q ∈ leadIdeal J → q = 0)
    (q : MvPolynomial u ℂ) (hq : rename Subtype.val q ∈ J) : q = 0 := by
  by_contra hq0
  have hf : rename Subtype.val q ≠ 0 := by
    rwa [Ne, ← map_zero (rename (Subtype.val : u → Fin n)),
      (rename_injective _ Subtype.val_injective).eq_iff]
  have hvars : ((leadForm (rename Subtype.val q)).vars : Set (Fin n)) ⊆
      Set.range (Subtype.val : u → Fin n) := by
    intro i hi
    obtain ⟨j, -, rfl⟩ := mem_vars_rename _ _ (vars_leadForm_subset _ hi)
    exact ⟨j, rfl⟩
  obtain ⟨r, hr⟩ := exists_rename_eq_of_vars_subset_range _ _ Subtype.val_injective hvars
  have hr0 : r = 0 := h r (hr ▸ Ideal.subset_span ⟨_, hq, rfl⟩)
  exact leadForm_ne_zero hf (by rw [← hr, hr0, map_zero])

theorem quotient_dim_le_of_minimalPrimes {R : Type*} [CommRing R] (I : Ideal R)
    {N : WithBot ℕ∞} (h : ∀ Z ∈ I.minimalPrimes, ringKrullDim (R ⧸ Z) ≤ N) :
    ringKrullDim (R ⧸ I) ≤ N := by
  rw [ringKrullDim_quotient, Order.krullDim_eq_iSup_coheight, iSup_le_iff]
  intro a
  obtain ⟨Z, hZ, hZa⟩ :=
    Ideal.exists_minimalPrimes_le ((PrimeSpectrum.mem_zeroLocus _ _).mp a.2)
  have : Z.IsPrime := hZ.1.1
  let z : PrimeSpectrum.zeroLocus (R := R) (I : Set R) :=
    ⟨⟨Z, inferInstance⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr hZ.1.2⟩
  have hza : z ≤ a := hZa
  let e : Set.Ici z ↪o PrimeSpectrum.zeroLocus (R := R) (Z : Set R) :=
    OrderEmbedding.ofMapLEIff
      (fun x => ⟨x.1.1, (PrimeSpectrum.mem_zeroLocus _ _).mpr (show Z ≤ x.1.1.asIdeal from x.2)⟩)
      fun _ _ => Iff.rfl
  calc ((Order.coheight a : ℕ∞) : WithBot ℕ∞) ≤ ((Order.coheight z : ℕ∞) : WithBot ℕ∞) :=
        WithBot.coe_le_coe.mpr (Order.coheight_anti hza)
    _ = Order.krullDim (Set.Ici z) := Order.coheight_eq_krullDim_Ici z
    _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := R) (Z : Set R)) :=
        Order.krullDim_le_of_orderEmbedding e
    _ = ringKrullDim (R ⧸ Z) := (ringKrullDim_quotient Z).symm
    _ ≤ N := h Z hZ

theorem exists_vars_isTranscendenceBasis (P : Ideal (MvPolynomial (Fin n) ℂ)) [P.IsPrime] :
    ∃ u : Set (Fin n), AlgebraicIndependent ℂ (fun i : u => Ideal.Quotient.mk P (X (i : Fin n))) ∧
      Cardinal.mk u = Algebra.trdeg ℂ (MvPolynomial (Fin n) ℂ ⧸ P) := by
  set x : Fin n → MvPolynomial (Fin n) ℂ ⧸ P := fun i => Ideal.Quotient.mk P (X i) with hx
  have hrange : Set.range x = Ideal.Quotient.mkₐ ℂ P '' Set.range X := by
    rw [← Set.range_comp]; rfl
  have hadj : Algebra.adjoin ℂ (Set.range x) = ⊤ := by
    rw [hrange, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top,
      AlgHom.range_eq_top]
    exact Ideal.Quotient.mkₐ_surjective ℂ P
  have _ : Algebra.IsAlgebraic (Algebra.adjoin ℂ (Set.range x)) (MvPolynomial (Fin n) ℂ ⧸ P) :=
    ⟨fun a => isAlgebraic_algebraMap (R := Algebra.adjoin ℂ (Set.range x))
      (⟨a, hadj ▸ Algebra.mem_top⟩ : Algebra.adjoin ℂ (Set.range x))⟩
  have _ := (faithfulSMul_iff_algebraMap_injective ℂ (MvPolynomial (Fin n) ℂ ⧸ P)).mpr
    (algebraMap ℂ _).injective
  obtain ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := ℂ) (Set.range x)
  obtain ⟨u, hu, hinj⟩ := Set.exists_image_eq_injOn_of_subset_range hts
  let g : u → t := fun i => ⟨x i, hu ▸ Set.mem_image_of_mem x i.2⟩
  have hg : Function.Injective g := fun i j hij =>
    Subtype.ext (hinj i.2 j.2 (congrArg Subtype.val hij))
  refine ⟨u, ht.1.comp g hg, ?_⟩
  rw [← ht.cardinalMk_eq_trdeg, ← hu, Cardinal.mk_image_eq_of_injOn _ _ hinj]

theorem LeadIdealDim.proof : LeadIdealDim.Statement := by
  intro n J
  apply quotient_dim_le_of_minimalPrimes
  intro P hP
  have _ : P.IsPrime := hP.1.1
  obtain ⟨u, hu, hcard⟩ := exists_vars_isTranscendenceBasis P
  have hJ : ∀ q : MvPolynomial u ℂ, rename Subtype.val q ∈ J → q = 0 :=
    rename_mem_of_leadIdeal J u fun q hq => (algebraicIndependent_mk_X_iff P u).mp hu q (hP.1.2 hq)

  let M : Submonoid (MvPolynomial (Fin n) ℂ) :=
    (nonZeroDivisors (MvPolynomial u ℂ)).map (rename (R := ℂ) (Subtype.val : u → Fin n))
  have hdis : Disjoint (J : Set (MvPolynomial (Fin n) ℂ)) M := by
    rw [Set.disjoint_left]
    rintro _ hJf ⟨q, hq, rfl⟩
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hq) (hJ q hJf)
  obtain ⟨Q, hQ, hJQ, hQM⟩ := Ideal.exists_le_prime_disjoint J M hdis
  have hQu : AlgebraicIndependent ℂ (fun i : u => Ideal.Quotient.mk Q (X (i : Fin n))) := by
    rw [algebraicIndependent_mk_X_iff]
    intro q hq
    by_contra hq0
    exact Set.disjoint_left.mp hQM hq ⟨q, mem_nonZeroDivisors_of_ne_zero hq0, rfl⟩
  obtain ⟨a, haP, htP⟩ :=
    GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg ℂ (A := MvPolynomial (Fin n) ℂ ⧸ P)
  obtain ⟨b, hbQ, htQ⟩ :=
    GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg ℂ (A := MvPolynomial (Fin n) ℂ ⧸ Q)
  have hab : a ≤ b := by
    have h := hQu.cardinalMk_le_trdeg
    rw [hcard, htP, htQ] at h
    exact_mod_cast h
  calc ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) = a := haP
    _ ≤ b := by exact_mod_cast hab
    _ = ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ Q) := hbQ.symm
    _ ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) :=
      ringKrullDim_le_of_surjective (Ideal.Quotient.factor hJQ) (Ideal.Quotient.factor_surjective hJQ)

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology MeasureTheory

noncomputable section

theorem dim_component_linForm {n d : ℕ} {J W : Ideal (MvPolynomial (Fin n) ℂ)} {u : Fin n → ℂ}
    (hJ : J.IsPrime) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ))
    (hu : linForm u ∉ J) (hW : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) := by
  have := hJ
  have hIW : J ≤ W := le_sup_left.trans hW.1.2
  have huW : linForm u ∈ W := (le_sup_right.trans hW.1.2) (Ideal.mem_span_singleton_self _)
  have hWprime : W.IsPrime := hW.1.1
  set B := MvPolynomial (Fin n) ℂ ⧸ J
  have _ : Algebra.FiniteType ℂ B :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ J) (Ideal.Quotient.mkₐ_surjective ℂ J)
  set W' : Ideal B := W.map (Ideal.Quotient.mk J)
  have hW'prime : W'.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hW'ne : W' ≠ ⊥ := by
    intro h
    apply hu
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.Quotient.mk J (linForm u) ∈ W' := Ideal.mem_map_of_mem _ huW
    rw [h, Ideal.mem_bot] at this
    exact this
  have hht : W'.height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  have hquot : ringKrullDim (B ⧸ W') = ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIW)
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient ℂ (A := B) W'
  have hdrop := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le W' hW'ne
  rw [hquot] at hform hdrop
  change ringKrullDim B = _ at hdim
  rw [hdim] at hform hdrop
  obtain ⟨y, hy⟩ : ∃ y : ℕ∞, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = y := by
    cases h : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) with
    | bot =>
      have := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ W)
      rw [h] at this
      exact absurd this (by simp)
    | coe y => exact ⟨y, rfl⟩
  rw [hy] at hform hdrop ⊢
  have h1 : y + 1 ≤ ((d + 1 : ℕ) : ℕ∞) := by exact_mod_cast hdrop
  have h2 : W'.height + y = ((d + 1 : ℕ) : ℕ∞) := by exact_mod_cast hform
  have hyle : y ≤ d := by
    have : y + 1 ≤ (d : ℕ∞) + 1 := by exact_mod_cast h1
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp this
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, (k : ℕ∞) = y :=
    ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top d) hyle)
  have h3 : ((d + 1 : ℕ) : ℕ∞) ≤ 1 + k := by rw [← h2]; gcongr
  have h4 : d + 1 ≤ 1 + k := by exact_mod_cast h3
  have h5 : k ≤ d := by exact_mod_cast hyle
  have : k = d := by omega
  subst this
  rfl

def hyperplaneEmb (d : ℕ) : (Fin d → ℂ) →L[ℂ] (Fin (d + 1) → ℂ) :=
  ContinuousLinearMap.pi
    (Fin.cons 0 fun j => ContinuousLinearMap.proj j : Fin (d + 1) → (Fin d → ℂ) →L[ℂ] ℂ)

theorem hyperplaneEmb_apply (d : ℕ) (t : Fin d → ℂ) : hyperplaneEmb d t = Fin.cons 0 t := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [hyperplaneEmb]

theorem hyperplaneEmb_tail {d : ℕ} {s : Fin (d + 1) → ℂ} (hs : s 0 = 0) :
    hyperplaneEmb d (Fin.tail s) = s := by
  rw [hyperplaneEmb_apply, ← hs]
  exact Fin.cons_self_tail s

def sliceMap {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ}
    (γ : GroundTheory.Heights₂.Heights.VarBranch J (d + 1) p) : (Fin d → ℂ) → Fin n → ℂ :=
  fun t => γ.toFun (hyperplaneEmb d t)

theorem SliceImmersiveGeneral.proof (hcrit : CriticalImageNull.Statement)
    (hmass : ZeroSetOpenMass.Statement) : SliceImmersiveGeneral.Statement := by
  intro n d J W u p m γ hJ hdim hu hW hp hN
  obtain ⟨N, hN, hsl⟩ := hN
  have hWd := dim_component_linForm hJ hdim hu hW

  have hball : ∀ b, ∀ s ∈ Metric.ball (0 : Fin (d + 1) → ℂ) (γ b).radius,
      Fin.tail s ∈ Metric.ball (0 : Fin d → ℂ) (γ b).radius := by
    intro b s hs
    rw [ball_pi _ (γ b).radius_pos] at hs ⊢
    exact fun j _ => hs j.succ (Set.mem_univ _)
  have hmaps : ∀ b, Set.MapsTo (hyperplaneEmb d) (Metric.ball 0 (γ b).radius)
      (Metric.ball 0 (γ b).radius) := by
    intro b t ht
    rw [ball_pi _ (γ b).radius_pos] at ht ⊢
    intro i _
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hyperplaneEmb_apply, (γ b).radius_pos]
    · simpa [hyperplaneEmb_apply] using ht j (Set.mem_univ _)

  have hnull : ∀ b, μH[((2 * d : ℕ) : ℝ)] (sliceMap (γ b) '' {t | t ∈ Metric.ball 0 (γ b).radius ∧
      ¬ Function.Injective (fderiv ℂ (sliceMap (γ b)) t)}) = 0 := fun b =>
    hcrit d n _ _ Metric.isOpen_ball
      ((γ b).differentiableOn.comp (hyperplaneEmb d).differentiableOn (hmaps b))
  refine ⟨interior N, interior_mem_nhds.2 hN, ?_⟩
  rintro x ⟨hxW, hxN⟩
  rw [mem_closure_iff]
  intro o ho hxo
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne

  have hsub : GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ (o ∩ interior N) ⊆
      ⋃ b, sliceMap (γ b) '' {t | t ∈ Metric.ball 0 (γ b).radius ∧
        ¬ Function.Injective (fderiv ℂ (sliceMap (γ b)) t)} := by
    rintro y ⟨hyW, hyo, hyN⟩
    by_contra hy
    simp only [Set.mem_iUnion, not_exists] at hy
    have hyG : y ∈ o ∩ {x | x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∧
        ∀ b, ∃ s ∈ Metric.ball 0 (γ b).radius, s 0 = 0 ∧ (γ b).toFun s = x ∧
          ∀ v : Fin (d + 1) → ℂ, v 0 = 0 → fderiv ℂ (γ b).toFun s v = 0 → v = 0} := by
      refine ⟨hyo, hyW, fun b => ?_⟩
      obtain ⟨s, ⟨hs, hs0⟩, hsy⟩ := hsl b ⟨hyW, interior_subset hyN⟩
      have hs0' : s 0 = 0 := hs0
      refine ⟨s, hs, hs0', hsy, fun v hv0 hv => ?_⟩
      have hst := hyperplaneEmb_tail hs0'
      have hinj : Function.Injective (fderiv ℂ (sliceMap (γ b)) (Fin.tail s)) := by
        by_contra hni
        exact hy b ⟨Fin.tail s, ⟨hball b s hs, hni⟩, by simp only [sliceMap, hst, hsy]⟩
      have hγd : DifferentiableAt ℂ (γ b).toFun (hyperplaneEmb d (Fin.tail s)) := by
        rw [hst]
        exact (γ b).differentiableOn.differentiableAt (Metric.isOpen_ball.mem_nhds hs)
      have hchain : fderiv ℂ (sliceMap (γ b)) (Fin.tail s) =
          (fderiv ℂ (γ b).toFun (hyperplaneEmb d (Fin.tail s))).comp (hyperplaneEmb d) := by
        have h := fderiv_comp (Fin.tail s) hγd (hyperplaneEmb d).differentiableAt
        rw [ContinuousLinearMap.fderiv] at h
        exact h
      have hvt := hyperplaneEmb_tail hv0
      have : Fin.tail v = 0 := hinj (by
        rw [hchain, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hvt, hst, hv,
          map_zero, map_zero])
      rw [← hvt, this, map_zero]
    rw [hne] at hyG
    exact hyG
  have hpos := hmass n d W hW.1.1 hWd x (o ∩ interior N) (ho.inter isOpen_interior) ⟨hxo, hxN⟩ hxW
  exact hpos.ne' (measure_mono_null hsub (measure_iUnion_null hnull))

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem StokesOnVariety.proof (hD : ComplexSets.DiscriminantCover.Statement)
    (hS : StokesOffDiscriminant.Statement) (hL : CutOffLimit.Statement) :
    StokesOnVariety.Statement := by
  have key : ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (f g : (Fin n → ℂ) → ℝ)
      (φ : Fin d → (Fin n → ℂ) → ℝ), J.IsPrime →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) →
      SmoothNear (zeroSet J) f → SmoothNear (zeroSet J) g → (∀ i, SmoothNear (zeroSet J) (φ i)) →
      HasCompactSupport f → varInt J (d + 1) f (vecCons g φ) = varInt J (d + 1) g (vecCons f φ) := by
    intro n d J f g φ hJ hdim hf hg hφ hc
    unfold varInt
    split_ifs with hA
    · have hAf := hA.choose_spec
      generalize hA.choose = A at hAf ⊢
      obtain ⟨P, hP0, hPcov⟩ := hD n (d + 1) J A hJ hdim hAf

      have hsheet : ∀ x ∈ zeroSet J, eval (A *ᵥ x) P ≠ 0 → ∃ s, IsSheetAt J A x s := by
        intro x hx hPx
        obtain ⟨-, -, hloc⟩ := hPcov (A *ᵥ x) hPx
        obtain ⟨U, V, s, hU, hyU, hV, hxV, hs, hsy, hAs, hZV⟩ := hloc x ⟨hx, rfl⟩
        refine ⟨s, U, hU, hyU, hs, hsy, fun w hw => ⟨hAs w hw, ?_⟩, V, hV.mem_nhds hxV, ?_⟩
        · have hw' : s w ∈ zeroSet J ∩ V := hZV ▸ Set.mem_image_of_mem s hw
          exact hw'.1
        · rintro x' hx' -
          rw [hZV] at hx'
          obtain ⟨w, hw, rfl⟩ := hx'
          rw [hAs w hw]
      obtain ⟨χ, hχs, hχU, hlim⟩ := hL n d J A P hJ hdim hAf hP0
      obtain ⟨h1, h2⟩ := hlim f g φ hf hg hφ hc
      refine tendsto_nhds_unique h1 (Tendsto.congr (fun k => ?_) h2)
      obtain ⟨U, hU, hDU, hχ0⟩ := hχU k
      obtain ⟨V, hV, hZV, hfV⟩ := hf
      have hcχ : HasCompactSupport (fun x => χ k x * f x) := hc.mul_left (f := χ k)
      refine (hS n d J A P hJ hdim hAf hP0 hsheet (fun x => χ k x * f x) g φ
        ⟨V, hV, hZV, (hχs k).contDiffOn.mul hfV⟩ hg hφ hcχ ⟨U, hU, hDU, fun x hx => ?_⟩).symm
      rw [hχ0 x hx, zero_mul]
    · rfl
  intro n d J f g φ hJ hdim hf hg hφ hc
  rcases hc with hc | hc
  · exact key n d J f g φ hJ hdim hf hg hφ hc
  · exact (key n d J g f φ hJ hdim hg hf hφ hc).symm

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.AnForm Filter Topology

noncomputable section

theorem HessCCompPluri.fderiv_fderiv_comp_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → ℝ} {L : E → ℝ} {z : E} (hF : ContDiffAt ℝ 2 F (L z)) (hL : ContDiffAt ℝ 2 L z)
    (v u : E) :
    fderiv ℝ (fderiv ℝ (fun w => F (L w))) z v u =
      deriv (deriv F) (L z) * (fderiv ℝ L z v * fderiv ℝ L z u) +
        deriv F (L z) * fderiv ℝ (fderiv ℝ L) z v u := by
  have hL2 : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 2 L w := hL.eventually (by simp)
  have hF2 : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 2 F (L w) :=
    hL.continuousAt.tendsto.eventually (hF.eventually (by simp))
  have heq : fderiv ℝ (fun w => F (L w)) =ᶠ[𝓝 z] fun w => deriv F (L w) • fderiv ℝ L w := by
    filter_upwards [hL2, hF2] with w hw hFw
    exact ((hFw.differentiableAt (by norm_num)).hasDerivAt.comp_hasFDerivAt w
      (hw.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hdF : DifferentiableAt ℝ (deriv F) (L z) := by
    have h1 := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    exact h1.clm_apply (differentiableAt_const (1 : ℝ))
  have hdL : DifferentiableAt ℝ (fderiv ℝ L) z :=
    (hL.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : HasFDerivAt (fun w => deriv F (L w)) (deriv (deriv F) (L z) • fderiv ℝ L z) z :=
    hdF.hasDerivAt.comp_hasFDerivAt z (hL.differentiableAt (by norm_num)).hasFDerivAt
  have hs : HasFDerivAt (fun w => deriv F (L w) • fderiv ℝ L w)
      (deriv F (L z) • fderiv ℝ (fderiv ℝ L) z +
        (deriv (deriv F) (L z) • fderiv ℝ L z).smulRight (fderiv ℝ L z)) z :=
    hc.smul hdL.hasFDerivAt
  rw [heq.fderiv_eq, hs.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

theorem HessCCompPluri.proof : HessCCompPluri.Statement := by
  intro D F L z hF hL h0
  have hQ : ContDiffAt ℝ 2 (fun t : ℝ => t ^ 2 / 2) (L z) :=
    ((contDiff_id.pow 2).div_const 2).contDiffAt
  have hd1 : deriv (fun t : ℝ => t ^ 2 / 2) = fun t => t := by
    funext t
    rw [((hasDerivAt_pow 2 t).div_const 2).deriv]
    norm_num
  have key := HessCCompPluri.fderiv_fderiv_comp_apply hF hL
  have keyQ := HessCCompPluri.fderiv_fderiv_comp_apply hQ hL
  simp only [hd1, deriv_id'', one_mul] at keyQ
  ext i j
  have hij := congrFun (congrFun h0 i) j
  simp only [hessC, Matrix.zero_apply, Matrix.smul_apply, smul_eq_mul] at hij ⊢
  simp only [key, keyQ]
  push_cast at hij ⊢
  linear_combination (((deriv F (L z) : ℝ) : ℂ) - ((deriv (deriv F) (L z) : ℝ) : ℂ) * ((L z : ℝ) : ℂ)) * hij

end

end GroundTheory.Heights₂.Heights
end
