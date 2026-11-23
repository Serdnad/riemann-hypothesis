module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle004
public import ReciprocityTheory.DualLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle034
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle045
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle233
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle237
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle036
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle048
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle130
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle271
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle239
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle240
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle218
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.PGsh

namespace GlobalTheory.CayleyBlock

theorem det_pow_eq {p q : ℕ} (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q) :
    (GlobalTheory.DomainDens.blockSym h1 ()).det ^ q = rename (blockEmb h1) (sumMap p q (cayDet p ℂ ^ q)) := by
  rw [map_pow, map_pow, cayDet, AlgHom.map_det, AlgHom.map_det]
  congr 2
  ext i j
  simp [GlobalTheory.DomainDens.blockSym_apply, sumMap, blockEmb, Matrix.mvPolynomialX]

theorem bigList_nodup {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) : (bigList τ).Nodup := by
  rw [bigList, List.nodup_flatMap]
  refine ⟨fun b _ => (List.nodup_finRange p).map fun j k h => by simpa using congrArg (fun x => x.2.2) h, ?_⟩
  refine (List.nodup_finRange q).imp fun {a b} hab => ?_
  show List.Disjoint _ _
  rw [List.disjoint_left]
  intro x hx hy
  simp only [List.mem_map, List.mem_finRange, true_and] at hx hy
  obtain ⟨j, rfl⟩ := hx
  obtain ⟨k, hk⟩ := hy
  exact hab (congrArg Prod.fst hk).symm

theorem bigList_sum {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) :
    ((bigList τ).map fun v => Finsupp.single v 1).sum = blockGraph τ := by
  simp [bigList, blockGraph, List.map_flatMap, Fin.sum_univ_def, List.map_map, Function.comp_def]
  simp [List.flatMap, List.sum_flatten, List.map_map, Function.comp_def]

theorem pderiv_sumMap {p q : ℕ} (v : Fin q × Fin p × Fin p) (P : MvPolynomial (Fin p × Fin p) ℂ) :
    pderiv v (sumMap p q P) = sumMap p q (pderiv v.2 P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [sumMap]
  | add f g hf hg => simp only [map_add (f := _), hf, hg]
  | mul_X f w hf =>
    simp only [map_mul, Derivation.leibniz, hf, smul_eq_mul, map_add (f := _)]
    congr 1
    simp [sumMap, pderiv_X, Pi.single_apply, Prod.ext_iff]
    by_cases h : w.1 = v.2.1 ∧ w.2 = v.2.2 <;> simp [h, Finset.filter_eq']

theorem dList_sumMap {p q : ℕ} (l : List (Fin q × Fin p × Fin p)) (P : MvPolynomial (Fin p × Fin p) ℂ) :
    dList l (sumMap p q P) = sumMap p q (dList (l.map fun v => v.2) P) := by
  induction l with
  | nil => simp [dList]
  | cons v l ih =>
    simp only [dList, List.map_cons, List.prod_cons, Module.End.mul_apply] at ih ⊢
    rw [ih]
    exact pderiv_sumMap v _

theorem bigList_map {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) : (bigList τ).map (fun v => v.2) = smallList τ := by
  simp [bigList, smallList, List.map_flatMap, List.map_map, Function.comp_def]

theorem constantCoeff_sumMap (p q : ℕ) (P : MvPolynomial (Fin p × Fin p) ℂ) :
    constantCoeff (sumMap p q P) = constantCoeff P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [sumMap]
  | add f g hf hg => simp only [map_add (f := _), hf, hg]
  | mul_X f w hf => simp [sumMap, constantCoeff_X]

end GlobalTheory.CayleyBlock


open GlobalTheory.CayleyBlock ReciprocityTheory.PGsh MvPolynomial in
theorem GlobalTheory.topCoeff_blockSym_det_pow : ∀ (p q : ℕ) (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q),
    GlobalTheory.GoodMetric.topCoeff ((GlobalTheory.DomainDens.blockSym h1 ()).det ^ q) =
      ∏ i ∈ Finset.range p, (((q + i).factorial : ℂ) / i.factorial) := by
  intro p q h1
  rw [det_pow_eq, GlobalTheory.T.topDegreeFormCoeff_rename_cayleyBlockSymbolEmbedding, ← GlobalTheory.T.constantCoeff_cayleyOperator_pow_determinant_pow, GlobalTheory.T.cayleyOperator_pow_eq_signed_sum_partialDerivs, LinearMap.sum_apply]
  have key : ∀ τ : Fin q → Equiv.Perm (Fin p), (sgnProd τ : ℂ) * AddMonoidAlgebra.coeff (sumMap p q (cayDet p ℂ ^ q)) (blockGraph τ) =
      constantCoeff (sgnProd τ • dList (smallList τ) (cayDet p ℂ ^ q)) := by
    intro τ
    rw [← bigList_sum, ← zero_add ((bigList τ).map _).sum, ← GlobalTheory.T.coeff_composedPartialDerivList_of_nodup _ (bigList_nodup τ) 0 (fun _ _ => rfl),
      dList_sumMap, bigList_map, ← constantCoeff_sumMap p q, map_zsmul, zsmul_eq_mul,
      ← map_intCast (C : ℂ →+* MvPolynomial (Fin q × Fin p × Fin p) ℂ), map_mul, constantCoeff_C, constantCoeff_eq]

  simp_rw [LinearMap.smul_apply, key, map_sum]
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory

theorem _root_.GlobalTheory.T.nonempty_fockModel_unitary_dual_pair : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s), Nonempty (FockData T0 T1 T2) := by
  first | exact @GlobalTheory.nonempty_fockData_pair | exact GlobalTheory.nonempty_fockData_pair | (intros; apply GlobalTheory.nonempty_fockData_pair <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ReadingSpan

section Gen

variable {K C H Y : Type} [Field K] [AddCommGroup C] [Module K C] [AddCommGroup H] [Module ℂ H] {σ : K →+* ℂ}

theorem span_range_eq_basis {n : ℕ} (b : Module.Basis (Fin n) K C) (j : C →ₛₗ[σ] H) :
    Submodule.span ℂ (Set.range j) = Submodule.span ℂ (Set.range fun k => j (b k)) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
  · rintro _ ⟨f, rfl⟩

    rw [← b.sum_repr f, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rintro _ ⟨k, rfl⟩
    exact ⟨_, rfl⟩

theorem span_eq_top_of_ev (j : C → H) (ev : H →ₗ[ℂ] (Y → ℂ)) (hinj : Function.Injective ev)
    (h : ∀ x, ev x ∈ Submodule.span ℂ (Set.range fun f => ev (j f))) : Submodule.span ℂ (Set.range j) = ⊤ := by
  refine top_le_iff.1 fun x _ => ?_
  have e : (Set.range fun f => ev (j f)) = ev '' Set.range j := Set.range_comp ev j
  have h1 := h x
  rw [e, Submodule.span_image] at h1
  obtain ⟨y, hy, hxy⟩ := h1
  exact hinj hxy ▸ hy

theorem indep_conj {m : ℕ} {φ : Fin m → Y → ℂ} (h : LinearIndependent ℂ φ) :
    LinearIndependent ℂ fun k g => starRingEnd ℂ (φ k g) := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro c hc k
  have h2 : ∑ i, star (c i) • φ i = 0 := by
    funext g
    have := congrArg (starRingEnd ℂ) (congrFun hc g)
    simpa [Finset.sum_apply] using this
  simpa using h _ h2 k

end Gen

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

def evL (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : (R.MW i σ).Vec) : (R.HW i σ).H →ₗ[ℂ] (GA D (Wc D i) → ℂ) where
  toFun := evAt R i σ v
  map_add' a b := by simp [evAt]
  map_smul' c a := by simp [evAt]



theorem jUnif_of (hl : LawsJ T) (hJ : JEvExists T R κ v₀) (hB : JEvBar T R κ) (hI : EvInj T R v₀)
    (h1 : ∀ (i : Fin D.R.m) σ, GoodEmb T.Q.c σ → ∀ (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (m : ℕ) (b : Fin m → Cu T κ i),
      LinearIndependent T.Q.c.F b → LinearIndependent ℂ fun k => phiC T hV (wtA (κ i)) (b k : T.R ((i : ℕ) + 1)))
    (h2 : ∀ (i : Fin D.R.m) σ, GoodEmb T.Q.c (res T σ) → ∀ (hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i) (x : (R.HW i σ).H),
      evAt R i σ (v₀ i σ) x ∈
        Submodule.span ℂ (Set.range fun f : Cu T κ i => phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1))))
    (h3 : ∀ (i : Fin D.R.m) σ, ¬ GoodEmb T.Q.c (res T σ) →
      Module.finrank ℂ (R.HW i σ).H ≤ Module.finrank ℂ (R.HW i ((starRingEnd ℂ).comp σ)).H) :
    JUnif T R κ v₀ := by
  have good : ∀ (i : Fin D.R.m) σ, GoodEmb T.Q.c (res T σ) →
      (∀ (m : ℕ) (b : Fin m → Cu T κ i), LinearIndependent T.Q.c.F b →
        LinearIndependent ℂ fun k => jTop T R κ v₀ i σ (b k)) ∧
      Submodule.span ℂ (Set.range (jTop T R κ v₀ i σ)) = ⊤ := by
    intro i σ hσ
    have hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i := hl.spaceW _ (inR i) _ hσ
    have he : ∀ f, evL T R i σ (v₀ i σ) (jTop T R κ v₀ i σ f) = phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) :=
      jTop_good T R κ v₀ hσ hV (hJ i σ hσ hV)
    refine ⟨fun m b hb => LinearIndependent.of_comp (evL T R i σ (v₀ i σ)) ?_,
      span_eq_top_of_ev _ (evL T R i σ (v₀ i σ)) (hI i σ hσ) fun x => ?_⟩
    · have e : (evL T R i σ (v₀ i σ)) ∘ (fun k => jTop T R κ v₀ i σ (b k)) =
          fun k => phiC T hV (wtA (κ i)) (b k : T.R ((i : ℕ) + 1)) := funext fun k => he (b k)
      rw [e]
      exact h1 i _ hσ hV m b hb
    · rw [funext he]
      exact h2 i σ hσ hV x
  intro i σ
  by_cases hσ : GoodEmb T.Q.c (res T σ)
  · exact good i σ hσ
  have hσ' : GoodEmb T.Q.c (resC T σ) := good_resC T hσ
  have hV : T.V ((i : ℕ) + 1) (resC T σ) = Wc D i := hl.spaceW _ (inR i) _ hσ'
  obtain ⟨v, -, he⟩ := jTop_bar T R κ v₀ hσ hV (hB i σ hσ hV)
  have hind : ∀ (m : ℕ) (b : Fin m → Cu T κ i), LinearIndependent T.Q.c.F b →
      LinearIndependent ℂ fun k => jTop T R κ v₀ i σ (b k) := fun m b hb => by
    refine LinearIndependent.of_comp (evL T R i σ v) ?_
    have e : (evL T R i σ v) ∘ (fun k => jTop T R κ v₀ i σ (b k)) =
        fun k g => starRingEnd ℂ (phiC T hV (wtA (κ i)) (b k : T.R ((i : ℕ) + 1)) g) := funext fun k => he (b k)
    rw [e]
    exact indep_conj (h1 i _ hσ' hV m b hb)
  refine ⟨hind, ?_⟩
  obtain ⟨b⟩ := hasB_nTop T hl κ i
  have hs := (good i ((starRingEnd ℂ).comp σ) hσ').2
  rw [span_range_eq_basis b] at hs ⊢
  have d1 : Module.finrank ℂ (R.HW i ((starRingEnd ℂ).comp σ)).H ≤ nTop T κ i := by
    rw [← finrank_top, ← hs]
    exact (finrank_range_le_card _).trans (Fintype.card_fin _).le
  have hi := hind _ b b.linearIndependent
  refine Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) ?_)
  rw [finrank_span_eq_card hi, Fintype.card_fin]
  exact (h3 i σ hσ).trans d1

end GlobalTheory.ReadingSpan
end
end

section

noncomputable section

open NumberField

namespace GlobalTheory.OneMapRefObj

open _root_.Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.IndefR.Links Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tieIn_of_fwTie {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, Formalism.MainNotions.WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (t : FWTie T R κ v₀) : TieIn T R κ v₀ :=
  ⟨t.laws, t.alg_eq, t.kap, t.hv₀, t.chiR, t.x0⟩

end GlobalTheory.OneMapRefObj
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefMapRecord

open Formalism.L2.NTheta

lemma floor_toNat_cast {x : ℚ} (z : ℤ) (hz : x = z) (h0 : 0 ≤ x) : ((⌊x⌋.toNat : ℕ) : ℚ) = x := by
  subst hz
  rw [Int.floor_intCast]
  have h : 0 ≤ z := by exact_mod_cast h0
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h]

lemma lamAt_b {R : Ranks} (h : HCParam R) (n c : ℕ) (hc : c < R.m) (hn : n = R.k - 1 + c) : lamAt h n = -h.b ⟨c, hc⟩ := by
  subst hn
  unfold lamAt
  rw [dite_eq_right (by omega), dite_eq_left (by omega)]
  congr 3
  omega

variable (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau)

lemma aPl_cast (n : ℕ) (hn : n < D.R.k + i) :
    (aPl D i (D.R.k + i) τ n : ℚ) =
      lamAt (D.hc τ) n + (D.hc τ).e i - (((D.R.k + i : ℕ) : ℚ) - (n + 1)) - ((D.R.t : ℚ) + 1) / 2 := by
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  obtain ⟨z, hz⟩ := lamAt_int (D.hc τ) n
  obtain ⟨e, he⟩ := (D.hc τ).e_int i
  obtain ⟨s, hs⟩ := D.R.t_odd
  have hs' : (D.R.t : ℚ) = 2 * s + 1 := by exact_mod_cast hs
  rw [aPl, if_pos hn]
  refine floor_toNat_cast (z + e - ((D.R.k + i : ℕ) - (n + 1)) - (s + 1)) ?_ ?_
  · rw [hz, he, hs']; push_cast; ring
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hn
    have h1 := lamAt_add_add_le (D.hc τ) d n (by unfold Ranks.r; omega)
    rw [lamAt_b (D.hc τ) (n + d) i hi (by omega)] at h1
    have h2 := (D.hc τ).gap_be i
    rw [hd]
    push_cast
    simp only [Fin.eta] at h1
    linarith

lemma aMi_cast (q n c : ℕ) (hq : i + 1 + q = D.R.m) (hn : n + c + 1 = q) :
    (aMi D i (D.R.k + i) q τ n : ℚ) =
      -((D.hc τ).e i - (D.hc τ).b ⟨i + 1 + c, by omega⟩ + (c + 1) + ((D.R.t : ℚ) - 1) / 2) := by
  have hk := D.R.m_add_three_le_k
  obtain ⟨z, hz⟩ := (D.hc τ).b_int ⟨i + 1 + c, by omega⟩
  obtain ⟨e, he⟩ := (D.hc τ).e_int i
  obtain ⟨s, hs⟩ := D.R.t_odd
  have hs' : (D.R.t : ℚ) = 2 * s + 1 := by exact_mod_cast hs
  have h0 := lamAt_b (D.hc τ) (D.R.k + i + c) (i + 1 + c) (by omega) (by omega)
  rw [aMi, if_pos (by omega), show q - n = c + 1 by omega, show D.R.k + i + (c + 1) - 1 = D.R.k + i + c by omega, h0,
    ← sub_eq_add_neg, Nat.cast_succ]
  refine floor_toNat_cast (-(e - z + (c + 1) + s)) ?_ ?_
  · rw [hz, he, hs']; push_cast; ring
  · have h1 := lamAt_add_add_le (D.hc τ) c (D.R.k + i) (by unfold Ranks.r; omega)
    rw [h0, lamAt_b (D.hc τ) (D.R.k + i) (i + 1) (by omega) (by omega)] at h1
    have h2 := (D.hc τ).gap_eb i (by omega)
    linarith

lemma lamV_eq : ∃ s : ℤ, ∀ n : Fin (Vc D i).rank, (lamV D i τ).w n =
    s + (if (n : ℕ) < D.R.k + i then (aPl D i (D.R.k + i) τ n : ℤ) else 0) -
      (if (Fin.rev n : ℕ) < D.R.m - (i + 1) then (aMi D i (D.R.k + i) (D.R.m - (i + 1)) τ (Fin.rev n) : ℤ) else 0) := by
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  obtain ⟨hj, W, hWk, hWm, hWt, hWj, hWe, hWv, hWb, hW⟩ :=
    GlobalTheory.ForcedWeights.lamLForced D (i + 1) (Nat.le_add_left _ _) hi τ
  have hWe' : (W.e : ℚ) = (D.hc τ).e i := hWe
  have hr : (Vc D i).rank = D.R.k + D.R.m - 1 + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) hi
  obtain ⟨q, hq⟩ : ∃ q, i + 1 + q = D.R.m := ⟨D.R.m - (i + 1), by omega⟩
  have hp : W.p = D.R.k + i := by unfold IndefiniteWeightData.WeightData.p; omega
  have hq' : W.q = q := by unfold IndefiniteWeightData.WeightData.q; omega
  have hnV : W.nV = D.R.k + i + q + D.R.t := by unfold IndefiniteWeightData.WeightData.nV IndefiniteWeightData.WeightData.r; omega
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have ha' : (D.R.k : ℚ) = a + a := by exact_mod_cast ha
  have hb' : (q : ℚ) = b + b - i - 1 := by
    have : ((i : ℕ) : ℚ) + 1 + q = b + b := by exact_mod_cast hq.trans hb
    linarith
  have hd : W.dTau = ((a + (i : ℕ) - b - W.e : ℤ) : ℚ) := by
    unfold IndefiniteWeightData.WeightData.dTau
    rw [hp, hq']
    push_cast
    rw [ha', hb']
    ring
  generalize (a + (i : ℕ) - b - W.e : ℤ) = s at hd
  rw [show D.R.m - (i + 1) = q by omega]
  refine ⟨s, fun n => ?_⟩
  have hn := n.2
  rw [← Int.cast_inj (α := ℚ), hW n, IndefiniteWeightData.WeightData.lamPrime, hd, IndefiniteWeightData.WeightData.thetaWt, hp, hq', hWt, Fin.val_rev,
    Int.cast_sub, Int.cast_add]
  by_cases h1 : (n : ℕ) < D.R.k + i
  · rw [if_pos (by omega), if_pos h1, if_neg (by omega), Int.cast_natCast, aPl_cast D i τ n h1, IndefiniteWeightData.WeightData.aPlus,
      hp, hq', hnV, hWe']
    have hl : (W.lam (n + 1) : ℚ) = lamAt (D.hc τ) n := by
      unfold IndefiniteWeightData.WeightData.lam
      rw [hWk]
      split_ifs with h2
      · rw [lamAt, dite_eq_left (by omega)]
        exact hWv ⟨n, by omega⟩
      · rw [lamAt_b (D.hc τ) n (n - (D.R.k - 1)) (by omega) (by omega), Int.cast_neg,
          show (n : ℕ) + 1 - (D.R.k - 1) = n - (D.R.k - 1) + 1 by omega]
        exact congrArg _ (hWb ⟨n - (D.R.k - 1), by omega⟩)
    rw [hl]
    push_cast
    ring
  · rw [if_neg (by omega), if_neg h1]
    by_cases h2 : (n : ℕ) + 1 ≤ D.R.k + i + D.R.t
    · rw [if_pos h2, if_neg (by omega)]
      push_cast
      ring
    · obtain ⟨c, hc⟩ : ∃ c, (n : ℕ) = D.R.k + i + D.R.t + c := ⟨n - (D.R.k + i + D.R.t), by omega⟩
      rw [if_neg h2, if_pos (by omega), Int.cast_natCast, aMi_cast D i τ q _ c hq (by omega), IndefiniteWeightData.WeightData.aMinus,
        hq', hWj, hWt, hWe', show q + 1 - (q + 1 - (n + 1 - (D.R.k + i) - D.R.t)) = c + 1 by omega,
        show (i : ℕ) + 1 + (c + 1) = i + 1 + c + 1 by omega, hWb ⟨i + 1 + c, by omega⟩]
      push_cast
      ring

theorem exists_io_record : ∀ (D : D7) (Q : Formalism.L2.Pj.Par D), Q.Pins → ∀ (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), KapIs κ → ∀ (i : Fin D.R.m) (c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff Q.l), ∃ (io : VsV D i c'.F →ₗ[c'.F] MvPolynomial (LtN (Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c'.F) (hw : VsV D i c'.F), IoLFRec c' (fun τ => embF c' (tauE D τ)) (lamV D i) (wtA (κ i)) io hw := by
  intro D Q hQ κ hκ i c'
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  obtain ⟨-, hinj, hΨ, -, hval⟩ := GlobalTheory.WeightExponents.weight_exponents D Q hQ _ (inR i) (κ i)
  obtain ⟨hp, hq, -⟩ := hQ.2.2.2 _ (inR i)
  have hp1 : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + i := rfl
  have hq1 : (D.R.sigW ((i : ℕ) + 1)).2 = D.R.m - (i + 1) := rfl
  choose s hs using lamV_eq D i
  refine GlobalTheory.FrameRead.CoefMap.exists_ioLFRec D.host.E Q.H (Q.Dw ((i : ℕ) + 1)) (Vc D i).rank D.what₂.Tau (DV.tauEmb D)
    ⟨hinj, fun τ => (hΨ τ).trans (exists_congr fun _ => eq_comm)⟩ ?_ Q.l c' (wtA (κ i)) s (lamV D i) (dom_wtA (κ i)).1 ?_
  · refine le_trans ?_ (r_le_V i)
    rw [hp, hq, hp1, hq1, Ranks.r]
    omega
  · intro τ n
    have ht := hQ.1.2.2.2 τ
    have hc : ¬ ComplexEmbedding.conjugate (DV.tauEmb D τ) (Q.H.rt : D.host.E) = Q.H.rt0 :=
      GlobalTheory.WeightExponents.not_inPsi_conj hQ.1 τ
    have hsig : (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (inR i).1 (inR i).2 _
    obtain ⟨h1, h2, -⟩ := hκ i τ
    rw [hsig] at h1 h2
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult, if_pos ht, if_neg hc, hp, hq, hs τ n,
      (hval τ _).1, (hval τ _).2]
    congr 1
    · congr 1
      refine if_ctx_congr Iff.rfl (fun h => ?_) fun _ => rfl
      rw [ext0, dite_eq_left (show (n : ℕ) < (D.R.sigW ((i : ℕ) + 1)).1 from h), h1]
      rfl
    · refine if_ctx_congr Iff.rfl (fun h => ?_) fun _ => rfl
      rw [ext0, dite_eq_left (show (Fin.rev n : ℕ) < (D.R.sigW ((i : ℕ) + 1)).2 from h), h2]
      rfl

end GlobalTheory.CoefMapRecord
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

theorem _root_.GlobalTheory.T.mixed_laplacian_kills_product_of_minors : ∀ (D : D7) (m n : ℕ) (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ), (∀ τ, p τ + q τ ≤ n) → ∀ τ (a b : Fin m), p τ ≤ (a : ℕ) → (b : ℕ) < p τ → ∑ c : Fin n, MvPolynomial.pderiv (τ, a, c) (MvPolynomial.pderiv (τ, b, c) (delta p q ap am : PolF D m n)) = 0 := by
  first | exact @GlobalTheory.MinorHarmonic.laplacian_delta | exact GlobalTheory.MinorHarmonic.laplacian_delta | (intros; apply GlobalTheory.MinorHarmonic.laplacian_delta <;> assumption)
end

section

open Formalism.BasicNotions

namespace GlobalTheory.Mem.SRe

theorem cdScale_eq_cdScaleOf : ∀ D : D7, cdScaleTie D → D.s.cdScale = Formalism.L2.SG.PairVal.cdScaleOf D := by
  intro D h
  exact GlobalTheory.Mem.Vol.Scale.cdScaleIs_unique D.cd ((GlobalTheory.Mem.Vol.cdScaleTie_iff D).1 h)
    (fun n ε => (Formalism.L2.SG.PairVal.cdScaleOf_tie D (Formalism.L2.SG.PairVal.cdScaleExists_of_tie D h) n ε).2)

end GlobalTheory.Mem.SRe
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

theorem _root_.GlobalTheory.T.host_etaTilde_character_exists : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), _root_.Formalism.L2.Host.EtaTExists H := by
  first | exact @GlobalTheory.Mem.EtaT.etaT_exists | exact GlobalTheory.Mem.EtaT.etaT_exists | (intros; apply GlobalTheory.Mem.EtaT.etaT_exists <;> assumption)
end

section

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_intertwiner_with_highestWeight_vector_in_range : ∀ (k : ℕ) (Λ : Fin k → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (τ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (π : Matrix (Fin k) (Fin k) ℂ → (E →L[ℂ] E)) (Δ : E), IsURepOn (UJset (allPos k)) τ → IsKTypeOf (allPos k) τ Λ ⊤ → IsURepOn (UJset (allPos k)) π → (∀ w : E, DifferentiableAt ℂ (fun g : Fin k → Fin k → ℂ => π (Matrix.of g) w) (fun i j => (1 : Matrix (Fin k) (Fin k) ℂ) i j)) → Δ ≠ 0 → (∀ a b : Fin k, a < b → ∀ s : ℂ, π (1 + Matrix.single a b s) Δ = Δ) → IsWtOn (Formalism.REAL.Kset (allPos k)) π Λ Δ → ∃ L : H →ₗ[ℂ] E, (∀ g ∈ UJset (allPos k), ∀ u, L (τ g u) = π g (L u)) ∧ ∃ v, L v = Δ := by
  first | exact @GlobalTheory.HighestWeightMap.exists_intertwiner | exact GlobalTheory.HighestWeightMap.exists_intertwiner | (intros; apply GlobalTheory.HighestWeightMap.exists_intertwiner <;> assumption)
end
