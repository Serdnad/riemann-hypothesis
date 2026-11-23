module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Mathlib.RingTheory.PowerSeries.Exp
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle001
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalAcrisToBdRPlusUniqueEquivariantApprox
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormalDeformationPowerSeriesSolution
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle209
import Formalism.LocalRingCardinality.DataTheta
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle210
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ExpJets

open PowerSeries

variable {p : ℕ} [Fact p.Prime]

theorem expPS_eq_subst (F : PowerSeries ℂ_[p]) (hF : constantCoeff F = 0) :
    expPS F = (PowerSeries.exp ℂ_[p]).subst F := by
  ext n
  rw [PowerSeries.coeff_subst' (HasSubst.of_constantCoeff_zero' hF), expPS, coeff_mk,
    finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp [PowerSeries.coeff_exp, div_eq_inv_mul]
  · intro k hk
    by_contra h
    apply hk
    have hlt : n < k := by simpa using h
    have h0 : coeff n (F ^ k) = 0 := by
      have : (X : PowerSeries ℂ_[p]) ^ k ∣ F ^ k := pow_dvd_pow_of_dvd (X_dvd_iff.2 hF) k
      exact X_pow_dvd_iff.1 this n hlt
    simp [h0]

theorem derivative_expPS (F : PowerSeries ℂ_[p]) (hF : constantCoeff F = 0) :
    d⁄dX (expPS F) = expPS F * d⁄dX F := by
  rw [expPS_eq_subst F hF, PowerSeries.derivative_subst (HasSubst.of_constantCoeff_zero' hF),
    PowerSeries.derivative_exp]

theorem norm_jet_mul_le (A B : PowerSeries ℂ_[p]) (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ i j, i + j = n →
      ‖(i.factorial : ℂ_[p]) * coeff i A‖ * ‖(j.factorial : ℂ_[p]) * coeff j B‖ ≤ C) :
    ‖(n.factorial : ℂ_[p]) * coeff n (A * B)‖ ≤ C := by
  rw [coeff_mul, Finset.mul_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun x hx => ?_
  obtain ⟨i, j⟩ := x
  have hij : i + j = n := by simpa using hx
  have e : (n.factorial : ℂ_[p]) * (coeff i A * coeff j B) =
      (((i + j).choose j : ℕ) : ℂ_[p]) *
        (((i.factorial : ℂ_[p]) * coeff i A) * ((j.factorial : ℂ_[p]) * coeff j B)) := by
    rw [← hij, ← Nat.add_choose_mul_factorial_mul_factorial i j]
    push_cast
    ring
  simp only
  rw [e, norm_mul, norm_mul]
  have h1 : ‖(((i + j).choose j : ℕ) : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ _
  calc _ ≤ 1 * C := mul_le_mul h1 (h i j hij) (by positivity) zero_le_one
    _ = C := one_mul C

theorem jet_derivative (A : PowerSeries ℂ_[p]) (n : ℕ) :
    (n.factorial : ℂ_[p]) * coeff n (d⁄dX A) =
      ((n + 1).factorial : ℂ_[p]) * coeff (n + 1) A := by
  rw [PowerSeries.coeff_derivative, Nat.factorial_succ]
  push_cast
  ring

theorem norm_jet_expPS_le (F : PowerSeries ℂ_[p]) (hF : constantCoeff F = 0) (s : ℝ)
    (hs : 0 ≤ s) (h : ∀ n : ℕ, ‖(n.factorial : ℂ_[p]) * coeff n F‖ ≤ s ^ n) (n : ℕ) :
    ‖(n.factorial : ℂ_[p]) * coeff n (expPS F)‖ ≤ s ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [expPS]
    | succ n =>
      rw [← jet_derivative, derivative_expPS F hF]
      refine norm_jet_mul_le _ _ n _ (by positivity) fun i j hij => ?_
      rw [jet_derivative, ← hij, add_assoc, pow_add]
      exact mul_le_mul (ih i (by omega)) (h (j + 1)) (norm_nonneg _) (by positivity)

theorem norm_jet_exp_neg_mul_le : ∀ (p : ℕ) [Fact p.Prime] (ph : PowerSeries ℂ_[p]) (s : ℝ), 1 ≤ s → PowerSeries.constantCoeff ph = 0 → (∀ i, i ≠ 2 → ‖(i.factorial : ℂ_[p]) * PowerSeries.coeff i ph‖ ≤ 1) → ‖(2 : ℂ_[p]) * PowerSeries.coeff 2 ph‖ ≤ s ^ 2 → ∀ (f : PowerSeries ℂ_[p]), (∀ n : ℕ, ‖(n.factorial : ℂ_[p]) * PowerSeries.coeff n f‖ ≤ 1) → ∀ n : ℕ, ‖(n.factorial : ℂ_[p]) * PowerSeries.coeff n (expPS (-ph) * f)‖ ≤ s ^ n := by
  intro p _ ph s hs h0 h1 h2 f hf n
  have hs0 : 0 ≤ s := zero_le_one.trans hs
  have hE := norm_jet_expPS_le (-ph) (by simp [h0]) s hs0 fun m => by
    rw [map_neg, mul_neg, norm_neg]
    by_cases hm : m = 2
    · subst hm
      simpa using h2
    · exact (h1 m hm).trans (one_le_pow₀ hs)
  refine norm_jet_mul_le _ _ n _ (by positivity) fun i j hij => ?_
  rw [← hij, pow_add]
  exact mul_le_mul (hE i) ((hf j).trans (one_le_pow₀ hs)) (norm_nonneg _) (by positivity)

end GlobalTheory.ExpJets
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.FundSeq

def OntoAt (l : ℕ) [Fact l.Prime] : Prop :=
  ∀ ι : Per.Bcris l →+* Per.BdR l, Per.IsCrisDR l ι →
    (∀ u : Per.Bcris l, ∃ x : Per.Bcris l, ι x ∈ Per.FilD l 0 ∧ x - Per.φB l x = u) ∧
    (∀ w : Per.BdR l, ∃ b : Per.Bcris l, Per.φB l b = b ∧ ι b - w ∈ Per.FilD l 0)

theorem pair_onto {B D : Type} [AddCommGroup B] [AddCommGroup D] (φ : B →+ B) (ι : B →+ D) (F : Set D)
    (h1 : ∀ u, ∃ x, x - φ x = u) (h2 : ∀ w, ∃ b, φ b = b ∧ ι b - w ∈ F) (u : B) (w : D) :
    ∃ x y, y ∈ F ∧ x - φ x = u ∧ ι x - y = w := by
  obtain ⟨x0, hx0⟩ := h1 u
  obtain ⟨b, hb, hF⟩ := h2 (w - ι x0)
  refine ⟨x0 + b, _, hF, ?_, ?_⟩
  · rw [map_add (f := _), hb, ← hx0]; abel
  · rw [map_add (f := _)]; abel

variable {l : ℕ} [Fact l.Prime]

theorem exists_restrict_aCris_bdRPlus {ι : Per.Bcris l →+* Per.BdR l} (h : Per.IsCrisDR l ι) :
    ∃ j : Per.Acris l →+* Per.BdRp l, IsCrisP j ∧ ∀ x : Per.Acris l,
      ι (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.BdRp l) (Per.BdR l) (j x) := by
  obtain ⟨j, h1, h2, h3⟩ := GlobalTheory.CrisIncl.exists_restrict l ι h
  exact ⟨j, ⟨h2, h3⟩, h1⟩

theorem eq_core_of_isCrisDR {ι : Per.Bcris l →+* Per.BdR l} (h : Per.IsCrisDR l ι) (C : Core l) :
    ι = C.ι := by
  obtain ⟨j, hj, hι⟩ := exists_restrict_aCris_bdRPlus h
  have e : j = C.j := (crisP_unique_equivariant l C.j C.j_cris).1 j hj
  refine GlobalTheory.RingIface.bcris_ext l fun x => ?_
  rw [hι, C.ι_j, e]

theorem ontoAt_of_core (C : Core l) (h1 : C.OneSubPhiOnto) (h2 : C.FundOnto) : OntoAt l := by
  intro ι hι
  rw [eq_core_of_isCrisDR hι C]
  refine ⟨fun u => ?_, h2⟩
  obtain ⟨x, y, hy, hx, hxy⟩ := pair_onto (Per.φB l).toAddMonoidHom C.ι.toAddMonoidHom
    (Per.FilD l 0 : Set (Per.BdR l)) h1 h2 u 0
  exact ⟨x, (sub_eq_zero.1 hxy : C.ι x = y) ▸ hy, hx⟩

theorem pair_onto_of_tied {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (h : OntoAt l)
    (K : FinExt l) (u : P.R.B) (w : P.R.BdR) :
    ∃ (x : P.R.B) (y : P.R.BdR), y ∈ (P.PD K).Fil 0 ∧ x - (P.PD K).φ x = u ∧ (P.PD K).ι x - y = w := by
  obtain ⟨h1, h2⟩ := h _ T.incl
  have H := pair_onto (P.φB : P.R.B →+* P.R.B).toAddMonoidHom
    (P.ιB : P.R.B →+* P.R.BdR).toAddMonoidHom ((P.PD K).Fil 0 : Set P.R.BdR) (fun u => ?_) (fun w => ?_) u w
  · obtain ⟨x, y, hy, hx, hxy⟩ := H
    exact ⟨x, y, hy, by rw [P.PD_φ]; exact hx, by rw [P.PD_ι]; exact hxy⟩
  · obtain ⟨x, -, hx⟩ := h1 (T.eB u)
    obtain ⟨x, rfl⟩ := T.eB.surjective x
    refine ⟨x, T.eB.injective ?_⟩
    rw [← hx, map_sub, ← T.frob]
    rfl
  · obtain ⟨b, hb, hF⟩ := h2 (T.eD w)
    obtain ⟨b, rfl⟩ := T.eB.surjective b
    refine ⟨b, T.eB.injective ((T.frob b).trans hb), (T.fil K 0 _).2 ?_⟩
    have e : T.eB.symm.toRingHom (T.eB b) = b := T.eB.symm_apply_apply b
    rw [RingHom.comp_apply, e] at hF
    rw [map_sub]
    exact hF

theorem surjective_half_of_onto (h : ∀ (l : ℕ) [Fact l.Prime], OntoAt l) (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.LocalSituation.adm1 D :=
  fun l _ K u w => pair_onto_of_tied (D.locT l) (h l) K u w

end GlobalTheory.FundSeq
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.HolDS Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.HolDS

theorem form_aeval_of_left_eigen {V : Type} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V)
    (φ : V →ₗ[ℂ] ℂ) (c : ℂ) (h : ∀ v, φ (T v) = c * φ v) (f : Polynomial ℂ) (v : V) :
    φ (Polynomial.aeval T f v) = f.eval c * φ v := by
  have hpow : ∀ (n : ℕ) (v : V), φ ((T ^ n) v) = c ^ n * φ v := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, ih, h]; ring
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, add_mul]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, Module.End.mul_apply,
      Module.algebraMap_end_apply, map_smul, hpow, smul_eq_mul, mul_assoc]

theorem finiteDimensional_stable_le_iSup_eigen :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (U : H →L[ℂ] H), (∀ v, ‖U v‖ = ‖v‖) → ∀ (E : ℕ → Submodule ℂ H) (lam : ℕ → ℂ), Function.Injective lam → (∀ m, FiniteDimensional ℂ (E m)) → (∀ m, ∀ e ∈ E m, U e = lam m • e) → Dense ((⨆ m, E m : Submodule ℂ H) : Set H) → ∀ (W : Submodule ℂ H), FiniteDimensional ℂ W → (∀ w ∈ W, U w ∈ W) → W ≤ ⨆ m, E m := by
  intro H _ _ _ U hU E lam hinj hfin heig hdense W hW hst
  classical
  have hinner : ∀ a b : H, ⟪U a, U b⟫_ℂ = ⟪a, b⟫_ℂ := fun a b =>
    (⟨(U : H →ₗ[ℂ] H), hU⟩ : H →ₗᵢ[ℂ] H).inner_map_map a b
  have hleft : ∀ m, ∀ e ∈ E m, ∀ y, ⟪e, U y⟫_ℂ = lam m * ⟪e, y⟫_ℂ := by
    intro m e he y
    by_cases h0 : e = 0
    · simp [h0]
    have h1 : ‖lam m‖ = 1 := by
      have := hU e
      rw [heig m e he, norm_smul] at this
      have hne : ‖e‖ ≠ 0 := norm_ne_zero_iff.mpr h0
      exact mul_right_cancel₀ hne (by rw [this, one_mul])
    have h2 : lam m * (starRingEnd ℂ) (lam m) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; simp
    have h3 := hinner e y
    rw [heig m e he, inner_smul_left] at h3
    rw [← h3, ← mul_assoc, h2, one_mul]
  let T : Module.End ℂ W := (U : H →ₗ[ℂ] H).restrict hst
  let f : Polynomial ℂ := LinearMap.charpoly T
  have hf0 : f ≠ 0 := (LinearMap.charpoly_monic T).ne_zero
  have hfT : Polynomial.aeval T f = 0 := LinearMap.aeval_self_charpoly T
  have hsfin : (lam ⁻¹' {z | f.IsRoot z}).Finite :=
    (Polynomial.finite_setOf_isRoot hf0).preimage hinj.injOn
  let s : Finset ℕ := hsfin.toFinset
  have hout : ∀ m, m ∉ s → ∀ e ∈ E m, ∀ y ∈ W, ⟪e, y⟫_ℂ = 0 := by
    intro m hm e he y hy
    have hne : f.eval (lam m) ≠ 0 := by
      intro h
      exact hm (hsfin.mem_toFinset.mpr h)
    have := form_aeval_of_left_eigen T (((innerₛₗ ℂ e : H →ₗ[ℂ] ℂ)).comp W.subtype) (lam m)
      (fun v => hleft m e he v) f ⟨y, hy⟩
    rw [hfT] at this
    simp only [LinearMap.zero_apply, map_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hne
  let F : Submodule ℂ H := ⨆ m ∈ s, E m
  haveI hF : FiniteDimensional ℂ F := by
    have : F = s.sup E := by simp [F, Finset.sup_eq_iSup]
    rw [this]; infer_instance
  have hFle : F ≤ ⨆ m, E m := iSup₂_le fun m _ => le_iSup E m
  have hForth : ∀ m, m ∉ s → F ≤ (E m)ᗮ := by
    intro m hm
    refine iSup₂_le fun k hk x hx => ?_
    rw [Submodule.mem_orthogonal]
    intro e he
    have h1 := hleft m e he x
    rw [heig k x hx, inner_smul_right] at h1
    have hne : lam k - lam m ≠ 0 := by
      intro h
      have := hinj (sub_eq_zero.mp h)
      exact hm (this ▸ hk)
    have : (lam k - lam m) * ⟪e, x⟫_ℂ = 0 := by rw [sub_mul, h1, sub_self]
    exact (mul_eq_zero.mp this).resolve_left hne
  intro y hy
  have hz : y - F.starProjection y ∈ (⨆ m, E m)ᗮ := by
    rw [← Submodule.iInf_orthogonal, Submodule.mem_iInf]
    intro m
    by_cases hm : m ∈ s
    · have hle : E m ≤ F := le_iSup₂_of_le (f := fun m (_ : m ∈ s) => E m) m hm le_rfl
      exact Submodule.orthogonal_le hle (Submodule.sub_starProjection_mem_orthogonal y)
    · refine Submodule.sub_mem _ ?_ (hForth m hm (F.starProjection_apply_mem y))
      rw [Submodule.mem_orthogonal]
      intro e he
      exact hout m hm e he y hy
  have hz0 : y - F.starProjection y = 0 := by
    have htop : (⨆ m, E m : Submodule ℂ H).topologicalClosure = ⊤ :=
      Submodule.dense_iff_topologicalClosure_eq_top.mp hdense
    rw [Submodule.topologicalClosure_eq_top_iff] at htop
    rw [htop] at hz
    exact (Submodule.mem_bot ℂ).mp hz
  rw [sub_eq_zero.mp hz0]
  exact hFle (F.starProjection_apply_mem y)

end GlobalTheory.HolDS
end

section

open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta

theorem integral_cexp_gaussian_plane : ∀ l u v : ℂ, 0 < l.re → Integrable (fun z : ℂ => cexp (-(π : ℂ) * l * (z * conj z) + π * (u * conj z) + π * (z * conj v))) ∧ ∫ z : ℂ, cexp (-(π : ℂ) * l * (z * conj z) + π * (u * conj z) + π * (z * conj v)) = l⁻¹ * cexp (π * (u * conj v) / l) := by
  intro l u v hl
  have hl0 : l ≠ 0 := by
    intro h
    simp [h] at hl
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hb : (-(π : ℂ) * l).re < 0 := by
    have := mul_pos Real.pi_pos hl
    simpa using this
  set f : ℝ → ℂ := fun x => cexp ((-(π : ℂ) * l) * x ^ 2 + (π * (u + conj v)) * x + 0) with hf
  set g : ℝ → ℂ := fun y => cexp ((-(π : ℂ) * l) * y ^ 2 + (π * I * (conj v - u)) * y + 0) with hg
  have hfi : Integrable f := integrable_cexp_quadratic' hb _ _
  have hgi : Integrable g := integrable_cexp_quadratic' hb _ _
  have key : (fun z : ℂ => cexp (-(π : ℂ) * l * (z * conj z) + π * (u * conj z) + π * (z * conj v)))
      = (fun p : ℝ × ℝ => f p.1 * g p.2) ∘ Complex.measurableEquivRealProd := by
    funext z
    simp only [hf, hg, Function.comp, Complex.measurableEquivRealProd_apply, ← Complex.exp_add]
    congr 1
    have hz : z = z.re + z.im * I := (Complex.re_add_im z).symm
    have hc : conj z = z.re - z.im * I := by
      apply Complex.ext <;> simp
    rw [hc]
    generalize (z.re : ℂ) = a at hz ⊢
    generalize (z.im : ℂ) = b at hz ⊢
    subst hz
    linear_combination (π * l * b ^ 2) * Complex.I_sq
  have hmp := Complex.volume_preserving_equiv_real_prod
  refine ⟨?_, ?_⟩
  · rw [key, hmp.integrable_comp_emb Complex.measurableEquivRealProd.measurableEmbedding]
    exact hfi.mul_prod hgi
  · rw [key]
    have h1 := hmp.integral_comp' (fun p : ℝ × ℝ => f p.1 * g p.2)
    simp only [Function.comp_def]
    rw [h1, Measure.volume_eq_prod, integral_prod_mul, hf, hg, integral_cexp_quadratic hb,
      integral_cexp_quadratic hb]
    have h2 : (π : ℂ) / -(-(π : ℂ) * l) = l⁻¹ := by field_simp
    have h3 : (l⁻¹ : ℂ) ^ (1 / 2 : ℂ) * (l⁻¹ : ℂ) ^ (1 / 2 : ℂ) = l⁻¹ := by
      rw [← Complex.cpow_add _ _ (inv_ne_zero hl0)]
      norm_num
    rw [h2, mul_mul_mul_comm, h3, ← Complex.exp_add]
    congr 2
    field_simp
    linear_combination (π * (conj v - u) ^ 2) * Complex.I_sq

end GlobalTheory.UnitaryTheta
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.HolDS Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory

theorem mem_of_isometry_eigen_of_dense_iSup :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (U : H →L[ℂ] H), (∀ v, ‖U v‖ = ‖v‖) → ∀ (E : ℕ → Submodule ℂ H) (lam : ℕ → ℂ), Function.Injective lam → (∀ m, FiniteDimensional ℂ (E m)) → (∀ m, ∀ e ∈ E m, U e = lam m • e) → Dense ((⨆ m, E m : Submodule ℂ H) : Set H) → ∀ (m : ℕ) (y : H), U y = lam m • y → y ∈ E m := by
  intro H _ _ _ U hU E lam hlam hfin hE hd m y hy
  let V : H →ₗᵢ[ℂ] H := ⟨U.toLinearMap, hU⟩
  have hin : ∀ a b : H, ⟪U a, U b⟫_ℂ = ⟪a, b⟫_ℂ := fun a b => V.inner_map_map a b
  haveI := hfin m
  obtain ⟨p, hp, q, hq, rfl⟩ := (E m).exists_add_mem_mem_orthogonal y
  have hUq : U q = lam m • q := by
    rw [map_add (f := _), hE m p hp, smul_add] at hy
    exact add_left_cancel hy
  have horth : ∀ m', ∀ e ∈ E m', ⟪e, q⟫_ℂ = 0 := by
    intro m' e he
    by_cases hm : m' = m
    · subst hm
      exact (Submodule.mem_orthogonal _ _).1 hq e he
    by_cases he0 : e = 0
    · simp [he0]
    have h1 := hin e q
    have h2 := hin e e
    rw [hE m' e he, hUq, inner_smul_left, inner_smul_right] at h1
    rw [hE m' e he, inner_smul_left, inner_smul_right] at h2
    have hee : ⟪e, e⟫_ℂ ≠ 0 := by simpa using he0
    have h3 : (starRingEnd ℂ) (lam m') * lam m' = 1 := by
      apply mul_right_cancel₀ hee
      rw [one_mul, mul_assoc, h2]
    by_contra hne
    have h4 : (starRingEnd ℂ) (lam m') * lam m = 1 := by
      apply mul_right_cancel₀ hne
      rw [one_mul, mul_assoc, h1]
    have h5 : (starRingEnd ℂ) (lam m') ≠ 0 := left_ne_zero_of_mul_eq_one h3
    exact hm (hlam (mul_left_cancel₀ h5 (h3.trans h4.symm)))
  have hle : (⨆ m, E m : Submodule ℂ H) ≤ (ℂ ∙ q)ᗮ := by
    refine iSup_le fun m' e he => ?_
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    exact horth m' e he
  have hq0 : q = 0 := by
    have hcl : closure ((⨆ m, E m : Submodule ℂ H) : Set H) ⊆ ((ℂ ∙ q)ᗮ : Submodule ℂ H) :=
      closure_minimal hle (Submodule.isClosed_orthogonal _)
    have := hcl (hd q)
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left] at this
    simpa using this
  simpa [hq0] using hp

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.HolDS Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace
open scoped ComplexOrder MatrixOrder

namespace GlobalTheory.HolDS

theorem exists_congr_one_of_posDef {n : Type} [Fintype n] [DecidableEq n] {S : Matrix n n ℂ} (h : S.PosDef) :
    ∃ d : Matrix n n ℂ, IsUnit d.det ∧ dᴴ * S * d = 1 := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 h.posSemidef.nonneg
  rw [Matrix.star_eq_conjTranspose] at hB
  have hd : B.det ≠ 0 := by
    have h2 := h.det_pos.ne'
    rw [hB, Matrix.det_mul] at h2
    exact right_ne_zero_of_mul h2
  refine ⟨B⁻¹, Matrix.isUnit_nonsing_inv_det _ hd.isUnit, ?_⟩
  rw [hB, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd.isUnit]
  simp

end GlobalTheory.HolDS
end

section

open Polynomial

theorem _root_.GlobalTheory.T.exists_formal_deformation_powerSeries_solution : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ) (I : Type) [Fintype I] (V : Submodule k A) (D P₀ : Ideal A) (Q : I → Ideal A) (f₀ : A), 2 ≤ N → P₀.IsMaximal → (FiniteDimensional k V ∧ (∀ v ∈ V, v ∈ D) ∧ (∀ i, (Q i).IsMaximal) ∧ Function.Injective Q ∧ (∀ i, Q i ≠ P₀) ∧ (∀ i, ¬ D ≤ Q i) ∧ ¬ D ≤ P₀ ∧ f₀ ∈ V ∧ f₀ ≠ 0 ∧ Ideal.span {f₀} = P₀ * D * ∏ i, Q i ^ N ∧ (∀ u : A, ∃ v ∈ V, u - v ∈ P₀ * ∏ i, Q i ^ (N - 1))) → ∃ (ξ : A →ₐ[k] PowerSeries k) (Δ : I → ℕ → A →ₗ[k] PowerSeries k) (m : ℕ) (v : Fin m → A) (y : Fin m → PowerSeries k),
  Function.Injective ξ ∧ (∀ i, Δ i 0 1 = 1) ∧ (∀ i, (∀ l, ∀ u w : A, Δ i l (u * w) = ∑ p ∈ Finset.range (l + 1), l.choose p • (Δ i p u * Δ i (l - p) w))) ∧ (∀ i, ∃ π : A, Δ i 1 π = 1) ∧
  (∀ j, v j ∈ V) ∧ LinearIndependent k v ∧ (∃ j, IsUnit (y j)) ∧ ∑ j, y j * ξ (v j) = 0 ∧ (∀ i, ∀ l < N, ∑ j, y j * Δ i l (v j) = 0) ∧
  (∀ i i', i ≠ i' → ∃ u : A, IsUnit (Δ i 0 u - Δ i' 0 u)) ∧ (∀ i, ∃ u : A, IsUnit (Δ i 0 u - ξ u)) ∧ (∀ i, ∃ u ∈ D, IsUnit (Δ i 0 u)) ∧ (∃ u ∈ D, IsUnit (ξ u)) := by
  first | exact @GlobalTheory.FormalDeform.formal_deformation | exact GlobalTheory.FormalDeform.formal_deformation | (intros; apply GlobalTheory.FormalDeform.formal_deformation <;> assumption)
end
