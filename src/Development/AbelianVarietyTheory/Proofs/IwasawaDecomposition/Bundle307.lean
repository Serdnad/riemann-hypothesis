module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle293
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle222
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle223
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle253
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle302
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeLeSmoothVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIdentificationRespectsRealFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle232
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle298
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1603
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle257
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle299
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin

@[expose] public section

section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

theorem eq_zero_of_sum_coef {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mx n → (H →L[ℂ] H)} {d : ℝ} (hd : IsFdeg (muG ε) σ d) {m : ℕ} {a y : Fin m → H} (ha : Orthonormal ℂ a)
    (h0 : ∀ g ∈ UJset ε, ∑ j, ⟪y j, σ g (a j)⟫_ℂ = 0) (k : Fin m) : y k = 0 := by
  have h1 : ∫ g, ∑ j, coefOn σ (a j) (y j) g * star (coefOn σ (a k) (y k) g) ∂(muG ε) = 0 := by
    have : ∀ g : UJ ε, ∑ j, coefOn σ (a j) (y j) g * star (coefOn σ (a k) (y k) g) = 0 := fun g => by
      rw [← Finset.sum_mul]
      have := h0 (umat g) g.2
      simp only [coefOn]
      rw [this, zero_mul]
    simp only [this, integral_zero]
  rw [integral_finsetSum _ fun j _ => (hd.2 _ _ _ _).1] at h1
  simp only [fun j => (hd.2 (a j) (y j) (a k) (y k)).2, orthonormal_iff_ite.1 ha, ite_mul, ite_div, one_mul, zero_mul,
    zero_div, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1
  have hd' : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd.1.ne'
  exact inner_self_eq_zero.1 ((div_eq_zero_iff.1 h1).resolve_right hd')

theorem exists_rank_one_isAvg : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∃ a c : H, a ≠ 0 ∧ c ≠ 0 ∧ IsKFin ε σ a ∧ IsKFin ε σ c ∧ IsAvg ε σ (fun w => ⟪c, w⟫_ℂ • a) := by
  intro n ε H _ _ _ σ h
  obtain ⟨hσ, -, -, ⟨d, hd⟩, b, hb, hb0⟩ := id h
  obtain ⟨A1, A2, A3, A4, A5⟩ := isAvg_closure n ε H σ hσ
  obtain ⟨B1, B2, -, -⟩ := kCoef_kAvg n ε H σ hσ
  have he := B1 b hb
  obtain ⟨m, a, c, ha, haK, hcK, hQ⟩ := GlobalTheory.T.compactAverage_kFinite_finiteRank n ε H σ h _ he
  have hQavg := A4 _ (by obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1)
  have hc : ∃ k, c k ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply B2 b hb0
    rw [hQ]; simp [hc]
  obtain ⟨k, hk⟩ := hc
  let V : Submodule ℂ (Fin m × Fin m → ℂ) :=
    Submodule.span ℂ ((fun g (p : Fin m × Fin m) => ⟪c p.1, σ g (a p.2)⟫_ℂ) '' UJset ε)
  have hV : ∀ M ∈ V, IsAvg ε σ (fun w => ∑ i, ∑ j, (M (i, j) * ⟪c j, w⟫_ℂ) • a i) := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem M hM =>
      obtain ⟨g, hg, rfl⟩ := hM
      have := (A2 _ _ hQavg (A2 _ _ (A1 g hg) hQavg).2).2

      simp only [hQ, map_sum, map_smul, inner_sum, inner_smul_right, Finset.sum_smul] at this
      simpa only [mul_comm] using this
    | zero => simpa using A5
    | add M N _ _ hM hN =>
      simpa only [Pi.add_apply, add_mul, add_smul, Finset.sum_add_distrib] using (A2 _ _ hM hN).1
    | smul t M _ hM =>
      simpa only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, mul_assoc] using A3 t _ hM
  have hN : (fun p : Fin m × Fin m => if p.2 = k then ⟪c p.1, c k⟫_ℂ else 0) ∈ V := by
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
    intro φ hφ
    rw [Submodule.mem_dualAnnihilator] at hφ
    have e : ∀ z : Fin m → H, φ (fun p => ⟪c p.1, z p.2⟫_ℂ) =
        ∑ j, ⟪∑ i, star (φ fun q => if (i, j) = q then 1 else 0) • c i, z j⟫_ℂ := fun z => by
      rw [LinearMap.pi_apply_eq_sum_univ, Fintype.sum_prod_type, Finset.sum_comm]
      simp [sum_inner, inner_smul_left, mul_comm]
    have hy := eq_zero_of_sum_coef hd ha (y := fun j => ∑ i, star (φ fun q => if (i, j) = q then 1 else 0) • c i)
      (fun g hg => by rw [← e fun j => σ g (a j)]; exact hφ _ (Submodule.subset_span ⟨g, hg, rfl⟩))
    have := e fun j => if j = k then c k else 0
    simp only [hy, inner_zero_left, Finset.sum_const_zero] at this
    refine Eq.trans (congrArg φ ?_) this
    funext p
    by_cases hp : p.2 = k <;> simp [hp]
  refine ⟨∑ i, ⟪c i, c k⟫_ℂ • a i, c k, fun h0 => hk ?_, hk,
    (kfin ε σ).sum_mem fun i _ => (kfin ε σ).smul_mem _ (haK i), hcK k, ?_⟩
  · have := ha.inner_right_fintype (fun i => ⟪c i, c k⟫_ℂ) k
    rw [h0, inner_zero_right] at this
    exact inner_self_eq_zero.1 this.symm
  · have := hV _ hN
    simp only [ite_mul, zero_mul, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    simpa only [Finset.smul_sum, smul_smul, mul_comm] using this

end GlobalTheory.TypeSum
end

section

noncomputable section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

theorem exists_isAvg_apply_eq : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ a : H, a ≠ 0 → ∀ v, IsKFin ε σ v → ∃ T : H → H, IsAvg ε σ T ∧ T a = v := by
  intro n ε H _ _ _ σ h a ha v hv
  obtain ⟨a1, a2, a3, a4, a5⟩ := isAvg_closure n ε H σ h.1
  obtain ⟨c1, c2, c3, c4⟩ := kCoef_kAvg n ε H σ h.1
  let A : Submodule ℂ H :=
    { carrier := {x | ∃ T : H → H, IsAvg ε σ T ∧ T a = x}
      add_mem' := by
        rintro _ _ ⟨T, hT, rfl⟩ ⟨T', hT', rfl⟩
        exact ⟨_, (a2 T T' hT hT').1, rfl⟩
      zero_mem' := ⟨_, a5, rfl⟩
      smul_mem' := by
        rintro c _ ⟨T, hT, rfl⟩
        exact ⟨_, a3 c T hT, rfl⟩ }
  have hA : ∀ T : H → H, IsAvg ε σ T → ∀ x ∈ A, T x ∈ A := by
    rintro T hT _ ⟨T', hT', rfl⟩
    exact ⟨_, (a2 T T' hT hT').2, rfl⟩
  have haA : a ∈ A := ⟨_, a1 1 (one_mem_UJ ε), sigma_one h.1 a⟩
  have hdense : Dense (A : Set H) :=
    dense_of_irred h.2.1 (fun g hg x hx => hA _ (a1 g hg) x hx) ((Submodule.ne_bot_iff _).2 ⟨a, haA, ha⟩)
  have hrange : ∀ e : KG ε → ℂ, KFinFun ε e → Continuous e → ∀ w, kAvg ε σ e w ∈ A := by
    intro e he hc w
    obtain ⟨m, b, c, -, -, -, hbc⟩ := GlobalTheory.T.compactAverage_kFinite_finiteRank n ε H σ h e he
    obtain ⟨Q, hQ⟩ := c3 e hc
    let F : Submodule ℂ H := Submodule.span ℂ (Set.range b)
    haveI : FiniteDimensional ℂ F := FiniteDimensional.span_of_finite ℂ (Set.finite_range b)
    haveI : FiniteDimensional ℂ (A ⊓ F : Submodule ℂ H) := Submodule.finiteDimensional_inf_right A F
    have hcl : IsClosed (Q ⁻¹' ((A ⊓ F : Submodule ℂ H) : Set H)) :=
      (Submodule.closed_of_finiteDimensional _).preimage Q.continuous
    have hsub : (A : Set H) ⊆ Q ⁻¹' ((A ⊓ F : Submodule ℂ H) : Set H) := by
      intro x hx
      refine Submodule.mem_inf.2 ⟨?_, ?_⟩
      · rw [hQ]; exact hA _ (a4 e hc) x hx
      · rw [hQ, hbc]
        exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have := closure_minimal hsub hcl (hdense w)
    rw [← hQ]
    exact (Submodule.mem_inf.1 this).1
  obtain ⟨S, hS, hvS, hK⟩ := hv
  haveI : FiniteDimensional ℂ (S ⊓ A : Submodule ℂ H) := Submodule.finiteDimensional_inf_left S A
  obtain ⟨w, hw, y, hy, hvwy⟩ := (S ⊓ A).exists_add_mem_mem_orthogonal v
  have hyS : y ∈ S := by
    have := S.sub_mem hvS (Submodule.mem_inf.1 hw).1
    rwa [hvwy, add_sub_cancel_left] at this
  have hy0 : y = 0 := by
    by_contra hy0
    have hk := c1 y ⟨S, hS, hyS, hK⟩
    have hc : Continuous fun k : KG ε => star ⟪y, σ (toMK k) y⟫_ℂ := by
      obtain ⟨F, -, h1, h2, -⟩ := hk
      exact h2 _ h1
    exact c2 y hy0 (Submodule.inner_left_of_mem_orthogonal
      (Submodule.mem_inf.2 ⟨c4 _ hc S hS hK y hyS, hrange _ hk hc y⟩) hy)
  rw [hvwy, hy0, add_zero]
  exact (Submodule.mem_inf.1 hw).2

end GlobalTheory.TypeSum

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ConjVecLow

open Formalism.L2.SG.InstExistsPf

theorem lowKSub_le_sm_of_unique {D : D7} {V : HSp D} {Sp : D.what₂.Tau → SPar} (M : DSModel V Sp) (τ : D.what₂.Tau)
    (hone : ∀ S S' : Submodule ℂ (M.H τ),
      Formalism.MainNotions.S.IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) S →
      Formalism.MainNotions.S.IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) S' → S = S') :
    Formalism.MainNotions.S.lowKSub (M.ε τ) (M.lam τ) (M.σ τ) ≤ M.sm τ := by
  obtain ⟨S, hS, hSle⟩ := GlobalTheory.SmoothLowType.exists_lowK_le_sm D V Sp M τ
  exact le_trans (sSup_le fun S' hS' => (hone S' S hS' hS).le) hSle

theorem gap_rows {D : D7} (hG : GapHyp D) {n : ℕ} (hn : n = D.R.r) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.GapAtLeast (fun i : Fin n => Formalism.MainNotions.S.epsS D.R (Fin.cast hn i))
      (fun i : Fin n => Formalism.MainNotions.S.lamS D.R (D.hc τ) (Fin.cast hn i)) (16 * (D.R.r : ℝ) ^ 19) := by
  subst hn
  have h := Formalism.L2.SG.Pf.BunD.gap_lamS D.R (D.hc τ) (h := 16 * (D.R.r : ℚ) ^ 19) (by positivity)
    (fun j hj => hG.2 τ j hj)
  intro a b hab
  have := h a b (by simpa using hab)
  push_cast at this
  simpa using this

theorem npq_lt {n : ℕ} (ε : Fin n → Bool) (hn : 1 ≤ n) :
    (n : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) + 1 < 16 * (n : ℝ) ^ 19 := by
  have hp : ReciprocityTheory.ChartRestriction.DS.pOf ε ≤ n := by
    unfold ReciprocityTheory.ChartRestriction.DS.pOf
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hq : ReciprocityTheory.ChartRestriction.DS.qOf ε ≤ n := by
    unfold ReciprocityTheory.ChartRestriction.DS.qOf
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp' : (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) ≤ n := by exact_mod_cast hp
  have hq' : (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) ≤ n := by exact_mod_cast hq
  have h3 : (n : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) ≤ (n : ℝ) ^ 3 := by
    have := mul_le_mul (mul_le_mul_of_nonneg_left hp' (by positivity)) hq' (by positivity) (by positivity)
    nlinarith
  have h19 : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 19 := pow_le_pow_right₀ hn' (by norm_num)
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 19 := one_le_pow₀ hn'
  linarith

theorem exists_conj_intertwiner_of_gap (hUq : GlobalTheory.Published.DiscreteSeriesUpqUnique) {D : D7} (hG : GapHyp D)
    (I : Formalism.MainNotions.S.AutInst) (hI : I = instOf D)
    (pl : InfinitePlace I.F ≃ D.what₂.Tau) (n_eq : I.n = D.R.r)
    (eps_eq : ∀ v (i : Fin I.n), I.ε v i = Formalism.MainNotions.S.epsS D.R (Fin.cast n_eq i))
    (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)
    (lam : InfinitePlace I.F → Fin I.n → ℝ)
    (lam_eq : ∀ v (i : Fin I.n), lam v i = Formalism.MainNotions.S.lamS D.R (D.hc (pl v)) (Fin.cast n_eq i))
    (ds : ∀ v, Formalism.MainNotions.S.IsDS (I.ε v) (lam v) (σ v)) (low : ∀ v, Formalism.MainNotions.S.IsLowUnit (I.ε v) (lam v) (σ v) (w v))
    (N : DSModel (D.sp.Y 0) (parB (tparRec D) 0)) :
    ∃ c : ∀ τ, N.H τ ≃ₗᵢ⋆[ℂ] H (pl.symm τ),
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ m : Matrix (Fin I.n) (Fin I.n) ℂ,
        HEq m ((GlobalTheory.SeeInt.frP D τ)⁻¹ * g * GlobalTheory.SeeInt.frP D τ) → ∀ x, c τ (N.rep τ g x) = σ (pl.symm τ) m (c τ x)) ∧
      ∀ τ, (c τ).symm (w (pl.symm τ)) ∈ N.sm τ := by
  subst hI
  have hU := GlobalTheory.Published.discreteSeriesHermitianUnique_iff.2 hUq
  let M0 : DSModel (D.sp.Y 0) (parA (tparRec D) 0) :=
    { H := fun τ => H (pl.symm τ)
      σ := fun τ => σ (pl.symm τ)
      lam := fun τ => lam (pl.symm τ)
      ε := fun τ => (instOf D).ε (pl.symm τ)
      fr := fun τ => (GlobalTheory.SeeInt.frP D τ)⁻¹
      enum := fun τ => by
        have e1 : lam (pl.symm τ) = fun i => Formalism.MainNotions.S.lamS D.R (D.hc τ) (Fin.cast n_eq i) :=
          funext fun i => by rw [lam_eq, Equiv.apply_symm_apply]
        have e2 : (instOf D).ε (pl.symm τ) = fun i => Formalism.MainNotions.S.epsS D.R (Fin.cast n_eq i) :=
          funext fun i => eps_eq _ i
        rw [e1, e2]
        exact GlobalTheory.RowLev.isEnum_parA_zero D n_eq τ
      ds := fun τ => ds _
      fr_unit := fun τ => Matrix.isUnit_nonsing_inv_iff.mpr ((instOf D).P_unit _)
      fr_gram := fun τ => GlobalTheory.SeeInt.fr_gram D τ }
  obtain ⟨M', c, hc⟩ := GlobalTheory.ConjDS.exists_conjModel M0
  obtain ⟨U, hUi⟩ := hU.exists_intertwiner (M := (M' : DSModel (D.sp.Y 0) (parB (tparRec D) 0))) (M' := N)
  have key : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ x,
      c τ (U τ (N.rep τ g x)) = M0.rep τ g (c τ (U τ x)) := by
    intro τ g hg x
    exact (congrArg (c τ) (hUi τ g hg x)).trans (hc τ g hg _)
  refine ⟨fun τ => (U τ).trans (c τ), ?_, ?_⟩
  · intro τ g hg m hm x
    have hm' : m = (GlobalTheory.SeeInt.frP D τ)⁻¹ * g * GlobalTheory.SeeInt.frP D τ := eq_of_heq hm
    show c τ (U τ (N.rep τ g x)) = σ (pl.symm τ) m (c τ (U τ x))
    rw [key τ g hg x, hm']
    show σ (pl.symm τ) ((GlobalTheory.SeeInt.frP D τ)⁻¹ * g * ((GlobalTheory.SeeInt.frP D τ)⁻¹)⁻¹) _ = _
    rw [Matrix.nonsing_inv_nonsing_inv _ (GlobalTheory.SeeInt.frP_unit D τ)]
  · intro τ
    have hone : ∀ S S' : Submodule ℂ (M0.H τ),
        Formalism.MainNotions.S.IsKTypeOf (M0.ε τ) (M0.σ τ) (Formalism.QuantumDeterminants.lowK (M0.ε τ) (M0.lam τ)) S →
        Formalism.MainNotions.S.IsKTypeOf (M0.ε τ) (M0.σ τ) (Formalism.QuantumDeterminants.lowK (M0.ε τ) (M0.lam τ)) S' → S = S' := by
      have hHC := GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (M0.enum τ).1 (M0.ds τ)
      haveI : CompleteSpace (M0.H τ) := (M0.ds τ).1
      have hgap : Formalism.QuantumDeterminants.GapAtLeast (M0.ε τ) (M0.lam τ) (16 * (D.R.r : ℝ) ^ 19) := by
        have e1 : M0.ε τ = fun i => Formalism.MainNotions.S.epsS D.R (Fin.cast n_eq i) := funext fun i => eps_eq (pl.symm τ) i
        have e2 : M0.lam τ = fun i => Formalism.MainNotions.S.lamS D.R (D.hc τ) (Fin.cast n_eq i) :=
          funext fun i => by
            show lam (pl.symm τ) i = _
            exact (lam_eq (pl.symm τ) i).trans (by rw [Equiv.apply_symm_apply])
        rw [e1, e2]
        exact gap_rows hG n_eq τ
      have hr : (D.sp.Y 0).rank = D.R.r := n_eq
      have hbig : ((D.sp.Y 0).rank : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf (M0.ε τ) : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf (M0.ε τ) : ℝ) + 1 <
          16 * (D.R.r : ℝ) ^ 19 := by
        have h1 : 1 ≤ (D.sp.Y 0).rank := by have := hG.1; omega
        exact (npq_lt (M0.ε τ) h1).trans_eq (by rw [hr])
      exact (ReciprocityTheory.ChartRestriction.DS.isDS_props_of_gap _ _ _ hHC _ hgap hbig _ _ (M0.ds τ)).2.1
    have hw : w (pl.symm τ) ∈ M0.sm τ := lowKSub_le_sm_of_unique M0 τ hone (low _).2
    set e := (U τ).trans (c τ) with he
    have hint : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ y,
        e.symm (M0.rep τ g y) = N.rep τ g (e.symm y) := by
      intro g hg y
      apply e.injective
      rw [LinearIsometryEquiv.apply_symm_apply]
      have := key τ g hg (e.symm y)
      change e (N.rep τ g (e.symm y)) = M0.rep τ g (e (e.symm y)) at this
      rw [this, LinearIsometryEquiv.apply_symm_apply]
    exact GlobalTheory.ConjMult.span_conj (GlobalTheory.SmoothAutCheck.gramAt_unit _ τ) e.symm hint hw

theorem conjModel_of_gap : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∃ c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) ∧ ∀ τ, (c τ).symm (X.B.w (X.pl.symm τ)) ∈ (MP R).sm τ := by
  intro _ _ hUq _ D G' _ _ Pl0 T A Ks _ _ _ R F X h t hιE hG _ hinf _ _
  have key : (∀ k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) ↔ (iotaX X h k).1 = 1) ∧ (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).2 = 1 ∧ (∀ v, v ≠ X.pl.symm τ → (iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 v = 1) ∧ HEq (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) ((fun Pm : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ => Pm⁻¹ * g * Pm) ((Formalism.L2.SG.InstExistsPf.instOf D).P (Formalism.L2.Host.tauPl D τ)))) ∧ ∀ τ (y : Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ))), ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ) = y :=
    GlobalTheory.IotaReal.iota_real_finite_of_eq R.θ hinf X.B.I h X.ιE X.pl X.φ_eq hιE
  obtain ⟨-, hreal, -⟩ := key
  obtain ⟨c, hc1, hc2⟩ := exists_conj_intertwiner_of_gap hUq hG X.B.I h X.pl X.n_eq X.eps_eq X.B.H X.B.σ X.B.w
    X.B.lam X.lam_eq X.ds X.low (MP R)
  exact ⟨c, fun τ g hg x => hc1 τ g hg _ (hreal τ g hg).2.2 x, hc2⟩

end GlobalTheory.ConjVecLow
end
end

section

open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
noncomputable section

namespace GlobalTheory.ConjRowLevelSee

theorem conjMap_level_of_seeAt : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, ∀ k ∈ JR R F, ∀ g : GA D (Yc D 0), GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ g k) = chiR R F k * GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u g := by
  intro _ _ _ _ D G' _ _ Pl0 T A Ks _ _ _ R F X h t _ _ _ _ _ hsee c _ Φ hΦ hrep u (k : GA D (D.sp.Y 0)) hk (g : GA D (D.sp.Y 0))
  obtain ⟨ψ, hψ⟩ := hrep u
  show star (GlobalTheory.ConjRowMult.contRepL X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u)))
      (iotaX X h ((g * k * t⁻¹ : GA D (D.sp.Y 0))))) = _ *
    star (GlobalTheory.ConjRowMult.contRepL X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u)))
      (iotaX X h ((g * t⁻¹ : GA D (D.sp.Y 0)))))
  rw [GlobalTheory.ConjRowMult.contRepL_spec X hψ]
  obtain ⟨hJ, hχ⟩ := hsee.conj k
  have hmem := hJ.1 hk
  have hval := hχ hk
  set x := iotaX X h ((t⁻¹)⁻¹ * k * t⁻¹ : GA D (D.sp.Y 0)) with hxdef
  have hx : x.1 = 1 ∧ x.2 ∈ X.K2 := hmem
  have hxeq : x = (1, x.2) := Prod.ext hx.1 rfl
  have hΦk : X.B.R (1, x.2) (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) =
      X.chi2 x.2 • Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u)) := by
    obtain ⟨T', -, hT'⟩ := hΦ
    rw [← hT']
    exact congrArg (fun C : L2X X →L[ℂ] L2X X => C (T' _)) (GlobalTheory.ConjRowLevel.reg_comp_Re X x.2 hx.2)
  have hrep2 := Formalism.L2.SG.EvalTOntoRep.contRep_reg X hψ (1, x.2)
  rw [hΦk] at hrep2
  have key := Formalism.L2.SG.EvalTOntoRep.contRep_unique X hrep2 (Formalism.L2.SG.EvalTOntoRep.contRep_smul X _ hψ)
  have e1 : (g * k * t⁻¹ : GA D (D.sp.Y 0)) = g * t⁻¹ * ((t⁻¹)⁻¹ * k * t⁻¹) := by group
  have hkey : ∀ z, ψ (z * x) = X.chi2 x.2 * ψ z := by
    intro z
    conv_lhs => rw [hxeq]
    exact congrFun key z
  have hm : iotaX X h ((g * k * t⁻¹ : GA D (D.sp.Y 0))) = iotaX X h ((g * t⁻¹ : GA D (D.sp.Y 0))) * x := by
    rw [e1, hxdef]
    exact map_mul (iotaX X h) _ _
  rw [hm, hkey, star_mul']
  exact congrArg (· * _) hval

end GlobalTheory.ConjRowLevelSee
end
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

theorem _root_.GlobalTheory.T.exists_continuous_retraction_onto_unitaryArchimedeanPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (τ : E →+* ℂ), ∃ r : UA E n →* embU n τ, Continuous r ∧ (∀ x : embU n τ, r x = x) ∧ ∀ (g : UA E n) (y : embU n τ), Commute ((r g : UA E n)⁻¹ * g) (y : UA E n) := by
  first | exact @GlobalTheory.DefU.exists_embRet | exact GlobalTheory.DefU.exists_embRet | (intros; apply GlobalTheory.DefU.exists_embRet <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

theorem _root_.GlobalTheory.T.fixedPlace_unitaryLocalPoints_equiv_localUnitaryGroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E), (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → (∀ x, Valued.v (s x) = Valued.v x) → ∃ e : locU n w ≃ₜ* UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)), ∀ x : locU n w, (e x : GL (Fin n) (w.adicCompletion E)) = cLoc w (x : UA E n) := by
  first | exact @GlobalTheory.DefU.Inert.locU_equiv | exact GlobalTheory.DefU.Inert.locU_equiv | (intros; apply GlobalTheory.DefU.Inert.locU_equiv <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

theorem _root_.GlobalTheory.T.unramified_nonsplit_exists_conj_involution_uniformiser : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → ¬ IsSplitAt w → ∃ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ), (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧ IsUnramInv ϖ s q := by
  first | exact @GlobalTheory.InertPlaceConj.exists_conj_isUnramInv | exact GlobalTheory.InertPlaceConj.exists_conj_isUnramInv | (intros; apply GlobalTheory.InertPlaceConj.exists_conj_isUnramInv <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

theorem _root_.GlobalTheory.T.definiteUnitary_classSet_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (K : Subgroup (finU (E := E) (n := n))), IsOpen (K : Set (finU (E := E) (n := n))) → ∃ S : Finset (UA E n), ∀ g : UA E n, ∃ γ ∈ ratU E n, ∃ s ∈ S, ∃ x ∈ infU E n, ∃ k ∈ K, g = γ * s * x * (k : UA E n) := by
  first | exact @GlobalTheory.DefU.ClassFin.classSet_finite | exact GlobalTheory.DefU.ClassFin.classSet_finite | (intros; apply GlobalTheory.DefU.ClassFin.classSet_finite <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU

theorem exists_finU_mul_infU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (g : UA E n),
    ∃ k ∈ finU (E := E) (n := n), ∃ x ∈ infU E n, g = k * x := by
  intro E _ _ _ n g
  let k : UA E n := ⟨finGL E n (GeneralLinearGroup.map (pFin E) g.1), ClassFin.finGL_mem_UA _ (ClassFin.cT_pFin g)⟩
  have hk : k ∈ finU (E := E) (n := n) := pInf_finGL _
  refine ⟨k, hk, k⁻¹ * g, ?_, (mul_inv_cancel_left k g).symm⟩
  change GeneralLinearGroup.map (pFin E) (k⁻¹ * g).1 = 1
  have h : GeneralLinearGroup.map (pFin E) k.1 = GeneralLinearGroup.map (pFin E) g.1 := pFin_finGL _
  rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, h, inv_mul_cancel]

end GlobalTheory.DefU
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

theorem _root_.GlobalTheory.T.splitPlace_unitaryLocalPoints_equiv_GL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → ∃ e : locU n w ≃ₜ* GL (Fin n) (w.adicCompletion E), ∀ x : locU n w, e x = cLoc w (x : UA E n) := by
  first | exact @GlobalTheory.locU_equiv_GL | exact GlobalTheory.locU_equiv_GL | (intros; apply GlobalTheory.locU_equiv_GL <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LevelSmooth

theorem level_open_compact_smooth (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    IsOpen (((lev D.sp.cm V.gram β L).comap (finE V) : Subgroup (GA D V)) : Set (GA D V)) ∧
    IsCompact ((levA V (lev D.sp.cm V.gram β L) : Subgroup (GA D V)) : Set (GA D V)) ∧
    levS V β L ⊆ (GfC V : Set (GA D V)) ∧
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧
      ∀ k ∈ U, k ∈ GfC V → k ∈ levS V β L ∧ levChi V β L k = 1 :=
  ⟨GlobalTheory.ParahoricCompact.isOpen_comap_lev V β L, GlobalTheory.ParahoricCompact.isCompact_levG V β L, fun _ hk => hk.1,
    GlobalTheory.GoodFiniteDim.exists_open_subgroup V β L⟩

end GlobalTheory.Mem.LevelSmooth
end

section

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_local_howe_contraction_compact_unitary : ∀ (N n : ℕ) (hn : n ≤ N) (ν : Fin N → ℕ) (x₁ x₃ : ℤ) (Λ : Fin n → ℝ) (Λ' : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H'] (σ' : Matrix (Fin N) (Fin N) ℂ → (H' →L[ℂ] H')), Antitone ν → (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) → (∀ a, Λ a = (x₃ : ℝ) - ν (Fin.castLE hn (Fin.rev a))) → (∀ b, Λ' b = -(x₁ : ℝ) - ν (Fin.rev b)) → IsURepOn (UJset (allPos n)) σ → IsKTypeOf (allPos n) σ Λ ⊤ → IsURepOn (UJset (allPos N)) σ' → IsKTypeOf (allPos N) σ' Λ' ⊤ → ∃ I : MvPolynomial (Fin N × Fin n) ℂ →ₗ[ℂ] H' →ₗ[ℂ] H, I ≠ 0 ∧ ∀ h ∈ UJset (allPos N), ∀ g ∈ UJset (allPos n), ∀ P v, I ((h.det ^ x₁ * g.det ^ x₃) • subst2 h (g⁻¹)ᵀ P) (σ' h v) = σ g (I P v) := by
  first | exact @GlobalTheory.CompactHowe.exists_local_contraction | exact GlobalTheory.CompactHowe.exists_local_contraction | (intros; apply GlobalTheory.CompactHowe.exists_local_contraction <;> assumption)
end
