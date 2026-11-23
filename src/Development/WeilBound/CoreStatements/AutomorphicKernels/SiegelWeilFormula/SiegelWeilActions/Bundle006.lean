module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.Bundle001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle005
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.MemStabiliserIffFrameLowerBlock
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.CountableRationalPointsDoubled
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContinuousCj
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle011
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

theorem range_or (L : LD d) (u : Fin d.n ⊕ Fin d.n) :
    (∃ u', Sum.map L.em L.em u' = u) ∨ u ∈ ({Sum.inl L.i₀, Sum.inr L.i₀} : Set (Fin d.n ⊕ Fin d.n)) := by
  rcases u with a | a <;>
  · by_cases ha : a = L.i₀
    · right; simp [ha]
    · obtain ⟨a', rfl⟩ := (L.rng a).1 ha
      left; first | exact ⟨Sum.inl a', rfl⟩ | exact ⟨Sum.inr a', rfl⟩

theorem j_par (L : LD d) {p : G2 σ L.Y} (hp : p ∈ par2 σ L.Y) : L.j p ∈ par2 σ d.Y := by
  rw [ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame]
  rw [ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block L.sd.ok.frame] at hp
  ext a c
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply]
  rcases range_or L (Sum.inr a) with ⟨u', hu'⟩ | hu
  · rcases range_or L (Sum.inl c) with ⟨v', hv'⟩ | hv
    · rcases u' with a' | a'
      · simp at hu'
      rcases v' with c' | c'
      · have h1 := congrFun (congrFun (L.j_in p) (Sum.inr a')) (Sum.inl c')
        simp only [Matrix.submatrix_apply, Sum.map_inr, Sum.map_inl] at h1
        simp only [Sum.map_inr, Sum.inr.injEq] at hu'
        simp only [Sum.map_inl, Sum.inl.injEq] at hv'
        rw [← hu', ← hv', h1]
        exact congrFun (congrFun hp a') c'
      · simp at hv'
    · rw [(L.j_out p _ hv (Sum.inr a)).2]
      simp
  · rw [(L.j_out p _ hu (Sum.inl c)).1]
    simp

theorem j_rat (L : LD d) {p : G2 σ L.Y} (hp : p ∈ rat2 σ L.Y) : L.j p ∈ rat2 σ d.Y := by
  obtain ⟨g, hg⟩ := hp
  have hm : mat2 p = incM F g.1 := (congrArg Units.val hg).symm
  have hL : inFrame L.b p = incM F ((L.b⁻¹).1 * g.1 * L.b.1) := by
    rw [kunf.incM_mul', kunf.incM_mul', ← hm]; rfl
  let M' := (L.b⁻¹).1 * g.1 * L.b.1
  let M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E := fun u v =>
    if hu : ∃ u', Sum.map L.em L.em u' = u then
      if hv : ∃ v', Sum.map L.em L.em v' = v then M' hu.choose hv.choose else (1 : Matrix _ _ E) u v
    else (1 : Matrix _ _ E) u v
  refine kunf.rat_of_inFrame (b := d.b) (M := M) ?_
  ext u v
  show inFrame d.b (L.j p) u v = inclR (F := F) (AF F) (M u v)
  dsimp only [M]
  by_cases hu : ∃ u', Sum.map L.em L.em u' = u
  · by_cases hv : ∃ v', Sum.map L.em L.em v' = v
    · rw [dite_eq_left hu, dite_eq_left hv]
      have h1 := congrFun (congrFun (L.j_in p) hu.choose) hv.choose
      simp only [Matrix.submatrix_apply, hu.choose_spec, hv.choose_spec] at h1
      rw [h1, hL]
      rfl
    · rw [dite_eq_left hu, dite_eq_right hv]
      have hv' := (range_or L v).resolve_left hv
      rw [(L.j_out p _ hv' u).2]
      simp [Matrix.one_apply, apply_ite]
  · rw [dite_eq_right hu]
    have hu' := (range_or L u).resolve_left hu
    rw [(L.j_out p _ hu' v).1]
    simp [Matrix.one_apply, apply_ite]

theorem phz_j_leftInv (L : LD d) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) (x : d.G) :
    GlobalTheory.AutomorphicL2Unitary.LeftInv (par2 σ L.Y ⊓ rat2 σ L.Y)
      (fun g : G2 σ L.Y => ((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s₁) * f (L.j g * x)) := by
  intro p hp g
  show phz d f s₁ z (L.j (p * g) * x) = phz d f s₁ z (L.j g * x)
  rw [map_mul, mul_assoc]
  exact phz_leftInv d hf z (L.j p) ⟨j_par L hp.1, j_rat L hp.2⟩ _

end PositivityTheory.SiegelWeilFormula.Act.C1

end
end

section

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C5

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} (R : RD d) (L : LD d)

variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}

def th (T : nF σ d.Y d.b) (β : nA σ d.Y d.b) : ℂ := d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))

def th' (T' : nF σ L.Y L.b) (β : nA σ L.Y L.b) : ℂ :=
  d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T'.1.1 * β.1))))

theorem section_sum_integral_expand {f : d.G → ℂ} {s₁ z : ℂ} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)} {T : nF σ d.Y d.b}
    {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)} (hν : ν 𝓤 = 1) (hlam : lam 𝓖 = 1) (x : d.G)
    (hi : ∀ q : Cs d, Integrable (kq L f s₁ z nb T uM (rep q) x) ((ν.restrict 𝓤).prod (lam.restrict 𝓖)))
    (hs : Summable fun q : Cs d => ∫ p, ‖kq L f s₁ z nb T uM (rep q) x p‖ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖))) :
    sec2 L f s₁ z nb lam 𝓖 T uM ν 𝓤 x =
        ∫ p, E2 L (phz d f s₁ z) (nb p.2 * (uM p.1 * x)) * th T p.2 ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) ∧
      ∫⁻ p, ∑' q : {q : Cs d // ¬ LagrangianCondition L (rep q)}, ‖phz d f s₁ z (rep q.1 * (nb p.2 * (uM p.1 * x))) * th T p.2‖ₑ
        ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) < ⊤ := by
  have : Countable (rat2 σ d.Y) := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ d.Y
  have : Countable (Cs d) := Quotient.countable
  have : IsFiniteMeasure (ν.restrict 𝓤) := isFiniteMeasure_restrict.2 (by simp [hν])
  have : IsFiniteMeasure (lam.restrict 𝓖) := isFiniteMeasure_restrict.2 (by simp [hlam])
  set μ := (ν.restrict 𝓤).prod (lam.restrict 𝓖) with hμ
  let g : {q : Cs d // ¬ LagrangianCondition L (rep q)} → (Fin L.n → AE F E) × nA σ d.Y d.b → ℂ :=
    fun q => kq L f s₁ z nb T uM (rep q.1) x
  have hgi : ∀ q, Integrable (g q) μ := fun q => hi q.1
  have hgs : Summable fun q => ∫ p, ‖g q p‖ ∂μ := hs.subtype _
  have htm : ∀ q : {q : Cs d // ¬ LagrangianCondition L (rep q)}, tm L f s₁ z nb lam 𝓖 T uM ν 𝓤 (rep q.1) x = ∫ p, g q p ∂μ := by
    intro q
    rw [hμ, integral_prod _ (hgi q)]
    rfl
  constructor
  · unfold sec2
    simp_rw [htm]
    rw [(hasSum_integral_of_summable_integral_norm hgi hgs).tsum_eq]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [g, kq, E2, th]
    rw [tsum_mul_right]
  · have hm : ∀ q, AEMeasurable (fun p => ‖g q p‖ₑ) μ := fun q => (hgi q).aemeasurable.enorm
    have e1 : ∫⁻ p, ∑' q : {q : Cs d // ¬ LagrangianCondition L (rep q)}, ‖phz d f s₁ z (rep q.1 * (nb p.2 * (uM p.1 * x))) * th T p.2‖ₑ ∂μ =
        ∑' q, ENNReal.ofReal (∫ p, ‖g q p‖ ∂μ) := by
      rw [show (fun p => ∑' q : {q : Cs d // ¬ LagrangianCondition L (rep q)},
          ‖phz d f s₁ z (rep q.1 * (nb p.2 * (uM p.1 * x))) * th T p.2‖ₑ) = fun p => ∑' q, ‖g q p‖ₑ from rfl,
        lintegral_tsum hm]
      exact tsum_congr fun q => (ofReal_integral_norm_eq_lintegral_enorm (hgi q)).symm
    rw [e1, ← ENNReal.ofReal_tsum_of_nonneg (fun q => integral_nonneg fun p => norm_nonneg _) hgs]
    exact ENNReal.ofReal_lt_top

end PositivityTheory.SiegelWeilFormula.Act.C5

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ} {L : LD d} {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
  {𝓤 : Set (Fin L.n → AE F E)} {nb : nA σ d.Y d.b → d.G}

theorem ratV_inc {u : Fin L.n → AE F E} (hu : u ∈ L.ratV) : ∃ v : Fin L.n → E, u = GlobalTheory.ThK.incV F v := by
  induction hu using AddSubgroup.closure_induction with
  | mem _ h => obtain ⟨v, rfl⟩ := h; exact ⟨v, rfl⟩
  | zero => exact ⟨0, funext fun i => by simp [GlobalTheory.ThK.incV]⟩
  | add _ _ _ _ h h' =>
    obtain ⟨v, rfl⟩ := h; obtain ⟨w, rfl⟩ := h'; exact ⟨v + w, funext fun i => by simp [GlobalTheory.ThK.incV]⟩
  | neg _ _ h => obtain ⟨v, rfl⟩ := h; exact ⟨-v, funext fun i => by simp [GlobalTheory.ThK.incV]⟩

theorem neg_incV (v : Fin L.n → E) : -GlobalTheory.ThK.incV F v = GlobalTheory.ThK.incV F (-v) := funext fun i => by simp [GlobalTheory.ThK.incV]

def A0 (L : LD d) (v : Fin L.n → E) : Matrix (Fin d.n) (Fin d.n) E := 1 + ∑ j, Matrix.single L.i₀ (L.em j) (v j)

theorem Au_inc (v : Fin L.n → E) : Au L (GlobalTheory.ThK.incV F v) = incM F (A0 L v) := by
  ext a b

  simp [Au, A0, incM, Matrix.one_apply, Matrix.sum_apply, Matrix.single_apply, GlobalTheory.ThK.incV, map_sum, apply_ite]

theorem Apc (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : (Ap hU u).map (cA σ) = (Au L (-u))ᵀ := by
  have h1 : (Ap hU u).map (cA σ) * (Au L u)ᵀ = 1 := mul_eq_one_comm.1 (frame_blk d (inFrame_uM hU u))
  have h2 : (Au L u)ᵀ * (Au L (-u))ᵀ = 1 := by rw [← Matrix.transpose_mul, Au_mul, neg_add_cancel, Au_zero, Matrix.transpose_one]
  calc (Ap hU u).map (cA σ) = (Ap hU u).map (cA σ) * ((Au L u)ᵀ * (Au L (-u))ᵀ) := by rw [h2, Matrix.mul_one]
    _ = (Au L (-u))ᵀ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem Ap_inc (hU : L.UData uM ν 𝓤) (v : Fin L.n → E) : ∃ M : Matrix (Fin d.n) (Fin d.n) E,
    Ap hU (GlobalTheory.ThK.incV F v) = incM F M := by
  have : FiniteDimensional F E := Module.Finite.of_basis d.bs
  let e := AlgEquiv.ofBijective σ (AlgHom.bijective σ)
  refine ⟨((A0 L (-v))ᵀ).map e.symm, Matrix.map_injective (cA_injective d) ?_⟩
  show (Ap hU (GlobalTheory.ThK.incV F v)).map (cA σ) = (incM F (((A0 L (-v))ᵀ).map e.symm)).map (cA σ)
  rw [Apc, kunf.incM_map_cA, Matrix.map_map, neg_incV, Au_inc]
  have h : (⇑σ ∘ ⇑e.symm) = id := funext fun x => e.apply_symm_apply x
  rw [h, Matrix.map_id]
  rfl

theorem uM_rat (hU : L.UData uM ν 𝓤) {u : Fin L.n → AE F E} (hu : u ∈ L.ratV) : uM u ∈ rat2 σ d.Y := by
  obtain ⟨v, rfl⟩ := ratV_inc hu
  obtain ⟨M, hM⟩ := Ap_inc hU v
  refine kunf.rat_of_inFrame (b := d.b) (M := Matrix.fromBlocks (A0 L v) 0 0 M) ?_
  rw [inFrame_uM hU, Au_inc, hM]
  simp [incM, Matrix.fromBlocks_map]

theorem cj_rat (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) {u : Fin L.n → AE F E} (hu : u ∈ L.ratV)
    {β : nA σ d.Y d.b} (hβ : β ∈ nF σ d.Y d.b) : cj hU hN u β ∈ nF σ d.Y d.b := by
  obtain ⟨v, rfl⟩ := ratV_inc hu
  obtain ⟨M, hM⟩ := Ap_inc hU v
  obtain ⟨T, hT⟩ := kunf.mem_nF_iff.1 hβ
  refine kunf.mem_nF_iff.2 ⟨A0 L (-v) * T * M, ?_⟩
  rw [cj_val, neg_incV, Au_inc, hT, hM, kunf.incM_mul', kunf.incM_mul']

theorem mul_Au (X : Matrix (Fin d.n) (Fin d.n) (AE F E)) (hX : ∀ a, X a L.i₀ = 0) (u : Fin L.n → AE F E) :
    X * Au L u = X := by
  have h : ∀ j, X * Matrix.single L.i₀ (L.em j) (u j) = 0 := fun j => by
    ext a b
    simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    split_ifs with h
    · rw [← h.1, hX, zero_mul]
    · exact mul_zero _
  simp only [Au, Matrix.mul_add, Matrix.mul_one, Finset.mul_sum, h, Finset.sum_const_zero, add_zero]

theorem AuT_mul (X : Matrix (Fin d.n) (Fin d.n) (AE F E)) (hX : ∀ b, X L.i₀ b = 0) (u : Fin L.n → AE F E) :
    (Au L u)ᵀ * X = X := by
  have h : ∀ j, (Matrix.single L.i₀ (L.em j) (u j))ᵀ * X = 0 := fun j => by
    ext a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    split_ifs with h
    · rw [← h.1, hX, mul_zero]
    · exact zero_mul _
  simp only [Au, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_sum, Matrix.add_mul, Matrix.one_mul,
    Finset.sum_mul, h, Finset.sum_const_zero, add_zero]

theorem trace_cj (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b}
    (hT : L.IsSub T T') (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    Matrix.trace (T.1.1 * (cj hU hN u β).1) = Matrix.trace (T.1.1 * β.1) := by
  have h1 : T.1.1 * Au L (-u) = T.1.1 := mul_Au _ (fun a => (hT.1 a).2) _
  have h2 : Ap hU u * T.1.1 = T.1.1 := by
    apply Matrix.map_injective (cA_injective d)
    show (Ap hU u * T.1.1).map (cA σ) = T.1.1.map (cA σ)
    rw [kunf.map_cA_mul, Apc]
    exact AuT_mul _ (fun b => by simp [(hT.1 b).1]) _
  rw [cj_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h2]

end PositivityTheory.SiegelWeilFormula.Act.C1

end
end
