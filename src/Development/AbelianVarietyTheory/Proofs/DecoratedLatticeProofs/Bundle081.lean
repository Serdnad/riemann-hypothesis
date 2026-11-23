module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle053
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle058
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle057
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle059
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle077
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle079
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle149
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.LocalOrderMatrix
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

@[expose] public section

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.segments_bounds_and_doubling_lFactor : ∀ {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (k t N : ℕ) (z : ℕ → ℂˣ), (∀ i, ‖(z i : ℂ)‖ = 1) → ∀ α : Fin N → ℂˣ, Finset.univ.val.map α = ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.seg w (z i) t → (∀ j, ‖(α j : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((t : ℝ) - 1) / 2) ∧ ‖(α j : ℂ)‖⁻¹ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((t : ℝ) - 1) / 2)) ∧ GlobalTheory.GLDoubling.lFactor (Ideal.absNorm w.asIdeal) α ((t : ℂ) / 2 + 1 / 2) * GlobalTheory.GLDoubling.lFactor (Ideal.absNorm w.asIdeal) α⁻¹ ((t : ℂ) / 2 + 1 / 2) = ∏ i ∈ Finset.Icc 1 k, ∏ n ∈ Finset.Icc 1 t, ((1 - (z i : ℂ) * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹) * (1 - (z i : ℂ)⁻¹ * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹))⁻¹ := by
  first | exact @GlobalTheory.LFun.seg_bounds_and_doubling_lFactor | exact GlobalTheory.LFun.seg_bounds_and_doubling_lFactor | (intros; apply GlobalTheory.LFun.seg_bounds_and_doubling_lFactor <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.card_matrixStep_indices_le_exp : ∃ C : ℝ, 0 ≤ C ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ j, j + 2 ≤ N.R.m → (Fintype.card (I.β j) : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u)) := by
  first | exact @GlobalTheory.Core.Ht2.IndexCountS.card_index_le_sharp | exact GlobalTheory.Core.Ht2.IndexCountS.card_index_le_sharp | (intros; apply GlobalTheory.Core.Ht2.IndexCountS.card_index_le_sharp <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge

noncomputable section

namespace GlobalTheory.TwLast

theorem toLoc_of_mat {E k A B : Type} [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : E →+* k) {a b : ℕ} (e : A ≃ Fin a) (e' : B ≃ Fin b) (x : Matrix A B E) :
    x.map ι = toLoc ι e e' (Matrix.toLin' (Matrix.of fun i j => x (e.symm i) (e'.symm j))) := by
  ext i j
  simp [toLoc, Matrix.toLin'_apply, Matrix.mulVec_single, Function.swap]

theorem psi_isLocallyConstant {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (R : Ranks) (W : TwData k) (g : GL (XIx (Fin R.k) (Fin R.t) s ⊕ Fin (0 + 1)) k) :
    IsLocallyConstant (fun p : Matrix (XIx (Fin R.k) (Fin R.t) (s + 1)) (XIx (Fin R.k) (Fin R.t) s) k × (XIx (Fin R.k) (Fin R.t) (s + 1) → k) =>
      (W.T s R).Psi g p.1 p.2) := by
  have hΦ : (W.T s R).Phi s 0 rfl ∈ SB _ := (Chain.ofTwist_regular _ _ _ _ _).1 s 0 rfl
  unfold Chain.Psi om
  refine (IsLocallyConstant.const _).mul (hΦ.1.comp_continuous ?_)
  refine (continuous_const.matrix_mul ?_).matrix_mul continuous_const
  refine continuous_pi fun r => continuous_pi fun c => ?_
  rcases r with r | r <;> rcases c with c | c
  · exact (continuous_apply c).comp ((continuous_apply r).comp continuous_fst)
  · exact (continuous_apply r).comp continuous_snd
  · exact r.elim0
  · exact r.elim0

theorem lastAgree : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → LastAgree Ch sel mu cst σ₀ P ι s W ν L := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν hc hA L G hL
  have hPhi := GlobalTheory.T.parahoric_test_functions_agree_rational_points X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hc hA
  have hnm : P.1 ∉ Pr.vGs := hA.nmem
  have hint : ∀ a : X.E, ι a ∈ 𝒪[k] ↔ IntAt P.1 a := hA.compl.int
  have hϖ : (W.ϖ : k) = ι (qOf P.1 : X.E) := hA.compl.unif
  refine ⟨fun al g hg => ⟨fun x₀ y => ?_, fun e' e he' he x₀ y' =>
    GlobalTheory.T.penultimateStepPsi_rationalRep_eq_columnsDatum X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hc hA hPhi _ g hg e' e he' he x₀ y'⟩, ?_⟩
  · have hrat := GlobalTheory.T.penultimateStepPsi_rationalRep_eq_columnsDatum X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hc hA hPhi _ g hg
      (GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R s) (GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) (GlobalTheory.MatchCompare.isOrd_ordX R s) (GlobalTheory.MatchCompare.isOrd_ordX R (s + 1))
    refine GlobalTheory.T.locallyConstant_support_invariance_of_dense_rational k X.E ι hA.compl.dense _ _ ((W.T s R).Psi g) (psi_isLocallyConstant s R W g) (W.ϖ ^ cst.M) ?_ ?_ x₀ y
    · intro x y hne
      rw [toLoc_of_mat ι (GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) (GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R s) x] at hne
      have hy : (fun a => ι (y a)) = fun a => ι ((fun i => y ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i)) ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) a)) := by
        simp
      rw [hy, hrat _ (fun i => y ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i))] at hne
      have hs := hL.psiSupp al P _ _ (fun h => (right_ne_zero_of_mul hne) (by rw [h, map_zero]))
      rw [if_neg hnm] at hs
      rw [mem_box]
      intro a
      have h1 := hs ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) a)
      simp only [Equiv.symm_apply_apply] at h1
      have h' := (hint _).2 h1
      rw [map_mul, map_pow, ← hϖ] at h'
      have hϖ0 : ((W.ϖ : k) ^ cst.M) ≠ 0 := pow_ne_zero _ W.ϖ.ne_zero
      calc valuation k (ι (y a)) = valuation k (((W.ϖ : k) ^ cst.M)⁻¹ * ((W.ϖ : k) ^ cst.M * ι (y a))) := by
            rw [inv_mul_cancel_left₀ hϖ0]
        _ = valuation k (((W.ϖ : k) ^ cst.M)⁻¹) * valuation k ((W.ϖ : k) ^ cst.M * ι (y a)) := map_mul _ _ _
        _ ≤ valuation k (((W.ϖ : k) ^ cst.M)⁻¹) * 1 := by gcongr; exact (Valuation.mem_integer_iff _ _).1 h'
        _ = valuation k (((W.ϖ ^ cst.M)⁻¹ : kˣ) : k) := by simp
    · intro x y z hz
      rw [toLoc_of_mat ι (GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) (GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R s) x]
      have hy : (fun a => ι (y a)) = fun a => ι ((fun i => y ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i)) ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) a)) := by
        simp
      have hyz : (fun a => ι (y a + z a)) = fun a => ι (((fun i => y ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i)) +
          (fun i => z ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i))) ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) a)) := by
        simp
      rw [hy, hyz, hrat, hrat _ (fun i => y ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i)), hL.psiInv al P _ _ _ ?_]
      rw [if_neg hnm]
      intro i
      apply (hint _).1
      rw [mem_box] at hz
      have h1 := hz ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i)
      rw [map_mul, map_inv₀, map_pow, ← hϖ, Valuation.mem_integer_iff, map_mul, map_inv₀]
      have hv0 : valuation k ((W.ϖ : k) ^ cst.M) ≠ 0 := by simp
      calc (valuation k ((W.ϖ : k) ^ cst.M))⁻¹ * valuation k (ι (z ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i)))
          ≤ (valuation k ((W.ϖ : k) ^ cst.M))⁻¹ * valuation k ((W.ϖ : k) ^ cst.M) :=
            by gcongr; simpa using h1
        _ = 1 := inv_mul_cancel₀ hv0
  · intro e' e he' he y y' hy'
    simp only [Chain.xiTop]
    rw [GlobalTheory.T.lastStepTestFunction_eq_columnsTestFunction X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hA hPhi e' e he' he y,
      GlobalTheory.T.fourierTransform_cosetIndicator_eq_finiteColumnTransform X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hc hA (hL.depthQ P hnm) e' e he' he y y' hy', map_mul]

end GlobalTheory.TwLast
end
end

section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

namespace GlobalTheory.BasesFin

theorem trForm_denom : ∀ (I : AutInst), ∃ c : ℕ, 0 < c ∧ ∀ x y : Fin I.n → I.E, IntVec I x → IntVec I y →
    ∃ m : ℤ, (c : ℚ) * trForm I x y = m := by
  intro I
  classical
  obtain ⟨y, hy0, hyi⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image fun p : Fin I.n × Fin I.n => I.J p.1 p.2)
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, ?_⟩
  have hcJ : ∀ a b, IsIntegral ℤ ((y.natAbs : I.E) * I.J a b) := by
    intro a b
    have h := hyi (I.J a b) (Finset.mem_image.mpr ⟨(a, b), Finset.mem_univ _, rfl⟩)
    rw [zsmul_eq_mul] at h
    rcases Int.natAbs_eq y with hy | hy
    · rw [hy] at h; simpa using h
    · rw [hy] at h
      have := h.neg
      simpa [neg_mul] using this
  intro x z hx hz
  have hint : IsIntegral ℤ ((y.natAbs : I.E) * Formalism.UG.hform (starRingEnd I.E) I.J x z) := by
    unfold Formalism.UG.hform
    rw [Finset.mul_sum]
    refine IsIntegral.sum _ fun i _ => ?_
    rw [Finset.mul_sum]
    refine IsIntegral.sum _ fun j _ => ?_
    have : (y.natAbs : I.E) * ((starRingEnd I.E) (x i) * I.J i j * z j)
        = (starRingEnd I.E) (x i) * ((y.natAbs : I.E) * I.J i j) * z j := by ring
    rw [this]
    have hs : IsIntegral ℤ ((starRingEnd I.E) (x i)) := (hx i).map (starRingEnd I.E).toIntAlgHom
    exact (hs.mul (hcJ i j)).mul (hz j)
  have htr := Algebra.isIntegral_trace (R := ℤ) (L := ℚ) hint
  obtain ⟨m, hm⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp htr
  refine ⟨m, ?_⟩
  rw [eq_intCast] at hm
  rw [hm]
  unfold trForm
  rw [← map_natCast (algebraMap ℚ I.E), ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem fix_one (I : AutInst) {N : ℕ} (e : Fin N → Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I.n) I.E)
    (he : IsZBasis I e) (hA : ∀ j, A *ᵥ e j = e j) : A = 1 := by
  have key : ∀ u, IntVec I u → A *ᵥ u = u := by
    intro u hu
    obtain ⟨z, rfl⟩ := (he.2 u).1 hu
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul, hA]
  ext i j
  have hs : IntVec I (Pi.single j 1) := by
    intro l
    by_cases h : l = j
    · subst h; simpa using isIntegral_one
    · simp [Pi.single_apply, h, isIntegral_zero]
  have := congrFun (key _ hs) i
  rw [Matrix.mulVec_single_one] at this
  simpa [Matrix.col, Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem bases_finite_classes : ∀ (I : AutInst) (N : ℕ) (R : ℝ), ∃ S : Set (Fin N → Fin I.n → I.E), S.Finite ∧ (∀ e₀ ∈ S, IsZBasis I e₀) ∧ ∀ e : Fin N → Fin I.n → I.E, IsZBasis I e → BddType I R e → ∃ e₀ ∈ S, ∃ γ : GL (Fin I.n) I.E, γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧ (∀ i j, IsIntegral ℤ ((γ : Matrix (Fin I.n) (Fin I.n) I.E) i j)) ∧ (∀ i j, IsIntegral ℤ (((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) i j)) ∧ ∀ j, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ e j = e₀ j := by
  intro I N R
  classical
  obtain ⟨c, hc0, hc⟩ := trForm_denom I
  let T := (Module.Free.ChooseBasisIndex ℤ (𝓞 I.E) → Fin N → Fin N → ℤ) × (Fin N → Fin N → ℚ)
  let has : (Fin N → Fin I.n → I.E) → T → Prop := fun e t =>
    (∀ k j, (integralBasis I.E k : I.E) • e j = ∑ i, t.1 k j i • e i) ∧ ∀ i j, trForm I (e i) (e j) = t.2 i j
  let A : Set T := (Set.univ.pi fun _ => Set.univ.pi fun _ => Set.univ.pi fun _ => {z : ℤ | |(z:ℝ)| ≤ R}) ×ˢ
    (Set.univ.pi fun _ => Set.univ.pi fun _ => {q : ℚ | |(q:ℝ)| ≤ R ∧ ∃ m : ℤ, (c:ℚ) * q = m})
  have hZ : {z : ℤ | |(z:ℝ)| ≤ R}.Finite := by
    refine (Set.finite_Icc (-⌈R⌉) ⌈R⌉).subset fun z hz => ?_
    simp only [Set.mem_setOf_eq] at hz
    have h := abs_le.mp hz
    have hR := Int.le_ceil R
    constructor
    · have : (-(⌈R⌉:ℝ)) ≤ z := by linarith
      exact_mod_cast this
    · have : (z:ℝ) ≤ ⌈R⌉ := by linarith
      exact_mod_cast this
  have hQ : {q : ℚ | |(q:ℝ)| ≤ R ∧ ∃ m : ℤ, (c:ℚ) * q = m}.Finite := by
    refine ((Set.finite_Icc (-⌈R * c⌉) ⌈R * c⌉).image fun m : ℤ => (m : ℚ) / c).subset ?_
    rintro q ⟨hq, m, hm⟩
    have hcpos : (0:ℝ) < c := by exact_mod_cast hc0
    have hmq : (m:ℝ) = c * q := by exact_mod_cast hm.symm
    have h := abs_le.mp hq
    have hR := Int.le_ceil (R * c)
    refine ⟨m, ⟨?_, ?_⟩, ?_⟩
    · have : (-(⌈R*c⌉:ℝ)) ≤ m := by rw [hmq]; nlinarith
      exact_mod_cast this
    · have : (m:ℝ) ≤ ⌈R*c⌉ := by rw [hmq]; nlinarith
      exact_mod_cast this
    · have hc' : (c:ℚ) ≠ 0 := by exact_mod_cast hc0.ne'
      simp only
      rw [← hm]; field_simp
  have hA : A.Finite := (Set.Finite.pi fun _ => Set.Finite.pi fun _ => Set.Finite.pi fun _ => hZ).prod
    (Set.Finite.pi fun _ => Set.Finite.pi fun _ => hQ)
  let pick : T → (Fin N → Fin I.n → I.E) := fun t =>
    if h : ∃ e, IsZBasis I e ∧ has e t then Classical.choose h else 0
  have hpick : ∀ t (h : ∃ e, IsZBasis I e ∧ has e t), IsZBasis I (pick t) ∧ has (pick t) t := by
    intro t h
    simp only [pick, dif_pos h]
    exact Classical.choose_spec h
  have uniq : ∀ (f : Fin N → Fin I.n → I.E) (t : T), IsZBasis I f → has f t → ∀ k j (w : Fin N → ℤ),
      (integralBasis I.E k : I.E) • f j = ∑ i, w i • f i → w = t.1 k j := by
    intro f t hf hft k j w hw
    rw [hft.1 k j] at hw
    have h0 : ∑ i, (w i - t.1 k j i) • f i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← hw, sub_self]
    funext i
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hf.1 _ h0 i)
  have compat : ∀ (f g : Fin N → Fin I.n → I.E) (t : T), IsZBasis I f → has f t → has g t →
      ∀ (k : Module.Free.ChooseBasisIndex ℤ (𝓞 I.E)) (j : Fin N) (w : Fin N → ℤ),
      (integralBasis I.E k : I.E) • f j = ∑ i, w i • f i → (integralBasis I.E k : I.E) • g j = ∑ i, w i • g i := by
    intro f g t hf hft hgt k j w hw
    rw [uniq f t hf hft k j w hw]
    exact hgt.1 k j
  refine ⟨pick '' {t ∈ A | ∃ e, IsZBasis I e ∧ has e t}, (hA.subset (Set.sep_subset _ _)).image _, ?_, ?_⟩
  · rintro _ ⟨t, ⟨-, h⟩, rfl⟩
    exact (hpick t h).1
  · intro e he hb
    choose z hz hzb using hb.1
    let t : T := (z, fun i j => trForm I (e i) (e j))
    have ht : has e t := ⟨hz, fun i j => rfl⟩
    have hint : ∀ i, IntVec I (e i) := fun i => (he.2 (e i)).2 ⟨Pi.single i 1, by simp [Pi.single_apply]⟩
    have htA : t ∈ A := ⟨fun k _ j _ i _ => hzb k j i, fun i _ j _ => ⟨hb.2 i j, hc _ _ (hint i) (hint j)⟩⟩
    have hex : ∃ e', IsZBasis I e' ∧ has e' t := ⟨e, he, ht⟩
    obtain ⟨he₀, ht₀⟩ := hpick t hex
    obtain ⟨M, hMi, hMe⟩ := GlobalTheory.T.exists_integralMatrix_relating_integralVectorZBases I e (pick t) he he₀ (compat e (pick t) t he ht ht₀)
    obtain ⟨M', hM'i, hM'e⟩ := GlobalTheory.T.exists_integralMatrix_relating_integralVectorZBases I (pick t) e he₀ he (compat (pick t) e t he₀ ht₀ ht)
    have h1 : M' * M = 1 := fix_one I e _ he fun j => by rw [← Matrix.mulVec_mulVec, hMe, hM'e]
    have h2 : M * M' = 1 := (mul_eq_one_comm_of_card_eq (Fin I.n) (Fin I.n) I.E rfl).mp h1
    let γ : GL (Fin I.n) I.E := ⟨M, M', h2, h1⟩
    refine ⟨pick t, ⟨t, ⟨htA, hex⟩, rfl⟩, γ, ?_, hMi, hM'i, hMe⟩
    show Formalism.UG.cT (starRingEnd I.E) M * I.J * M = I.J
    exact GlobalTheory.T.unitary_of_preserves_hermitianTraceForm_integralBasis I e M he fun i j => by rw [hMe, hMe]; exact ht₀.2 i j

end GlobalTheory.BasesFin
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

theorem _root_.GlobalTheory.T.exchange_eq_finiteTranslateComb_of_level : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (U : Subgroup (GL (n ⊕ Fin c) k)) (_ : IsOpen (U : Set (GL (n ⊕ Fin c) k))), ∃ e e' : GL (n ⊕ Fin c) k →₀ ℂ, ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (l : A →ₗ[ℂ] ℂ) (v : A), (∀ u ∈ U, σ u v = v) → (IsNEquiv ψ (p + 1) σ l → exDown ν p σ l v = comb e fun g => l (σ g v)) ∧ (IsNEquiv ψ p σ l → exUp ν p σ l v = comb e' fun g => l (σ g v)) := by
  first | exact @GlobalTheory.PosOne.exchange_eq_comb | exact GlobalTheory.PosOne.exchange_eq_comb | (intros; apply GlobalTheory.PosOne.exchange_eq_comb <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

theorem _root_.GlobalTheory.T.fourierJacobi_target_bilinear_form_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : c = 2 * ρ) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (fj : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : Represents ψ ν ρ σ fj B) (_ : BilPos ψ μ (ρ + 1) σ B) (F : A) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (z : ℂ), IsQuotInt ν μX μG (ρ + 1) (tInt ψ ν μ (ρ + 1) σ B F Φ.1) z ↔ FJInt ψ ν μX μG μ ρ (fun h Ψ Φ₀ => fj Ψ (σ h F) Φ₀) Φ.1 z := by
  first | exact @GlobalTheory.PosOne.FJTarget.target_bilinear | exact GlobalTheory.PosOne.FJTarget.target_bilinear | (intros; apply GlobalTheory.PosOne.FJTarget.target_bilinear <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaTranslate

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

theorem hasDerivAt_expLine {H : ℝ → ℂ} {h' : ℂ} (hH : HasDerivAt H h' 0) (a k : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (-(Real.pi * Complex.I) * ((a + s * k : ℝ) : ℂ)) * H s)
      (Complex.exp (-(Real.pi * Complex.I) * (a : ℂ)) * (-(Real.pi * Complex.I) * (k : ℂ) * H 0 + h')) 0 := by
  have h1 : HasDerivAt (fun s : ℝ => a + s * k) k 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const k).const_add a
  have h2 : HasDerivAt (fun s : ℝ => ((a + s * k : ℝ) : ℂ)) (k : ℂ) 0 := h1.ofReal_comp
  have h3 := ((h2.const_mul (-(Real.pi * Complex.I))).cexp).mul hH
  exact h3.congr_deriv (by simp only [zero_mul, add_zero]; ring)

theorem contDiff_heisO_iota_fderiv : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ v : WO S T, ContDiff ℝ ∞ (fun z : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S z) F v) ∧ ∀ z u : GlobalTheory.FockCompare.RW T S, fderiv ℝ (fun z : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S z) F v) z u = (Real.pi * Complex.I) * ((GlobalTheory.OrientedHeis.omO S T z u : ℝ) : ℂ) * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S z) F v + heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S z) (fun y => deriv (fun s : ℝ => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S (s • u)) F y) 0) v := by
  intro D θ σ h ψ hψ S T F hF v
  have hG : ContDiff ℝ ∞ fun x : RW T S => F (v + iotaW σ T S x) := theta_sm h hF v
  have eg : (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F v) = fun z =>
      Complex.exp (-(Real.pi * Complex.I) * (Complex.ofRealCLM (omO S T (piW θ T S v) z))) *
        F (v + iotaW σ T S z) := by
    funext z; rw [heisO_iota h hψ]; rfl
  have hsm : ContDiff ℝ ∞ (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F v) := by
    rw [eg]
    exact (Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (LinearMap.toContinuousLinearMap (omO S T (piW θ T S v))).contDiff))).mul hG
  refine ⟨hsm, fun z u => ?_⟩
  have hHc : ContDiff ℝ ∞ fun x : RW T S => F ((v + iotaW σ T S z) + iotaW σ T S x) := theta_sm h hF _
  have hH : HasDerivAt (fun s : ℝ => F ((v + iotaW σ T S z) + iotaW σ T S (s • u)))
      (deriv (fun s : ℝ => F ((v + iotaW σ T S z) + iotaW σ T S (s • u))) 0) 0 :=
    ((hHc.comp (contDiff_id.smul contDiff_const)).differentiable (by simp) 0).hasDerivAt
  have hline : HasDerivAt (fun s : ℝ => heisO ψ S T (iotaW σ T S (z + s • u)) F v)
      (Complex.exp (-(Real.pi * Complex.I) * ((omO S T (piW θ T S v) z : ℝ) : ℂ)) *
        (-(Real.pi * Complex.I) * ((omO S T (piW θ T S v) u : ℝ) : ℂ) *
          F ((v + iotaW σ T S z) + iotaW σ T S ((0 : ℝ) • u)) +
          deriv (fun s : ℝ => F ((v + iotaW σ T S z) + iotaW σ T S (s • u))) 0)) 0 := by
    have eline : (fun s : ℝ => heisO ψ S T (iotaW σ T S (z + s • u)) F v) = fun s =>
        Complex.exp (-(Real.pi * Complex.I) * ((omO S T (piW θ T S v) z + s * omO S T (piW θ T S v) u : ℝ) : ℂ)) *
          F ((v + iotaW σ T S z) + iotaW σ T S (s • u)) := by
      funext s
      rw [heisO_iota h hψ, (omO S T (piW θ T S v)).map_add, LinearMap.map_smul, smul_eq_mul, (iotaW σ T S).map_add,
        add_assoc]
    rw [eline]
    exact hasDerivAt_expLine hH _ _
  have hf : HasDerivAt (fun s : ℝ => heisO ψ S T (iotaW σ T S (z + s • u)) F v)
      (fderiv ℝ (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F v) z u) 0 := by
    have hd : HasFDerivAt (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F v)
        (fderiv ℝ (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F v) z) (z + (0 : ℝ) • u) := by
      rw [zero_smul, add_zero]; exact (hsm.differentiable (by simp) z).hasFDerivAt
    have hl : HasDerivAt (fun s : ℝ => z + s • u) u 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add z
    exact hd.comp_hasDerivAt (0 : ℝ) hl
  have hF' : HasDerivAt (fun s : ℝ => heisO ψ S T (iotaW σ T S (s • u)) F (v + iotaW σ T S z))
      (Complex.exp (-(Real.pi * Complex.I) * ((0 : ℝ) : ℂ)) *
        (-(Real.pi * Complex.I) * ((omO S T (piW θ T S v) u + omO S T z u : ℝ) : ℂ) *
          F ((v + iotaW σ T S z) + iotaW σ T S ((0 : ℝ) • u)) +
          deriv (fun s : ℝ => F ((v + iotaW σ T S z) + iotaW σ T S (s • u))) 0)) 0 := by
    have eF : (fun s : ℝ => heisO ψ S T (iotaW σ T S (s • u)) F (v + iotaW σ T S z)) = fun s =>
        Complex.exp (-(Real.pi * Complex.I) *
          ((0 + s * (omO S T (piW θ T S v) u + omO S T z u) : ℝ) : ℂ)) *
          F ((v + iotaW σ T S z) + iotaW σ T S (s • u)) := by
      funext s
      rw [heisO_iota h hψ, (piW θ T S).map_add, h.pi_iota, LinearMap.map_smul, smul_eq_mul, (omO S T).map_add,
        LinearMap.add_apply, zero_add]
    rw [eF]
    exact hasDerivAt_expLine hH _ _
  rw [hf.unique hline, heisO_iota h hψ z F v, heisO_iota h hψ z _ v]
  beta_reduce
  rw [hF'.deriv]
  simp only [zero_smul, map_zero, add_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul,
    Complex.ofReal_add]
  ring

end GlobalTheory.ThetaTranslate

end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

namespace GlobalTheory.FlatFactor.KerRedStep

theorem mul_sum_law : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (m m' : Type) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix m m' k) →ₗ[ℂ] M) (β : Matrix m m' k) (S : Finset (m × m')), (∀ e ∈ S, ∀ (b : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ) → ∀ (b : m × m' → k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (∑ e ∈ S, b e * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν m m' _ _ _ _ M _ _ l β S hS b
  have hlc := GlobalTheory.RootEx.OpenKernel.isLocallyConstant_coe_addChar ψ hψc
  induction S using Finset.induction_on with
  | empty =>
    intro Θ Θ' h
    congr 1
    exact Subtype.ext (funext fun t => by simp [h])
  | insert j S hj ih =>
    intro Θ Θ' h
    have hc : Continuous fun t : Matrix m m' k => ∑ e ∈ S, b e * (t e.1 e.2 - β e.1 e.2) :=
      continuous_finsetSum _ fun e _ => continuous_const.mul
        ((continuous_id.matrix_elem _ _).sub continuous_const)
    let Θm : SB (Matrix m m' k) := ⟨fun t => (ψ (∑ e ∈ S, b e * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t,
      (hlc.comp_continuous hc).mul Θ.2.1, Θ.2.2.mul_left⟩
    have h1 : l Θ' = l Θm := hS j (Finset.mem_insert_self j S) (b j) Θm Θ' fun t => by
      rw [h t, Finset.sum_insert hj, AddChar.map_add_eq_mul, Circle.coe_mul, mul_assoc]
    rw [h1]
    exact ih (fun e he => hS e (Finset.mem_insert_of_mem he)) Θ Θm fun t => rfl

theorem trans_sum_law : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (m m' : Type) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix m m' k) →ₗ[ℂ] M) (β : Matrix m m' k) (S : Finset (m × m')), (∀ e ∈ S, ∀ (a : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + Matrix.single e.1 e.2 a)) → l Θ' = l Θ) → ∀ (a : m × m' → k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + ∑ e ∈ S, Matrix.single e.1 e.2 (a e))) → l Θ' = l Θ := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν m m' _ _ _ _ M _ _ l β S hS a
  induction S using Finset.induction_on with
  | empty =>
    intro Θ Θ' h
    congr 1
    exact Subtype.ext (funext fun t => by simp [h])
  | insert j S hj ih =>
    intro Θ Θ' h
    let c : Matrix m m' k := ∑ e ∈ S, Matrix.single e.1 e.2 (a e)
    let Θm : SB (Matrix m m' k) := ⟨fun t => Θ.1 (t + c),
      Θ.2.1.comp_continuous (continuous_id.add continuous_const),
      Θ.2.2.comp_homeomorph (Homeomorph.addRight c)⟩
    have h1 : l Θ' = l Θm := hS j (Finset.mem_insert_self j S) (a j) Θm Θ' fun t => by
      rw [h t, Finset.sum_insert hj, ← add_assoc]
    rw [h1]
    exact ih (fun e he => hS e (Finset.mem_insert_of_mem he)) Θ Θm fun t => rfl

theorem kerRed_extend : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (m m' : Type) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix m m' k) →ₗ[ℂ] M) (β : Matrix m m' k) (ev it ev' it' : Finset (m × m')), ev ⊆ ev' → it ⊆ it' → Disjoint ev' it' → GlobalTheory.FlatFactor.KerRed ν ev it β l → (∀ e ∈ ev', e ∉ ev → ∀ (b : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ) → (∀ e ∈ it', e ∉ it → ∀ (a : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + Matrix.single e.1 e.2 a)) → l Θ' = l Θ) → GlobalTheory.FlatFactor.KerRed ν ev' it' β l := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν m m' _ _ _ _ M _ _ l β ev it ev' it' hev hit hd hK hmul htr
  have hd0 : Disjoint ev it := Finset.disjoint_of_subset_left hev (Finset.disjoint_of_subset_right hit hd)
  have L1 : (∀ e ∈ ev, ∀ (b : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ) := by
    intro e he b Θ Θ' h
    have he' : e ∉ it := Finset.disjoint_left.mp hd0 he
    have h0 : l (Θ' - Θ) = 0 := hK _ fun t => by
      unfold GlobalTheory.FlatFactor.red
      have hz : ∀ a, (Θ' - Θ).1 (GlobalTheory.FlatFactor.fill ev it β t a) = 0 := by
        intro a
        have hf : GlobalTheory.FlatFactor.fill ev it β t a e.1 e.2 = β e.1 e.2 := by
          simp [GlobalTheory.FlatFactor.fill, he, he']
        simp [h, hf]
      simp [hz]
    rwa [map_sub, sub_eq_zero] at h0
  have hM : (∀ e ∈ ev', ∀ (b : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ) := by
    intro e he
    by_cases h : e ∈ ev
    · exact L1 e h
    · exact hmul e he h
  have hT : (∀ e ∈ it', ∀ (a : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + Matrix.single e.1 e.2 a)) → l Θ' = l Θ) := by
    intro e he
    by_cases h : e ∈ it
    · exact GlobalTheory.T.linearMap_killing_partialEvalIntegralKernel_translation_invariant k ψ ν hψc hψ1 hν m m' M l β ev it hd0 hK e h
    · exact htr e he h
  exact GlobalTheory.T.linearMap_kills_partialEvalIntegralKernel_of_laws k ψ ν hψc hψ1 hν m m' M l β ev' it' hd
    (mul_sum_law k ψ ν hψc hψ1 hν m m' M l β ev' hM) (trans_sum_law k ψ ν hψc hψ1 hν m m' M l β it' hT)

end GlobalTheory.FlatFactor.KerRedStep
end
