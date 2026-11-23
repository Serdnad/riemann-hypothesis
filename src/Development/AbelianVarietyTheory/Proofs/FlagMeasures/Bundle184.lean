module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle145
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle126
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeRightTranslateLowerBoun
import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle159
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFramesSameGradedDefinitePartLatticeEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDefiniteSpaceIsometryOfAdaptedPair
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormUniqueUpToUnipotent
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle166
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselUnipotentMulVecMiddleVec
import Formalism.FormalDegreeBessel.FinalG
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle165
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep Formalism.HN
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.OmegaLeast


open scoped Matrix.Norms.L2Operator in
theorem opNorm_le_sqrt_hs {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ‖A‖ ≤ Real.sqrt (Formalism.REAL.hs A) := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  have hhs : 0 ≤ Formalism.REAL.hs A := by unfold Formalism.REAL.hs; positivity
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_mul hhs]
  apply Real.sqrt_le_sqrt
  unfold Formalism.REAL.hs
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖∑ j, A i j * x j‖ ≤ ∑ j, ‖A i j‖ * ‖x j‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖A i j‖) (fun j => ‖x j‖)
  refine le_trans ?_ h2
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2


open scoped Matrix.Norms.L2Operator in
theorem opNorm_exp_le {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖NormedSpace.exp A‖ ≤ Real.exp ‖A‖ := by
  have h1 : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ = 1 := GlobalTheory.LeastVar.opN_one hn
  haveI : NormOneClass (Matrix (Fin n) (Fin n) ℂ) := ⟨h1⟩
  have h := NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ) A
  have h' := NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) ‖A‖
  rw [Real.exp_eq_exp_ℝ]
  refine h.norm_le_of_bounded h' fun k => ?_
  rw [NormedSpace.expSeries_apply_eq, NormedSpace.expSeries_apply_eq, norm_smul, smul_eq_mul]
  gcongr
  · simp
  · exact norm_pow_le _ _

open scoped Matrix.Norms.L2Operator in
theorem dOp_exp_mul_exp_le {n : ℕ} (hn : 1 ≤ n) (A Z : Matrix (Fin n) (Fin n) ℂ) :
    dOp (NormedSpace.exp A * NormedSpace.exp Z) ≤
      Real.sqrt (Formalism.REAL.hs A) + Real.sqrt (Formalism.REAL.hs Z) := by
  have h : ‖NormedSpace.exp A * NormedSpace.exp Z‖ ≤
      Real.exp (Real.sqrt (Formalism.REAL.hs A) + Real.sqrt (Formalism.REAL.hs Z)) := by
    rw [Real.exp_add]
    refine (norm_mul_le _ _).trans ?_
    gcongr
    · exact (opNorm_exp_le hn A).trans (Real.exp_le_exp.2 (opNorm_le_sqrt_hs A))
    · exact (opNorm_exp_le hn Z).trans (Real.exp_le_exp.2 (opNorm_le_sqrt_hs Z))
  change Real.log ‖NormedSpace.exp A * NormedSpace.exp Z‖ ≤ _
  rcases (norm_nonneg (NormedSpace.exp A * NormedSpace.exp Z)).eq_or_lt with h0 | h0
  · rw [← h0, Real.log_zero]; positivity
  · exact (Real.log_le_iff_le_exp h0).2 h

theorem half_truncatedLeastLatticeSize_le_unipotentNeighbourhood : ∀ (I : AutInst) (x : I.GA) (W : Submodule I.E (Fin I.n → I.E)) (ρ : ℝ), 1 ≤ I.n → ρ ≤ Real.log 2 → ∀ y ∈ omega I x W ρ, tau1 I x / 2 ≤ tau1 I y := by
  intro I x W ρ hn hρ y hy
  obtain ⟨h2, A, Z, -, hAZ, hy1, -⟩ := hy
  obtain ⟨-, -, -, -, -, ⟨K, hK⟩, -⟩ := GlobalTheory.CongTop.adelic_topology I
  have hk : (x⁻¹ * y).2 ∈ I.Kset := by
    have : (x⁻¹ * y).2 = 1 := by simp [h2]
    rw [this, ← hK]; exact K.one_mem
  have hv := GlobalTheory.LeastVar.truncatedLeastLatticeSize_rightTranslate_lower_bound I hn x (x⁻¹ * y) hk
  rw [mul_inv_cancel_left] at hv
  have hcard := (GlobalTheory.Count.FrameMajorant.frames_give_majorants I x).2.2.1
  have hfpos : (0 : ℝ) < I.f := by
    rw [← hcard]; exact_mod_cast Fintype.card_pos
  have hhs : ∀ B : Matrix (Fin I.n) (Fin I.n) ℂ, 0 ≤ Formalism.REAL.hs B := fun B => by
    unfold Formalism.REAL.hs; positivity
  have hd : ∀ v, dOp (uMat ((x⁻¹ * y).1 v)) ≤ Real.log 2 := by
    intro v
    have e : uMat ((x⁻¹ * y).1 v) = NormedSpace.exp (A v) * NormedSpace.exp (Z v) := by
      have e1 : uMat ((x⁻¹ * y).1 v) = uMat ((x.1 v)⁻¹) * uMat (y.1 v) := by simp [uMat]
      have e2 : uMat ((x.1 v)⁻¹) * uMat (x.1 v) = 1 := by simp [uMat]
      rw [e1, hy1 v, Matrix.mul_assoc, ← Matrix.mul_assoc, e2, Matrix.one_mul]
    rw [e]
    refine (dOp_exp_mul_exp_le hn _ _).trans (le_trans ?_ (hAZ.trans hρ))
    gcongr
    · exact Finset.single_le_sum (f := fun v => Formalism.REAL.hs (A v)) (fun v _ => hhs _) (Finset.mem_univ v)
    · exact Finset.single_le_sum (f := fun v => Formalism.REAL.hs (Z v)) (fun v _ => hhs _) (Finset.mem_univ v)
  have hs : (∑ v, dOp (uMat ((x⁻¹ * y).1 v))) / I.f ≤ Real.log 2 := by
    rw [div_le_iff₀ hfpos]
    refine (Finset.sum_le_sum fun v _ => hd v).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, mul_comm]
  have he : (1 / 2 : ℝ) ≤ Real.exp (-((∑ v, dOp (uMat ((x⁻¹ * y).1 v))) / I.f)) := by
    have : (1 / 2 : ℝ) = Real.exp (-Real.log 2) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    rw [this]
    exact Real.exp_le_exp.2 (neg_le_neg hs)
  have ht : 0 ≤ tau1 I x := by
    obtain ⟨-, hfg, hspan, -, -⟩ := GlobalTheory.T.autPointLatticeIntersection_selfDual_properties I x
    haveI := (GlobalTheory.Count.FrameMajorant.frames_give_majorants I x).1
    have hx := (GlobalTheory.Count.FrameMajorant.frames_give_majorants I x).2.2.2.2
    have hne : lamX I x ≠ ⊥ := by
      intro h
      haveI : Nonempty (Fin I.n) := ⟨⟨0, hn⟩⟩
      rw [h] at hspan
      simp at hspan
    have h3 := (sizeMu I.E _ _ (bas I) (frm I x) (fun w => (hx w).1) (lamX I x) hfg hne).2.2.2.1
    unfold tau1 least
    rw [h3]
    exact le_min (by norm_num) (Real.exp_pos _).le
  have := mul_le_mul_of_nonneg_left he ht
  linarith

end GlobalTheory.OmegaLeast
end
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.DegAsm.FrameEqv
open AdaptInv
section
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

theorem map_xa {G G' : FlagD H r} {n : V ≃ₗ[K] V} (h : ∀ a : Fin (r + 1), n (G.e a) - G'.e a ∈ G'.Xa a.val)
    (k : ℕ) {x : V} (hx : x ∈ G.Xa k) : n x ∈ G'.Xa k := by
  have key : G.Xa k ≤ (G'.Xa k).comap (n : V →ₗ[K] V) := by
    show Submodule.span K _ ≤ _
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, rfl⟩
    have hb' : b.val < k := hb
    have h1 : n (G.e b.castSucc) - G'.e b.castSucc ∈ G'.Xa b.val := h b.castSucc
    have h2 : n (G.e b.castSucc) =
        (n (G.e b.castSucc) - G'.e b.castSucc) + G'.e b.castSucc := by abel
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe]
    rw [h2]
    exact (G'.Xa k).add_mem (xa_mono G' hb'.le h1) (e_mem_xa G' b hb')
  exact key hx

theorem symm_xa {G G' : FlagD H r} {n : V ≃ₗ[K] V} (h : ∀ a : Fin (r + 1), n (G.e a) - G'.e a ∈ G'.Xa a.val)
    (k : ℕ) : ∀ x ∈ G'.Xa k, n.symm x ∈ G.Xa k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hx
    have key : G'.Xa k ≤ (G.Xa k).comap (n.symm : V →ₗ[K] V) := by
      show Submodule.span K _ ≤ _
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, hb, rfl⟩
      have hb' : b.val < k := hb
      have h1 : n (G.e b.castSucc) - G'.e b.castSucc ∈ G'.Xa b.val := h b.castSucc
      have h2 := ih b.val hb' _ h1
      have e1 : n.symm (G'.e b.castSucc) =
          G.e b.castSucc - n.symm (n (G.e b.castSucc) - G'.e b.castSucc) := by
        rw [map_sub, LinearEquiv.symm_apply_apply, sub_sub_cancel]
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe]
      rw [e1]
      exact (G.Xa k).sub_mem (e_mem_xa G b hb') (xa_mono G hb'.le h2)
    exact key hx

theorem symm_gr {G G' : FlagD H r} {n : V ≃ₗ[K] V} (h : ∀ a : Fin (r + 1), n (G.e a) - G'.e a ∈ G'.Xa a.val)
    (a : Fin (r + 1)) : n.symm (G'.e a) - G.e a ∈ G.Xa a.val := by
  have h1 := symm_xa h a.val _ (h a)
  have e1 : n.symm (G'.e a) - G.e a = -(n.symm (n (G.e a) - G'.e a)) := by
    rw [map_sub, LinearEquiv.symm_apply_apply, neg_sub]
  rw [e1]
  exact (G.Xa a.val).neg_mem h1

theorem inN_gr {F : FlagD H r} {n : V ≃ₗ[K] V} (h : F.InN (n : V →ₗ[K] V)) (a : Fin (r + 1)) :
    n (F.e a) - F.e a ∈ F.Xa a.val := by
  induction a using Fin.lastCases with
  | last =>
    rw [Fin.val_last]
    exact h.2.2.2 _ F.zperp
  | cast b =>
    rw [Fin.coe_castSucc]
    exact h.2.2.1 b

theorem gr_comp {G G' M : FlagD H r} {n : V ≃ₗ[K] V} (h : ∀ a : Fin (r + 1), n (G.e a) - G'.e a ∈ G'.Xa a.val)
    (hM : SameGr G M) (a : Fin (r + 1)) : n (M.e a) - G'.e a ∈ G'.Xa a.val := by
  have e1 : n (M.e a) - G'.e a = n (M.e a - G.e a) + (n (G.e a) - G'.e a) := by
    rw [map_sub]; abel
  rw [e1]
  exact (G'.Xa a.val).add_mem (map_xa h a.val (hM a)) (h a)
end

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

theorem frEqv_equivalence (F : FlagD H r) (Λ : Submodule (𝓞 K) V) : Equivalence (FrEqv F Λ) := by
  refine ⟨fun G => ⟨1, GlobalTheory.UnipStab.inN_one, one_smul _ _, fun a => by simp⟩, ?_, ?_⟩
  · rintro G G' ⟨n, hn, hΛ, hG⟩
    refine ⟨n⁻¹, GlobalTheory.UnipStab.inN_inv hn, ?_, fun a => symm_gr hG a⟩
    conv_lhs => rw [← hΛ]
    exact inv_smul_smul n Λ
  · rintro G G' G'' ⟨n, hn, hΛ, hG⟩ ⟨m, hm, hΛ', hG'⟩
    refine ⟨m * n, GlobalTheory.UnipStab.inN_mul hm hn, by rw [mul_smul, hΛ, hΛ'], fun a => ?_⟩
    have e1 : (m * n) (G.e a) - G''.e a = m (n (G.e a) - G'.e a) + (m (G'.e a) - G''.e a) := by
      rw [LinearEquiv.mul_apply, map_sub]; abel
    rw [e1]
    exact (G''.Xa a.val).add_mem (map_xa hG' a.val (hG a)) (hG' a)

theorem move (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {F G G' : FlagD H r} {𝔡 : Ideal (𝓞 K)} {Λ : Submodule (𝓞 K) V}
    (h : FrEqv F Λ G G') (N : NF H r) (hN : Adapt F G 𝔡 N) :
    ∃ N' : NF H r, Adapt F G' 𝔡 N' ∧ N'.om Λ = N.om Λ ∧
      ∀ g : ℕ, (N'.IsTerm g Λ ↔ N.IsTerm g Λ) ∧ N'.gI g Λ = N.gI g Λ := by
  obtain ⟨n, hn, hΛ, hG⟩ := h
  have hiso : n ∈ isomGrp H := (mem_isomGrp H n).2 fun x y => hn.1 x y
  obtain ⟨N', he, -, -, -, hd, -, hrest⟩ := GlobalTheory.T.exists_hermFramePairNormalForm_moved_by_isometry K V H hK r N n hiso
  refine ⟨N', ⟨hd.trans hN.1, fun a => ?_, fun a => ?_⟩, ?_, fun g => ?_⟩
  · rw [(he a).1]
    have e1 : n (N.F.e a) - F.e a = n (N.F.e a - F.e a) + (n (F.e a) - F.e a) := by
      rw [map_sub]; abel
    rw [e1]
    exact (F.Xa a.val).add_mem (GlobalTheory.UnipStab.map_Xa hn a.val (hN.2.1 a)) (inN_gr hn a)
  · rw [(he a).2]
    exact gr_comp hG hN.2.2 a
  · have h1 := (hrest 0 Λ).1
    rwa [hΛ] at h1
  · have h1 := hrest g Λ
    rw [hΛ] at h1
    exact ⟨h1.2.1, h1.2.2⟩

end GlobalTheory.DegAsm.FrameEqv

namespace GlobalTheory.DegAsm
open FrameEqv

theorem frEqv_invariants : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F : FlagD H r) (𝔡 : Ideal (𝓞 K)) (Λ : Submodule (𝓞 K) V), Equivalence (FrEqv F Λ) ∧ ∀ G G' : FlagD H r, FrEqv F Λ G G' → omI F G 𝔡 Λ = omI F G' 𝔡 Λ ∧ ∀ N : NF H r, Adapt F G 𝔡 N → ∃ N' : NF H r, Adapt F G' 𝔡 N' ∧ N'.om Λ = N.om Λ ∧ ∀ g : ℕ, (N'.IsTerm g Λ ↔ N.IsTerm g Λ) ∧ N'.gI g Λ = N.gI g Λ := by
  intro K V _ _ _ _ _ _ _ _ H hK r F 𝔡 Λ
  refine ⟨frEqv_equivalence F Λ, fun G G' h => ⟨?_, fun N hN => move hK h N hN⟩⟩
  have sub : ∀ {G G' : FlagD H r}, FrEqv F Λ G G' →
      (fun N : NF H r => N.om Λ) '' {N | Adapt F G 𝔡 N} ⊆
        (fun N : NF H r => N.om Λ) '' {N | Adapt F G' 𝔡 N} := by
    intro G G' h x hx
    obtain ⟨N, hN, rfl⟩ := hx
    obtain ⟨N', hN', hom, -⟩ := move hK h N hN
    exact ⟨N', hN', hom⟩
  unfold omI
  rw [Set.Subset.antisymm (sub h) (sub ((frEqv_equivalence F Λ).symm h))]

end GlobalTheory.DegAsm
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.exists_definiteSpace_isometry_of_adapted_pair : ∀ (K V W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (H : HermSpace K V) (HW : HermSpace K W) (e : W →ₗ[K] V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F G : FlagD H r) (𝔡 : Ideal (𝓞 K)) (N : NF H r) (γ : V ≃ₗ[K] V), IsEmb F HW e → Adapt F G 𝔡 N → γ ∈ isomGrp H → (∀ a, G.e a = γ (F.e a)) → ∃ h : W ≃ₗ[K] W, h ∈ isomGrp HW ∧ IsH F G e γ h ∧ (∀ h' : W ≃ₗ[K] W, IsH F G e γ h' → h' = h) ∧ ∀ (g : ℕ) (Λ' : Submodule (𝓞 K) V), (datOf F G e g (γ • Λ')).1 = imLat h (lat0 F e Λ') := by
  first | exact @GlobalTheory.DegAsm.exists_isH | exact GlobalTheory.DegAsm.exists_isH | (intros; apply GlobalTheory.DegAsm.exists_isH <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermFramePairNormalForm_unique_up_to_unipotent : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F : FlagD H r) (N₀ N₁ : NF H r), SameGr F N₀.F → SameGr F N₁.F → N₀.j = N₁.j → N₀.c = N₁.c → N₀.T = N₁.T → pairM N₀.F N₀.F' N₀.j = pairM N₁.F N₁.F' N₁.j → ∃ s : V ≃ₗ[K] V, F.InN (s : V →ₗ[K] V) ∧ ∀ a, s (N₀.F.e a) = N₁.F.e a ∧ s (N₀.F'.e a) = N₁.F'.e a := by
  first | exact @GlobalTheory.DegAsm.nf_unique | exact GlobalTheory.DegAsm.nf_unique | (intros; apply GlobalTheory.DegAsm.nf_unique <;> assumption)
end

section

noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegVol.RefCov

def crd (k r j : ℕ) (β : Fin r → ℕ) (q : (UTin β → ℂ) × PTop k r j) : Mat k r :=
  pTop k r j q.2 * uEmb k r (upperIn β q.1)

abbrev Crd (ι : Type) (k r j : ℕ) (β : Fin r → ℕ) :=
  (UTin β → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ) ×
    (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ))

def atP {ι : Type} {k r j : ℕ} {β : Fin r → ℕ} (p : Crd ι k r j β) (v : ι) : (UTin β → ℂ) × PTop k r j :=
  (fun i => p.1 i v, fun a => p.2.1 a v, fun s => p.2.2.1 s v, fun a => p.2.2.2 a v)

def CC {ι : Type} {k r j : ℕ} {β : Fin r → ℕ} (p : Crd ι k r j β) : ι → Mat k r := fun v => crd k r j β (atP p v)

theorem usage₂ {ι : Type} {k r j : ℕ} {β : Fin r → ℕ} :
    Function.Bijective (atP : Crd ι k r j β → ι → (UTin β → ℂ) × PTop k r j) := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun q => (fun i v => (q v).1 i, fun a v => (q v).2.1 a,
    fun s v => (q v).2.2.1 s, fun a v => (q v).2.2.2 a), fun _ => rfl, fun _ => rfl⟩

end GlobalTheory.DegVol.RefCov
end
end

section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.majorantMomentBound_both_sides : ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn C1 CMo : ℝ), 4 ≤ D.R.m → MomIn D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 25 CMo → HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W → ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ S : LocS W, GoodS D lam' S → MomBd W.z W.νS S.Φ (24 * D.R.rS ^ 3 + 1) (large₂.sc.b ^ (max CMo 0 * D.R.m)) ∧ MomBd W.z' W.νS' S.Φ' (24 * D.R.rS ^ 3 + 1) (large₂.sc.b ^ (max CMo 0 * D.R.m)) := by
  first | exact @GlobalTheory.Amp.MomBoth.momBd_both | exact GlobalTheory.Amp.MomBoth.momBd_both | (intros; apply GlobalTheory.Amp.MomBoth.momBd_both <;> assumption)
end

section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Amp.YInv
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.YjInv

variable {k r j : ℕ}

theorem N_ej (hj : j ≤ r) {n : Mat k r} (hn : n ∈ Nset k r) (a : Fin j) :
    n *ᵥ bvec (eI k r (Fin.castLE hj a)) =
      ∑ b : Fin j, n (eI k r (Fin.castLE hj b)) (eI k r (Fin.castLE hj a)) • bvec (eI k r (Fin.castLE hj b)) := by
  rw [N_e hn]
  symm
  refine Finset.sum_of_injOn (Fin.castLE hj) ((Fin.castLE_injective hj).injOn) (by simp) ?_ (by simp)
  intro b _ hb
  have hb' : j ≤ b.val := by
    by_contra h
    exact hb ⟨⟨b.val, by omega⟩, by simp, rfl⟩
  have ha := a.isLt
  rw [hn.2.1 (Fin.castLE hj a) _ (by simp [eI]; omega), if_neg, zero_smul]
  intro h
  have := congrArg Fin.val h
  simp [eI] at this
  omega

theorem N_detj (hj : j ≤ r) {n : Mat k r} (hn : n ∈ Nset k r) :
    (Matrix.of fun b a : Fin j => n (eI k r (Fin.castLE hj b)) (eI k r (Fin.castLE hj a))).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp only [Matrix.of_apply]
    rw [hn.2.1 (Fin.castLE hj a) _ le_rfl, if_pos rfl]
  · intro b a hab
    have hab' : a.val < b.val := hab
    simp only [Matrix.of_apply]
    rw [hn.2.1 (Fin.castLE hj a) (eI k r (Fin.castLE hj b)) hab'.le, if_neg]
    intro h
    have := congrArg Fin.val h
    simp [eI] at this
    omega

theorem Yj_N (hj : j ≤ r) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (γ : Mat k r)
    {n₁ n₂ : Mat k r} (h₁ : n₁ ∈ Nset k r) (h₂ : n₂ ∈ Nset k r) (x : Mat k r) :
    Yj k r hj z z' (n₁ * γ * n₂) x = Yj k r hj z z' γ (n₂ * x) := by
  have h₁' := (nSubgroup k r).2.2 _ h₁
  unfold Yj Dj
  rw [dInv k r z z' hz hz' n₁ (N_sub_S z h₁) n₂ (N_sub_S z' h₂), Ppos_N hz hz' h₁ h₂,
    ← gramProj_comb _ (fun a : Fin j => (n₂ * x)⁻¹ *ᵥ (γ⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj a)))) _ (N_detj hj h₁')]
  congr 2
  funext a
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    N_ej hj h₁']
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.of_apply, ← Matrix.mulVec_mulVec]

theorem Yj_K (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ x : Mat k r) {κ : Mat k r} (hG : κ ∈ GG k r)
    (hκ : κ ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ) :
    Yj k r hj z z' γ (x * κ) = Yj k r hj z z' γ x := by
  have h1 : star κ * κ = 1 := Matrix.mem_unitaryGroup_iff'.1 hκ
  have h2 : κ * star κ = 1 := Matrix.mem_unitaryGroup_iff.1 hκ
  have hG' : star κ * Hpk k r * κ = Hpk k r := hG
  have hc : (Hpk k r - 1) * κ = κ * (Hpk k r - 1) := by
    have : κ * Hpk k r = Hpk k r * κ := by
      conv_lhs => rw [← hG', ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
    rw [Matrix.sub_mul, Matrix.mul_sub, this, Matrix.one_mul, Matrix.mul_one]
  unfold Yj
  rw [gramProj_unitary (Ppos k r z z' γ x) (Ppos k r z z' γ (x * κ)) _ κ hκ]
  · congr 2
    funext a
    rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ κ,
      Matrix.mul_nonsing_inv _ (det_unit hG), Matrix.one_mulVec]
  · intro p
    rw [mem_Ppos, mem_Ppos]
    simp only [Matrix.mulVec_mulVec, hc]
    refine and_congr ⟨fun h => ?_, fun h => ?_⟩ Iff.rfl
    · rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
    · have := congrArg (star κ *ᵥ ·) h
      simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
      rwa [← Matrix.mul_assoc, h1, Matrix.one_mul] at this

theorem yj_invariant : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ γ : Mat k r, inWb k r z → inWb k r z' → γ ∈ GG k r → ∀ x ∈ GG k r, (∀ κ ∈ (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))), Yj k r hj z z' γ (x * κ) = Yj k r hj z z' γ x) ∧ (∀ n₁ ∈ Nset k r, ∀ n₂ ∈ Nset k r, Yj k r hj z z' (n₁ * γ * n₂) x = Yj k r hj z z' γ (n₂ * x)) ∧ ∀ ρ ∈ Rset k r γ, Yj k r hj z z' γ (ρ * x) = Yj k r hj z z' γ x := by
  intro k r j hj z z' γ hz hz' hγ x _
  refine ⟨fun κ hκ => Yj_K hj z z' γ x hκ.1 hκ.2, fun n₁ h₁ n₂ h₂ => Yj_N hj hz hz' γ h₁ h₂ x, fun ρ hρ => ?_⟩
  rw [← Yj_N hj hz hz' γ ((nSubgroup k r).2.2 _ hρ.2) hρ.1 x]
  congr 1
  have hm : IsUnit (γ * ρ * γ⁻¹).det := det_unit hρ.2.1
  have e : γ * ρ = γ * ρ * γ⁻¹ * γ := by
    rw [Matrix.mul_assoc (γ * ρ), Matrix.nonsing_inv_mul _ (det_unit hγ), Matrix.mul_one]
  rw [Matrix.mul_assoc]
  conv_lhs => rw [show (γ * ρ * γ⁻¹)⁻¹ * (γ * ρ) = (γ * ρ * γ⁻¹)⁻¹ * (γ * ρ * γ⁻¹ * γ) from by rw [← e]]
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hm, Matrix.one_mul]

end GlobalTheory.Amp.YjInv
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

theorem _root_.GlobalTheory.T.flagLatticeStabiliserRealGroup_mul_mem : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), ∀ x ∈ flagGroup I xf S, ∀ y ∈ flagGroup I xf S, x * y ∈ flagGroup I xf S := by
  first | exact @GlobalTheory.FlagStabMul.flagGroup_mul | exact GlobalTheory.FlagStabMul.flagGroup_mul | (intros; apply GlobalTheory.FlagStabMul.flagGroup_mul <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

theorem _root_.GlobalTheory.T.isSaturatedIsotropicFlag_of_adaptedBasis : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → IsSatFlag I (lamX I (1, xf)) j S := by
  first | exact @GlobalTheory.FlagBase.AdSat.isSatFlag_of_isAdapted | exact GlobalTheory.FlagBase.AdSat.isSatFlag_of_isAdapted | (intros; apply GlobalTheory.FlagBase.AdSat.isSatFlag_of_isAdapted <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

theorem _root_.GlobalTheory.T.exists_adapted_basis_change_models : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ (Λ' : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀' : I₀.Gf), (∀ i, ∃ γ : GL (Fin (j i)) I.E, ∀ y, (γ : Matrix (Fin (j i)) (Fin (j i)) I.E) *ᵥ y ∈ Λ' i ↔ y ∈ Λ i) → (∃ γ ∈ I₀.GFset, ∃ k ∈ I₀.Kset, γ.2 * x₀ = x₀' * k) → ∃ U U' U₀, IsAdapted I I₀ e xf j S Λ' x₀' U U' U₀ := by
  first | exact @GlobalTheory.AdaptedMove.adapted_move | exact GlobalTheory.AdaptedMove.adapted_move | (intros; apply GlobalTheory.AdaptedMove.adapted_move <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

theorem _root_.GlobalTheory.T.flagGradedPieceSizes_stabiliser_mul : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∀ γ ∈ flagGroup I xf S, ∀ g : I.Ginf, sizesAt I xf S (γ * g) = sizesAt I xf S g := by
  first | exact @GlobalTheory.FlagSizeInv.sizesAt_mul | exact GlobalTheory.FlagSizeInv.sizesAt_mul | (intros; apply GlobalTheory.FlagSizeInv.sizesAt_mul <;> assumption)
end
