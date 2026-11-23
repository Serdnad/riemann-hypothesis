module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.WeilBound.CoreStatements.LocalThetaKernels.ExistsSmallSubgroups
public import Development.WeilBound.CoreStatements.LocalThetaKernels.LinearIndependentOfNotMem
public import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep
import Development.WeilBound.CoreStatements.LocalThetaKernels.LocrepAd
public import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle005
public import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowDef
public import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle001
import Aesop.Main
public import Development.WeilBound.ThetaLifts.LeviDeterminants.ContinuousOfMem
public import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowInt
public import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle004
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1330
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MCSpan
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Real.Pi.Bounds
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle002
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

noncomputable section

namespace PositivityTheory.ThKF0

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK
open PositivityTheory.ThKH.Locrep

theorem actsEx : GlobalTheory.ThK.ActsEx := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v
  obtain ⟨ω, ρ, L⟩ := locRepEx F E σ n d B X W M om ⟨hP.base, ⟨r, s, hP.herm⟩, ⟨r', s', hP.skew⟩, hP.good, χX, χW, hP.weil⟩ v
  refine ⟨fun g hg h hh φ hφ => ⟨ω (g, h) φ, ⟨L.pres g hg h hh φ hφ, (L.acts g hg h hh φ hφ _).2 rfl⟩,
      fun φ₁ h₁ => (L.acts g hg h hh φ hφ _).1 h₁.2⟩,
    fun u hu φ hφ => ⟨ρ u φ, ⟨L.presH u hu φ hφ, (L.actsH u hu φ hφ _).2 rfl⟩,
      fun φ₁ h₁ => (L.actsH u hu φ hφ _).1 h₁.2⟩, fun φ hφ => ?_⟩
  have hs := IsUWeilPair.isUSplitting hP.weil
  obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base (Fin n × Fin d) v
  let loc : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v) := fun p => res v x₀ ∘ₗ om p ∘ₗ tensL v r₀
  have hloc : ∀ p : UA σ X.J × UA σ W.J, p.1 ∈ UAt σ X (evFin F v) → p.2 ∈ UAt σ W (evFin F v) → ∀ φ ∈ SB _,
      loc p φ = ω p φ := fun p h1 h2 φ hφ =>
    (eq_of_acts v h₁ (h₀ φ hφ) ((L.acts p.1 h1 p.2 h2 φ hφ _).2 rfl)).symm
  obtain ⟨K, hK1, hK2, hK3, hK4⟩ := exists_small_subgroups σ X v
  obtain ⟨K', hK1', hK2', hK3', hK4'⟩ := exists_small_subgroups σ W v
  obtain ⟨m, hm⟩ := smooth_of_weak (SB _) (fun k => (K k).prod (K' k))
    (fun a b hab => Subgroup.prod_mono (hK1 hab) (hK1' hab))
    (fun U hU => by
      obtain ⟨U₁, h1, U₂, h2, h⟩ := mem_nhds_prod_iff.1 hU
      obtain ⟨a, ha⟩ := hK2 U₁ h1
      obtain ⟨b, hb⟩ := hK2' U₂ h2
      exact ⟨max a b, fun p hp => h ⟨ha (hK1 (le_max_left a b) hp.1), hb (hK1' (le_max_right a b) hp.2)⟩⟩)
    loc (fun p hp φ hφ => by
      rw [hloc p (hK3 0 hp.1) (hK3' 0 hp.2) φ hφ]
      exact L.pres p.1 (hK3 0 hp.1) p.2 (hK3' 0 hp.2) φ hφ)
    (fun φ hφ => by
      rw [hloc 1 (one_mem_UAt X v) (one_mem_UAt W v) φ hφ]
      exact L.one φ hφ)
    (fun p hp q hq φ hφ => by
      rw [hloc (p * q) (mul_mem_UAt (hK3 0 hp.1) (hK3 0 hq.1)) (mul_mem_UAt (hK3' 0 hp.2) (hK3' 0 hq.2)) φ hφ,
        hloc q (hK3 0 hq.1) (hK3' 0 hq.2) φ hφ,
        hloc p (hK3 0 hp.1) (hK3' 0 hp.2) _ (L.pres q.1 (hK3 0 hq.1) q.2 (hK3' 0 hq.2) φ hφ)]
      exact L.mul p.1 (hK3 0 hp.1) p.2 (hK3' 0 hp.2) q.1 (hK3 0 hq.1) q.2 (hK3' 0 hq.2) φ hφ)
    (fun l φ hφ => hs.cont _ (res_adm v x₀ l) _ (h₀ φ hφ).2) φ hφ
  obtain ⟨U, hU, hUK⟩ := hK4 m
  obtain ⟨U', hU', hUK'⟩ := hK4' m
  refine ⟨U ×ˢ U', prod_mem_nhds hU hU', fun x hx h1 h2 => ?_⟩
  refine (L.acts x.1 h1 x.2 h2 φ hφ φ).2 ?_
  rw [← hloc x h1 h2 φ hφ]
  exact (hm x ⟨hUK _ hx.1 h1, hUK' _ hx.2 h2⟩).symm

end PositivityTheory.ThKF0
end
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

noncomputable section
namespace PositivityTheory.ThKF0

theorem rat_det_ne_zero_of_hasSig {n r s : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  have key : (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA, Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
      Matrix.submatrix_mul Aᵀ M e.symm id id Function.bijective_id]
    simp [Matrix.transpose_submatrix, Matrix.submatrix_map]
  intro h0
  have := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_submatrix_equiv_self] at this
  simp [Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg] at this
  exact pow_ne_zero s (by norm_num : (-1 : ℂ) ≠ 0) this.symm

theorem rat_det_ne_zero_of_map {E : Type} [Field E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (f : E →+* ℂ)
    (h : (J.map f).det ≠ 0) : J.det ≠ 0 := by
  intro h0
  apply h
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

theorem theta_sum_rational_invariance : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP γ hγ γ' hγ' Φ hΦ
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have hX : X.J.det ≠ 0 := rat_det_ne_zero_of_map X.J (B.emb w).1 (rat_det_ne_zero_of_hasSig _ (hP.herm.sig w))
  have hW : W.J.det ≠ 0 := by
    refine rat_det_ne_zero_of_map W.J (B.emb w).1 fun h0 => rat_det_ne_zero_of_hasSig _ (hP.skew.sig w) ?_
    rw [Matrix.det_smul, h0, mul_zero]
  exact darboux_coordinates_rational_exist F E σ hP.base.cm B.ψ hP.base.std n d X.J W.J hP.herm.herm hX hP.skew.skew hW M.co
    hP.good.rat χX χW hP.hX hP.hW om hP.weil γ hγ γ' hγ' Φ hΦ

end PositivityTheory.ThKF0
end
end

section

noncomputable section

namespace PositivityTheory.ThKF0.Grow

open scoped Matrix NNReal ENNReal Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}

theorem dR_mult (hψ : IsStd ψ) (b : V F κ) (Θ : (κ → AF F) → ℂ) (x : κ → AF F) :
    dR ψ (0, b) Θ x = -(2 * Real.pi * Complex.I) * (linForm b fun i => evI F (x i) : ℝ) * Θ x := by
  have e : ∀ t : ℝ, schr ψ (emb (t • ((0, b) : V F κ × V F κ))) Θ x =
      Complex.exp (-(2 * Real.pi * Complex.I) * (linForm b fun i => evI F (x i) : ℝ) * t) * Θ x := fun t => by
    have h0 : (emb ((0, b) : V F κ × V F κ)).1 = 0 := congrArg Prod.fst (emb_zero (F := F) (κ := κ))
    have := phase_line ψ hψ 0 _ x (at_inf b) t
    simp only [evI_inf, Pi.zero_apply, evI_zero, zero_mul, Finset.sum_const_zero, mul_zero, map_zero, add_zero] at this
    rw [emb_smul, schr, Prod.smul_fst, Prod.smul_snd, h0]
    change ψ (x ⬝ᵥ (realAd F t • fun i => inf (b i)) + _ * (_ ⬝ᵥ (realAd F t • fun i => inf (b i)))) * _ = _
    rw [this, smul_zero, add_zero]
    push_cast
    ring_nf
  simp only [dR, e]
  have := ((((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul
    (-(2 * Real.pi * Complex.I) * (linForm b fun i => evI F (x i) : ℝ))).cexp).mul_const (Θ x)
  simpa using this.deriv

theorem word_mult (hψ : IsStd ψ) (b : V F κ) (j : ℕ) (Θ : (κ → AF F) → ℂ) (x : κ → AF F) :
    word ψ (List.replicate j (0, b)) Θ x = (-(2 * Real.pi * Complex.I) * (linForm b fun i => evI F (x i) : ℝ)) ^ j * Θ x := by
  induction j with
  | zero => simp [word]
  | succ j ih =>
    change dR ψ (0, b) (word ψ (List.replicate j (0, b)) Θ) x = _
    rw [dR_mult hψ, ih, pow_succ', mul_assoc (_ * _)]

theorem word_lev (hψ : IsStd ψ) (l : List (V F κ × V F κ)) {Θ : (κ → AF F) → ℂ} (hΘ : Θ ∈ schA F κ) {m : ℕ} (h : Lev m Θ) :
    Lev m (word ψ l Θ) := by
  induction l with
  | nil => exact h
  | cons w l ih => exact (derivOK F κ ψ hψ w _ (word_mem hψ l hΘ)).2.2 m ih

theorem list_bound (hψ : IsStd ψ) {μ : @Measure (κ → AF F) (borel _)} (hμ : IsHaar μ) {Φ : (κ → AF F) → ℂ}
    (hΦ : Φ ∈ schA F κ) (j : ℕ) (S : List (List (V F κ × V F κ))) : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∃ k : ℕ,
      ∀ T s d (y : ℝ≥0), 1 ≤ y → Impl ψ T s → Bd s d y → ∀ b : V F κ, ‖b‖ ≤ 1 →
        (S.map fun l => nsq μ (word ψ l (word ψ (List.replicate j (0, b)) (T Φ)))).sum ≤ C * (y : ℝ≥0∞) ^ k := by
  induction S with
  | nil => exact ⟨0, by simp, 0, by simp⟩
  | cons l S ih =>
    obtain ⟨C, hC, k, h⟩ := ih
    obtain ⟨C', hC', h'⟩ := word_bound hψ hμ (l.length + j) Φ hΦ
    obtain ⟨R, hR1, hR⟩ : ∃ R : ℝ≥0, 1 ≤ R ∧ ∀ w ∈ l, ‖w‖ ≤ R :=
      ⟨1 + (l.map nnnorm).sum, le_self_add, fun w hw => by
        have : ‖w‖₊ ≤ (l.map nnnorm).sum := List.single_le_sum (fun _ _ => zero_le) _ (List.mem_map_of_mem hw)
        exact NNReal.coe_le_coe.2 (this.trans le_add_self)⟩
    refine ⟨C' * (R : ℝ≥0∞) ^ (2 * (l.length + j)) + C, by finiteness, 2 * (l.length + j) + k,
      fun T s d y hy hT hs b hb => ?_⟩
    obtain ⟨l', h1, h2, h3⟩ := hT.word hψ hμ y.2 hs hΦ R (l ++ List.replicate j (0, b)) fun w hw => by
      rcases List.mem_append.1 hw with hw | hw
      · exact hR w hw
      · rw [List.eq_of_mem_replicate hw, Prod.norm_mk, norm_zero]
        exact max_le R.2 (hb.trans hR1)
    have hy' : (1 : ℝ≥0∞) ≤ y := by exact_mod_cast hy
    rw [List.map_cons, List.sum_cons, add_mul]
    refine add_le_add ?_ ((h T s d y hy hT hs b hb).trans (mul_le_mul' le_rfl (pow_le_pow_right₀ hy' le_add_self)))
    have e : word ψ l (word ψ (List.replicate j (0, b)) (T Φ)) = T (word ψ l' Φ) := by
      rw [h3, word, word, word, List.foldr_append]
    rw [e, hT.unit μ hμ _ (word_mem hψ l' hΦ)]
    refine (h' l' (by simpa using h1) (y * R) h2).trans ?_
    rw [ENNReal.coe_mul, mul_pow, mul_comm ((y : ℝ≥0∞) ^ _), ← mul_assoc]
    exact mul_le_mul' le_rfl (pow_le_pow_right₀ hy' le_self_add)

theorem core (hF : FinInv) (hS : Sob) (hψ : IsStd ψ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (j : ℕ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ T s (d : ℕ) (y : ℝ), 1 ≤ d → (d : ℝ) ≤ y → Impl ψ T s → Bd s d y → ∀ b : V F κ, ‖b‖ ≤ 1 →
      ∀ x, ‖word ψ (List.replicate j (0, b)) (T Φ) x‖ ≤ C * y ^ k := by
  obtain ⟨μ, hμ, S, C, k, h⟩ := hS F κ ψ hψ
  obtain ⟨m₀, hm₀, h₀⟩ := hF F κ ψ hψ Φ hΦ
  obtain ⟨C', hC', k', h'⟩ := list_bound hψ hμ hΦ j S
  lift C' to ℝ≥0 using hC'
  refine ⟨1 + C * m₀ ^ k * C', k + k', by positivity, fun T s d y hd hy hT hs b hb x => ?_⟩
  have hy1 : (1 : ℝ) ≤ y := le_trans (by exact_mod_cast hd) hy
  lift y to ℝ≥0 using zero_le_one.trans hy1
  have lev : Lev (m₀ * d) (T Φ) := fun u hu x => by
    have := congrFun (h₀ T s d y hT hs (u, 0) ⟨hu, fun _ => ⟨rfl, fun v => by simp⟩⟩) x
    simpa [schr] using this
  have h1 := (h (m₀ * d) (Nat.mul_pos hm₀ hd) _ (word_mem hψ _ (hT.pres _ hΦ))
    (word_lev hψ (List.replicate j (0, b)) (hT.pres _ hΦ) lev) x).trans
    (mul_le_mul' le_rfl (h' T s d y (by exact_mod_cast hy1) hT hs b hb))
  rw [enorm_eq_nnnorm] at h1
  have h2 : ‖word ψ (List.replicate j (0, b)) (T Φ) x‖ ^ 2 ≤ C * ((m₀ : ℝ) * d) ^ k * (C' * (y : ℝ) ^ k') := by
    exact_mod_cast h1
  have h3 : C * ((m₀ : ℝ) * d) ^ k * (C' * (y : ℝ) ^ k') ≤ C * m₀ ^ k * C' * (y : ℝ) ^ (k + k') := by
    calc _ ≤ C * ((m₀ : ℝ) * y) ^ k * (C' * (y : ℝ) ^ k') := by gcongr
      _ = _ := by ring
  have h4 : (1 : ℝ) ≤ (y : ℝ) ^ (k + k') := one_le_pow₀ hy1
  rw [add_mul]
  nlinarith [sq_nonneg (‖word ψ (List.replicate j (0, b)) (T Φ) x‖ - 1), norm_nonneg (word ψ (List.replicate j (0, b)) (T Φ) x)]

theorem weighted (hF : FinInv) (hS : Sob) (hT : TrBd) (hψ : IsStd ψ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (N : ℕ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ T s (d : ℕ) (y : ℝ), 1 ≤ d → (d : ℝ) ≤ y → Impl ψ T s → Bd s d y →
      ∀ x, ‖T Φ x‖ * (1 + ‖fun i => evI F (x i)‖) ^ N ≤ C * y ^ k := by
  obtain ⟨C₀, k₀, p₀, h₀⟩ := core hF hS hψ hΦ 0
  obtain ⟨C₁, k₁, p₁, h₁⟩ := core hF hS hψ hΦ N
  obtain ⟨c, hc, hb⟩ := hT F κ
  refine ⟨2 ^ (N - 1) * (C₀ + c ^ N * C₁), k₀ + k₁, by positivity, fun T s d y hd hy hI hs x => ?_⟩
  have hy1 : (1 : ℝ) ≤ y := le_trans (by exact_mod_cast hd) hy
  obtain ⟨b, hb1, hb2⟩ := hb fun i => evI F (x i)
  have a₀ : ‖T Φ x‖ ≤ C₀ * y ^ k₀ := h₀ T s d y hd hy hI hs b hb1 x
  have a₁ := h₁ T s d y hd hy hI hs b hb1 x
  rw [word_mult hψ, norm_mul, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs, linForm_apply] at a₁
  have hπ : (1 : ℝ) ≤ ‖-(2 * Real.pi * Complex.I : ℂ)‖ := by
    simp only [norm_neg, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_ofNat, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    linarith [Real.pi_gt_three]
  have a₂ : ‖T Φ x‖ * ‖fun i => evI F (x i)‖ ^ N ≤ c ^ N * (C₁ * y ^ k₁) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left a₁ (by positivity))
    rw [← mul_assoc, ← mul_pow, mul_comm]
    refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hb2.trans ?_) N) (norm_nonneg _)
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (abs_nonneg _) hπ) hc
  have e₀ : y ^ k₀ ≤ y ^ (k₀ + k₁) := pow_le_pow_right₀ hy1 le_self_add
  have e₁ : y ^ k₁ ≤ y ^ (k₀ + k₁) := pow_le_pow_right₀ hy1 le_add_self
  calc _ ≤ ‖T Φ x‖ * (2 ^ (N - 1) * (1 ^ N + ‖fun i => evI F (x i)‖ ^ N)) :=
        mul_le_mul_of_nonneg_left (add_pow_le zero_le_one (norm_nonneg _) N) (norm_nonneg _)
    _ = 2 ^ (N - 1) * (‖T Φ x‖ + ‖T Φ x‖ * ‖fun i => evI F (x i)‖ ^ N) := by ring
    _ ≤ 2 ^ (N - 1) * (C₀ * y ^ (k₀ + k₁) + c ^ N * (C₁ * y ^ (k₀ + k₁))) :=
        mul_le_mul_of_nonneg_left (add_le_add (a₀.trans (mul_le_mul_of_nonneg_left e₀ p₀))
          (a₂.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e₁ p₁) (pow_nonneg hc N)))) (by positivity)
    _ = _ := by ring

open GlobalTheory.LFun GlobalTheory.ThK in
theorem weil_rep_rapid_decay_of_growth (hA : HtBd) (hF : FinInv) (hS : Sob) (hT : TrBd) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ g h (x : Fin n × Fin d → AF F),
    ‖om (g, h) Φ x‖ * (1 + ‖fun i => evI F (x i)‖) ^ N ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ N
  obtain ⟨C, -, hC⟩ := hA F E σ n d X W M
  obtain ⟨C', k, -, h⟩ := weighted hF hS hT hP.base.std hΦ N
  refine ⟨C' * C ^ k, k, fun g g' x => ?_⟩
  obtain ⟨m, h1, h2, h3⟩ := hC g g'
  rw [mul_assoc, ← mul_pow]
  exact h _ _ m _ h1 h2 (impl_sOf hP.weil g g') h3 x

end PositivityTheory.ThKF0.Grow
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace PositivityTheory.ThKF0

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem surjOn_of_pure (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ)) (hi : Function.Surjective ei)
    (hSB : ∀ v, Set.SurjOn (ev v) (SB (κ → Fv F v) : Set _) (SB (κ → Fv F v) : Set _))
    (hstd : ∀ᶠ v in cofinite, ev v (Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) =
      Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (hloc : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
      e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v)) :
    Set.SurjOn e (schA F κ : Set _) (schA F κ : Set _) := by
  change schA F κ ≤ (schA F κ).map e
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, g, hg, rfl⟩
  obtain ⟨m, c, φ, hφSB, hφstd, hgeq⟩ := Span.exists_sum_finprod hg
  have h1 : pureA F (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) g = ∑ k, c k • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ k) := by
    rw [hgeq]
    funext x
    simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    rw [mul_left_comm]
    rfl
  rw [h1]
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
  obtain ⟨f₀, rfl⟩ := hi f
  have hp : ∀ v, ∃ φ₀ ∈ SB (κ → Fv F v), ev v φ₀ = φ k v ∧ (ev v (φ k v) = φ k v → φ₀ = φ k v) := fun v => by
    by_cases h : ev v (φ k v) = φ k v
    · exact ⟨_, hφSB k v, h, fun _ => rfl⟩
    · obtain ⟨φ₀, h0, h1⟩ := hSB v (hφSB k v)
      exact ⟨φ₀, h0, h1, fun h' => absurd h' h⟩
  choose φ₀ h0 h1 h2 using hp
  have hs : ∀ᶠ v in cofinite, φ₀ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
    filter_upwards [hφstd k, hstd] with v e1 e2
    rw [h2 v (by rw [e1, e2]), e1]
  refine ⟨_, GlobalTheory.TensUniq.pure_mem_schA f₀ φ₀ h0 hs, ?_⟩
  rw [hloc f₀ φ₀ h0 hs]
  simp only [h1]

theorem exists_ne_of_surjOn {e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)} (h : Set.SurjOn e (schA F κ : Set _) (schA F κ : Set _)) :
    ∃ Φ ∈ schA F κ, e Φ ≠ 0 := by
  obtain ⟨φ, hφ, h0⟩ := GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin F κ
  obtain ⟨Φ, hΦ, rfl⟩ := h hφ
  exact ⟨Φ, hΦ, fun h1 => h0 (by rw [h1]; rfl)⟩

theorem tw_surj (hA : PositivityTheory.Mix.AdelSt) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} (d d₁ : Darboux B κ) : ∃ e, Tw ψ d d₁ e ∧ Set.SurjOn e (schA F κ : Set _) (schA F κ : Set _) := by
  obtain ⟨e, ei, ev, h1, h2, h3, -, h5, h6⟩ := hA F ψ hψ κ (d.e.symm.trans d₁.e) fun w w' => by
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, ← d₁.form, d.form, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
  have hs := surjOn_of_pure e ei ev ei.surjective (fun v => (h3 v).surjOn) h5 h6
  refine ⟨e, ⟨h1, fun u Φ hΦ => ?_, Span.comp_mem_adm e ei ev (fun v φ hφ => (h3 v).mapsTo hφ) h5 h6, exists_ne_of_surjOn hs⟩, hs⟩
  have := h2 (d.e u) Φ hΦ
  rwa [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at this

theorem twEx (hA : PositivityTheory.Mix.AdelSt) : TwEx := fun _ _ _ _ hψ _ _ _ _ _ _ d d₁ => (tw_surj hA hψ d d₁).imp fun _ h => h.1

theorem tw_bij (hA : PositivityTheory.Mix.AdelSt) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} (d d₁ : Darboux B κ) : ∃ e e', Tw ψ d d₁ e ∧ Tw ψ d₁ d e' ∧
      Set.BijOn e (schA F κ : Set _) (schA F κ : Set _) ∧ (∀ Φ ∈ schA F κ, e' (e Φ) = Φ) ∧ ∀ Φ ∈ schA F κ, e (e' Φ) = Φ := by
  obtain ⟨e, h, hs⟩ := tw_surj hA hψ d d₁
  obtain ⟨e', h', -⟩ := tw_surj hA hψ d₁ d
  obtain ⟨a, ha⟩ := schur hψ d (e' ∘ₗ e) (fun Φ hΦ => h'.maps _ (h.maps Φ hΦ))
    (fun l hl => h.adm _ (h'.adm l hl)) fun w Φ hΦ => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, h.Heisenberg₂ w Φ hΦ, h'.Heisenberg₂ w _ (h.maps Φ hΦ)]
  have a0 : a ≠ 0 := fun a0 => by
    obtain ⟨Φ, hΦ, hne⟩ := h'.ne
    obtain ⟨Ψ, hΨ, rfl⟩ := hs hΦ
    exact hne ((ha Ψ hΨ).trans (by rw [a0, zero_smul]))
  have h1 : ∀ Φ ∈ schA F κ, (a⁻¹ • e') (e Φ) = Φ := fun Φ hΦ => by
    rw [LinearMap.smul_apply, show e' (e Φ) = a • Φ from ha Φ hΦ, smul_smul, inv_mul_cancel₀ a0, one_smul]
  have hscaled : Tw ψ d₁ d (a⁻¹ • e') := by
    constructor
    · exact fun Φ hΦ => Submodule.smul_mem _ _ (h'.maps Φ hΦ)
    · intro w Φ hΦ
      rw [LinearMap.smul_apply, LinearMap.smul_apply, h'.Heisenberg₂ w Φ hΦ, rho_smul]
    · intro l hl g hg
      obtain ⟨T, hT⟩ := h'.adm l hl g hg
      refine ⟨a⁻¹ • T, fun f => ?_⟩
      rw [LinearMap.comp_smul, LinearMap.smul_apply, hT, ContinuousLinearMap.smul_apply]
    ·
      obtain ⟨Φ, hΦ, h0⟩ := h'.ne
      exact ⟨Φ, hΦ, smul_ne_zero (inv_ne_zero a0) h0⟩
  refine ⟨e, _, h, hscaled, ⟨h.maps, fun x hx y hy hxy => ?_, hs⟩, h1, fun Φ hΦ => ?_⟩
  · rw [← h1 x hx, hxy, h1 y hy]
  · obtain ⟨Ψ, hΨ, rfl⟩ := hs hΦ
    rw [h1 Ψ hΨ]

end PositivityTheory.ThKF0

end
end
