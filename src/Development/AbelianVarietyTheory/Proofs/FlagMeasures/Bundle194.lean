module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle165
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle137
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasSignatureComplement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle167
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle097
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle111
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianQuadricDensityExistsPosContinuous
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle173
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle176
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle177
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle121
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Formalism.FormalDegreeBessel.StatementWR

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov

theorem exists_biorth {E : Type} [Field E] {n m : ℕ} {r : ℕ → ℕ}
    (T : ∀ b, Matrix (Fin n) (Fin (r b)) E) (hr : ∀ b, m ≤ b → r b = 0)
    (hn : n = ∑ b ∈ Finset.range m, r b)
    (hs : ∀ y : Fin n → E, ∃ u : ∀ b, Fin (r b) → E, y = ∑ b ∈ Finset.range m, T b *ᵥ u b) :
    ∃ T' : ∀ b, Matrix (Fin (r b)) (Fin n) E, Biorth r m T T' := by
  classical
  let Φ : ((b : Fin m) → Fin (r b) → E) →ₗ[E] (Fin n → E) :=
    ∑ b : Fin m, (T b).mulVecLin ∘ₗ LinearMap.proj b
  have hΦ : ∀ u : ∀ b, Fin (r b) → E, Φ (fun b => u b) = ∑ b ∈ Finset.range m, T b *ᵥ u b := by
    intro u
    rw [← Fin.sum_univ_eq_sum_range (fun b => T b *ᵥ u b)]
    simp [Φ]
  have hsurj : Function.Surjective Φ := fun y => by
    obtain ⟨u, hu⟩ := hs y
    exact ⟨_, (hΦ u).trans hu.symm⟩
  have hinj : Function.Injective Φ := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).2 hsurj
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    rw [hn, Fin.sum_univ_eq_sum_range]
  let e := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  let T' : ∀ b, Matrix (Fin (r b)) (Fin n) E := fun b =>
    if h : b < m then LinearMap.toMatrix'
      ((LinearMap.proj (⟨b, h⟩ : Fin m) : ((b : Fin m) → Fin (r b) → E) →ₗ[E] _) ∘ₗ e.symm.toLinearMap)
    else 0
  have hemp : ∀ b, ¬ b < m → IsEmpty (Fin (r b)) := fun b hb => by
    rw [hr b (by omega)]; infer_instance
  have hT' : ∀ (b : Fin m) y, T' b *ᵥ y = e.symm y b := fun b y => by
    simp only [T', dif_pos b.2]
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  have H1 : ∀ (u : ∀ b, Fin (r b) → E) b, T' b *ᵥ (∑ c ∈ Finset.range m, T c *ᵥ u c) = u b := by
    intro u b
    by_cases hb : b < m
    · rw [hT' ⟨b, hb⟩, ← hΦ]
      exact congrFun (e.symm_apply_apply _) _
    · have := hemp b hb
      exact Subsingleton.elim _ _
  have H2 : ∀ b c v, T' b *ᵥ (T c *ᵥ v) = (Pi.single c v : ∀ b, Fin (r b) → E) b := by
    intro b c v
    rw [← H1 (Pi.single c v) b]
    congr 1
    by_cases hc : c < m
    · rw [Finset.sum_eq_single c (fun d _ hd => by simp [Pi.single_eq_of_ne hd])
        (fun h => absurd (Finset.mem_range.2 hc) h)]
      simp
    · have := hemp c hc
      obtain rfl : v = 0 := Subsingleton.elim _ _
      simp
  refine ⟨T', fun b => ?_, fun b c hbc => ?_, ?_⟩
  · refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    simp only [Matrix.toLin'_apply]
    rw [← Matrix.mulVec_mulVec, H2]; simp
  · refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    simp only [Matrix.toLin'_apply]
    rw [← Matrix.mulVec_mulVec, H2]; simp [Pi.single_eq_of_ne hbc]
  · refine Matrix.toLin'.injective (LinearMap.ext fun y => ?_)
    obtain ⟨u, rfl⟩ := hs y
    simp only [Matrix.toLin'_apply]
    rw [Matrix.sum_mulVec, Matrix.one_mulVec]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Matrix.mulVec_mulVec, H1]

theorem exists_biorth_of_saturated_flag : ∀ (E : Type) [Field E] [NumberField E] (n m : ℕ) (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (r : ℕ → ℕ), Monotone F → F 0 = ⊥ → (∀ b, m ≤ b → F b = F m) → Submodule.IsFullLattice E (F m) → (∀ b, ∀ y ∈ F m, y ∈ Submodule.span E (F b : Set (Fin n → E)) → y ∈ F b) → (∀ b, Formalism.HN.rkK (F (b + 1)) = Formalism.HN.rkK (F b) + r b) → ∃ (T : ∀ b, Matrix (Fin n) (Fin (r b)) E) (T' : ∀ b, Matrix (Fin (r b)) (Fin n) E) (Λ : ∀ b, Submodule (𝓞 E) (Fin (r b) → E)), Biorth r m T T' ∧ (∀ b, Submodule.IsFullLattice E (Λ b)) ∧ ∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0) := by
  intro E _ _ n m F r hmono h0 hm hL hsat hrk
  letI := hL
  have hle : ∀ b, F b ≤ F m := fun b => by
    rcases le_total b m with h | h
    · exact hmono h
    · exact (hm b h).le
  have key : ∀ b, ∃ A : Submodule (𝓞 E) (Fin n → E), A ⊓ F b = ⊥ ∧ A ⊔ F b = F (b + 1) := by
    intro b
    refine exists_compl_of_saturated _ _ (hmono b.le_succ) (Submodule.FG.of_le hL.fg (hle _)) ?_
    intro c y hc hy hcy
    apply hsat _ y (hle _ hy)
    have hc' : (c : E) ≠ 0 := by simpa using hc
    rw [← Submodule.smul_mem_iff _ hc']
    exact Submodule.subset_span hcy
  choose A hA1 hA2 using key
  have hAF : ∀ b, A b ≤ F (b + 1) := fun b => hA2 b ▸ le_sup_left
  have hAr : ∀ b, Formalism.HN.rkK (A b) = r b := fun b => by
    have := AdaptedExists.rkK_add (hA1 b)
    rw [hA2, hrk] at this
    omega
  choose Λ T hΛ hT using fun b => AdaptedExists.exists_model (A b)
    (Submodule.FG.of_le hL.fg ((hAF b).trans (hle _))) (hAr b)
  have hdec : ∀ k, ∀ y ∈ F k, ∃ u : ∀ b, Fin (r b) → E, (∀ b, u b ∈ Λ b) ∧
      y = ∑ b ∈ Finset.range k, T b *ᵥ u b := by
    intro k
    induction k with
    | zero =>
      intro y hy
      rw [h0, Submodule.mem_bot] at hy
      exact ⟨0, fun b => zero_mem _, by simpa using hy⟩
    | succ k ih =>
      intro y hy
      rw [← hA2] at hy
      obtain ⟨a, ha, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
      obtain ⟨v, hv, rfl⟩ := (hT k a).1 ha
      obtain ⟨u, hu, rfl⟩ := ih z hz
      refine ⟨Function.update u k v, fun b => ?_, ?_⟩
      · by_cases hb : b = k
        · subst hb; simpa using hv
        · rw [Function.update_of_ne hb]; exact hu b
      · rw [Finset.sum_range_succ, add_comm, Function.update_self]
        congr 1
        refine Finset.sum_congr rfl fun c hc => ?_
        rw [Function.update_of_ne (Finset.mem_range.1 hc).ne]
  have hr0 : ∀ b, m ≤ b → r b = 0 := fun b hb => by
    have := hrk b
    rw [hm b hb, hm (b + 1) (by omega)] at this
    omega
  have hsum : ∀ k, Formalism.HN.rkK (F k) = ∑ b ∈ Finset.range k, r b := by
    intro k
    induction k with
    | zero => rw [h0]; simp [Formalism.HN.rkK]
    | succ k ih => rw [hrk, ih, Finset.sum_range_succ]
  have hn : n = ∑ b ∈ Finset.range m, r b := by
    rw [← hsum, Formalism.HN.rkK, Submodule.IsFullLattice.span_eq_top (A := E) (M := F m)]
    simp
  obtain ⟨T', hB⟩ := exists_biorth T hr0 hn (fun y => by
    obtain ⟨c, hc, hcy⟩ := AdaptedExists.exists_smul_mem (L := F m) (x := y)
      (by rw [Submodule.IsFullLattice.span_eq_top (A := E) (M := F m)]; trivial)
    obtain ⟨u, -, hu⟩ := hdec m _ hcy
    have hc' : (c : E) ≠ 0 := by simpa using hc
    refine ⟨fun b => (c : E)⁻¹ • u b, ?_⟩
    simp only [Matrix.mulVec_smul]
    rw [← Finset.smul_sum, ← hu, eq_inv_smul_iff₀ hc']
    rfl)
  refine ⟨T, T', Λ, hB, hΛ, fun k y => ⟨fun hy b => ?_, fun hy => ?_⟩⟩
  · obtain ⟨u, hu, rfl⟩ := hdec k y hy
    have h1 : T' b *ᵥ (∑ c ∈ Finset.range k, T c *ᵥ u c) = if b < k then u b else 0 := by
      rw [Matrix.mulVec_sum]
      simp only [Matrix.mulVec_mulVec]
      split_ifs with hb
      · rw [Finset.sum_eq_single b (fun c _ hc => by rw [hB.2.1 b c hc.symm, Matrix.zero_mulVec])
          (fun h => absurd (Finset.mem_range.2 hb) h), hB.1, Matrix.one_mulVec]
      · refine Finset.sum_eq_zero fun c hc => ?_
        rw [hB.2.1 b c (by have := Finset.mem_range.1 hc; omega), Matrix.zero_mulVec]
    rw [h1]
    refine ⟨?_, fun h => if_neg (by omega)⟩
    split_ifs
    · exact hu b
    · exact zero_mem _
  · have h1 : y = ∑ b ∈ Finset.range m, T b *ᵥ (T' b *ᵥ y) := by
      simp only [Matrix.mulVec_mulVec]
      rw [← Matrix.sum_mulVec, hB.2.2, Matrix.one_mulVec]
    rw [h1]
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : k ≤ b
    · rw [(hy b).2 hb, Matrix.mulVec_zero]; exact zero_mem _
    · exact hmono (show b + 1 ≤ k by omega) (hAF b ((hT b _).2 ⟨_, (hy b).1, rfl⟩))

end GlobalTheory.RadCov
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.StabUnfold

theorem ofReal_qEps_eq {n : ℕ} (ε : Fin n → Bool) (y : Fin n → ℂ) :
    ((qEps ε y : ℝ) : ℂ) = star y ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := by
  unfold qEps Formalism.REAL.Jm
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : star (y i) * y i = ((‖y i‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.star_def, Complex.conj_mul']
  split_ifs <;> simp [← h]

theorem frame_inv_form (I : AutInst) (v : InfinitePlace I.F) :
    ((I.P v)⁻¹)ᴴ * Formalism.REAL.Jm (I.ε v) * (I.P v)⁻¹ = I.J.map (I.φ v) := by
  have hd : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have h1 : I.P v * (I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  rw [← I.P_spec v]
  calc ((I.P v)⁻¹)ᴴ * ((I.P v)ᴴ * I.J.map (I.φ v) * I.P v) * (I.P v)⁻¹
      = (I.P v * (I.P v)⁻¹)ᴴ * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1]; simp

theorem isPerp_at_place (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E)
    (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf) (h : IsPerp D s x A xf) (v : InfinitePlace I.F) :
    qEps (I.ε v) (infVec I v x) = sgn ℝ s ∧
      star (infVec I v x) ᵥ* (Formalism.REAL.Jm (I.ε v) * infMat D v A) = 0 ∧
      (infMat D v A)ᴴ * Formalism.REAL.Jm (I.ε v) * infMat D v A = Formalism.REAL.Jm (D.ε v) := by
  obtain ⟨-, h1, h2, h3, -⟩ := h
  have hφ : ∀ a : I.E, I.φ v (star a) = star (I.φ v a) := fun a => I.cm.cmUnram.2.1 _ a
  have hF := frame_inv_form I v
  have hs : star (fun i => I.φ v (x i)) = fun i => I.φ v (star x i) := by
    funext i; simp [hφ]
  refine ⟨?_, ?_, ?_⟩
  · apply Complex.ofReal_injective
    rw [ofReal_qEps_eq, infVec, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hF, hs]
    have := congrArg (I.φ v) h1
    have e : ((sgn ℝ s : ℝ) : ℂ) = I.φ v (sgn I.E s) := by
      unfold sgn; split_ifs <;> simp
    rw [e, ← this]

    simp [dotProduct, mulVec, map_sum]
  · rw [infVec, infMat, star_mulVec, vecMul_vecMul]
    have e : ((I.P v)⁻¹)ᴴ * (Formalism.REAL.Jm (I.ε v) * ((I.P v)⁻¹ * A.map (I.φ v) * D.P v))
        = (I.J * A).map (I.φ v) * D.P v := by
      rw [Matrix.map_mul, ← hF]; simp only [Matrix.mul_assoc]
    rw [e, ← vecMul_vecMul, hs]
    have e2 : (fun i => I.φ v (star x i)) ᵥ* (I.J * A).map (I.φ v) = 0 := by
      funext j
      have := congrArg (I.φ v) (congrFun h2 j)

      simpa [vecMul, dotProduct, map_sum] using this
    rw [e2, zero_vecMul]
  · rw [← D.P_spec v, ← h3, Matrix.map_mul, Matrix.map_mul, ← hF, infMat,
      Matrix.conjTranspose_map (I.φ v) hφ, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]

end GlobalTheory.StabUnfold
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem mem_lamX_mul_right (I : AutInst) (x : Fin I.n → I.E) (g : I.Gf) (k : I.Gf) (hk : k ∈ I.Kset) :
    x ∈ lamX I (1, g * k) ↔ x ∈ lamX I (1, g) := by
  have h := (GlobalTheory.PointLattice.lamX_selfDual I (1, g)).2.2.2.2 (1, k) hk
  rw [Prod.mk_mul_mk, mul_one] at h
  rw [h]

theorem uMat_inv_eq {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : (uMat g)⁻¹ = uMat g⁻¹ :=
  (Matrix.coe_units_inv (g : (Matrix (Fin n) (Fin n) ℂ)ˣ)).symm

theorem gaussAt_meas_inv : ∀ (I : AutInst) (x : Fin I.n → I.E), IsOpen {h : I.Gf | x ∈ lamX I (1, h)} ∧ (∀ v, Measurable fun g : Formalism.REAL.UJ (I.ε v) => ENNReal.ofReal (gauss ((uMat g)⁻¹ *ᵥ infVec I v x))) ∧ (∀ h g : I.Gf, I.fmat h *ᵥ afVec I x = afVec I x → (x ∈ lamX I (1, h * g) ↔ x ∈ lamX I (1, g))) ∧ (∀ g : I.Gf, ∀ k ∈ I.Kset, x ∈ lamX I (1, g * k) ↔ x ∈ lamX I (1, g)) ∧ ∀ v (h g : Formalism.REAL.UJ (I.ε v)), uMat h *ᵥ infVec I v x = infVec I v x → (uMat (h * g))⁻¹ *ᵥ infVec I v x = (uMat g)⁻¹ *ᵥ infVec I v x := by
  intro I x
  refine ⟨?_, fun v => ?_, fun h g hh => ?_, fun g k hk => mem_lamX_mul_right I x g k hk, fun v h g hh => ?_⟩
  · rw [isOpen_iff_mem_nhds]
    intro g hg
    have hK : IsOpen I.Kset := (GlobalTheory.adelicStab_isCompact_isOpen I).2.1
    have hc : Continuous fun h : I.Gf => g⁻¹ * h := continuous_const.mul continuous_id
    have h1 : (1 : I.Gf) ∈ I.Kset := (Ksub I).one_mem
    refine Filter.mem_of_superset ((hK.preimage hc).mem_nhds (by simpa using h1)) fun h hh => ?_
    have := (mem_lamX_mul_right I x g (g⁻¹ * h) hh).2 hg
    rwa [mul_inv_cancel_left] at this
  · refine Continuous.measurable (ENNReal.continuous_ofReal.comp ?_)
    have hc : Continuous fun g : Formalism.REAL.UJ (I.ε v) => (uMat g)⁻¹ := by
      simp only [uMat_inv_eq]
      exact Units.continuous_coe_inv.comp continuous_subtype_val
    have hc2 := hc.matrix_mulVec (continuous_const (y := infVec I v x))
    unfold gauss
    refine Real.continuous_exp.comp (Continuous.neg (continuous_finsetSum _ fun i _ => ?_))
    exact (((continuous_apply i).comp hc2).norm).pow 2
  · rw [(GlobalTheory.PointLattice.lamX_selfDual I (1, h * g)).1, (GlobalTheory.PointLattice.lamX_selfDual I (1, g)).1]
    have h1 : I.fmat g⁻¹ = I.fmat (h * g)⁻¹ * I.fmat h := by
      have : g⁻¹ = (h * g)⁻¹ * h := by simp
      rw [this]; rfl
    change I.fmat (h * g)⁻¹ *ᵥ afVec I x ∈ I.Lf ↔ I.fmat g⁻¹ *ᵥ afVec I x ∈ I.Lf
    rw [h1, ← Matrix.mulVec_mulVec, hh]
  · rw [uMat_inv_eq, uMat_inv_eq]
    have h1 : uMat g⁻¹ = uMat (h * g)⁻¹ * uMat h := by
      have : g⁻¹ = (h * g)⁻¹ * h := by simp
      rw [this]; rfl
    rw [h1, ← Matrix.mulVec_mulVec, hh]

end GlobalTheory.StabUnfold
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GaussMean.ProdDensity

open GlobalTheory.GaussMean.Density Filter Topology

theorem integral_lt_eq {n : ℕ} (ε : Fin n → Bool) {a : ℝ} (ha : a ≠ 0) :
    ∫ y in {y : Fin n → ℂ | qEps ε y < a}, gauss y = cdf ε a := by
  apply le_antisymm
  · exact setIntegral_mono_set (integrable_gauss n).integrableOn
      (Filter.Eventually.of_forall fun y => (gauss_pos y).le)
      (Filter.Eventually.of_forall fun y (hy : qEps ε y < a) => hy.le)
  · have hc : Tendsto (cdf ε) (𝓝[<] a) (𝓝 (cdf ε a)) :=
      (differentiableAt_cdf ε ha).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hc ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : t < a)
    exact setIntegral_mono_set (integrable_gauss n).integrableOn
      (Filter.Eventually.of_forall fun y => (gauss_pos y).le)
      (Filter.Eventually.of_forall fun y (hy : qEps ε y ≤ t) => lt_of_le_of_lt hy ht)

theorem integral_Icc_eq {n : ℕ} (ε : Fin n → Bool) {a c : ℝ} (ha : a ≠ 0) (hac : a ≤ c) :
    ∫ y in qEps ε ⁻¹' Set.Icc a c, gauss y = cdf ε c - cdf ε a := by
  have hm : MeasurableSet {y : Fin n → ℂ | qEps ε y < a} :=
    measurableSet_lt (continuous_qEps ε).measurable measurable_const
  have h := setIntegral_sdiff hm ((integrable_gauss n).integrableOn (s := {y | qEps ε y ≤ c}))
    (fun y (hy : qEps ε y < a) => show qEps ε y ≤ c by linarith)
  rw [integral_lt_eq ε ha] at h
  rw [cdf, ← h]
  congr 2
  ext y
  simp [and_comm]

theorem integral_box {ι : Type} [Fintype ι] {n : ℕ} (ε : ι → Fin n → Bool) (a c : ι → ℝ) (ha : ∀ v, a v ≠ 0)
    (hac : a ≤ c) :
    ∫ y in (fun (y : ι → Fin n → ℂ) (v : ι) => qEps (ε v) (y v)) ⁻¹' Set.Icc a c, ∏ v, gauss (y v) =
      ∏ v, (cdf (ε v) (c v) - cdf (ε v) (a v)) := by
  have hm : MeasurableSet ((fun (y : ι → Fin n → ℂ) (v : ι) => qEps (ε v) (y v)) ⁻¹' Set.Icc a c) :=
    measurableSet_Icc.preimage
      (continuous_pi fun v => (continuous_qEps (ε v)).comp (continuous_apply v)).measurable
  rw [← integral_indicator hm, ← Finset.prod_congr rfl fun v _ => integral_Icc_eq (ε v) (ha v) (hac v),
    ← Finset.prod_congr rfl fun v _ => integral_indicator
      (measurableSet_Icc.preimage (continuous_qEps (ε v)).measurable),
    ← integral_fintype_prod_volume_eq_prod]
  congr 1
  funext y
  by_cases hy : y ∈ (fun (y : ι → Fin n → ℂ) (v : ι) => qEps (ε v) (y v)) ⁻¹' Set.Icc a c
  · rw [Set.indicator_of_mem hy]
    exact Finset.prod_congr rfl fun v _ => (Set.indicator_of_mem (s := qEps (ε v) ⁻¹' Set.Icc (a v) (c v))
      ⟨hy.1 v, hy.2 v⟩ _).symm
  · rw [Set.indicator_of_notMem hy]
    obtain ⟨v, hv⟩ : ∃ v, y v ∉ qEps (ε v) ⁻¹' Set.Icc (a v) (c v) := by
      by_contra! h
      exact hy ⟨fun v => (h v).1, fun v => (h v).2⟩
    exact (Finset.prod_eq_zero (Finset.mem_univ v) (Set.indicator_of_notMem hv _)).symm

theorem tendsto_mean_cube {ι : Type} [Fintype ι] {G : (ι → ℝ) → ℂ} (hG : Continuous G) (b : ι → ℝ) :
    Tendsto (fun r : ℝ => (r ^ Fintype.card ι)⁻¹ • ∫ x in Set.Icc b (fun v => b v + r), G x) (𝓝[>] 0)
      (𝓝 (G b)) := by
  rw [Metric.tendsto_nhds]
  intro e he
  obtain ⟨d, hd, hδ⟩ := Metric.continuousAt_iff.1 (hG.continuousAt (x := b)) (e / 2) (half_pos he)
  filter_upwards [Ioo_mem_nhdsGT hd] with r hr
  have hr0 := hr.1
  have hk : 0 < r ^ Fintype.card ι := pow_pos hr0 _
  have hvol : volume.real (Set.Icc b (fun v => b v + r)) = r ^ Fintype.card ι := by
    rw [Measure.real, Real.volume_Icc_pi_toReal (fun v => by simp [hr0.le])]
    simp
  have hfin : volume (Set.Icc b (fun v => b v + r)) < ⊤ := isCompact_Icc.measure_lt_top
  have h1 : ∫ x in Set.Icc b (fun v => b v + r), (G x - G b) =
      (∫ x in Set.Icc b (fun v => b v + r), G x) - (r ^ Fintype.card ι) • G b := by
    rw [integral_sub hG.continuousOn.integrableOn_Icc continuousOn_const.integrableOn_Icc,
      setIntegral_const, hvol]
  have h2 : ‖∫ x in Set.Icc b (fun v => b v + r), (G x - G b)‖ ≤ e / 2 * r ^ Fintype.card ι := by
    rw [← hvol]
    refine norm_setIntegral_le_of_norm_le_const hfin fun x hx => ?_
    rw [← dist_eq_norm]
    refine (hδ (lt_of_le_of_lt ?_ hr.2)).le
    rw [dist_pi_le_iff hr0.le]
    intro v
    have h3 := hx.1 v
    have h4 := hx.2 v
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith
  have h3 : (r ^ Fintype.card ι)⁻¹ • (∫ x in Set.Icc b (fun v => b v + r), G x) - G b =
      (r ^ Fintype.card ι)⁻¹ • ∫ x in Set.Icc b (fun v => b v + r), (G x - G b) := by
    rw [h1, smul_sub, smul_smul, inv_mul_cancel₀ hk.ne', one_smul]
  rw [dist_eq_norm, h3, norm_smul, Real.norm_of_nonneg (inv_pos.2 hk).le, inv_mul_lt_iff₀ hk]
  nlinarith

theorem density_eq_prod (ι : Type) [Fintype ι] (n : ℕ) (ε : ι → Fin n → Bool) (G : (ι → ℝ) → ℂ)
    (hG : Continuous G)
    (h : ∀ S : Set (ι → ℝ), IsCompact S →
      ∫ y in (fun (y : ι → Fin n → ℂ) (v : ι) => qEps (ε v) (y v)) ⁻¹' S, ((∏ v, gauss (y v) : ℝ) : ℂ) =
        ∫ b in S, G b)
    (b : ι → ℝ) (hb : ∀ v, b v ≠ 0) : G b = ((∏ v, gaussDens (ε v) (b v) : ℝ) : ℂ) := by
  have h1 : Tendsto (fun r : ℝ => ∏ v, r⁻¹ • (cdf (ε v) (b v + r) - cdf (ε v) (b v))) (𝓝[>] 0)
      (𝓝 (∏ v, gaussDens (ε v) (b v))) :=
    tendsto_finsetProd _ fun v _ =>
      (differentiableAt_cdf (ε v) (hb v)).hasDerivAt.tendsto_slope_zero_right
  have h2 := (Complex.continuous_ofReal.tendsto _).comp h1
  refine tendsto_nhds_unique (tendsto_mean_cube hG b) (h2.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  rw [← h _ isCompact_Icc, integral_complex_ofReal, integral_box ε b _ hb (fun v => by simp [hr.le])]
  simp [Finset.prod_mul_distrib]

end GlobalTheory.GaussMean.ProdDensity
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

theorem _root_.GlobalTheory.T.realPlaces_match_isomorphic_CM_instances : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E), (∀ y, e (star y) = star (e y)) → ∃ (β : InfinitePlace I.F ≃ InfinitePlace I.E) (σ : InfinitePlace I.F ≃ InfinitePlace I₀.F) (τ τ₀ : InfinitePlace I.F → (ℂ →+* ℂ)), (∀ v, τ v = RingHom.id ℂ ∨ τ v = starRingEnd ℂ) ∧ (∀ v, τ₀ v = RingHom.id ℂ ∨ τ₀ v = starRingEnd ℂ) ∧ (∀ v y, I.φ v y = τ v ((β v).embedding y)) ∧ ∀ v y, I.φ v (e y) = τ₀ v (I₀.φ (σ v) y) := by
  first | exact @GlobalTheory.LeviIso.Places.places_match | exact GlobalTheory.LeviIso.Places.places_match | (intros; apply GlobalTheory.LeviIso.Places.places_match <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

theorem _root_.GlobalTheory.T.exists_hermitian_sqrt_in_signedUnitaryGroup : ∀ (n : ℕ) (ε : Fin n → Bool) (C : Matrix (Fin n) (Fin n) ℂ), C.det ≠ 0 → (Cᴴ * C) * Formalism.REAL.Jm ε * (Cᴴ * C) = Formalism.REAL.Jm ε → ∃ s : Formalism.REAL.UJ ε, (uMat s)ᴴ = uMat s ∧ uMat s * uMat s = Cᴴ * C := by
  first | exact @GlobalTheory.LeviIso.exists_hermitian_sqrt_mem_UJ | exact GlobalTheory.LeviIso.exists_hermitian_sqrt_mem_UJ | (intros; apply GlobalTheory.LeviIso.exists_hermitian_sqrt_mem_UJ <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.rightConvolution_operator_ae_eq_integral_adelic : ∀ (B : RowsAut) (φ : B.I.GA → ℂ) (T : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund), B.I.IsRConv B.μf B.fund B.R φ T → ∀ y : B.I.L2 B.μf B.fund, (∀ᵐ x ∂((B.I.muA B.μf).restrict B.fund), Integrable (fun g => φ g * B.I.ext y (x * g)) (B.I.muA B.μf)) ∧ (T y : B.I.GA → ℂ) =ᵐ[(B.I.muA B.μf).restrict B.fund] fun x => ∫ g, φ g * B.I.ext y (x * g) ∂(B.I.muA B.μf) := by
  first | exact @GlobalTheory.ConvKernel.rconv_eq_integral | exact GlobalTheory.ConvKernel.rconv_eq_integral | (intros; apply GlobalTheory.ConvKernel.rconv_eq_integral <;> assumption)
end

section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped ENNReal

theorem _root_.GlobalTheory.T.rootMeasure_transport_doubleCoset : ∀ (D : D7) (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (p : Point ℂ (D.R.rS + 1)) (g a a' : MatKR D.R.k D.R.rS) (μ : Measure (Mt D.R.k D.R.rS)), inWb D.R.k D.R.rS z → inWb D.R.k D.R.rS z' → 0 < Tz D.R.k D.R.rS z → 0 < Tz D.R.k D.R.rS z' → g ∈ UH (Hpk D.R.k D.R.rS) → a ∈ Sset D.R.k D.R.rS z → a' ∈ Sset D.R.k D.R.rS z' → IsRootMeasR D z z' p g μ → IsRootMeasR D z z' p (a * g * a'⁻¹) (μ.map fun x => fun i j => (a' * Matrix.of x * a'⁻¹) i j) := by
  first | exact @GlobalTheory.Amp.RootMove.rootMeas_move | exact GlobalTheory.Amp.RootMove.rootMeas_move | (intros; apply GlobalTheory.Amp.RootMove.rootMeas_move <;> assumption)
end
