module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToZModPowKummerEqIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle037
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle339
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem tame_scale : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c c' : Coef l) (y : G ℚ Ω → Fin 2 → Qbar l) (n : ℕ) (w : Pl) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (a : Qbar l), c.O ≤ c'.O → a ∈ c'.O → Tame c W y n w ψ → Tame c' W (fun s => a • y s) n w ψ := by
  intro l _ Ω _ _ _ W c c' y n w ψ a hle ha hT
  obtain ⟨Y, P, u, b, hY, hYO, hP, hu, hb, hco, hsum, hfr, htame⟩ := hT
  refine ⟨fun s x => a • Y s x, P, u, a • b, ?_, ?_, hle hP, hu, ?_, ?_, ?_, hfr, ?_⟩
  · exact hY.const_smul a
  · intro s x i
    simpa using c'.O.mul_mem ha (hle (hYO s x i))
  · intro i
    simpa using c'.O.mul_mem ha (hle (hb i))
  · intro s t x
    simp only [hco s t x, smul_add, Matrix.mulVec_smul]
  · intro s
    rw [finsum_eq_sum_of_fintype] at *
    rw [← Finset.smul_sum, ← finsum_eq_sum_of_fintype, hsum s]
    simp only [smul_add, smul_sub, Matrix.mulVec_smul, smul_comm a P]
  · intro q hq hl
    obtain ⟨B, hB, t, htO, ht⟩ := htame q hq hl
    refine ⟨B, hB, fun x => a • t x, ?_, ?_⟩
    · intro x i
      simpa using c'.O.mul_mem ha (hle (htO x i))
    · intro s hs x
      simp only [ht s hs x, smul_sub, Matrix.mulVec_smul]

end GlobalTheory.Ord2
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem galoisRepRankTwoTateDual_eq_one_of_mem_ker_unramified : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ a ∈ (toGS Ω (S : Set Pl)).ker, dual1 W a = 1 := by
  intro l _ Ω _ _ _ e S A W hW a ha
  set T : Subgroup (G ℚ Ω) := W.ker ⊓ (cycZ ℚ Ω l).ker with hT
  have hTc : IsClosed (T : Set (G ℚ Ω)) := by
    have h1 : IsClosed (W.ker : Set (G ℚ Ω)) := isClosed_singleton.preimage hW.cont
    have h2 : IsClosed ((cycZ ℚ Ω l).ker : Set (G ℚ Ω)) := isClosed_singleton.preimage (continuous_cycZ ℚ Ω l)
    exact h1.inter h2
  have hNS : NS Ω (S : Set Pl) ≤ T := by
    refine Subgroup.topologicalClosure_minimal _ ?_ hTc
    apply Subgroup.normalClosure_le_normal
    intro τ hτ
    simp only [Set.mem_iUnion] at hτ
    obtain ⟨v, hv, B, hB, hτ⟩ := hτ
    refine ⟨hW.unr v hv B hB hτ, ?_⟩
    have hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hv (hW.above v h)
    exact GlobalTheory.WeilDeligne.cycZ_of_mem_Ine hB hl hτ
  have haT : a ∈ T := hNS ((QuotientGroup.eq_one_iff _).mp ha)
  have hWa : W a = 1 := haT.1
  have hca : cycZ ℚ Ω l a = 1 := haT.2
  have hcb : cycBar ℚ Ω l a = 1 := by simp [cycBar, hca]
  have hdt : dt W a = 1 := by simp [dt, hWa]
  apply Units.ext
  rw [dual1, tw_val]
  simp [hcb, hdt, hWa]

end GlobalTheory.Ord2
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.GwCount

theorem exists_bound_of_mem_span {K E ι : Type} [NormedField K] [AddCommGroup E] [Module K E] (φ : ι → E →ₗ[K] K)
    (f : E →ₗ[K] K) (hf : f ∈ Submodule.span K (Set.range φ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : E) (r : ℝ), 0 ≤ r → (∀ j, ‖φ j p‖ ≤ r) → ‖f p‖ ≤ C * r := by
  first
  | exact @_root_.GlobalTheory.NormBoundOfSpan.norm_le_of_mem_span
  | exact _root_.GlobalTheory.NormBoundOfSpan.norm_le_of_mem_span
  | (apply _root_.GlobalTheory.NormBoundOfSpan.norm_le_of_mem_span <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormBoundOfSpan.norm_le_of_mem_span <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormBoundOfSpan.norm_le_of_mem_span <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormBoundOfSpan.norm_le_of_mem_span ..)

theorem exists_bound_multiplier {K Γ : Type} [NormedField K] (M : Γ → Matrix (Fin 2) (Fin 2) K) (Y : Γ → Fin 2 → K)
    (hY : ¬ ∃ x : Fin 2 → K, ∀ s, Y s = M s *ᵥ x - x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : K) (x : Fin 2 → K) (r : ℝ), 0 ≤ r →
      (∀ s i, ‖(a • Y s) i - (M s *ᵥ x - x) i‖ ≤ r) → ‖a‖ ≤ C * r := by
  let φ : Γ × Fin 2 → (K × (Fin 2 → K)) →ₗ[K] K := fun j =>
    (LinearMap.proj j.2).comp (((LinearMap.fst K K (Fin 2 → K)).smulRight (Y j.1)) -
      ((Matrix.toLin' (M j.1) - LinearMap.id).comp (LinearMap.snd K K (Fin 2 → K))))
  have hφ : ∀ s i a x, φ (s, i) (a, x) = (a • Y s) i - (M s *ᵥ x - x) i := by
    intro s i a x
    simp only [φ, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smulRight_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, LinearMap.id_apply, Matrix.toLin'_apply, LinearMap.proj_apply, Pi.sub_apply]
  have hker : ⨅ j, LinearMap.ker (φ j) ≤ LinearMap.ker (LinearMap.fst K K (Fin 2 → K)) := by
    rintro ⟨a, x⟩ h
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at h
    simp only [LinearMap.mem_ker, LinearMap.fst_apply]
    by_contra ha
    refine hY ⟨a⁻¹ • x, fun s => ?_⟩
    have h1 : a • Y s = M s *ᵥ x - x := by
      funext i
      have := h (s, i)
      rw [hφ] at this
      exact sub_eq_zero.1 this
    rw [Matrix.mulVec_smul, ← smul_sub, ← h1, smul_smul, inv_mul_cancel₀ ha, one_smul]
  obtain ⟨C, hC, h⟩ := exists_bound_of_mem_span φ _ (FiniteDimensional.mem_span_of_iInf_ker_le_ker hker)
  exact ⟨C, hC, fun a x r hr hb => h (a, x) r hr fun j => by rw [show j = (j.1, j.2) from rfl, hφ]; exact hb _ _⟩

theorem closed_multiplier : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (Y : G ℚ Ω → Fin 2 → Qbar l), (∀ s i j, mat W s i j ∈ c.O) → Y ∈ Z1 (Loc.colRep W) → (∀ s i, Y s i ∈ c.O) → Y ∉ ReciprocityTheory.Gal.B1 (Loc.colRep W) → ∃ k0 : ℕ, ∀ (n : ℕ) (a : Qbar l), a ∈ c.O → Cob1 c n W ⊤ (fun s => a • Y s) → Cg n (a * ((l : ℕ) : Qbar l) ^ k0) 0 := by
  intro l hl Ω _ _ _ W c Y _ _ _ hY
  obtain ⟨C, hC, h⟩ := exists_bound_multiplier (mat W) Y (by
    rintro ⟨x, hx⟩
    refine hY ⟨x, ?_⟩
    funext s
    rw [hx s]
    simp [ReciprocityTheory.Gal.d0, Loc.colRep, Matrix.toLin'_apply])
  have hlt : ‖((l : ℕ) : Qbar l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']
    exact Padic.norm_p_lt_one
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < (C + 1)⁻¹ by positivity) hlt
  refine ⟨k, fun n a _ ⟨x, _, hx⟩ => ?_⟩
  have h1 := h a x _ (norm_nonneg _) fun s i => hx s (Subgroup.mem_top s) i
  unfold Cg
  rw [sub_zero, norm_mul, norm_pow _ k]
  have h2 : C * ‖((l : ℕ) : Qbar l)‖ ^ k ≤ 1 := by
    calc C * ‖((l : ℕ) : Qbar l)‖ ^ k ≤ (C + 1) * (C + 1)⁻¹ :=
          mul_le_mul (by linarith) hk.le (by positivity) (by positivity)
      _ = 1 := mul_inv_cancel₀ (by positivity)
  calc ‖a‖ * ‖((l : ℕ) : Qbar l)‖ ^ k ≤ C * ‖((l : ℕ) : Qbar l) ^ n‖ * ‖((l : ℕ) : Qbar l)‖ ^ k :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = ‖((l : ℕ) : Qbar l) ^ n‖ * (C * ‖((l : ℕ) : Qbar l)‖ ^ k) := by ring
    _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _) h2

end GlobalTheory.Ord2.GwCount
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2

private theorem commHt_norm_le_one_of_isIntegral (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.AlgebraMapNormLeOne.norm_le_one_of_isIntegral
  | exact _root_.GlobalTheory.AlgebraMapNormLeOne.norm_le_one_of_isIntegral
  | (apply _root_.GlobalTheory.AlgebraMapNormLeOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.AlgebraMapNormLeOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AlgebraMapNormLeOne.norm_le_one_of_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AlgebraMapNormLeOne.norm_le_one_of_isIntegral ..)

theorem commHt_norm_le_one_of_mem {l : ℕ} [Fact l.Prime] (c : Coef l) (x : Qbar l) (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  commHt_norm_le_one_of_isIntegral l x ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem commHt_cocycle_mulVec (V : R2 Ω l) {x : G ℚ Ω → Fin 2 → Qbar l} (hx : x ∈ Z1 (Loc.colRep V)) (s t : G ℚ Ω) :
    x (s * t) = x s + mat V s *ᵥ x t := by
  have := hx.2 s t
  simpa [Loc.colRep, Matrix.toLin'_apply] using this

theorem commHt_cocycle_commutator (V : R2 Ω l) {x : G ℚ Ω → Fin 2 → Qbar l} (hx : x ∈ Z1 (Loc.colRep V)) (a b : G ℚ Ω)
    (ha : V a = 1) (hb : V b = 1) : x (a * b * a⁻¹ * b⁻¹) = 0 := by
  have hm := commHt_cocycle_mulVec V hx
  have m1 : ∀ s, V s = 1 → mat V s = 1 := fun s hs => by simp [mat, hs]
  have h1 : x 1 = 0 := by
    have := hm 1 1
    rw [m1 1 (map_one V), Matrix.one_mulVec, mul_one] at this
    simpa using this
  have hinv : ∀ s, V s = 1 → x s⁻¹ = - x s := by
    intro s hs
    have := hm s s⁻¹
    rw [mul_inv_cancel, h1, m1 s hs, Matrix.one_mulVec] at this
    exact (neg_eq_of_add_eq_zero_right this.symm).symm
  have hai : V a⁻¹ = 1 := by rw [map_inv, ha, inv_one]
  have hab : V (a * b) = 1 := by rw [map_mul, ha, hb, one_mul]
  have haba : V (a * b * a⁻¹) = 1 := by rw [map_mul, hab, hai, one_mul]
  rw [hm, m1 _ haba, Matrix.one_mulVec, hm, m1 _ hab, Matrix.one_mulVec, hm, m1 _ ha, Matrix.one_mulVec,
    hinv a ha, hinv b hb]
  abel

theorem commHt_dual1_eq_one {W : R2 Ω l} {s : G ℚ Ω} (hs : s ∈ N0g W) : dual1 W s = 1 := by
  obtain ⟨hc, hw⟩ := Subgroup.mem_inf.1 hs
  rw [MonoidHom.mem_ker] at hc hw
  have hd : dt W s = 1 := by simp [dt, hw]
  simp [dual1, _root_.UpperTheory.V.Af.tw, hw, hc, hd]

theorem ht_commutator : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (c : Coef l) (W : R2 Ω l) (y z : G ℚ Ω → Fin 2 → Qbar l) (u : G ℚ Ω → Qbar l), (∀ s i j, mat W s i j ∈ c.O) → y ∈ Z1 (Loc.colRep W) → z ∈ Z1 (Loc.colRep (dual1 W)) → (∀ s t, Cg n (cup W y z s t) (eps l s * u t - u (s * t) + u s)) → ∀ φ ∈ H0g W, ∀ g ∈ N0g W, ∀ h ∈ N0g W, Cg n (ht W y z u (φ * (g * h * g⁻¹ * h⁻¹)) - ht W y z u φ) ((mat W φ - 1).det * (om (y h) (z g) - om (y g) (z h))) := by
  intro l _ Ω _ _ _ n c W y z u hO hy hz hu φ hφ g hg h hh
  have hk : g * h * g⁻¹ * h⁻¹ ∈ N0g W :=
    mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  set k := g * h * g⁻¹ * h⁻¹ with hkdef
  have kerW : ∀ s ∈ N0g W, W s = 1 := fun s hs => (Subgroup.mem_inf.1 hs).2
  have epsN : ∀ s ∈ N0g W, eps l s = 1 := fun s hs => by
    have := (Subgroup.mem_inf.1 hs).1
    rw [MonoidHom.mem_ker] at this
    simp [eps, this]
  have epsφ : eps l φ = 1 := by
    have := (Subgroup.mem_inf.1 hφ).1
    rw [MonoidHom.mem_ker] at this
    simp [eps, this]
  have matN : ∀ s ∈ N0g W, mat W s = 1 := fun s hs => by simp [mat, kerW s hs]
  have matD : ∀ s ∈ N0g W, mat (dual1 W) s = 1 := fun s hs => by simp [mat, commHt_dual1_eq_one hs]
  have hyk : y k = 0 := commHt_cocycle_commutator W hy g h (kerW g hg) (kerW h hh)
  have hzk : z k = 0 := commHt_cocycle_commutator (dual1 W) hz g h (commHt_dual1_eq_one hg) (commHt_dual1_eq_one hh)
  have hmat : mat W (φ * k) = mat W φ := by simp [mat, map_mul, kerW k hk]
  have hyφ : y (φ * k) = y φ := by rw [commHt_cocycle_mulVec W hy, hyk, Matrix.mulVec_zero, add_zero]
  have hzφ : z (φ * k) = z φ := by rw [commHt_cocycle_mulVec (dual1 W) hz, hzk, Matrix.mulVec_zero, add_zero]
  have hdiff : ht W y z u (φ * k) - ht W y z u φ = (mat W φ - 1).det * (u (φ * k) - u φ) := by
    simp only [ht, hmat, hyφ, hzφ]; ring
  have hkhg : k * (h * g) = g * h := by simp only [hkdef]; group

  set E : G ℚ Ω → G ℚ Ω → Qbar l := fun s t => cup W y z s t - (eps l s * u t - u (s * t) + u s) with hEdef
  have hE : ∀ s t, ‖E s t‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := fun s t => hu s t
  have c1 : cup W y z φ k = 0 := by simp [cup, hzk, om]
  have c2 : cup W y z k (h * g) = 0 := by simp [cup, hyk, om]
  have c3 : cup W y z g h = om (y g) (z h) := by simp [cup, matD g hg]
  have c4 : cup W y z h g = om (y h) (z g) := by simp [cup, matD h hh]
  have key : (u (φ * k) - u φ) - (om (y h) (z g) - om (y g) (z h)) =
      E φ k + E g h - E h g - E k (h * g) := by
    simp only [hEdef, c1, c2, c3, c4, hkhg, epsφ, epsN k hk, epsN g hg, epsN h hh]
    ring
  have hdet : ‖(mat W φ - 1).det‖ ≤ 1 := by
    apply commHt_norm_le_one_of_mem c
    rw [Matrix.det_fin_two]
    have he : ∀ i j, (mat W φ - 1) i j ∈ c.O := by
      intro i j
      rw [Matrix.sub_apply, Matrix.one_apply]
      split_ifs
      · exact sub_mem (hO φ i j) (one_mem _)
      · exact sub_mem (hO φ i j) (zero_mem _)
    exact sub_mem (mul_mem (he 0 0) (he 1 1)) (mul_mem (he 0 1) (he 1 0))
  have hsum : ‖E φ k + E g h - E h g - E k (h * g)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := by
    have hs : ∀ a b : Qbar l, ‖a‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ → ‖b‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ →
        ‖a - b‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := fun a b ha hb => by
      rw [sub_eq_add_neg]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (by rwa [norm_neg]))
    exact hs _ _ (hs _ _ ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hE _ _) (hE _ _))) (hE _ _)) (hE _ _)
  unfold Cg
  rw [hdiff, ← mul_sub, norm_mul, key]
  calc ‖(mat W φ - 1).det‖ * ‖E φ k + E g h - E h g - E k (h * g)‖ ≤ 1 * ‖((l : ℕ) : Qbar l) ^ n‖ :=
        mul_le_mul hdet hsum (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

end GlobalTheory.Ord2

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.CupCob

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_int (x : Qbar l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt
  | exact _root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt
  | (apply _root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt <;> assumption)
  | (intros; apply _root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt ..)

theorem nsub_le_max (x y : Qbar l) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]; exact IsUltrametricDist.norm_add_le_max _ _

theorem norm_le_one_of_mem (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  norm_le_one_of_int x ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)

theorem eps_mem (c : Coef l) (s : G ℚ Ω) : eps l s ∈ c.O := by
  have : eps l s = algebraMap ℤ_[l] (Qbar l) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) := by
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]; rfl
  rw [this]; exact c.O.algebraMap_mem _

theorem eps_cont : Continuous fun s : G ℚ Ω => eps l s :=
  (continuous_algebraMap ℚ_[l] (Qbar l)).comp
    (continuous_subtype_val.comp ((Units.continuous_val (M := ℤ_[l])).comp (continuous_cycZ ℚ Ω l)))

theorem det_sq (W : R2 Ω l) (h : dt W ^ 2 = 1) (s : G ℚ Ω) : (mat W s).det ^ 2 = 1 := by
  have := congrArg (fun f => ((f s : (Qbar l)ˣ) : Qbar l)) h
  simpa [dt] using this

theorem mat_dual1 (W : R2 Ω l) (h : dt W ^ 2 = 1) (s : G ℚ Ω) :
    mat (dual1 W) s = (eps l s * (mat W s).det) • mat W s := by
  have hinv : (dt W s)⁻¹ = dt W s := by
    have h2 := congrArg (fun f => f s) h
    simp only [pow_two, MonoidHom.mul_apply, MonoidHom.one_apply] at h2
    exact inv_eq_of_mul_eq_one_left h2
  simp only [mat, dual1, tw_val, MonoidHom.mul_apply, MonoidHom.inv_apply, hinv, Units.val_mul]
  simp [dt, eps]

theorem om_smul_right (k : Qbar l) (p q : Fin 2 → Qbar l) : om p (k • q) = k * om p q := by
  simp only [om, Pi.smul_apply, smul_eq_mul]; ring

theorem om_mulVec (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (p q : Fin 2 → Qbar l) :
    om (M *ᵥ p) (M *ᵥ q) = M.det * om p q := by
  simp only [om, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]; ring

theorem om_key (W : R2 Ω l) (h : dt W ^ 2 = 1) (s : G ℚ Ω) (p q : Fin 2 → Qbar l) :
    om (mat W s *ᵥ p) (mat (dual1 W) s *ᵥ q) = eps l s * om p q := by
  rw [mat_dual1 W h, Matrix.smul_mulVec, om_smul_right, om_mulVec]
  linear_combination (eps l s * om p q) * det_sq W h s

theorem mat_dual1_mul (W : R2 Ω l) (s t : G ℚ Ω) (x : Fin 2 → Qbar l) :
    mat (dual1 W) (s * t) *ᵥ x = mat (dual1 W) s *ᵥ (mat (dual1 W) t *ᵥ x) := by
  simp only [mat, map_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem mulVec_mem (c : Coef l) (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (x : Fin 2 → Qbar l)
    (hM : ∀ i j, M i j ∈ c.O) (hx : ∀ i, x i ∈ c.O) (i : Fin 2) : (M *ᵥ x) i ∈ c.O := by
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact add_mem (mul_mem (hM _ _) (hx _)) (mul_mem (hM _ _) (hx _))

theorem om_mem (c : Coef l) (p q : Fin 2 → Qbar l) (hp : ∀ i, p i ∈ c.O) (hq : ∀ i, q i ∈ c.O) : om p q ∈ c.O :=
  sub_mem (mul_mem (hp _) (hq _)) (mul_mem (hp _) (hq _))

theorem dual_representation_integral (c : Coef l) (W : R2 Ω l) (h : dt W ^ 2 = 1) (hint : ∀ s i j, mat W s i j ∈ c.O) (s : G ℚ Ω)
    (i j : Fin 2) : mat (dual1 W) s i j ∈ c.O := by
  rw [mat_dual1 W h, Matrix.smul_apply, smul_eq_mul]
  refine mul_mem (mul_mem (eps_mem c s) ?_) (hint s i j)
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (hint _ _ _) (hint _ _ _)) (mul_mem (hint _ _ _) (hint _ _ _))

theorem mulVec_le {L : ℝ} (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (q : Fin 2 → Qbar l)
    (hM : ∀ i j, ‖M i j‖ ≤ 1) (hq : ∀ i, ‖q i‖ ≤ L) (i : Fin 2) : ‖(M *ᵥ q) i‖ ≤ L := by
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;> rw [norm_mul] <;>
    exact (mul_le_mul (hM _ _) (hq _) (norm_nonneg _) zero_le_one).trans (le_of_eq (one_mul L))

theorem om_le_left {L : ℝ} (p q : Fin 2 → Qbar l) (hp : ∀ i, ‖p i‖ ≤ L) (hq : ∀ i, ‖q i‖ ≤ 1) :
    ‖om p q‖ ≤ L := by
  have hL : 0 ≤ L := (norm_nonneg _).trans (hp 0)
  refine (nsub_le_max _ _).trans (max_le ?_ ?_) <;> rw [norm_mul] <;>
    exact (mul_le_mul (hp _) (hq _) (norm_nonneg _) hL).trans (le_of_eq (mul_one L))

theorem om_le_right {L : ℝ} (p q : Fin 2 → Qbar l) (hp : ∀ i, ‖p i‖ ≤ 1) (hq : ∀ i, ‖q i‖ ≤ L) :
    ‖om p q‖ ≤ L := by
  refine (nsub_le_max _ _).trans (max_le ?_ ?_) <;> rw [norm_mul] <;>
    exact (mul_le_mul (hp _) (hq _) (norm_nonneg _) zero_le_one).trans (le_of_eq (one_mul L))

theorem ident_a (A v w x B2 B1 B0 : Fin 2 → Qbar l) (e : Qbar l) (key : om w v = e * om x B0) :
    om A v - (e * om x B0 - om x B2 + om x B1) = om (A - (w - x)) v + om x (B2 - (B1 + v)) := by
  simp only [om, Pi.sub_apply, Pi.add_apply] at *
  linear_combination key

theorem ident_b (As At Ast Bt x : Fin 2 → Qbar l) (M P : Matrix (Fin 2) (Fin 2) (Qbar l)) (N : Matrix (Fin 2) (Fin 2) (Qbar l))
    (e : Qbar l) (key : om (P *ᵥ At) (M *ᵥ (N *ᵥ x)) = e * om At (N *ᵥ x)) :
    om As (M *ᵥ Bt) - (e * -om At (N *ᵥ x) - -om Ast (M *ᵥ (N *ᵥ x)) + -om As (M *ᵥ x)) =
      om As (M *ᵥ (Bt - (N *ᵥ x - x))) - om (Ast - (As + P *ᵥ At)) (M *ᵥ (N *ᵥ x)) := by
  simp only [om, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.sub_apply, Pi.add_apply] at *
  linear_combination -key

end GlobalTheory.Ord2.CupCob

namespace GlobalTheory.Ord2.CupCob

theorem cup_cob : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (W : R2 Ω l)
    (H : Subgroup (G ℚ Ω)) (a b : G ℚ Ω → Fin 2 → Qbar l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → dt W ^ 2 = 1 →
    Coc1 c n W H a → Coc1 c n (dual1 W) H b → (Cob1 c n W H a ∨ Cob1 c n (dual1 W) H b) → Cob2 c n H (cup W a b) := by
  intro l _ Ω _ _ _ c n W H a b hW hint hdet ha hb hcob
  have hWn : ∀ s i j, ‖mat W s i j‖ ≤ 1 := fun s i j => norm_le_one_of_mem c (hint s i j)
  have hDm : ∀ s i j, mat (dual1 W) s i j ∈ c.O := dual_representation_integral c W hdet hint
  have hDn : ∀ s i j, ‖mat (dual1 W) s i j‖ ≤ 1 := fun s i j => norm_le_one_of_mem c (hDm s i j)
  have han : ∀ s i, ‖a s i‖ ≤ 1 := fun s i => norm_le_one_of_mem c (ha.2.1 s i)
  have hbn : ∀ s i, ‖b s i‖ ≤ 1 := fun s i => norm_le_one_of_mem c (hb.2.1 s i)
  rcases hcob with ⟨x, hx, hax⟩ | ⟨x, hx, hbx⟩
  · have hxn : ∀ i, ‖x i‖ ≤ 1 := fun i => norm_le_one_of_mem c (hx i)
    refine ⟨fun t => om x (b t), ?_, fun t => om_mem c _ _ hx (hb.2.1 t), ?_⟩
    · show ContinuousOn (fun t => x 0 * b t 1 - x 1 * b t 0) H
      exact (continuousOn_const.mul (continuousOn_pi.1 hb.1 1)).sub (continuousOn_const.mul (continuousOn_pi.1 hb.1 0))
    · intro s hs t ht
      show ‖_ - _‖ ≤ _
      have key := om_key W hdet s x (b t)
      rw [cup, ident_a (a s) (mat (dual1 W) s *ᵥ b t) (mat W s *ᵥ x) x (b (s * t)) (b s) (b t) (eps l s) key]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · exact om_le_left _ _ (fun i => hax s hs i) (mulVec_le _ _ (hDn s) (hbn t))
      · exact om_le_right _ _ hxn (fun i => hb.2.2 s hs t ht i)
  · have hxn : ∀ i, ‖x i‖ ≤ 1 := fun i => norm_le_one_of_mem c (hx i)
    have hM : Continuous fun s => mat W s := Units.continuous_val.comp hW
    have hD : Continuous fun s => mat (dual1 W) s := by
      have : (fun s => mat (dual1 W) s) = fun s => (eps l s * (mat W s).det) • mat W s := funext (mat_dual1 W hdet)
      rw [this]
      exact (eps_cont.mul hM.matrix_det).smul hM
    have hv : Continuous fun s => mat (dual1 W) s *ᵥ x := hD.matrix_mulVec continuous_const
    refine ⟨fun s => -om (a s) (mat (dual1 W) s *ᵥ x), ?_,
      fun s => neg_mem (om_mem c _ _ (ha.2.1 s) (mulVec_mem c _ _ (hDm s) hx)), ?_⟩
    · show ContinuousOn (fun s => -(a s 0 * (mat (dual1 W) s *ᵥ x) 1 - a s 1 * (mat (dual1 W) s *ᵥ x) 0)) H
      exact (((continuousOn_pi.1 ha.1 0).mul ((continuous_apply 1).comp hv).continuousOn).sub
        ((continuousOn_pi.1 ha.1 1).mul ((continuous_apply 0).comp hv).continuousOn)).neg
    · intro s hs t ht
      show ‖_ - _‖ ≤ _
      have key := om_key W hdet s (a t) (mat (dual1 W) t *ᵥ x)
      beta_reduce
      rw [cup, mat_dual1_mul W s t x,
        ident_b (a s) (a t) (a (s * t)) (b t) x (mat (dual1 W) s) (mat W s) (mat (dual1 W) t) (eps l s) key]
      refine (nsub_le_max _ _).trans (max_le ?_ ?_)
      · exact om_le_right _ _ (han s) (mulVec_le _ _ (hDn s) (fun i => hbx t ht i))
      · exact om_le_left _ _ (fun i => ha.2.2 s hs t ht i)
          (mulVec_le _ _ (hDn s) (mulVec_le _ _ (hDn t) hxn))

end GlobalTheory.Ord2.CupCob
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

theorem _root_.GlobalTheory.T.decompositionGroup_mulEquiv_localGalois_cyclotomic : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → IsPlaceOver A v → ∃ (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (_ : FiniteDimensional ℚ_[l] K) (e : Dec (F := F) A ≃* GK l K), Continuous e ∧ Continuous e.symm ∧ ∀ (r : ℕ) (g : Dec (F := F) A), cycK l K r (e g) = cycMod F Ω l r (g : G F Ω) := by
  first | exact @GlobalTheory.DecLocal.exists_mulEquiv_cyc | exact GlobalTheory.DecLocal.exists_mulEquiv_cyc | (intros; apply GlobalTheory.DecLocal.exists_mulEquiv_cyc <;> assumption)
end

section

namespace GlobalTheory

theorem dualFrLattice_holds : Formalism.L2.DIV.DualFrLattice :=
  GlobalTheory.DualLat.dualFr_lattice_and_hdual.1

end GlobalTheory
end
