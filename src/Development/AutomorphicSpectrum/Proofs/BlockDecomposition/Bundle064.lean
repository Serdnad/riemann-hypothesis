module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle034
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle009
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle026
public import Mathlib.Analysis.Matrix.Spectrum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle015
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicDoubleCosetOfEqualCorank
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle028
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle029
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle018
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle031
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle027

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.UnitSemisimple

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem exists_proj_finset (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hp : ∀ v, v ≠ 0 → 0 < (B v v).re) (t : Finset V) :
    ∀ v : V, ∃ w ∈ Submodule.span ℂ (t : Set V),
      ∀ s ∈ Submodule.span ℂ (t : Set V), B (v - w) s = 0 := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro v
    refine ⟨0, zero_mem _, fun s hs => ?_⟩
    have : s = 0 := by simpa using hs
    simp [this]
  | insert a t _ ih =>
    intro v
    obtain ⟨w₁, hw₁, h₁⟩ := ih v
    obtain ⟨a₁, ha₁, h₂⟩ := ih a
    have hle : Submodule.span ℂ (t : Set V) ≤ Submodule.span ℂ ((insert a t : Finset V) : Set V) :=
      Submodule.span_mono (by simp)
    have ha : a ∈ Submodule.span ℂ ((insert a t : Finset V) : Set V) :=
      Submodule.subset_span (by simp)
    obtain ⟨x, hx⟩ : ∃ x, x = a - a₁ := ⟨_, rfl⟩
    obtain ⟨u, hu⟩ : ∃ u, u = v - w₁ := ⟨_, rfl⟩
    obtain ⟨c, hcdef⟩ : ∃ c, c = B u x / B x x := ⟨_, rfl⟩
    have hc : B u x = c * B x x := by
      by_cases hx0 : x = 0
      · simp [hx0]
      · have h0 : B x x ≠ 0 := fun h => by simpa [h] using hp x hx0
        rw [hcdef]; field_simp
    refine ⟨w₁ + c • x, ?_, ?_⟩
    · refine add_mem (hle hw₁) (Submodule.smul_mem _ _ ?_)
      rw [hx]; exact sub_mem ha (hle ha₁)
    · intro s hs
      rw [Finset.coe_insert] at hs
      obtain ⟨b, z, hz, rfl⟩ := Submodule.mem_span_insert.1 hs
      have hz' : b • a₁ + z ∈ Submodule.span ℂ (t : Set V) :=
        add_mem (Submodule.smul_mem _ _ ha₁) hz
      have e1 : v - (w₁ + c • x) = u - c • x := by rw [hu]; abel
      have e2 : b • a + z = b • x + (b • a₁ + z) := by rw [hx, smul_sub]; abel
      have k1 : B u (b • a₁ + z) = 0 := by rw [hu]; exact h₁ _ hz'
      have k2 : B x (b • a₁ + z) = 0 := by rw [hx]; exact h₂ _ hz'
      rw [e1, e2, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
        (B u).map_add (b • x), (B x).map_add (b • x),
        k1, k2, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, hc]
      simp only [smul_eq_mul, add_zero]
      ring

theorem mem_fixed_iff {G : Type} [Group G] (ρ : Representation ℂ G V) (K : Subgroup G) (v : V) :
    v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v := by
  constructor
  · intro h k hk
    simpa using h ⟨k, hk⟩
  · intro h k
    simpa using h k k.2

theorem orbit_finite {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (ρ : Representation ℂ G V) (K : Subgroup G) (hK : IsCompact (K : Set G)) (w : V)
    (hS : IsOpen {g : G | ρ g w = w}) : {x : V | ∃ k ∈ K, ρ k w = x}.Finite :=
  _root_.UpperTheory.Reformulated.B.Qf32.orbit_finite ρ K hK w hS

theorem orthogonal_of_fixed {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (ρ : Representation ℂ G V) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hi : ∀ g v w, B (ρ g v) (ρ g w) = B v w) (K : Subgroup G) (hK : IsCompact (K : Set G))
    (W : Subrepresentation ρ) (u : V) (hu : ∀ k ∈ K, ρ k u = u)
    (huW : ∀ s ∈ W.toSubmodule ⊓ fixed ρ K, B u s = 0)
    (w : V) (hw : w ∈ W.toSubmodule) (hS : IsOpen {g : G | ρ g w = w}) : B u w = 0 := by
  classical
  have hO := orbit_finite ρ K hK w hS
  set O : Finset V := hO.toFinset with hOdef
  have hmem : ∀ x, x ∈ O ↔ ∃ k ∈ K, ρ k w = x := fun x => by simp [hOdef]
  have hinv : ∀ k ∈ K, ∀ x, ρ k⁻¹ (ρ k x) = x := fun k _ x => by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  have hinv' : ∀ k ∈ K, ∀ x, ρ k (ρ k⁻¹ x) = x := fun k _ x => by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  have hst : ∀ k ∈ K, ∀ x ∈ O, ρ k x ∈ O := by
    intro k hk x hx
    obtain ⟨l, hl, rfl⟩ := (hmem x).1 hx
    refine (hmem _).2 ⟨k * l, K.mul_mem hk hl, ?_⟩
    rw [map_mul, Module.End.mul_apply]
  have hsW : ∑ x ∈ O, x ∈ W.toSubmodule := by
    refine Submodule.sum_mem _ fun x hx => ?_
    obtain ⟨l, _, rfl⟩ := (hmem x).1 hx
    exact W.apply_mem_toSubmodule l hw
  have hsF : ∑ x ∈ O, x ∈ fixed ρ K := by
    rw [mem_fixed_iff]
    intro k hk

    rw [map_sum]
    exact Finset.sum_nbij' (ρ k) (ρ k⁻¹) (fun x hx => hst k hk x hx)
      (fun x hx => hst _ (K.inv_mem hk) x hx) (fun x _ => hinv k hk x) (fun x _ => hinv' k hk x)
      (fun x _ => rfl)
  have h0 := huW _ ⟨hsW, hsF⟩
  have hterm : ∀ x ∈ O, B u x = B u w := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := (hmem x).1 hx
    conv_lhs => rw [← hu l hl]
    exact hi l u w

  rw [map_sum, Finset.sum_congr rfl hterm, Finset.sum_const] at h0
  have hne : O.card ≠ 0 := Finset.card_ne_zero.2 ⟨w, (hmem w).2 ⟨1, K.one_mem, by simp⟩⟩
  rw [nsmul_eq_mul] at h0
  exact (mul_eq_zero.1 h0).resolve_left (by exact_mod_cast hne)

def orth {G : Type} [Group G] (ρ : Representation ℂ G V) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hi : ∀ g v w, B (ρ g v) (ρ g w) = B v w) (W : Subrepresentation ρ) : Subrepresentation ρ where
  toSubmodule :=
    { carrier := {v | ∀ w ∈ W.toSubmodule, B v w = 0}
      add_mem' := fun {a b} ha hb w hw => by simp [ha w hw, hb w hw]
      zero_mem' := fun w _ => by simp
      smul_mem' := fun c v hv w hw => by simp [hv w hw] }
  apply_mem_toSubmodule := by
    intro g v hv w hw
    have e : ρ g (ρ g⁻¹ w) = w := by
      rw [← Module.End.mul_apply, ← map_mul]; simp
    have := hv _ (W.apply_mem_toSubmodule g⁻¹ hw)
    rw [← e, hi]; exact this

theorem exists_isCompl : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → IsAdmissible ρ → IsUnitarisable ρ → ∀ W : Subrepresentation ρ, ∃ W' : Subrepresentation ρ, IsCompl W W' := by
  intro G V _ _ _ _ _ ρ hbasis hadm hun W
  obtain ⟨B, hh, hp, hi⟩ := hun
  refine ⟨orth ρ B hi W, IsCompl.of_eq ?_ ?_⟩
  · apply Subrepresentation.toSubmodule_injective
    rw [Subrepresentation.toSubmodule_inf]
    refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
    by_contra hv0
    have h0 : B v v = 0 := hv.2 v hv.1
    simpa [h0] using hp v hv0
  · apply Subrepresentation.toSubmodule_injective
    rw [Subrepresentation.toSubmodule_sup]
    refine (Submodule.eq_top_iff').2 fun v => ?_
    obtain ⟨K, hKo, hKc, hKv⟩ := hbasis {g | ρ g v = v} ((hadm.1 v).mem_nhds (by simp))
    have hfd : FiniteDimensional ℂ (fixed ρ K) := hadm.2 K hKo hKc
    have hfd' : FiniteDimensional ℂ (W.toSubmodule ⊓ fixed ρ K : Submodule ℂ V) :=
      Submodule.finiteDimensional_inf_right _ _
    have hfg : (W.toSubmodule ⊓ fixed ρ K).FG := Module.Finite.iff_fg.1 hfd'
    obtain ⟨t, ht⟩ := hfg
    obtain ⟨w, hw, hort⟩ := exists_proj_finset B hp t v
    rw [ht] at hw hort
    have hfix : ∀ k ∈ K, ρ k (v - w) = v - w := by
      intro k hk
      have h1 : ρ k v = v := hKv hk
      have h2 : ρ k w = w := (mem_fixed_iff ρ K w).1 hw.2 k hk
      rw [map_sub, h1, h2]
    have hmem : v - w ∈ (orth ρ B hi W).toSubmodule := fun y hy =>
      orthogonal_of_fixed ρ B hi K hKc W (v - w) hfix hort y hy (hadm.1 y)
    have : v = w + (v - w) := by abel
    rw [this]
    exact Submodule.add_mem_sup hw.1 hmem

end GlobalTheory.CompanionTheory.UnitSemisimple
end

section

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem _root_.GlobalTheory.T.detW_eq_normSq_det_one_add_I : ∀ (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian →
    detW b = Complex.normSq (Matrix.det (1 + Complex.I • b)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.detW_eq_normSq_det_one_add_I_smul | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.detW_eq_normSq_det_one_add_I_smul | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.detW_eq_normSq_det_one_add_I_smul <;> assumption)
end

section

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem det_one_add_sq_eq_prod_eigenvalues (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) :
    Matrix.det (1 + b * b) = ((∏ i, (1 + hb.eigenvalues i ^ 2) : ℝ) : ℂ) := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hb.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  set D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => ((hb.eigenvalues i : ℝ) : ℂ)) with hD
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self hb.eigenvectorUnitary
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self hb.eigenvectorUnitary
  have hs : b = U * D * star U := by
    have := hb.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, hU, hD, Function.comp_def] using this
  have h1 : 1 + b * b = U * (1 + D * D) * star U := by
    rw [hs]
    calc 1 + U * D * star U * (U * D * star U)
        = U * star U + U * D * (star U * U) * D * star U := by
          rw [hUU']; simp only [Matrix.mul_assoc]
      _ = U * (1 + D * D) * star U := by
          rw [hUU]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
  have hdet : (star U).det * U.det = 1 := by
    rw [← Matrix.det_mul, hUU, Matrix.det_one]
  have h2 : 1 + D * D = Matrix.diagonal (fun i => (((1 + hb.eigenvalues i ^ 2 : ℝ)) : ℂ)) := by
    rw [hD, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one, Matrix.diagonal_add]
    congr 1
    ext i
    push_cast
    ring
  rw [h1, Matrix.det_mul, Matrix.det_mul, h2, Matrix.det_diagonal]
  push_cast
  calc U.det * (∏ i, (1 + ((hb.eigenvalues i : ℝ) : ℂ) ^ 2)) * (star U).det
      = ((star U).det * U.det) * ∏ i, (1 + ((hb.eigenvalues i : ℝ) : ℂ) ^ 2) := by ring
    _ = _ := by rw [hdet, one_mul]

theorem one_le_detW : ∀ (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian → 1 ≤ detW b := by
  intro n b hb
  unfold detW
  rw [det_one_add_sq_eq_prod_eigenvalues n b hb, Complex.ofReal_re]
  have : ∀ i ∈ (Finset.univ : Finset (Fin n)), (1 : ℝ) ≤ 1 + hb.eigenvalues i ^ 2 := fun i _ => by
    nlinarith [sq_nonneg (hb.eigenvalues i)]
  calc (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) this

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end

section

open Matrix GlobalTheory.CompanionTheory.Jp

theorem _root_.GlobalTheory.T.parabolic_double_coset_of_equal_corank : ∀ (k : Type) [Field k] (n : ℕ) (g₁ g₂ : GL (Ix n) k), iD g₁ = iD g₂ →
    ∃ (a d : GL (Fin n) k) (b : Matrix (Fin n) (Fin n) k) (x : GL (Ix n) k),
      x.1.toBlocks₁₂ = 0 ∧ g₂ = pM a d b * g₁ * x := by
  first | exact @GlobalTheory.CompanionTheory.Jp.Dbl.main | exact GlobalTheory.CompanionTheory.Jp.Dbl.main | (intros; apply GlobalTheory.CompanionTheory.Jp.Dbl.main <;> assumption)
end

section

open Matrix GlobalTheory.CompanionTheory.Jp

theorem _root_.GlobalTheory.T.card_fixed_lower_right_block : ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (D : Matrix (Fin n) (Fin n) k),
    Nat.card {g : GL (Ix n) k // dBlk g = D} =
      Nat.card {g : GL (Ix n) k // lowerLeftBlock g = 0 ∧ dBlk g = 1} *
        Nat.card {C : Matrix (Fin n) (Fin n) k // (Matrix.fromCols C D).rank = n} := by
  first | exact @GlobalTheory.CompanionTheory.Jp.CntHalf.card_lowerRightBlock_eq_fibre_formula | exact GlobalTheory.CompanionTheory.Jp.CntHalf.card_lowerRightBlock_eq_fibre_formula | (intros; apply GlobalTheory.CompanionTheory.Jp.CntHalf.card_lowerRightBlock_eq_fibre_formula <;> assumption)
end

section

open Matrix GlobalTheory.CompanionTheory.Jp

theorem _root_.GlobalTheory.T.residue_upper_unipotent_lift : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
    ∀ x : GL (Ix n) (IsLocalRing.ResidueField O), x.1.toBlocks₁₂ = 0 →
      ∃ j j' : GL (Ix n) O, inL j * tauM w = tauM w * inL j' ∧ resK j' = x := by
  first | exact @GlobalTheory.CompanionTheory.Jp.twist_low | exact GlobalTheory.CompanionTheory.Jp.twist_low | (intros; apply GlobalTheory.CompanionTheory.Jp.twist_low <;> assumption)
end

section

open Matrix GlobalTheory.CompanionTheory.Jp

theorem _root_.GlobalTheory.T.level_square_congruence_conjugation : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ → ∀ γ ∈ Gam2 (n := n) ϖ,
      ∃ j' : GL (Ix n) O, inL γ * tauM w = tauM w * inL j' ∧ resK j' = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Jp.Twist.twist_gam | exact GlobalTheory.CompanionTheory.Jp.Twist.twist_gam | (intros; apply GlobalTheory.CompanionTheory.Jp.Twist.twist_gam <;> assumption)
end

section

open Matrix GlobalTheory.CompanionTheory.Jp

theorem _root_.GlobalTheory.T.reduction_corank_eq_rank_lower_left : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
    ∀ (κ : GL (Ix n) O) (h : GL (Ix n) (IsLocalRing.ResidueField O)), IsRed (O := O) w κ h →
      iD h = (lowerLeftBlock (resK κ)).rank := by
  first | exact @GlobalTheory.CompanionTheory.Jp.RedRank.iD_eq_rank | exact GlobalTheory.CompanionTheory.Jp.RedRank.iD_eq_rank | (intros; apply GlobalTheory.CompanionTheory.Jp.RedRank.iD_eq_rank <;> assumption)
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

theorem _root_.GlobalTheory.T.parabolic_fundamental_domain_volume : ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (Γ : Subgroup P) (Γ₁ : Subgroup G₁) [Countable Γ₁], (∀ u ∈ Γ₁, ι u ∈ Γ) → ∀ (ν : Measure π.ker) [ν.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (D : Set π.ker) (𝓕₁ : Set G₁), (∀ x : π.ker, ∃! g : Γ.subgroupOf π.ker, g • x ∈ D) → IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → ∀ᵐ p ∂(Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)), ∃ γ : Γ, γ • p ∈ (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁)) := by
  first | exact @GlobalTheory.CompanionTheory.SplitExtLat.ae_exists_smul_mem_image_prod | exact GlobalTheory.CompanionTheory.SplitExtLat.ae_exists_smul_mem_image_prod | (intros; apply GlobalTheory.CompanionTheory.SplitExtLat.ae_exists_smul_mem_image_prod <;> assumption)
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

theorem _root_.GlobalTheory.T.parabolic_integral_unfolding : ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (Γ : Subgroup P) (Γ₁ : Subgroup G₁) [Countable Γ₁], (∀ γ ∈ Γ, π γ ∈ Γ₁) → ∀ (ν : Measure π.ker) [ν.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (D : Set π.ker) (𝓕₁ : Set G₁), (∀ x : π.ker, ∃! g : Γ.subgroupOf π.ker, g • x ∈ D) → IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → ∀ γ : Γ, γ ≠ 1 → AEDisjoint (Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)) (γ • (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁))) (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁)) := by
  first | exact @GlobalTheory.CompanionTheory.SplitExtLat.aedisjoint_smul_image_prod | exact GlobalTheory.CompanionTheory.SplitExtLat.aedisjoint_smul_image_prod | (intros; apply GlobalTheory.CompanionTheory.SplitExtLat.aedisjoint_smul_image_prod <;> assumption)
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

theorem _root_.GlobalTheory.T.parabolic_levi_integral_formula : ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (ν : Measure π.ker) [ν.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (D : Set π.ker) (𝓕₁ : Set G₁), MeasurableSet D → NullMeasurableSet 𝓕₁ μ₁ → NullMeasurableSet (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁)) (Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)) ∧ ∀ f : P → ℝ≥0∞, Measurable f → ∫⁻ p in (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁)), f p ∂(Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)) = ∫⁻ u in 𝓕₁, ∫⁻ m in D, f ((m : P) * ι u) ∂ν ∂μ₁ := by
  exact @GlobalTheory.CompanionTheory.SplitExtLat.setLIntegral_splitHomeo_image_prod
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

theorem _root_.GlobalTheory.T.parabolic_quotient_measure : ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (ν : Measure π.ker) [ν.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure], (∀ u, Measure.map (fun m : π.ker => MulAut.conjNormal (ι u) m) ν = ν) → (Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)).IsHaarMeasure := by
  first | exact @GlobalTheory.CompanionTheory.SplitExtLat.isHaarMeasure_map_splitHomeo | exact GlobalTheory.CompanionTheory.SplitExtLat.isHaarMeasure_map_splitHomeo | (intros; apply GlobalTheory.CompanionTheory.SplitExtLat.isHaarMeasure_map_splitHomeo <;> assumption)
end
