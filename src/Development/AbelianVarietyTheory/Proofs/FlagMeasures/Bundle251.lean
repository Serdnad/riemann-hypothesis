module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle103
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle046
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle239
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle081
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle243
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelUnitaryGroupOpNormPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle120
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle242
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle189
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle107
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle104
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle212
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle042
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle003
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NearTermsModeratePointsOneTypeBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle271
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle021

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.InvH

theorem tsum_orbit_normaliser {G X M : Type} [Group G] [MulAction G X] [AddCommMonoid M]
    [TopologicalSpace M] (K : Subgroup G) (h : G) (h1 : ∀ s ∈ K, h * s * h⁻¹ ∈ K)
    (h2 : ∀ s ∈ K, h⁻¹ * s * h ∈ K) (φ ψ : X → M) (hφ : ∀ s ∈ K, ∀ x, φ (s • x) = φ x)
    (hψ : ∀ x, ψ (h • x) = φ x) :
    ∑' o : MulAction.orbitRel.Quotient K X, ψ o.out =
      ∑' o : MulAction.orbitRel.Quotient K X, φ o.out := by
  let e : MulAction.orbitRel.Quotient K X ≃ MulAction.orbitRel.Quotient K X :=
    Quotient.congr (MulAction.toPerm h) (by
      intro a b
      simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, MulAction.toPerm_apply]
      constructor
      · rintro ⟨s, hs⟩
        refine ⟨⟨_, h1 s s.2⟩, ?_⟩
        rw [← hs]
        simp [Subgroup.smul_def, mul_smul]
      · rintro ⟨s, hs⟩
        refine ⟨⟨_, h2 s s.2⟩, ?_⟩
        simp only [Subgroup.smul_def, mul_smul] at hs ⊢
        rw [hs]; simp)
  rw [← e.tsum_eq]
  refine tsum_congr fun o => ?_
  have h3 : e o = Quotient.mk _ (h • o.out) := by
    conv_lhs => rw [← Quotient.out_eq o]
    rfl
  have h4 : (MulAction.orbitRel K X) (e o).out (h • o.out) := by
    rw [h3]; exact Quotient.mk_out (s := MulAction.orbitRel K X) _
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h4
  obtain ⟨s, hs⟩ := h4
  have h5 : (e o).out = h • ((h⁻¹ * s * h) • o.out) := by
    rw [← hs]; simp [Subgroup.smul_def, mul_smul]
  rw [h5, hψ, hφ _ (h2 s s.2)]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem conj_unipOn {n : ℕ} {A B : Submodule E (Fin n → E)} {h s : (Fin n → E) ≃ₗ[E] (Fin n → E)}
    (hA : ∀ v, h v ∈ A ↔ v ∈ A) (hB : ∀ v, h v ∈ B ↔ v ∈ B) (hs : s ∈ unipOn A B) :
    h * s * h⁻¹ ∈ unipOn A B := by
  have hA' : ∀ v, h.symm v ∈ A ↔ v ∈ A := fun v => by rw [← hA]; simp
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · change h (s (h.symm v)) ∈ A ↔ _
    rw [hA, hs.1, hA']
  · have := (hB _).2 (hs.2 _ ((hA' v).2 hv))
    rw [map_sub, LinearEquiv.apply_symm_apply] at this
    exact this

theorem mem_iff_of_fix {n : ℕ} {A : Submodule E (Fin n → E)} {h : (Fin n → E) ≃ₗ[E] (Fin n → E)}
    (hA : ∀ v ∈ A, h v = v) (v : Fin n → E) : h v ∈ A ↔ v ∈ A := by
  constructor
  · intro hv
    have := h.injective (hA _ hv)
    rwa [this] at hv
  · intro hv; rwa [hA v hv]

variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem spanTo_mono (g : Fin (r + 1) → S.V) {i j : ℕ} (hij : i ≤ j) : S.spanTo g i ≤ S.spanTo g j :=
  Submodule.span_mono (Set.image_mono fun _ ha => lt_of_lt_of_le ha hij)

theorem conj_Nof (g : Fin (r + 1) → S.V) {h s : S.GLV} (hi : h ∈ isomG L S.Hm)
    (hg : ∀ v ∈ S.spanTo g (r + 1), h v = v) (hs : s ∈ S.Nof g) : h * s * h⁻¹ ∈ S.Nof g := by
  have hfix : ∀ j ≤ r + 1, ∀ v, h v ∈ S.spanTo g j ↔ v ∈ S.spanTo g j := fun j hj =>
    mem_iff_of_fix fun v hv => hg v (spanTo_mono S g hj hv)
  obtain ⟨⟨s1, s2⟩, s3⟩ := hs
  refine ⟨⟨(isomG L S.Hm).mul_mem ((isomG L S.Hm).mul_mem hi s1) ((isomG L S.Hm).inv_mem hi), ?_⟩, ?_⟩
  · refine Subgroup.mem_iInf.2 fun j => ?_
    exact conj_unipOn (hfix _ (by omega)) (hfix _ (by omega)) (Subgroup.mem_iInf.1 s2 j)
  · refine conj_unipOn (fun v => ?_) (hfix _ (by omega)) s3
    refine forall₂_congr fun y hy => ?_
    have := hi v y
    rw [hg y (spanTo_mono S g (by omega) hy)] at this
    rw [this]

theorem conj_St {h s : S.GLV} (hh : h ∈ S.H0) (hs : s ∈ S.St) : h * s * h⁻¹ ∈ S.St := by
  have hfix : ∀ v ∈ S.ME, h v = v := fun v hv => sub_eq_zero.1 ((Submodule.mem_bot E).1 (hh.2.2 v hv))
  exact ⟨conj_Nof S _ hh.1 (fun v hv => hfix v (Submodule.mem_sup_left hv)) hs.1,
    conj_Nof S _ hh.1 (fun v hv => hfix v (Submodule.mem_sup_right hv)) hs.2⟩

theorem amp_mass_smul : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ h ∈ S.H0, ∀ (d : S.Datum) (Q Q' : Submodule L.O S.V → Prop), (∀ s ∈ S.St, ∀ Λ, S.IsTerm d Λ → Q Λ → Q (s • Λ)) → (∀ Λ, S.IsTerm d Λ → (Q Λ ↔ Q' (h • Λ))) → S.amp (h • d) Q' = S.amp d Q ∧ S.mass (h • d) Q' = S.mass d Q := by
  intro F _ _ _ _ _ E _ _ _ L r k S h hh d Q Q' hQ hQ'
  have c1 : ∀ s ∈ S.St, h * s * h⁻¹ ∈ S.St := fun s hs => conj_St S hh hs
  have c2 : ∀ s ∈ S.St, h⁻¹ * s * h ∈ S.St := fun s hs => by
    simpa using conj_St S (inv_mem hh) hs
  have aS := GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d
  have aH := GlobalTheory.T.hermitianFrames_complementUnitary_acts_on_terms L r k S
  have hmu : ∀ Λ, S.IsTerm d Λ → ∀ s ∈ S.St, S.mu (s • Λ) = S.mu Λ := fun Λ hΛ =>
    ((GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).1 Λ (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hΛ).1.1).2.2
  have iS : ∀ s ∈ S.St, ∀ Λ, (S.IsTerm d (s • Λ) ∧ Q (s • Λ)) ↔ (S.IsTerm d Λ ∧ Q Λ) := by
    intro s hs Λ
    constructor
    · rintro ⟨a, b⟩
      have a' := (aS _ a _ (inv_mem hs)).1
      have b' := hQ _ (inv_mem hs) _ a b
      rw [inv_smul_smul] at a' b'
      exact ⟨a', b'⟩
    · rintro ⟨a, b⟩
      exact ⟨(aS _ a _ hs).1, hQ _ hs _ a b⟩
  have iH : ∀ Λ, (S.IsTerm (h • d) (h • Λ) ∧ Q' (h • Λ)) ↔ (S.IsTerm d Λ ∧ Q Λ) := by
    intro Λ
    constructor
    · rintro ⟨a, b⟩
      have a' := (aH _ _ a _ (inv_mem hh)).1
      rw [inv_smul_smul, inv_smul_smul] at a'
      exact ⟨a', (hQ' _ a').2 b⟩
    · rintro ⟨a, b⟩
      exact ⟨(aH _ _ a _ hh).1, (hQ' _ a).1 b⟩
  constructor
  · refine tsum_orbit_normaliser S.St h c1 c2
      (fun Λ => if S.IsTerm d Λ ∧ Q Λ then (S.mu Λ : ℂ) * S.om d Λ else 0)
      (fun Λ => if S.IsTerm (h • d) Λ ∧ Q' Λ then (S.mu Λ : ℂ) * S.om (h • d) Λ else 0) ?_ ?_
    · intro s hs Λ
      exact if_ctx_congr (iS s hs Λ) (fun a => by rw [hmu _ a.1 s hs, (aS _ a.1 s hs).2.1])
        fun _ => rfl
    · intro Λ
      exact if_ctx_congr (iH Λ)
        (fun a => by rw [(aH _ _ a.1 h hh).2.1, (aH _ _ a.1 h hh).2.2.1]) fun _ => rfl
  · refine tsum_orbit_normaliser S.St h c1 c2
      (fun Λ => if S.IsTerm d Λ ∧ Q Λ then ENNReal.ofReal (S.mu Λ) else 0)
      (fun Λ => if S.IsTerm (h • d) Λ ∧ Q' Λ then ENNReal.ofReal (S.mu Λ) else 0) ?_ ?_
    · intro s hs Λ
      exact if_ctx_congr (iS s hs Λ) (fun a => by rw [hmu _ a.1 s hs]) fun _ => rfl
    · intro Λ
      exact if_ctx_congr (iH Λ) (fun a => by rw [(aH _ _ a.1 h hh).2.2.1]) fun _ => rfl

end GlobalTheory.InvH
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem decE_dOp_le_floor {n : ℕ} (hn : 1 ≤ n) (ε : Fin n → Bool) (h : ℝ)
    (hh : 32 * (n : ℝ) ^ 2 * Real.sqrt (rkR ε) ≤ h) (g : UJ ε) :
    decE (rkR ε) h (dOp (uMat g)) ≤ Real.exp (-(2 * (2 * (n : ℝ) ^ 2) * (⌊dOp (uMat g)⌋₊ : ℝ))) := by
  rcases Nat.eq_zero_or_pos (rkR ε) with h0 | hq
  · simp [GlobalTheory.Count.Majorant.dOp_eq_zero ε h0 g, decE]
  · obtain ⟨ha, hb, -⟩ := shell_sum_majorant n (rkR ε) h hn hq hh
    have hp : 0 ≤ dOp (uMat g) := ((GlobalTheory.Count.Cartan.cartan_distances n ε).2.1 g g hn).1
    refine (ha (Set.mem_Ici.2 (Nat.cast_nonneg _)) (Set.mem_Ici.2 hp) (Nat.floor_le hp)).trans ?_
    refine (hb _).trans (le_of_eq ?_)
    congr 2
    ring

theorem norm_phe_le_floor (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ) (hd : IsDSData B d)
    (hn : 1 ≤ B.I.n) (hl : LocDec B h) (hb : HBig B 32 h) (g : B.I.GA) :
    ‖phe B d g‖ ≤ ((∏ v, d v) * (B.e 1).re) *
      ∏ v, Real.exp (-(2 * (2 * (B.I.n : ℝ) ^ 2) * (⌊dOp (uMat (g.1 v))⌋₊ : ℝ))) := by
  obtain ⟨-, he0, he, -⟩ := GlobalTheory.rowsAut_idem_elementary B
  have hd0 : 0 ≤ ∏ v, d v := Finset.prod_nonneg fun v _ => (hd v).2.2.2.1.le
  have h1 : ‖∏ v, ⟪B.w v, B.σ v (uMat (g.1 v)) (B.w v)⟫_ℂ‖ ≤
      ∏ v, Real.exp (-(2 * (2 * (B.I.n : ℝ) ^ 2) * (⌊dOp (uMat (g.1 v))⌋₊ : ℝ))) := by
    rw [norm_prod]
    exact Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) fun v _ =>
      (hl v _).trans (decE_dOp_le_floor hn _ h (hb v) _)
  unfold phe ph
  rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_of_nonneg hd0, mul_assoc, mul_assoc,
    mul_comm (B.e 1).re]
  exact mul_le_mul_of_nonneg_left (mul_le_mul h1 (he _) (norm_nonneg _) ((norm_nonneg _).trans h1)) hd0

theorem kernel_abs_bound : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 32 h → ∀ x y : B.I.GA, Summable (fun γ : B.I.GFset => ‖phe B d (x⁻¹ * γ.1 * y)‖) ∧ ∑' γ : B.I.GFset, ‖phe B d (x⁻¹ * γ.1 * y)‖ ≤ kerC B d * (tau1 B.I x * tau1 B.I y)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) := by
  intro B d h hd hn hl hb x y
  obtain ⟨-, he0, -, -⟩ := GlobalTheory.rowsAut_idem_elementary B
  have hd0 : 0 ≤ ∏ v, d v := Finset.prod_nonneg fun v _ => (hd v).2.2.2.1.le
  have ht := (GlobalTheory.T.truncatedLeastLatticeSize_lipschitz_properties B.I hn).1
  have hx := ht x
  have hy := ht y
  have hn' : (1 : ℝ) ≤ B.I.n := by exact_mod_cast hn
  have ha : (1 : ℝ) ≤ 2 * (B.I.n : ℝ) ^ 2 := by nlinarith
  have hexp : (2 : ℝ) ≤ Real.exp (2 * (B.I.n : ℝ) ^ 2) := by
    have := Real.add_one_le_exp (2 * (B.I.n : ℝ) ^ 2)
    linarith
  have hA : 0 ≤ (3 * Real.sqrt B.I.n / (tau1 B.I x * tau1 B.I y)) ^ (2 * B.I.n ^ 2 * B.I.f) := by positivity
  have hc : 0 ≤ (∏ v, d v) * (B.e 1).re := mul_nonneg hd0 he0
  obtain ⟨hs, hle⟩ := GlobalTheory.summable_and_tsum_le_of_box_count (InfinitePlace B.I.F) B.I.GFset
    (fun γ v => dOp (uMat ((x⁻¹ * γ.1 * y).1 v))) (fun γ => ‖phe B d (x⁻¹ * γ.1 * y)‖)
    (2 * (B.I.n : ℝ) ^ 2) _ _ hA hc
    (by rw [Real.exp_neg, one_div]; exact inv_anti₀ two_pos hexp)
    (fun γ v => ((GlobalTheory.Count.Cartan.cartan_distances B.I.n _).2.1 _ 1 hn).1)
    (fun γ => ⟨norm_nonneg _, norm_phe_le_floor B d h hd hn hl hb _⟩)
    (by
      intro r hr
      obtain ⟨hf, hcnt⟩ := GlobalTheory.T.count_rational_elements_bounded_distance B.I x y r hn hr
      have hsub : Subtype.val '' {γ : B.I.GFset | ‖phe B d (x⁻¹ * γ.1 * y)‖ ≠ 0 ∧
            ∀ v, dOp (uMat ((x⁻¹ * γ.1 * y).1 v)) ≤ r v} ⊆
          {γ ∈ B.I.GFset | (x⁻¹ * γ * y).2 ∈ B.I.Kset ∧ ∀ v, dOp (uMat ((x⁻¹ * γ * y).1 v)) ≤ r v} := by
        rintro _ ⟨γ, ⟨h1, h2⟩, rfl⟩
        refine ⟨γ.2, B.e_adm.2.2.2.2.1 _ fun h0 => h1 ?_, h2⟩
        unfold phe
        rw [h0, mul_zero, norm_zero]
      refine ⟨Set.Finite.of_finite_image (hf.subset hsub) Subtype.val_injective.injOn, le_trans ?_ hcnt⟩
      rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
      exact_mod_cast Set.ncard_le_ncard hsub hf)
  refine ⟨hs, hle.trans ?_⟩
  have hcard : Fintype.card (InfinitePlace B.I.F) ≤ B.I.f := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank B.I.F
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces B.I.F
    unfold AutInst.f
    omega
  refine (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) hcard) (mul_nonneg hc hA)).trans
    (le_of_eq ?_)
  unfold kerC
  rw [div_eq_mul_inv, mul_pow (3 * Real.sqrt B.I.n)]
  ring

end GlobalTheory.Dec
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.PolyProper

variable {k r : ℕ}

theorem gram_det_unit : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_right_inverse (hermitian_pos_facts_hold k r).2.1

theorem mul_mem {g h : Mat k r} (hg : g ∈ GG k r) (hh : h ∈ GG k r) : g * h ∈ GG k r :=
  (unitary_group_holds _ _ gram_det_unit).2.1 g hg h hh

theorem inv_mem {g : Mat k r} (hg : g ∈ GG k r) : g⁻¹ ∈ GG k r :=
  ((unitary_group_holds _ _ gram_det_unit).2.2 g hg).2

theorem det_unit {g : Mat k r} (hg : g ∈ GG k r) : IsUnit g.det :=
  ((unitary_group_holds _ _ gram_det_unit).2.2 g hg).1

theorem mem_of_S {z : Fin (2 * r + k + 1) → ℂ} {s : Mat k r} (hs : s ∈ Sset k r z) : s ∈ GG k r := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  exact mul_mem hh.1 hm.1

theorem inv_eq {g : Mat k r} (hg : g ∈ GG k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  apply Matrix.inv_eq_left_inv
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  rw [Matrix.mul_assoc (Hpk k r), Matrix.mul_assoc (Hpk k r), h]
  exact (hermitian_pos_facts_hold k r).2.1

theorem left_bound (z z' : Fin (2 * r + k + 1) → ℂ) (C : Set (Mat k r)) (hz : inWb k r z)
    (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') (hC : IsCompact C)
    (hCr : C ⊆ Greg k r z z') :
    ∃ C0 : ℝ, ∀ γ ∈ C, ∀ s ∈ Sset k r z, ∀ s' ∈ Sset k r z',
      opn s ≤ C0 * opn (s * γ * s'⁻¹) ^ (2 * (r ^ 2 + r + 1)) := by
  obtain ⟨C1, h1⟩ := GlobalTheory.T.siegel_region_norm_bound k r z z' C hz hz' hT hT' hC hCr
  obtain ⟨C2, h2⟩ := GlobalTheory.T.isometry_opNorm_bounded_by_two_frames k r z z' C hz hz' hT hT' hC
    (fun γ hγ => ⟨(hCr hγ).1, (hCr hγ).2.2⟩)
  obtain ⟨hN1, -, -, -, hN5, -⟩ := GlobalTheory.T.besselModelUnitaryGroup_opNorm_properties k r
  refine ⟨C2 * (max 1 C1) ^ 2, fun γ hγ s hs s' hs' => ?_⟩
  have hsG := mem_of_S hs
  have hs'G := mem_of_S hs'
  have hγG : γ ∈ GG k r := (hCr hγ).1
  have hxG : s * γ * s'⁻¹ ∈ GG k r := mul_mem (mul_mem hsG hγG) (inv_mem hs'G)
  have hx1 : 1 ≤ opn (s * γ * s'⁻¹) := (hN1 _ hxG).2
  have hxs : (s * γ * s'⁻¹) * s' = s * γ := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (det_unit hs'G), Matrix.mul_one]
  have h1' := h1 γ hγ s hs s' hs'
  have h5 := hN5 (s * γ * s'⁻¹)
  set X := opn (s * γ * s'⁻¹) with hX
  have hp1 : 1 ≤ X ^ (r * (r + 1)) := one_le_pow₀ hx1
  have hm1 : (1 : ℝ) ≤ max 1 C1 := le_max_left _ _
  have hle : C1 * X ^ (r * (r + 1)) ≤ max 1 C1 * X ^ (r * (r + 1)) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hQ1 : 1 ≤ max 1 C1 * X ^ (r * (r + 1)) := one_le_mul_of_one_le_of_one_le hm1 hp1
  have hB : 1 ≤ X * (max 1 C1 * X ^ (r * (r + 1))) := one_le_mul_of_one_le_of_one_le hx1 hQ1
  have key := h2 γ hγ s hsG (X * (max 1 C1 * X ^ (r * (r + 1)))) hB (by
    rintro (a | b)
    · show eucl (s *ᵥ fvec k r z a) ≤ _
      refine ((h1' a).1.trans hle).trans ?_
      exact le_mul_of_one_le_left (by linarith) hx1
    · show eucl (s *ᵥ (γ *ᵥ fvec k r z' b)) ≤ _
      rw [Matrix.mulVec_mulVec, ← hxs, ← Matrix.mulVec_mulVec]
      refine (h5 _).trans ?_
      exact mul_le_mul_of_nonneg_left ((h1' b).2.trans hle) (by linarith))
  refine key.trans (le_of_eq ?_)
  ring

theorem poly_proper : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (C : Set (Mat k r)), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsCompact C → C ⊆ Greg k r z z' → ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ γ ∈ C, ∀ s ∈ Sset k r z, ∀ s' ∈ Sset k r z', max (opn s) (opn s') ≤ C0 * opn (s * γ * s'⁻¹) ^ (2 * (r ^ 2 + r + 1)) := by
  intro k r z z' C hz hz' hT hT' hC hCr
  obtain ⟨C1, h1⟩ := left_bound z z' C hz hz' hT hT' hC hCr
  have hcont : Continuous fun g : Mat k r => Hpk k r * gᴴ * Hpk k r :=
    (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
  have hCr' : (fun g : Mat k r => Hpk k r * gᴴ * Hpk k r) '' C ⊆ Greg k r z' z := by
    rintro _ ⟨γ, hγ, rfl⟩
    have hγG : γ ∈ GG k r := (hCr hγ).1
    show Hpk k r * γᴴ * Hpk k r ∈ _
    rw [← inv_eq hγG]
    exact (GlobalTheory.T.besselZhat_inv_and_regular_iff k r z z' γ hγG).2.1 (hCr hγ)
  obtain ⟨C2, h2⟩ := left_bound z' z _ hz' hz hT' hT (hC.image hcont) hCr'
  obtain ⟨hN1, -⟩ := GlobalTheory.T.besselModelUnitaryGroup_opNorm_properties k r
  refine ⟨max 1 (max C1 C2), le_max_left _ _, fun γ hγ s hs s' hs' => ?_⟩
  have hsG := mem_of_S hs
  have hs'G := mem_of_S hs'
  have hγG : γ ∈ GG k r := (hCr hγ).1
  have hxG : s * γ * s'⁻¹ ∈ GG k r := mul_mem (mul_mem hsG hγG) (inv_mem hs'G)
  have hinv : s' * γ⁻¹ * s⁻¹ = (s * γ * s'⁻¹)⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (det_unit hs'G),
      Matrix.mul_assoc]
  have ha := h1 γ hγ s hs s' hs'
  have hb := h2 γ⁻¹ ⟨γ, hγ, (inv_eq hγG).symm⟩ s' hs' s hs
  rw [hinv, (hN1 _ hxG).1] at hb
  have hp : 0 ≤ opn (s * γ * s'⁻¹) ^ (2 * (r ^ 2 + r + 1)) := pow_nonneg (opn_nonneg _) _
  refine max_le (ha.trans ?_) (hb.trans ?_)
  · exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hp
  · exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) hp

end GlobalTheory.SgInf.PolyProper
end

section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.GaugeQuot.BallProd

theorem volume_ball_eq_ballVol {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] {d : ℕ}
    (hd : Module.finrank ℝ F = d) (r : ℝ) :
    (volume : Measure F) (Metric.ball 0 r) = ballVol d r := by
  subst hd
  unfold ballVol
  have h := (stdOrthonormalBasis ℝ F).measurePreserving_repr
  rw [← h.measure_preimage measurableSet_ball.nullMeasurableSet]
  congr 1
  ext x
  simp

theorem prod_region_eq_ballVol (P Q : ℕ) (r : ℝ) (hr : 0 < r) :
    ((volume : Measure (ℝ × Sp P Q)).prod
      (volume : Measure (EuclideanSpace ℝ (Fin ((P + Q) ^ 2)))))
      {p | p.1.1 ^ 2 + ∑ i, ‖p.1.2 i‖ ^ 2 + ‖p.2‖ ^ 2 < r ^ 2} = ballVol ((P + Q + 1) ^ 2) r := by
  have h0 := GlobalTheory.volume_preserving_ofLp_complex (Fin P ⊕ Fin Q)
  have h1 := ((MeasurePreserving.id (volume : Measure ℝ)).prod h0).comp
    (WithLp.volume_preserving_ofLp ℝ (EuclideanSpace ℂ (Fin P ⊕ Fin Q)))
  have h2 := (h1.prod (MeasurePreserving.id
      (volume : Measure (EuclideanSpace ℝ (Fin ((P + Q) ^ 2)))))).comp
    (WithLp.volume_preserving_ofLp (WithLp 2 (ℝ × EuclideanSpace ℂ (Fin P ⊕ Fin Q)))
      (EuclideanSpace ℝ (Fin ((P + Q) ^ 2))))
  have hm : MeasurableSet {p : (ℝ × Sp P Q) × EuclideanSpace ℝ (Fin ((P + Q) ^ 2)) |
      p.1.1 ^ 2 + ∑ i, ‖p.1.2 i‖ ^ 2 + ‖p.2‖ ^ 2 < r ^ 2} :=
    (isOpen_lt (by fun_prop) continuous_const).measurableSet
  rw [Measure.volume_eq_prod, ← h2.measure_preimage hm.nullMeasurableSet,
    ← volume_ball_eq_ballVol (F := WithLp 2 (WithLp 2 (ℝ × EuclideanSpace ℂ (Fin P ⊕ Fin Q)) ×
      EuclideanSpace ℝ (Fin ((P + Q) ^ 2))))]
  · congr 1
    ext x
    rw [mem_ball_zero_iff, ← sq_lt_sq₀ (norm_nonneg _) hr.le, WithLp.prod_norm_sq_eq_of_L2,
      WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq]
    simp
  · rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq, Module.finrank_prod,
      (WithLp.linearEquiv 2 ℝ _).finrank_eq, Module.finrank_prod,
      (WithLp.linearEquiv 2 ℝ (Fin P ⊕ Fin Q → ℂ)).finrank_eq, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex]
    ring

theorem ballVol_succ_sq (P Q : ℕ) (r : ℝ) (hr : 0 < r) :
    ballVol ((P + Q + 1) ^ 2) r = (2 : ℝ≥0∞) ^ (P + Q) *
      ((volume : Measure (ℝ × Sp P Q)).prod
        (volume : Measure (EuclideanSpace ℝ (Fin ((P + Q) ^ 2)))))
        {p | tanSq p.1 + ‖p.2‖ ^ 2 < r ^ 2} := by
  have hs : (√2 : ℝ) ≠ 0 := by positivity
  have hfin : Module.finrank ℝ (Sp P Q) = 2 * (P + Q) := by
    rw [Module.finrank_pi_fintype]; simp [Complex.finrank_real_complex]; ring
  have h0 : MeasurePreserving (fun y : Sp P Q => (√2 : ℝ) • y) volume
      (((2 : ℝ≥0∞) ^ (P + Q))⁻¹ • volume) := by
    refine ⟨by fun_prop, ?_⟩
    rw [Measure.map_addHaar_smul _ hs, hfin, pow_mul, Real.sq_sqrt (by norm_num),
      abs_of_pos (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_pow (by norm_num)]
    simp
  have hne : ((2 : ℝ≥0∞) ^ (P + Q)) ≠ 0 := by simp
  have hnt : ((2 : ℝ≥0∞) ^ (P + Q)) ≠ ⊤ := by simp
  haveI : SFinite (((2 : ℝ≥0∞) ^ (P + Q))⁻¹ • (volume : Measure (Sp P Q))) := inferInstance
  have h1 := ((MeasurePreserving.id (volume : Measure ℝ)).prod h0).prod (MeasurePreserving.id
      (volume : Measure (EuclideanSpace ℝ (Fin ((P + Q) ^ 2)))))
  have hm : MeasurableSet {p : (ℝ × Sp P Q) × EuclideanSpace ℝ (Fin ((P + Q) ^ 2)) |
      p.1.1 ^ 2 + ∑ i, ‖p.1.2 i‖ ^ 2 + ‖p.2‖ ^ 2 < r ^ 2} :=
    (isOpen_lt (by fun_prop) continuous_const).measurableSet
  have h2 := h1.measure_preimage hm.nullMeasurableSet
  rw [Measure.prod_smul_right, Measure.prod_smul_left, Measure.smul_apply,
    ← Measure.volume_eq_prod, prod_region_eq_ballVol P Q r hr, smul_eq_mul] at h2
  have h3 : {p : (ℝ × Sp P Q) × EuclideanSpace ℝ (Fin ((P + Q) ^ 2)) |
      tanSq p.1 + ‖p.2‖ ^ 2 < r ^ 2} =
      Prod.map (Prod.map id fun y : Sp P Q => (√2 : ℝ) • y) id ⁻¹'
      {p | p.1.1 ^ 2 + ∑ i, ‖p.1.2 i‖ ^ 2 + ‖p.2‖ ^ 2 < r ^ 2} := by
    ext p
    simp [tanSq, norm_smul, mul_pow, Finset.mul_sum, mul_add]
  rw [h3, h2, ← mul_assoc, ENNReal.mul_inv_cancel hne hnt, one_mul]

end GlobalTheory.GaugeQuot.BallProd
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.nearTerms_moderate_points_one_type_bound : GlobalTheory.FlagMeas.FlagMeasureBound → GlobalTheory.Dec.NearUnip → GlobalTheory.Deep.PtBound → ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ → 1 ≤ q → CountHyp B Cg n₀ d p q b → (∀ x, 1 / 2 ≤ least B.I x → GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d x = 0) ∧ ∀ (a : ℕ) (j : Fin a → ℕ), 1 ≤ a → (∀ i, 1 ≤ j i) → ∑ i, j i ≤ q → ∫⁻ x in {x | ∃ τ, HasType B.I x j τ} ∩ B.fund, {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x ∂(B.I.muA B.μf) ≤ ENNReal.ofReal (mainTerm B d * (2 * GlobalTheory.FlagMeas.kapBd B.I.E p q j * (2 * B.I.f * q * (11 * q * Real.log (bigX B b))) ^ a)) := by
  first | exact @GlobalTheory.NearType.near_terms_one_type | exact GlobalTheory.NearType.near_terms_one_type | (intros; apply GlobalTheory.NearType.near_terms_one_type <;> assumption)
end
