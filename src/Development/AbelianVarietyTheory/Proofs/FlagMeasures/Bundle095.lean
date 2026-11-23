module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardPrimitiveTuplesHermitianGramModUniformizer
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Formalism.HermitianLattices.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle090
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle017
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Formalism.LocalToGlobal.HermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle091
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Mathlib.Algebra.Module.Lattice.Full
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle092
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle077
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle083
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle047
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnipotent
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty
public import Formalism.LocalToGlobal.HermitianForms.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
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
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.card_primitive_tuples_hermitian_gram_mod_uniformizer : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ (n m j : ℕ), 2 * m + 3 ≤ n → 1 ≤ j → ∀ (Gm : Matrix (Fin m) (Fin m) E), IsHerm L Gm → IsIntM L Gm → ∀ (R : Finset E), (∀ u ∈ R, u ∈ L.O) → (∀ u ∈ L.O, ∃! w, w ∈ R ∧ ∃ c ∈ L.O, u - w = algebraMap F E ((ϖ : F) ^ j) * c) → ∀ N : ℕ, N = Set.ncard {x : Fin m → Fin n → E | (∀ a i, x a i ∈ R) ∧ (∃ y : Fin m → Fin n → E, (∀ a i, y a i ∈ L.O) ∧ ∀ a b, hf L 1 (x a) (y b) = if a = b then 1 else 0) ∧ ∀ a b, ∃ c ∈ L.O, hf L 1 (x b) (x a) - Gm a b = algebraMap F E ((ϖ : F) ^ j) * c} → (resQ ϖ : ℝ) ^ (j * (2 * n * m - m ^ 2)) ≤ 2 * N ∧ (N : ℝ) ≤ 2 * (resQ ϖ : ℝ) ^ (j * (2 * n * m - m ^ 2)) := by
  first | exact @GlobalTheory.GramCount.primitive_gram_count | exact GlobalTheory.GramCount.primitive_gram_count | (intros; apply GlobalTheory.GramCount.primitive_gram_count <;> assumption)
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.primitive_hermitian_sublattice_discriminant_generators : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ (L : Submodule (𝓞 K) V) (U : Submodule K V) (e : ℕ), IsIntLat h L → (∃ t : Finset V, t.card ≤ e ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) → IsIntLat (hRes h U) (latIn U L) ∧ IsIntLat (hRes h (perp h U)) (latIn (perp h U) L) ∧ discN (hRes h (perp h U)) (latIn (perp h U) L) ≤ discN (hRes h U) (latIn U L) * discN h L ∧ (∃ t : Finset ↥U, t.card ≤ (Module.finrank K (perp h U) + e) ∧ dual (hRes h U) (latIn U L) = (latIn U L) ⊔ Submodule.span (𝓞 K) (t : Set _)) := by
  first | exact @GlobalTheory.Mass.PrimDisc.main | exact GlobalTheory.Mass.PrimDisc.main | (intros; apply GlobalTheory.Mass.PrimDisc.main <;> assumption)
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.PrimCount

section
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_smul_mem (L : Submodule (𝓞 K) V) (hL : Submodule.IsFullLattice K L) (x : V) :
    ∃ r : 𝓞 K, r ≠ 0 ∧ r • x ∈ L :=
  _root_.GlobalTheory.SmulMemSpan.exists_smul_mem L hL x

theorem latIn_isLattice (L : Submodule (𝓞 K) V) (hL : Submodule.IsLattice K L) (U : Submodule K V) :
    Submodule.IsLattice K (latIn U L) := by
  refine ⟨?_, ?_⟩
  · refine Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars (𝓞 K)) U.injective_subtype ?_
    exact Submodule.FG.of_le hL.fg (Submodule.map_comap_le _ _)
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
theorem latIn_isFullLattice (L : Submodule (𝓞 K) V) (hL : Submodule.IsFullLattice K L)
    (U : Submodule K V) : Submodule.IsFullLattice K (latIn U L) := by
  let _ := latIn_isLattice L hL.toIsLattice U
  refine ⟨?_⟩
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨r, hr, hx⟩ := exists_smul_mem L hL (x : V)
  have hrK : algebraMap (𝓞 K) K r ≠ 0 := by simpa using hr
  have hx' : r • x ∈ latIn U L := hx
  have hmem : r • x ∈ Submodule.span K (latIn U L : Set U) := Submodule.subset_span hx'
  have hmem' := (Submodule.span K (latIn U L : Set U)).smul_mem
    (algebraMap (𝓞 K) K r)⁻¹ hmem
  rw [← algebraMap_smul K r x, smul_smul, inv_mul_cancel₀ hrK, one_smul] at hmem'
  exact hmem'
end

theorem one_le_rd (K : Type) [Field K] [NumberField K] : 1 ≤ 2 * vInv K := by
  have h : (1 : ℝ) ≤ |(discr K : ℝ)| := by
    have := Int.one_le_abs (discr_ne_zero K)
    exact_mod_cast this
  have := Real.one_le_rpow h (z := (1 : ℝ) / (2 * fDeg K)) (by positivity)
  unfold vInv
  linarith

theorem real_bound (a : ℝ) (ha : 1 ≤ a) (n k f : ℕ) (hn : 1 ≤ n) (hf : 0 < f) :
    (1 + 2 * Real.sqrt (a * (n : ℝ) ^ ((1 : ℝ) / (2 * f)))) ^ (2 * k * f) ≤
      (9 * a) ^ (k * f) * (n : ℝ) ^ ((k : ℝ) / 2) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hf' : (0 : ℝ) < f := by exact_mod_cast hf
  have h1 : 1 ≤ (n : ℝ) ^ ((1 : ℝ) / (2 * f)) := Real.one_le_rpow hn' (by positivity)
  have e : (n : ℝ) ^ ((k : ℝ) / 2) = ((n : ℝ) ^ ((1 : ℝ) / (2 * f))) ^ (k * f) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    push_cast
    field_simp
  rw [e, ← mul_pow, mul_assoc 2, pow_mul]
  set B := a * (n : ℝ) ^ ((1 : ℝ) / (2 * f)) with hB
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le ha h1
  have hs : 1 ≤ Real.sqrt B := Real.one_le_sqrt.2 hB1
  have hq : Real.sqrt B ^ 2 = B := Real.sq_sqrt (by linarith)
  refine pow_le_pow_left₀ (by positivity) ?_ _
  rw [mul_assoc, ← hB]
  nlinarith

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ L : Submodule (𝓞 K) V, IsIntLat h L → ∀ n : ℕ, 1 ≤ n → (((primSp h L 1 n).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((9 * (2 * vInv K)) ^ (Module.finrank K V * fDeg K) * (n : ℝ) ^ ((Module.finrank K V : ℝ) / 2)) ∧ (primSp h L 0 n).encard ≤ 1 := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hp L hL n hn
  constructor
  · set B : ℝ := (2 * vInv K) * (n : ℝ) ^ ((1 : ℝ) / (2 * fDeg K)) with hB
    have hrd := one_le_rd K
    have hB0 : 0 ≤ B := by positivity
    have hsub : primSp h L 1 n ⊆ (fun x : V => Submodule.span K {x}) ''
        {x : V | x ∈ L ∧ ∀ τ : K →+* ℂ, (τ (h x x)).re ≤ B} := by
      rintro U ⟨hU, hd⟩
      obtain ⟨x, hx, hx0, hxB⟩ := GlobalTheory.T.exists_short_vector_integralHermitianLattice_rank_one K U (hRes h U) hK ⟨fun x y => hs.eq x y⟩
        (fun τ x hx => hp τ x (by simpa using hx)) hU (latIn U L)
        ⟨latIn_isFullLattice L hL.1 U, fun x hx y hy => hL.2 x hx y hy⟩
      rw [hd] at hxB
      refine ⟨x, ⟨hx, hxB⟩, ?_⟩
      refine Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2 x.2) ?_
      rw [hU, finrank_span_singleton (by simpa using hx0)]
    have h1 := (Set.encard_le_encard hsub).trans (Set.encard_image_le _ _)
    refine le_trans (by exact_mod_cast h1) ((GlobalTheory.T.encard_shortVectors_le' K V h hK hs hp L hL B hB0).trans ?_)
    exact ENNReal.ofReal_le_ofReal (real_bound _ hrd n _ _ hn Fintype.card_pos)
  · rw [Set.encard_le_one_iff]
    rintro U W ⟨hU, -⟩ ⟨hW, -⟩
    rw [Submodule.finrank_eq_zero.1 hU, Submodule.finrank_eq_zero.1 hW]

end GlobalTheory.Mass.PrimCount
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.exists_wt_eq_mul_nu' : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), ∀ d0 : LocNG.Datum P, ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (d : LocNG.Datum P) Λ, S.IsTerm (c.dat d) Λ → LocNG.Datum.wt d0 d = κ * S.nu (c.dat d) := by
  first | exact @GlobalTheory.HL.CoordDatum.exists_wt_eq_mul_nu | exact GlobalTheory.HL.CoordDatum.exists_wt_eq_mul_nu | (intros; apply GlobalTheory.HL.CoordDatum.exists_wt_eq_mul_nu <;> assumption)
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.local_integers_iff_split_at_type_prime : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (gp : Fin 2 → ℕ) (G : GLoc F E cm.sig gp), (∀ i, (gp i).Prime) → (∀ i, SplitsIn E (gp i)) → ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (hv : (gp i : 𝓞 F) ∈ v.asIdeal) (x : E ⊗[F] v.adicCompletion F), x ∈ intV E v ↔ (G.sp i v hv x).1 ∈ v.adicCompletionIntegers F ∧ (G.sp i v hv x).2 ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.St.G.intV_iff_sp | exact GlobalTheory.St.G.intV_iff_sp | (intros; apply GlobalTheory.St.G.intV_iff_sp <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.amplitude_mass_eq_one_of_single_orbit : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (P : Submodule L.O S.V → Prop), (∃ Λ, S.IsTerm d Λ) → (∀ Λ Λ', S.IsTerm d Λ → S.IsTerm d Λ' → ∃ h ∈ S.St, Λ' = h • Λ) → (∀ Λ, S.IsTerm d Λ → P Λ ∧ S.mu Λ = 1 ∧ S.om d Λ = 1) → S.amp d P = 1 ∧ S.mass d P = 1 := by
  first | exact @GlobalTheory.HL.Frames.amp_mass_eq_one_of_one_orbit | exact GlobalTheory.HL.Frames.amp_mass_eq_one_of_one_orbit | (intros; apply GlobalTheory.HL.Frames.amp_mass_eq_one_of_one_orbit <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.encard_selfDual_sat_inf_W0_le_q_pow : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ C, S.IsCls C → ∀ p ∈ C, ∀ Mh Λ₀ : Submodule L.O S.V, S.Mof p.1 p.2 ≤ Mh → (({Λ : Submodule L.O S.V | IsSD L S.Hm Λ ∧ S.sat Λ = Mh ∧ Λ ⊓ S.W0.restrictScalars L.O = Λ₀}.encard : ℕ∞) : ℝ≥0∞) ≤ (S.q : ℝ≥0∞) ^ (2 * S.a.toNat * (2 * r + 2)) := by
  first | exact @GlobalTheory.HL.Gluing.gluing_count | exact GlobalTheory.HL.Gluing.gluing_count | (intros; apply GlobalTheory.HL.Gluing.gluing_count <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.StrongSt

theorem mat_step {K V : Type} [CommRing K] [AddCommGroup V] [Module K V] {m : ℕ} (v : Fin m → V)
    (n g' : V ≃ₗ[K] V) (s t : Matrix (Fin m) (Fin m) K) (hs : IsUnit s.det)
    (hn : ∀ j, n (v j) = ∑ i, s i j • v i) (hg : ∀ j, g' (v j) = ∑ i, t i j • v i) :
    ∀ j, (n⁻¹ * g') (v j) = ∑ i, (s⁻¹ * t) i j • v i := by
  have hw : ∀ i, n.symm (v i) = ∑ k, s⁻¹ k i • v k := by
    intro i
    apply n.injective

    rw [LinearEquiv.apply_symm_apply, map_sum]
    simp_rw [map_smul, hn, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have h1 : s * s⁻¹ = 1 := Matrix.mul_nonsing_inv s hs
    have : ∀ l, ∑ k, s⁻¹ k i * s l k = (s * s⁻¹) l i := by
      intro l; rw [Matrix.mul_apply]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    simp_rw [← Finset.sum_smul, this, h1, Matrix.one_apply, ite_smul, one_smul, zero_smul]
    simp
  intro j
  change n.symm (g' (v j)) = _

  rw [hg, map_sum]
  simp_rw [map_smul, hw, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => by congr 1; exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end GlobalTheory.HL.StrongSt

namespace GlobalTheory.HL.StrongSt

theorem bc_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {n m : ℕ}
    (a : Fin m → E) (x : Fin m → Fin n → E) :
    A.bc p (∑ i, a i • x i) = ∑ i, (A.loc p).ιE (a i) • A.bc p (x i) := by
  funext l

  simp [Places.bc, Finset.sum_apply, map_sum, map_mul]

theorem unit_of_pat {K : Type} [CommRing K] {m : ℕ} (P : Fin m → Fin m → Prop)
    (hP : ∀ i j, P i j → i < j) (s : Matrix (Fin m) (Fin m) K)
    (hs : ∀ i j, ¬ P i j → s i j = if i = j then 1 else 0) : IsUnit s.det := by
  have hup : s.BlockTriangular id := by
    intro i j hij
    have := hs i j (fun h => absurd (hP i j h) (not_lt.mpr (le_of_lt hij)))
    rw [this, if_neg (ne_of_gt (show j < i from hij))]
  rw [Matrix.det_of_upperTriangular hup]
  have : ∀ i, s i i = 1 := fun i => by rw [hs i i (fun h => absurd (hP i i h) (lt_irrefl _)), if_pos rfl]
  simp [this]

end GlobalTheory.HL.StrongSt

namespace GlobalTheory.HL.StrongSt

theorem strong_approx_stab : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ Λ : G.Lt, Submodule.IsFullLattice E Λ → ∀ c : ∀ p, ((A.loc p).Fp)ˣ, {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite → ∀ n : ∀ p, (G.S p).GLV, (∀ p, n p ∈ (G.S p).St) → {p | n p ∉ (G.S p).K0}.Finite → ∃ g ∈ G.St, ∀ p g', A.Ext p g g' → (n p)⁻¹ * g' ∈ (G.S p).K0 ∧ ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, (n p).symm (g' x) - x = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) • y := by
  intro F E _ _ _ _ _ sig A r k G Λ hΛ c₁ hc₁ n hnSt hnK
  let c : ∀ p, ((A.loc p).Fp)ˣ := fun p => if ((c₁ p : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp]) then c₁ p else 1
  have hcO : ∀ p, ((c p : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp]) := by
    intro p
    by_cases h : ((c₁ p : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp])
    · simp only [c, if_pos h]; exact h
    · simp only [c, if_neg h]; exact one_mem _
  have hc : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite := by
    refine hc₁.subset fun p hp => ?_
    rintro ⟨u, hu⟩
    have h : ((c₁ p : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp]) := hu ▸ (u : 𝒪[(A.loc p).Fp]).2
    exact hp ⟨u, by simp only [c, if_pos h]; exact hu⟩
  have hq : ∀ p, ∃ a ∈ 𝒪[(A.loc p).Fp], (c p : (A.loc p).Fp) = c₁ p * a := by
    intro p
    by_cases h : ((c₁ p : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp])
    · exact ⟨1, one_mem _, by simp only [c, if_pos h, mul_one]⟩
    · refine ⟨(c₁ p : (A.loc p).Fp)⁻¹, ?_, by simp only [c, if_neg h]; simp⟩
      have h' : ¬ valuation (A.loc p).Fp (c₁ p : (A.loc p).Fp) ≤ 1 := h
      show valuation (A.loc p).Fp (c₁ p : (A.loc p).Fp)⁻¹ ≤ 1
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 h'))
  have hclose := by
    first
    | exact GlobalTheory.T.frameMatrix_close_gives_lattice_close_integral A r k G Λ hΛ
    | exact GlobalTheory.T.frameMatrix_close_gives_lattice_close_integral A r k G Λ hΛ.toIsLattice
  obtain ⟨d, hd0, hdfin, hd⟩ := hclose
  choose s hsP hsf hsI using fun p => GlobalTheory.T.localCommonStabiliser_blockUnitriangular_on_frame A r k G p (n p) (hnSt p)
  let c' : ∀ p, ((A.loc p).Fp)ˣ := fun p => c p * Units.mk0 (d p) (hd0 p)
  have hc' : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c' p}.Finite := by
    refine (hc.union hdfin).subset fun p hp => ?_
    by_contra hq
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hq
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := hq
    exact hp ⟨u * v, by simp [c', hu, hv]⟩
  have hsI' : {p | ¬ IsIntM (A.L p) (s p)}.Finite := by
    refine (hnK.union G.c_unit).subset fun p hp => ?_
    by_contra hq
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hq
    exact hp (hsI p hq.2 hq.1)
  obtain ⟨t, htP, htc⟩ := GlobalTheory.T.pattern_unitriangular_strong_approximation A (r + 1) _ (fun i j h => h.1)
    (fun i j l hij hjl => ⟨hij.1.trans hjl.1, fun m h1 h2 => by
      by_cases hm : (m : ℕ) ≤ (j : ℕ)
      · exact hij.2 m h1 hm
      · exact hjl.2 m (by omega) h2⟩) c' hc' s hsP hsI'
  obtain ⟨g, hgSt, hgf⟩ := GlobalTheory.T.blockUnitriangular_rational_from_commonStabiliser A r k G t htP
  refine ⟨g, hgSt, fun p g' hg' => ?_⟩
  obtain ⟨g'', hg''St, hg''⟩ := hgSt p
  have hgg : g' = g'' := ((GlobalTheory.HL.RatExt.rational_extend A _ p).2.2.1 g).unique hg' hg''
  subst hgg
  have hh : (n p)⁻¹ * g' ∈ (G.S p).St := (G.S p).St.mul_mem ((G.S p).St.inv_mem (hnSt p)) hg''St
  have hgv : ∀ j, g' (A.bc p (G.f j)) = ∑ i, (t.map (A.loc p).ιE) i j • A.bc p (G.f i) := by
    intro j
    rw [hg' (G.f j), hgf j, bc_sum]
    rfl
  have hM := mat_step (fun j => A.bc p (G.f j)) (n p) g' (s p) (t.map (A.loc p).ιE)
    (unit_of_pat _ (fun i j h => h.1) (s p) (hsP p)) (hsf p) hgv
  obtain ⟨hK, hL⟩ := hd p (c p) _ _ (Units.ne_zero _) (hcO p) hh hM fun i j => by
    obtain ⟨o, ho, he⟩ := htc p i j
    exact ⟨o, ho, by rw [he]; simp [c']⟩
  refine ⟨hK, fun x hx => ?_⟩
  obtain ⟨y, hy, he⟩ := hL x hx
  obtain ⟨a, ha, hae⟩ := hq p
  have haO : algebraMap (A.loc p).Fp (A.loc p).Ep a ∈ (A.L p).O := by
    rw [(A.L p).O_def]
    exact isIntegral_algebraMap (R := 𝒪[(A.loc p).Fp]) (x := (⟨a, ha⟩ : 𝒪[(A.loc p).Fp]))
  refine ⟨(⟨_, haO⟩ : (A.L p).O) • y, Submodule.smul_mem _ _ hy, ?_⟩
  refine he.trans ?_
  rw [hae, map_mul, mul_smul]
  rfl

end GlobalTheory.HL.StrongSt
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.strong_approximation_unipotent_alt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ Λ : G.Lt, Submodule.IsFullLattice E Λ → ∀ c : ∀ p, ((A.loc p).Fp)ˣ, {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite → ∀ n : ∀ p, (G.S p).GLV, {p | n p • A.lat p Λ ≠ A.lat p Λ}.Finite → ((∀ p, n p ∈ (G.S p).N) → ∃ g ∈ G.N, ∀ p g', A.Ext p g g' → ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, (n p).symm (g' x) - x = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) • y) ∧ ((∀ p, n p ∈ (G.S p).N') → ∃ g ∈ G.N', ∀ p g', A.Ext p g g' → ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, (n p).symm (g' x) - x = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) • y) := by
  intro F E _ _ _ _ _ sig A r k G Λ hΛ c hc n hn
  letI := hΛ
  exact GlobalTheory.HL.SAN.strong_approximation_unipotent A r k G Λ inferInstance c hc n hn
end

section

open GlobalTheory.Diag.PG

namespace GlobalTheory.Diag.PG

theorem rankNums_rootDisc :
    ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C : ℝ, 0 < C → ∃ x0 : ℝ, ∀ x, x0 ≤ x →
      ∀ m f k lrd Del : ℝ, RankNums x eps CD m f k lrd Del →
        C * (m * (lrd - Real.log 2)) ≤ k ∧ C * (m ^ 3 * x ^ eps * lrd) ≤ k * Real.log k ^ 2 ∧
          lrd ≤ x ^ eps / C := by
  intro eps CD heps _ _ C hC
  set M : ℝ := max C 3 with hMdef
  have hM3 : 3 ≤ M := le_max_right _ _
  have hMC : C ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := by linarith
  refine ⟨max (max 1 C) (M ^ (2 / eps)), ?_⟩
  intro x hx m f k lrd Del h
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxC : C ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxM : M ^ (2 / eps) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  set X : ℝ := x ^ (eps / 2) with hXdef
  have hXM : M ≤ X := by
    have h1 : (M ^ (2 / eps)) ^ (eps / 2) ≤ x ^ (eps / 2) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hM0 _) hxM (by linarith)
    rw [← Real.rpow_mul hM0] at h1
    have h2 : 2 / eps * (eps / 2) = 1 := by field_simp
    rw [h2, Real.rpow_one] at h1
    exact h1
  have hYX : x ^ eps = X * X := by
    rw [hXdef, ← Real.rpow_add hx0]; ring_nf
  have hX3 : 3 ≤ X := le_trans hM3 hXM
  have hXC : C ≤ X := le_trans hMC hXM
  have hm1 : 1 ≤ m := le_trans (Real.one_le_rpow hx1 (by norm_num)) h.m_lo
  have hm4 : x ≤ m ^ 4 := by
    have h1 : (x ^ ((1 : ℝ) / 4)) ^ 4 = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
    calc x = (x ^ ((1 : ℝ) / 4)) ^ 4 := h1.symm
      _ ≤ m ^ 4 := pow_le_pow_left₀ (Real.rpow_nonneg hx0.le _) h.m_lo 4
  have hf : x ≤ f := le_trans hm4 h.mf
  have hf1 : 1 ≤ f := le_trans hx1 hf
  have hm0 : 0 ≤ m := by linarith
  have hm2 : 1 ≤ m ^ 2 := one_le_pow₀ hm1
  have hm3 : 1 ≤ m ^ 3 := one_le_pow₀ hm1
  have hm4' : 1 ≤ m ^ 4 := one_le_pow₀ hm1
  have hk : X * (m ^ 5 * f * (X * X)) ≤ k := by
    have := h.k_lo; rw [hYX] at this; exact this
  have hlrd : lrd ≤ X := h.lrd_hi
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlrd0 : 0 ≤ lrd := le_trans hlog2 h.lrd_lo
  have hX0 : 0 ≤ X := by linarith
  have hXX : X ≤ X * X := by nlinarith

  have hA : C ≤ m ^ 4 * f * (X * X) := by
    have h1 : 1 ≤ m ^ 4 * f := by nlinarith
    calc C ≤ X * X := le_trans hXC hXX
      _ = 1 * (X * X) := by ring
      _ ≤ m ^ 4 * f * (X * X) := mul_le_mul_of_nonneg_right h1 (by positivity)

  have hB : C ≤ m ^ 2 * f := by
    calc C ≤ x := hxC
      _ ≤ f := hf
      _ = 1 * f := by ring
      _ ≤ m ^ 2 * f := mul_le_mul_of_nonneg_right hm2 (by linarith)
  have hkX : X ≤ k := by
    have h1 : 1 ≤ m ^ 5 * f * (X * X) := by
      have : 1 ≤ m ^ 5 := one_le_pow₀ hm1
      have : 1 ≤ X * X := by nlinarith
      have : 1 ≤ m ^ 5 * f := by nlinarith
      nlinarith
    nlinarith
  have hk0 : 0 < k := by linarith
  refine ⟨?_, ?_, ?_⟩
  · calc C * (m * (lrd - Real.log 2)) ≤ C * (m * X) := by
          apply mul_le_mul_of_nonneg_left _ hC.le
          apply mul_le_mul_of_nonneg_left _ hm0
          linarith
      _ = (m * X) * C := by ring
      _ ≤ (m * X) * (m ^ 4 * f * (X * X)) := mul_le_mul_of_nonneg_left hA (by positivity)
      _ = X * (m ^ 5 * f * (X * X)) := by ring
      _ ≤ k := hk
  · have hlogk : 1 ≤ Real.log k := by
      rw [Real.le_log_iff_exp_le hk0]
      have := Real.exp_one_lt_d9
      linarith
    have hl2 : 1 ≤ Real.log k ^ 2 := one_le_pow₀ hlogk
    rw [hYX]
    calc C * (m ^ 3 * (X * X) * lrd) ≤ C * (m ^ 3 * (X * X) * X) := by
          apply mul_le_mul_of_nonneg_left _ hC.le
          apply mul_le_mul_of_nonneg_left hlrd (by positivity)
      _ = (m ^ 3 * (X * X) * X) * C := by ring
      _ ≤ (m ^ 3 * (X * X) * X) * (m ^ 2 * f) := mul_le_mul_of_nonneg_left hB (by positivity)
      _ = X * (m ^ 5 * f * (X * X)) := by ring
      _ ≤ k := hk
      _ = k * 1 := by ring
      _ ≤ k * Real.log k ^ 2 := mul_le_mul_of_nonneg_left hl2 hk0.le
  · rw [hYX, le_div_iff₀ hC]
    calc lrd * C ≤ X * C := mul_le_mul_of_nonneg_right hlrd hC.le
      _ ≤ X * X := mul_le_mul_of_nonneg_left hXC hX0

end GlobalTheory.Diag.PG
end

section

open Formalism.BasicNotions

namespace GlobalTheory

theorem hcParam_eq_weight_step_zero_add_rho : ∀ (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : Fin D.R.k), (((D.hcW u τ).u i : ℚ) : ℝ) = ((Formalism.L2.Forms.lamT u 0 τ).w (Fin.cast D.R.N_zero.symm i) : ℝ) + ((rhoVec D.R.k i : ℚ) : ℝ) := by
  intro D u τ i
  rw [Formalism.L2.Forms.lamT_zero]
  have h0 := (D.fm u).lam_eq 0 (Nat.zero_le _) τ (Fin.cast D.R.N_zero.symm i)
  rw [dite_eq_left (show (Fin.cast D.R.N_zero.symm i : ℕ) < D.R.k from i.2)] at h0
  have hq : ((D.hcW u τ).u i : ℚ) =
      (((D.fm u).lam 0 τ).w (Fin.cast D.R.N_zero.symm i) : ℚ) + rhoVec D.R.k i := by
    rw [h0, hcToWeightQ]
    simp
  rw [hq]
  push_cast
  ring

end GlobalTheory
end
