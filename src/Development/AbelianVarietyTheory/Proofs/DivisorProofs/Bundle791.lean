module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsPrincipalIdealRingOfIsLocalization
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle767
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle248
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle590
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle394
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle592
public import Mathlib.FieldTheory.Finite.GaloisField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle753
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle540
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle757
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompositionAdmissibleFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivSqZeroExtPinchExistsExtendBasicOpen
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle756
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle758
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
open scoped CategoryTheory.Obj
open Classical

namespace GlobalTheory.DvrCentre

theorem exists_complete_dvr_centre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
    (M : RatModel o Ω) (z : M.Z), ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
    (_ : CharZero V) (ξ : Sp V ⟶ M.Z), IsAdicComplete (IsLocalRing.maximalIdeal V) V ∧
    ξ (IsLocalRing.closedPoint V) = z ∧ ∃ w, ξ w = genericPoint M.Z := by
  intro o Ω _ _ _ hA M z
  have hΩ : CharZero Ω := hA.char
  by_cases hz : z = genericPoint M.Z
  · subst hz
    have : CharZero (PowerSeries Ω) := charZero_of_injective_ringHom (PowerSeries.C_injective (R := Ω))
    have hc : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries Ω)) (PowerSeries Ω) := by
      first
      | infer_instance
      | (rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance)
    refine ⟨PowerSeries Ω, inferInstance, inferInstance, inferInstance, this,
      spMap (PowerSeries.C (R := Ω)) ≫ M.pt, hc, ?_, IsLocalRing.closedPoint _, ?_⟩
    · exact M.pt_apply _
    · exact M.pt_apply _
  · have : IsDedekindDomain o := hA.ded
    have : IsLocallyNoetherian M.Z := by
      have := M.lft
      exact LocallyOfFiniteType.isLocallyNoetherian M.s
    let S := M.Z.presheaf.stalk z
    have hS : CharZero S := (M.stalkHom z).charZero

    have hgen : M.Z.fromSpecStalk z (⊥ : PrimeSpectrum S) = genericPoint M.Z := by
      have h1 : genericPoint M.Z ∈ Set.range (M.Z.fromSpecStalk z) := by
        rw [Scheme.range_fromSpecStalk]
        exact genericPoint_specializes z
      obtain ⟨q, hq⟩ := h1
      have h2 : (⊥ : PrimeSpectrum S) ⤳ q := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
      have h3 := h2.map (M.Z.fromSpecStalk z).continuous
      rw [hq] at h3
      exact (h3.antisymm (genericPoint_specializes _)).eq
    have hne : (⊥ : Ideal S) ≠ IsLocalRing.maximalIdeal S := by
      intro e
      apply hz
      have : (⊥ : PrimeSpectrum S) = IsLocalRing.closedPoint S := PrimeSpectrum.ext e
      rw [← hgen, this, Scheme.fromSpecStalk_closedPoint]
    obtain ⟨O, _, hO, hO', hO'', φ, h1, h2⟩ :=
      GlobalTheory.exists_complete_discreteValuationRing_ker_eq (S := S) (⊥ : Ideal S) hne
    have hφ : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 h1
    have : CharZero O := charZero_of_injective_ringHom hφ
    refine ⟨O, inferInstance, hO, hO', this, spMap φ ≫ M.Z.fromSpecStalk z, hO'', ?_, (⊥ : PrimeSpectrum O), ?_⟩
    · refine (Scheme.Hom.comp_apply _ _ _).trans
        (Eq.trans (congrArg (M.Z.fromSpecStalk z) ?_) (Scheme.fromSpecStalk_closedPoint (x := z)))
      exact IsLocalRing.comap_closedPoint φ
    · refine (Scheme.Hom.comp_apply _ _ _).trans (Eq.trans (congrArg (M.Z.fromSpecStalk z) ?_) hgen)
      exact PrimeSpectrum.ext h1

end GlobalTheory.DvrCentre
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)

namespace GlobalTheory.QFam.QSz

section

variable {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} {N : ℕ}

theorem qAll_const {r : ℝ} {c : ℂ} (hc : Sz l lam r c) : QAll (Sz l lam r) N fun _ => c := by
  refine ⟨_, (GlobalTheory.T.hasQExpansionOfLevel_linear_operations N).2.2.2.1 c, fun n => ?_⟩
  by_cases h : n = 0
  · simpa only [h, if_true] using hc
  · simpa only [h, if_false] using (GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam).1 r

theorem qAll_mono {r s : ℝ} {f : ℍ → ℂ} (h : r ≤ s) (hf : QAll (Sz l lam r) N f) : QAll (Sz l lam s) N f := by
  obtain ⟨a, ha, hs⟩ := hf
  exact ⟨a, ha, fun n => (GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam).2.2.2.1 r s _ h (hs n)⟩

theorem qAll_add {r : ℝ} {f g : ℍ → ℂ} (hf : QAll (Sz l lam r) N f) (hg : QAll (Sz l lam r) N g) :
    QAll (Sz l lam r) N fun τ => f τ + g τ := by
  obtain ⟨a, ha, hs⟩ := hf
  obtain ⟨b, hb, ht⟩ := hg
  exact ⟨_, (GlobalTheory.T.hasQExpansionOfLevel_linear_operations N).1 f g a b ha hb, fun n => ((GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam).2.1 r _ _ (hs n) (ht n)).1⟩

theorem qAll_sub {r : ℝ} {f g : ℍ → ℂ} (hf : QAll (Sz l lam r) N f) (hg : QAll (Sz l lam r) N g) :
    QAll (Sz l lam r) N fun τ => f τ - g τ := by
  obtain ⟨a, ha, hs⟩ := hf
  obtain ⟨b, hb, ht⟩ := hg
  exact ⟨_, (GlobalTheory.T.hasQExpansionOfLevel_linear_operations N).2.1 f g a b ha hb, fun n => ((GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam).2.1 r _ _ (hs n) (ht n)).2⟩

theorem qAll_mul (hN : 0 < N) {r s : ℝ} {f g : ℍ → ℂ} (hf : QAll (Sz l lam r) N f) (hg : QAll (Sz l lam s) N g) :
    QAll (Sz l lam (r + s)) N fun τ => f τ * g τ := by
  obtain ⟨a, ha, hs⟩ := hf
  obtain ⟨b, hb, ht⟩ := hg
  refine ⟨_, GlobalTheory.T.hasQExpansionOfLevel_mul_of_pos_level N f g a b hN ha hb, fun n => ?_⟩
  exact (GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam).2.2.2.2.2 _ _ _ (fun p : ℕ × ℕ => a p.1 * b p.2)
    fun p _ => (GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam).2.2.1 r s _ _ (hs _) (ht _)

theorem qAll_one : QAll (Sz l lam 0) N fun _ => 1 :=
  qAll_const (by simpa using (GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam).2.2.2.2.1 1)

theorem qAll_pow (hN : 0 < N) {r : ℝ} {f : ℍ → ℂ} (k : ℕ) (hf : QAll (Sz l lam r) N f) :
    QAll (Sz l lam (k * r)) N fun τ => f τ ^ k := by
  induction k with
  | zero => simpa using (qAll_one : QAll (Sz l lam 0) N fun _ => 1)
  | succ k ih =>
    have h := qAll_mul hN ih hf
    have e : ((k + 1 : ℕ) : ℝ) * r = k * r + r := by push_cast; ring
    rw [e]
    simpa only [pow_succ] using h

theorem qAll_sum {κ : Type} (t : Finset κ) {r : ℝ} {f : κ → ℍ → ℂ} (hf : ∀ k ∈ t, QAll (Sz l lam r) N (f k)) :
    QAll (Sz l lam r) N fun τ => ∑ k ∈ t, f k τ := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (qAll_const ((GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam).1 r) : QAll (Sz l lam r) N fun _ => 0)
  | insert k t hk ih =>
    simp only [Finset.sum_insert hk]
    exact qAll_add (hf k (Finset.mem_insert_self k t)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem qAll_prod (hN : 0 < N) {κ : Type} (t : Finset κ) {r : κ → ℝ} {f : κ → ℍ → ℂ}
    (hf : ∀ k ∈ t, QAll (Sz l lam (r k)) N (f k)) :
    QAll (Sz l lam (∑ k ∈ t, r k)) N fun τ => ∏ k ∈ t, f k τ := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (qAll_one : QAll (Sz l lam 0) N fun _ => 1)
  | insert k t hk ih =>
    simp only [Finset.sum_insert hk, Finset.prod_insert hk]
    exact qAll_mul hN (hf k (Finset.mem_insert_self k t)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

end

theorem qAll_sz_ring : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∀ (N : ℕ), 0 < N → (∀ (r : ℝ) (c : ℂ), Sz l lam r c → QAll (Sz l lam r) N fun _ => c) ∧ (∀ (r s : ℝ) f, r ≤ s → QAll (Sz l lam r) N f → QAll (Sz l lam s) N f) ∧ (∀ (r : ℝ) f g, QAll (Sz l lam r) N f → QAll (Sz l lam r) N g → (QAll (Sz l lam r) N fun τ => f τ + g τ) ∧ QAll (Sz l lam r) N fun τ => f τ - g τ) ∧ (∀ (r s : ℝ) f g, QAll (Sz l lam r) N f → QAll (Sz l lam s) N g → QAll (Sz l lam (r + s)) N fun τ => f τ * g τ) ∧ (∀ (r : ℝ) f (k : ℕ), QAll (Sz l lam r) N f → QAll (Sz l lam (k * r)) N fun τ => f τ ^ k) ∧ (∀ (κ : Type) (t : Finset κ) (r : ℝ) (f : κ → ℍ → ℂ), (∀ k ∈ t, QAll (Sz l lam r) N (f k)) → QAll (Sz l lam r) N fun τ => ∑ k ∈ t, f k τ) ∧ (∀ (κ : Type) (t : Finset κ) (r : κ → ℝ) (f : κ → ℍ → ℂ), (∀ k ∈ t, QAll (Sz l lam (r k)) N (f k)) → QAll (Sz l lam (∑ k ∈ t, r k)) N fun τ => ∏ k ∈ t, f k τ) :=
  fun _ _ _ _ hN => ⟨fun _ _ h => qAll_const h, fun _ _ _ h hf => qAll_mono h hf,
    fun _ _ _ hf hg => ⟨qAll_add hf hg, qAll_sub hf hg⟩, fun _ _ _ _ hf hg => qAll_mul hN hf hg,
    fun _ _ k hf => qAll_pow hN k hf, fun _ t _ _ hf => qAll_sum t hf, fun _ t _ _ hf => qAll_prod hN t hf⟩

end GlobalTheory.QFam.QSz
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.isInCharacterIsotypicPart_self : ∀ (G : Type) [Group G] [Finite G] (Y : G → ℂ), IsChar ℂ ℂ Y → Kills Y Y := by
  first | (exact @GlobalTheory.Shin.kills_self) | (exact GlobalTheory.Shin.kills_self) | (intros; apply GlobalTheory.Shin.kills_self  <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.twisted_restricted_character_in_isotypic_part : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), ∀ (χ : G ⋊[φ] Γ → ℂ) (Y : G → ℂ), IsChar ℂ ℂ χ → IsIrrChar ℂ ℂ (fun g => χ (inl g)) → IsChar ℂ ℂ Y → ∑ᶠ g, χ (inl g) * star (Y g) ≠ 0 → Kills (fun δ => χ (inl δ * inr s)) Y := by
  first | (exact @GlobalTheory.Shin.kills_twist_of_pair_ne_zero) | (exact GlobalTheory.Shin.kills_twist_of_pair_ne_zero) | (intros; apply GlobalTheory.Shin.kills_twist_of_pair_ne_zero  <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

namespace GlobalTheory.WpFam.ExpansionIntegral

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (N : ℕ) [NeZero N] (M : ℕ)
    (x : Fin 2 → ZMod N), ¬ l ∣ M → M • x = 0 → x ≠ 0 →
    QAll (Sz l lam 0) N (wB N x) ∧ QAll (Sz l lam 0) N (wpd N x) := by
  intro l hl lam N _ M x hM hx hx0
  have hpos : 0 < M := Nat.pos_of_ne_zero fun h => hM (h ▸ dvd_zero l)
  have hpow : ∀ e : ℕ, ¬ l ∣ M ^ e := fun e h => hM (hl.out.dvd_of_dvd_pow h)
  have hsz := (GlobalTheory.T.algebraicValuationAtLeast_basic_properties l lam).1
  refine ⟨⟨cB N x, GlobalTheory.T.weierstrass_division_value_q_expansion N x hx0, fun k => hsz (M ^ 2) _ (hpow 2) ?_⟩,
    ⟨cD N x, GlobalTheory.T.hasQExpansion_normalizedDerivWeierstrassPTorsion N x, fun k => hsz (M ^ 3) _ (hpow 3) ?_⟩⟩
  · rw [Nat.cast_pow]
    exact (GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients N M x k hpos hx).1
  · rw [Nat.cast_pow]
    exact (GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients N M x k hpos hx).2.1

end GlobalTheory.WpFam.ExpansionIntegral
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

theorem _root_.GlobalTheory.T.weierstrassP_torsion_isModularFamily : ∀ (N : ℕ) [NeZero N], IsFam (vact N) 2 (wp N) ∧ IsFam (vact N) 3 (wpd N) := by
  first | exact @GlobalTheory.WpFam.isFam_wp_wpd | exact GlobalTheory.WpFam.isFam_wp_wpd | (intros; apply GlobalTheory.WpFam.isFam_wp_wpd <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem deg_of_forall₂ {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) {L₁ L₂ : List (ℕ × ℕ)}
    (h : List.Forall₂ (fun p p' : ℕ × ℕ => p.1 = p'.1 ∧ cusp θ p.1 p.2 = cusp θ p.1 p'.2) L₁ L₂) :
    deg L₁ = deg L₂ := by
  induction h with
  | nil => rfl
  | cons hab _ ih =>
    simp only [deg, List.map_cons, List.sum_cons] at ih ⊢
    rw [hab.1, ih]

theorem J_congr_forall₂ {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) {L₁ L₂ : List (ℕ × ℕ)}
    (h : List.Forall₂ (fun p p' : ℕ × ℕ => p.1 = p'.1 ∧ cusp θ p.1 p.2 = cusp θ p.1 p'.2) L₁ L₂) :
    J θ L₁ = J θ L₂ := by
  induction h with
  | nil => rfl
  | @cons a b l₁ l₂ hab hl ih =>
    funext n
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    obtain ⟨h1, h2⟩ := hab
    simp only at h1 h2
    subst h1
    rw [J_cons, J_cons, ih, deg_of_forall₂ θ hl]
    simp only [h2]

end GlobalTheory.Shin

namespace GlobalTheory.Shin

theorem forall₂_flatMap_of {α β : Type} (R : β → β → Prop) (L : List α) (f g : α → List β)
    (h : ∀ p ∈ L, List.Forall₂ R (f p) (g p)) : List.Forall₂ R (L.flatMap f) (L.flatMap g) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.flatMap_cons]
    exact List.rel_append (h a (by simp)) (ih fun p hp => h p (by simp [hp]))

theorem cusp_mul_card_pow (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F']
    (θ : AlgebraicClosure F' →* ℂ) (m K : ℕ) :
    cusp θ m (K * Nat.card F ^ Module.finrank F F') = cusp θ m K := by
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  letI := Fintype.ofFinite F
  letI := Fintype.ofFinite F'
  haveI : CharP F (ringChar F) := ringChar.charP F
  obtain ⟨r, hp, hcard⟩ := FiniteField.card F (ringChar F)
  have hchar : ringChar F' = ringChar F := (Algebra.ringChar_eq F F').symm
  have hq : Nat.card F = ringChar F' ^ (r : ℕ) := by rw [Nat.card_eq_fintype_card, hcard, hchar]
  funext x
  have key := GlobalTheory.T.cuspidalCharacterGLFiniteField_frobenius_pow F' θ (RingEquiv.refl F') (r * Module.finrank F F') (fun y => by
    rw [pow_mul, ← hq, Nat.card_eq_fintype_card, ← Module.card_eq_pow_finrank, FiniteField.pow_card]
    rfl) m K x
  rw [hq, ← pow_mul, ← key]
  congr 1

end GlobalTheory.Shin

namespace GlobalTheory.Shin

theorem J_liftL_galAct_frob (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F']
    (θ : AlgebraicClosure F' →* ℂ) [Fintype F] (L : List (ℕ × ℕ)) (n : ℕ)
    (hn : n = deg (liftL (Nat.card F) (Module.finrank F F') L)) (x : GL (Fin n) F') :
    J θ (liftL (Nat.card F) (Module.finrank F F') L) n
      (galAct F F' n (FiniteField.frobeniusAlgEquivOfAlgebraic F F') x) =
      J θ (liftL (Nat.card F) (Module.finrank F F') L) n x := by
  haveI : CharP F (ringChar F) := ringChar.charP F
  obtain ⟨r, hp, hcard⟩ := FiniteField.card F (ringChar F)
  have hchar : ringChar F' = ringChar F := (Algebra.ringChar_eq F F').symm
  have hq : Nat.card F = ringChar F' ^ (r : ℕ) := by rw [Nat.card_eq_fintype_card, hcard, hchar]
  set q := Nat.card F with hqdef
  set l := Module.finrank F F' with hldef
  have hl : 0 < l := Module.finrank_pos
  obtain ⟨l', hl'⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  have key := GlobalTheory.T.harishChandraProductCuspidalGL_frobenius_pow F' θ (FiniteField.frobeniusAlgEquivOfAlgebraic F F').toRingEquiv r (fun y => by
    rw [← hq]
    show (FiniteField.frobeniusAlgEquivOfAlgebraic F F') y = _
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, hqdef, Nat.card_eq_fintype_card]) (liftL q l L) n x
  rw [galAct_apply]
  refine (key.trans ?_)
  rw [← hq]

  set R : List (ℕ × ℕ) := L.flatMap fun p =>
    (List.range l').map (fun i => (p.1 / l, p.2 * q ^ (i + 1))) ++ [(p.1 / l, p.2)] with hR
  have hF : List.Forall₂ (fun p p' : ℕ × ℕ => p.1 = p'.1 ∧ cusp θ p.1 p.2 = cusp θ p.1 p'.2)
      ((liftL q l L).map fun p => (p.1, p.2 * q)) R := by
    rw [liftL, List.map_flatMap, hR]
    apply forall₂_flatMap_of
    intro p _
    rw [hl', List.range_succ, List.map_append, List.map_append]
    simp only [List.map_map, List.map_cons, List.map_nil]
    refine List.rel_append ?_ ?_
    · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
      intro z _
      refine ⟨rfl, ?_⟩
      simp only [Function.comp_apply, pow_succ, mul_assoc]
    · refine List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil
      simp only [Function.comp_apply]
      rw [mul_assoc, ← pow_succ, ← hl']
      exact cusp_mul_card_pow F F' θ _ _
  have hP : R.Perm (liftL q l L) := by
    rw [liftL, hR]
    apply List.Perm.flatMap_left
    intro p _
    rw [hl', List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, pow_zero, mul_one]
    refine List.perm_append_comm.trans ?_
    simp [Function.comp_def, ← hl']
  have hdeg : deg R = deg (liftL q l L) := by
    unfold deg
    exact (hP.map Prod.fst).sum_eq
  rw [J_congr_forall₂ θ hF]
  exact ((GlobalTheory.T.harishChandraProductCuspidalGL_list_properties F' θ).2.2 R (liftL q l L) n (hn.trans hdeg.symm) hP) ▸ rfl

end GlobalTheory.Shin

namespace GlobalTheory.Shin

theorem J_liftL_galAct : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (θ : AlgebraicClosure F' →* ℂ)
    (t : F' ≃ₐ[F] F') (L : List (ℕ × ℕ)) (n : ℕ), n = deg (liftL (Nat.card F) (Module.finrank F F') L) →
    ∀ x : GL (Fin n) F', J θ (liftL (Nat.card F) (Module.finrank F F') L) n (galAct F F' n t x) =
      J θ (liftL (Nat.card F) (Module.finrank F F') L) n x := by
  intro F F' _ _ _ _ θ t L n hn
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  letI := Fintype.ofFinite F
  obtain ⟨i, rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F F').2 t
  suffices h : ∀ k : ℕ, ∀ x : GL (Fin n) F',
      J θ (liftL (Nat.card F) (Module.finrank F F') L) n
        (galAct F F' n (FiniteField.frobeniusAlgEquivOfAlgebraic F F' ^ k) x) =
      J θ (liftL (Nat.card F) (Module.finrank F F') L) n x from h i.1
  intro k
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [pow_succ, map_mul, MulAut.mul_apply, ih]
    exact J_liftL_galAct_frob F F' θ L n hn x

end GlobalTheory.Shin
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.exists_section_of_large_adelic_degree : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∃ γ : ℕ, ∀ (n : ℕ) (g : Place k F → Matrix (Fin n) (Fin n) F), admitted g → (n : ℤ) * γ < deg g → ∃ p : Fin n → F, p ≠ 0 ∧ ∀ (v : Place k F) (i : Fin n), v.1 ((g v).mulVec p i) ≤ 1 := by
  first | exact @GlobalTheory.Nef.exists_section_of_large_deg | exact GlobalTheory.Nef.exists_section_of_large_deg | (intros; apply GlobalTheory.Nef.exists_section_of_large_deg <;> assumption)
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.iwasawa_decomposition_admissible_family : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (r : ℕ) (g : Place k F → Matrix (Fin (r + 1)) (Fin (r + 1)) F), admitted g → ∀ x : Fin (r + 1) → F, x ≠ 0 → ∃ (h : Matrix (Fin (r + 1)) (Fin (r + 1)) F) (u : Place k F → Matrix (Fin (r + 1)) (Fin (r + 1)) F), h.det ≠ 0 ∧ (∀ v, Unimod v (u v)) ∧ (∀ (v : Place k F) (i : Fin r), (u v * g v * h) i.succ 0 = 0) ∧ admitted (fun v => u v * g v * h) ∧ admitted (fun v => (u v * g v * h).submatrix Fin.succ Fin.succ) ∧ deg g = degLine g x + deg (fun v => (u v * g v * h).submatrix Fin.succ Fin.succ) ∧ ∑ᶠ v, ord v ((u v * g v * h) 0 0) = degLine g x ∧ ∀ b : ℝ, LinesLE g b → LinesLE (fun v => u v * g v * h) b := by
  first | exact @GlobalTheory.iwasawa_family | exact GlobalTheory.iwasawa_family | (intros; apply GlobalTheory.iwasawa_family <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.trivSqZeroExt_pinch_exists_extend_basicOpen : ∀ (R : Type) [CommRing R] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M), IsSum β (algebraMap R B) id → ∀ (X : Scheme.{0}) (x : Sp R ⟶ X) (z : Sp (TrivSqZeroExt B M) ⟶ X), spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z = spMap (algebraMap R B) ≫ x → ∀ (s : Γ((Sp (TrivSqZeroExt R M)), ⊤)) (U : X.affineOpens), spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s ≤ x ⁻¹ᵁ U.1 → ∃ g : ((Sp (TrivSqZeroExt R M)).basicOpen s).toScheme ⟶ X, (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl ≫ g = (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s).ι ≫ x ∧ (spMap β).resLE _ _ le_rfl ≫ g = (spMap β ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s).ι ≫ z := by
  first | exact @GlobalTheory.Pinch.exists_extend_basicOpen | exact GlobalTheory.Pinch.exists_extend_basicOpen | (intros; apply GlobalTheory.Pinch.exists_extend_basicOpen <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.tateTwistOne_sections_eq_rootsOfUnity : ∀ (q : ℕ) [NeZero q], ∃ e : ∀ (C : Type) [CommRing C], IsUnit (q : C) → (onRings (tw q 1)).obj (CommRingCat.of C) ≃+ Additive (rootsOfUnity q C), ∀ (C D : Type) [CommRing C] [CommRing D] (φ : C →+* D) (hC : IsUnit (q : C)) (hD : IsUnit (q : D)) (x : (onRings (tw q 1)).obj (CommRingCat.of C)), ((Additive.toMul (e D hD (((onRings (tw q 1)).map (CommRingCat.ofHom φ)).hom x)) : rootsOfUnity q D) : Dˣ) = Units.map φ.toMonoidHom ((Additive.toMul (e C hC x) : rootsOfUnity q C) : Cˣ) := by
  first | (exact @GlobalTheory.EtC.tw_one_mu) | (exact GlobalTheory.EtC.tw_one_mu) | (intros; apply GlobalTheory.EtC.tw_one_mu  <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.jacobianDet_isFrameOn_canonicalWeight : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → A.IsFrameOn A.kap U (jdet A z) := by
  first | exact @GlobalTheory.OTY.jdet_isFrameOn_kap | exact GlobalTheory.OTY.jdet_isFrameOn_kap | (intros; apply GlobalTheory.OTY.jdet_isFrameOn_kap <;> assumption)
end
