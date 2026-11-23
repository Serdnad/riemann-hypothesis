module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesVecReduceModUMulVec
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SndDualLiftAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemEisensteinFiltrationEqEisensteinPowMulDisc
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle106
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNonzeroIntertwiningMapFromUnitarySupercusp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantTestRepresentationTensorProduct
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle055
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle107
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle108
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace

@[expose] public section

section

noncomputable section

namespace GlobalTheory.BK

open PowerSeries

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]

theorem EIn_pow_eq_factorial_mul_Ediv (i : ℕ) :
    EIn l e (S O K e) ^ i = (i.factorial : S O K e) * ⟨Ediv K l e i, Ediv_mem_S l e i⟩ := by
  apply Subtype.ext
  have hf : (i.factorial : K) ≠ 0 := natCast_ne_zero' l i.factorial_ne_zero
  have hc : ((i.factorial : S O K e) : K⟦X⟧) = C (i.factorial : K) := by
    rw [map_natCast]; rfl
  simp only [SubmonoidClass.coe_pow, coe_EIn, Subalgebra.coe_mul, Ediv, hc]
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hf, map_one, one_mul]

theorem exists_uIn_pow_eq (j : ℕ) (hj : j ≤ l) : ∃ σ : S O K e, ∃ φ ∈ Fil O K l e j,
    uIn (S O K e) ^ (e * l) = (l : S O K e) ^ (l - j) * σ + φ := by
  have hu : uIn (S O K e) ^ e = EIn l e (S O K e) + -(l : S O K e) := by
    apply Subtype.ext
    simp [E]
  refine ⟨∑ i ∈ Finset.range j, EIn l e (S O K e) ^ i * (-1) ^ (l - i) * (l : S O K e) ^ (j - i) *
      (l.choose i : S O K e),
    ∑ i ∈ Finset.Ico j (l + 1), EIn l e (S O K e) ^ i * (-(l : S O K e)) ^ (l - i) *
      (l.choose i : S O K e), ?_, ?_⟩
  · refine Ideal.sum_mem _ fun i hi => ?_
    have hi' : j ≤ i := (Finset.mem_Ico.1 hi).1
    rw [EIn_pow_eq_factorial_mul_Ediv]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ediv_mem_Fil l e hi')))
  · rw [pow_mul, hu, add_pow, ← Finset.sum_range_add_sum_Ico _ (by omega : j ≤ l + 1),
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < j := Finset.mem_range.1 hi
    have h1 : l - i = (l - j) + (j - i) := by omega
    rw [neg_pow, h1, pow_add, pow_add]
    ring

theorem X_pow_smul_mem_l_pow_MM_add_FilMM (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι) (j : ℕ) (hj : j ≤ l)
    (w : Vec K a ι) (hw : w ∈ P.MM) : ∃ s ∈ P.MM, ∃ f ∈ P.FilMM j,
      (X : K⟦X⟧) ^ (e * l) • w = (l : K) ^ (l - j) • s + f := by
  obtain ⟨σ, φ, hφ, h⟩ := exists_uIn_pow_eq (O := O) (K := K) (l := l) (e := e) j hj
  refine ⟨σ • w, P.MM.smul_mem σ hw, φ • w, Submodule.smul_mem_smul hφ hw, ?_⟩
  have h2 : (X : K⟦X⟧) ^ (e * l) • w = (uIn (S O K e) ^ (e * l)) • w := by
    rw [Subalgebra.smul_def]
    simp
  have h3 : ((l : S O K e) ^ (l - j)) • (σ • w) = (l : K) ^ (l - j) • (σ • w) := by
    rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [h2, h, add_smul, mul_smul, h3]

end GlobalTheory.BK
end
end

section

open PowerSeries Filter Topology GlobalTheory.BK GlobalTheory.FilDiv

theorem _root_.GlobalTheory.T.mem_eisensteinFiltration_eq_eisenstein_pow_mul_disc : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (j : ℕ), ∀ φ : S O K e, φ ∈ Fil O K l e j → ∃ q ∈ Rpi (O := O) (K := K) l e, (φ : K⟦X⟧) = E K l e ^ j * q := by
  intro O K _ _ _ _ _ _ l e _ _ _ j φ hφ
  have filPre_divisible : ∀ {g : S O K e}, g ∈ FilPre O K l e j →
      ∃ q ∈ Rpi (O := O) (K := K) l e, (g : K⟦X⟧) = E K l e ^ j * q := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, hx⟩ := hx
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hi
      refine ⟨C (((m + j).factorial : K)⁻¹) * E K l e ^ m,
        mul_mem (HasK.C_mem _) (pow_mem (E_mem l e _) m), ?_⟩
      rw [hx, Ediv]; ring
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨q, hq, h⟩ := hx
      obtain ⟨q', hq', h'⟩ := hy
      exact ⟨q + q', add_mem hq hq', by rw [Subalgebra.coe_add, h, h', mul_add]⟩
    | smul c x _ hx =>
      obtain ⟨q, hq, h⟩ := hx
      exact ⟨c * q, mul_mem (S_le_R l e c.2) hq, by
        rw [smul_eq_mul, Subalgebra.coe_mul, h]; ring⟩
  have divisible_of_approximation : ∀ (j : ℕ) {ψ : K⟦X⟧}, ψ ∈ Rpi (O := O) (K := K) l e →
      (∀ n : ℕ, ∃ q ∈ Rpi (O := O) (K := K) l e,
        ∀ k, ‖coeff k (ψ - E K l e ^ j * q)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ n) →
      ∃ q ∈ Rpi (O := O) (K := K) l e, ψ = E K l e ^ j * q := by
    intro j ψ hψ H
    induction j generalizing ψ with
    | zero => exact ⟨ψ, hψ, by simp⟩
    | succ j ih =>
      have hQ := quotE_mem_Rpi l e hψ
      have key : ∀ n, ∃ q ∈ Rpi (O := O) (K := K) l e,
          (∀ k, ‖coeff k (quotE l e ψ - E K l e ^ j * q)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ n) ∧
          ∀ k, ‖coeff k (ψ - E K l e * quotE l e ψ)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ (n + 1) := by
        intro n
        obtain ⟨q, hq, hr⟩ := H (n + 1)
        have hrR : ψ - E K l e ^ (j + 1) * q ∈ Rpi (O := O) (K := K) l e :=
          sub_mem hψ (mul_mem (pow_mem (E_mem l e _) _) hq)
        generalize hr_def : ψ - E K l e ^ (j + 1) * q = r at hr hrR
        have hg : quotE l e ψ - E K l e ^ j * q - quotE l e r = 0 := by
          refine eq_zero_of_E_mul l e (sub_mem (sub_mem hQ (mul_mem (pow_mem (E_mem l e _) _) hq))
            (quotE_mem_Rpi l e hrR)) fun m => ?_
          have h1 := coeff_sub_E_mul_quotE l e hψ m
          have h2 := coeff_sub_E_mul_quotE l e hrR m
          have : E K l e * (quotE l e ψ - E K l e ^ j * q - quotE l e r) =
              (r - E K l e * quotE l e r) - (ψ - E K l e * quotE l e ψ) := by
            rw [← hr_def]; ring
          rw [this, map_sub, h1, h2, sub_zero]
        have hg' : quotE l e ψ - E K l e ^ j * q = quotE l e r := sub_eq_zero.1 hg
        have hrem : ψ - E K l e * quotE l e ψ = r - E K l e * quotE l e r := by
          rw [← hg', ← hr_def]; ring
        exact ⟨q, hq, fun k => by rw [hg']; exact norm_coeff_quotE_le l e hr k,
          fun k => by rw [hrem]; exact norm_coeff_rem_le l e hr k⟩
      choose qs hqs hsmall hrem using key
      obtain ⟨q, hq, hQ'⟩ := ih hQ fun n => ⟨qs n, hqs n, hsmall n⟩
      have hR0 : ψ - E K l e * quotE l e ψ = 0 := by
        ext k
        rw [map_zero]
        have hρ := pow_pos (rad_pos l (1 / (e : ℝ))) k
        have ht : Tendsto (fun n : ℕ => ‖(l : K)‖ ^ (n + 1)) atTop (𝓝 0) :=
          (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_l_lt_one l)).comp
            (tendsto_add_atTop_nat 1)
        have h0 : ‖coeff k (ψ - E K l e * quotE l e ψ)‖ * rad l (1 / e) ^ k ≤ 0 :=
          ge_of_tendsto' ht fun n => hrem n k
        exact norm_le_zero_iff.1 (le_of_mul_le_mul_right (by simpa using h0) hρ)
      refine ⟨q, hq, ?_⟩
      rw [sub_eq_zero] at hR0
      rw [hR0, hQ', pow_succ']; ring
  have hψ : (φ : K⟦X⟧) ∈ Rpi (O := O) (K := K) l e := S_le_R l e φ.2
  refine divisible_of_approximation j hψ fun n => ?_
  obtain ⟨g, hg, h, H⟩ := (mem_Fil l).1 hφ n
  obtain ⟨q, hq, hgq⟩ := filPre_divisible hg
  refine ⟨q, hq, fun k => ?_⟩
  have : (φ : K⟦X⟧) - E K l e ^ j * q = (l : K⟦X⟧) ^ n * h := by
    rw [H]; push_cast; rw [hgq]; ring
  rw [this]
  exact norm_coeff_pow_mul_le l e n h.2 k
end

section

noncomputable section

open Matrix GlobalTheory.SmGL GlobalTheory.PRep

namespace GlobalTheory.LocGL

section Rad

variable {R S : Type} [CommRing R] [CommRing S] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

theorem map_mem_unipRad_of_ringHom (f : R →+* S) {e : (Σ a, m a) ≃ n} {g : GL n R} (hg : g ∈ unipRad R e) :
    GeneralLinearGroup.map f g ∈ unipRad S e := by
  obtain ⟨h1, h2⟩ := mem_unipRad.1 hg
  refine mem_unipRad.2 ⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩
  · show f ((g : Matrix n n R) i j) = 0
    rw [mem_parab.1 h1 i j hij, map_zero]
  · show f ((g : Matrix n n R) _ _) = _
    rw [h2 a i j]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

end Rad

theorem isCuspidal_comp_generalLinearGroupMap {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k']
    [IsNonarchimedeanLocalField k'] (i : k ≃+* k') (hi : Continuous i.symm) {n : Type} [Fintype n]
    [DecidableEq n] {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V)
    (h : IsCuspidal π) : IsCuspidal (π.comp (GeneralLinearGroup.map (n := n) i.symm.toRingHom)) := by
  set M := GeneralLinearGroup.map (n := n) i.symm.toRingHom with hM
  have hc : Continuous M :=
    Units.continuous_iff.2 ⟨continuous_matrix fun a b => hi.comp (Units.continuous_val.matrix_elem a b),
      continuous_matrix fun a b => hi.comp (Units.continuous_coe_inv.matrix_elem a b)⟩
  refine ⟨fun v => (h.1 v).preimage hc, fun s d e he => ?_⟩
  have hmem : ∀ u ∈ unipRad k' e, M u ∈ unipRad k e := fun u hu => map_mem_unipRad_of_ringHom _ hu
  have hsurj : ∀ w ∈ unipRad k e, ∃ u ∈ unipRad k' e, M u = w := fun w hw =>
    ⟨GeneralLinearGroup.map i.toRingHom w, map_mem_unipRad_of_ringHom _ hw,
      Units.ext (Matrix.ext fun _ _ => i.symm_apply_apply _)⟩
  have hinj : Function.Injective M := fun x y hxy => Units.ext (Matrix.ext fun a b =>
    i.symm.injective (congrArg (fun g : GL n k => (g : Matrix n n k) a b) hxy))
  have hne : unipRad k e ≠ ⊥ := fun hb => he ((Subgroup.eq_bot_iff_forall _).2 fun u hu =>
    hinj ((((Subgroup.eq_bot_iff_forall _).1 hb) _ (hmem u hu)).trans (map_one M).symm))
  have h1 : twKer (π.comp M) (unipRad k' e) 1 = twKer π (unipRad k e) 1 := by
    unfold twKer
    congr 1
    ext w
    constructor
    · rintro ⟨u, v, rfl⟩
      exact ⟨⟨M u, hmem u u.2⟩, v, by simp⟩
    · rintro ⟨u, v, rfl⟩
      obtain ⟨u', hu', hu⟩ := hsurj u u.2
      exact ⟨⟨u', hu'⟩, v, by simp [hu]⟩
  exact Submodule.Quotient.subsingleton_iff.2 (h1 ▸ Submodule.Quotient.subsingleton_iff.1 (h.2 s d e hne))

end GlobalTheory.LocGL
end
end

section

open ValuativeRel

noncomputable section

namespace GlobalTheory.DZero.PsiM

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valueGroupIso_uniformizer :
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k (uniformizer k) = WithZero.exp (-1) := by
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have h0 : φ (uniformizer k) ≠ 0 := by simp
  apply le_antisymm
  · have : φ (uniformizer k) < φ 1 := φ.strictMono uniformizer_lt_one
    rw [map_one, ← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at this
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega
  · have : φ.symm (WithZero.exp (-1)) ≤ uniformizer k := by
      rw [le_uniformizer_iff, ← map_one φ.symm]
      exact φ.symm.strictMono (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
    simpa using φ.strictMono.monotone this

variable {k}

theorem ord_eq_one {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) : SmGL.ord k ϖ = 1 := by
  rw [SmGL.ord, hϖ, valueGroupIso_uniformizer, WithZero.log_exp]; rfl

end GlobalTheory.DZero.PsiM
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.JacStages

section Rel

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α : Type} [Fintype α] {β : α → Type} [∀ i, Fintype (β i)] [∀ i, LinearOrder (β i)]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {c : ∀ i, β i → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def relUnipD (f : ∀ i, (Σ j, c i j) ≃ m i) : Subgroup (Levi k m) :=
  Subgroup.pi Set.univ fun i => unipRad k (f i)

def relEmbD (f : ∀ i, (Σ j, c i j) ≃ m i) : (∀ i, Levi k (c i)) →* Levi k m :=
  MonoidHom.pi fun i => (leviEmb k (f i)).comp (Pi.evalMonoidHom (fun i => Levi k (c i)) i)

theorem relEmbD_apply (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ i, Levi k (c i)) (i : α) :
    relEmbD k f g i = leviEmb k (f i) (g i) := rfl

theorem relEmbD_mem_normalizer (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ i, Levi k (c i)) :
    relEmbD k f g ∈ Subgroup.normalizer (relUnipD k f : Set (Levi k m)) :=
  Subgroup.mem_normalizer_iff.2 fun u => forall₂_congr fun i _ =>
    Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer k (f i) (g i)) (u i)

def relDeltaHalfD (c : ∀ i, β i → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] :
    (∀ i, Levi k (c i)) →* ℂˣ :=
  ∏ i, (deltaHalf k (c i)).comp (Pi.evalMonoidHom (fun i => Levi k (c i)) i)

theorem relDeltaHalfD_apply (g : ∀ i, Levi k (c i)) :
    relDeltaHalfD k c g = ∏ i, deltaHalf k (c i) (g i) := by
  simp [relDeltaHalfD, MonoidHom.finsetProd_apply]

variable {k}

def relJacD (f : ∀ i, (Σ j, c i j) ≃ m i) (ρ : Representation ℂ (Levi k m) W) :
    Representation ℂ (∀ i, Levi k (c i)) (Jacquet ρ (relUnipD k f)) :=
  twist (jacquet ρ (relUnipD k f) (relEmbD k f) (relEmbD_mem_normalizer k f)) (relDeltaHalfD k c)⁻¹

theorem relJacD_mk (f : ∀ i, (Σ j, c i j) ≃ m i) (ρ : Representation ℂ (Levi k m) W)
    (g : ∀ i, Levi k (c i)) (v : W) :
    relJacD f ρ g (Submodule.Quotient.mk v) =
      (((relDeltaHalfD k c g)⁻¹ : ℂˣ) : ℂ) • Submodule.Quotient.mk (ρ (relEmbD k f g) v) := rfl

end Rel

section Flat

variable {s : ℕ} {t : Fin s → ℕ}

def refinePlace {n : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) {d' : ∀ a, Fin (t a) → ℕ}
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) :
    (Σ c : Fin (∑ a, t a), Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) ≃ Fin n :=
  (Equiv.sigmaCongrLeft (β := fun p : Σ a, Fin (t a) => Fin (d' p.1 p.2)) finSigmaFinEquiv.symm).trans
    ((Equiv.sigmaAssoc fun a b => Fin (d' a b)).trans ((Equiv.sigmaCongrRight e').trans e))

theorem refinePlace_apply {n : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) {d' : ∀ a, Fin (t a) → ℕ}
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (c : Fin (∑ a, t a))
    (i : Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) :
    refinePlace e e' ⟨c, i⟩ =
      e ⟨(finSigmaFinEquiv.symm c).1, e' _ ⟨(finSigmaFinEquiv.symm c).2, i⟩⟩ := rfl

def flatHom (Γ : ∀ a, Fin (t a) → Type) [∀ a b, Group (Γ a b)] :
    (∀ a b, Γ a b) →* ∀ c : Fin (∑ a, t a), Γ (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2 where
  toFun g c := g (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2
  map_one' := rfl
  map_mul' _ _ := rfl

theorem flatHom_apply (Γ : ∀ a, Fin (t a) → Type) [∀ a b, Group (Γ a b)] (g : ∀ a b, Γ a b)
    (c : Fin (∑ a, t a)) :
    flatHom Γ g c = g (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2 := rfl

theorem flatHom_surjective (Γ : ∀ a, Fin (t a) → Type) [∀ a b, Group (Γ a b)] :
    Function.Surjective (flatHom Γ) := by
  have h : ⇑(flatHom Γ) = (Equiv.piCongrLeft' (fun p : Σ a, Fin (t a) => Γ p.1 p.2) finSigmaFinEquiv) ∘
      (Equiv.piCurry fun a b => Γ a b).symm := rfl
  rw [h]
  exact (Equiv.surjective _).comp (Equiv.surjective _)

end Flat

section Pull

variable {G G' V W : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isSubquotient_of_comp {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (ψ : G' →* G)
    (hψ : Function.Surjective ψ) (h : IsSubquotient (σ.comp ψ) (ρ.comp ψ)) : IsSubquotient σ ρ := by
  obtain ⟨S, f, hf⟩ := h
  refine ⟨⟨S.toSubmodule, fun g v hv => ?_⟩, ⟨f.toLinearMap, fun g => ?_⟩, hf⟩
  · obtain ⟨g', rfl⟩ := hψ g
    exact S.apply_mem_toSubmodule g' hv
  · obtain ⟨g', rfl⟩ := hψ g
    exact f.isIntertwining' g'

theorem isSubquotient_of_equiv {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (φ : σ.Equiv ρ) :
    IsSubquotient σ ρ :=
  .of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective

end Pull

end GlobalTheory.JacStages
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

theorem _root_.GlobalTheory.T.exists_equiv_exteriorTensor_of_irreducible_prod_rep : ∀ (G H X Y : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (G × H) X) (ρ : Representation ℂ H Y), IsSmooth τ → τ.IsIrreducible → ρ.IsIrreducible → (∀ (M : Submodule ℂ (Y →ₗ[ℂ] X)), (∀ φ ∈ M, ∀ g v, φ (ρ g v) = τ (1, g) (φ v)) → Function.Injective (TensorProduct.lift M.subtype)) → (∃ ι : Y →ₗ[ℂ] X, ι ≠ 0 ∧ ∀ g v, ι (ρ g v) = τ (1, g) (ι v)) → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (σ : Representation ℂ G W), IsSmooth σ ∧ σ.IsIrreducible ∧ Nonempty (τ.Equiv (extTensor σ ρ)) := by
  first | exact @GlobalTheory.TensorFactor.exists_equiv_extTensor | exact GlobalTheory.TensorFactor.exists_equiv_extTensor | (intros; apply GlobalTheory.TensorFactor.exists_equiv_extTensor <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

theorem _root_.GlobalTheory.T.isUnitarisableComplexRep_of_supercuspidal_unitary_center : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (l : Module.Dual ℂ V), l ∈ smoothPart ρ.dual → l ≠ 0 → ρ.IsIrreducible → IsSupercuspidal ρ → (∀ z ∈ Subgroup.center G, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, ρ z v = c • v) → IsUnitarisable ρ := by
  first | exact @GlobalTheory.isUnitarisable_of_isSupercuspidal | exact GlobalTheory.isUnitarisable_of_isSupercuspidal | (intros; apply GlobalTheory.isUnitarisable_of_isSupercuspidal <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

theorem _root_.GlobalTheory.T.exists_nonzero_intertwiningMap_from_unitary_supercuspidal : ∀ (G W V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G W) (ρ : Representation ℂ G V) (p : π.IntertwiningMap ρ), IsSmooth π → IsSupercuspidal ρ → IsUnitarisable ρ → (∀ z ∈ Subgroup.center G, ∃ c : ℂ, ∀ w, π z w = c • w) → p ≠ 0 → ∃ ι : ρ.IntertwiningMap π, ι ≠ 0 := by
  first | exact @GlobalTheory.CuspBack.exists_back | exact GlobalTheory.CuspBack.exists_back | (intros; apply GlobalTheory.CuspBack.exists_back <;> assumption)
end

section

open GlobalTheory.JR GlobalTheory.JR.WeilProd

theorem _root_.GlobalTheory.T.isLocallyConstantTestRepresentation_tensorProduct : ∀ {G H X Y : Type} [Group G] [Group H] [TopologicalSpace X] [TopologicalSpace Y] (W₁ : G → (X → ℂ) → X → ℂ) (W₂ : H → (Y → ℂ) → Y → ℂ), IsTestRep W₁ → IsTestRep W₂ → IsTestRep (tensorRep W₁ W₂) ∧ ∀ f : X × Y → ℂ, IsTest f → (∀ u, IsTest (fun v => f (u, v))) ∧ ∀ h y, IsTest (fun u => W₂ h (fun v => f (u, v)) y) := by
  first | exact @GlobalTheory.JR.WeilProd.isTestRep_tensorRep | exact GlobalTheory.JR.WeilProd.isTestRep_tensorRep | (intros; apply GlobalTheory.JR.WeilProd.isTestRep_tensorRep <;> assumption)
end

section

open GlobalTheory.PMonE

theorem _root_.GlobalTheory.T.card_windowZeros_eq_integral_additiveSystem : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F) (lam π : Fin h → F), (∀ j, π j ≠ 0) → ∀ (L U : ℕ) (M : ℕ → Matrix (Fin h) (Fin h) F), (∀ z, gsum (p ^ h) (L + U) M z = 0 ↔ ∀ r, rowS p ϖ lam L U (winPt p π L z) r = 0) → Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam L U x r = 0} = Nat.card {z : Fin h → F // Integral z ∧ gsum (p ^ h) (L + U) M z = 0} := by
  first | exact @GlobalTheory.PMonE.winPt_card | exact GlobalTheory.PMonE.winPt_card | (intros; apply GlobalTheory.PMonE.winPt_card <;> assumption)
end

section

open GlobalTheory.PMonE

theorem _root_.GlobalTheory.T.card_windowZeros_inner_eq_shifted_outer : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h K : ℕ) (ϖ : F), ϖ ≠ 0 → 1 ≤ K → ∀ lam π : Fin h → F, Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖ ^ p ^ h) ∧ ∀ r, rowT p ϖ lam K x r = 0} = Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam (K - 1) (K + 1) x r = 0} := by
  first | exact @GlobalTheory.PMonE.win_inner | exact GlobalTheory.PMonE.win_inner | (intros; apply GlobalTheory.PMonE.win_inner <;> assumption)
end

section

open GlobalTheory.PMonE

theorem _root_.GlobalTheory.T.normalizedRowCoefficientMatrices_det_norm : ∀ (F : Type) [NormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F), ϖ ≠ 0 → ∀ lam π : Fin h → F, (∀ j, lam j ≠ 0) → (∀ j, π j ≠ 0) → Antitone (fun j => ‖lam j‖) → Orth p lam → ∀ L U : ℕ, ‖(coefB p ϖ lam π L U L).det‖ = 1 ∧ (coefB p ϖ lam π L U 0).det ≠ 0 := by
  first | exact @GlobalTheory.PMonE.coefB_det | exact GlobalTheory.PMonE.coefB_det | (intros; apply GlobalTheory.PMonE.coefB_det <;> assumption)
end
