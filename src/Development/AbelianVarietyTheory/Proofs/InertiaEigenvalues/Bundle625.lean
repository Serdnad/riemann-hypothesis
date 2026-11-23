module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsGenIsUnitSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltWittEqZeroOfPrimeMulEqZero
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InstTameDescentExponentDataPadicThree
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle307
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityWittTiltAinf
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittTwistInvariantBasisChange
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.ResidueUnitCoeff

theorem neZero_of_piSys {l : ℕ} [Fact l.Prime] {e : ℕ} (ϖ : PiSys l e) : NeZero e := by
  refine ⟨fun he => ?_⟩
  subst he
  have h := ϖ.seq_zero
  rw [pow_zero, eq_neg_iff_add_eq_zero, add_comm] at h
  exact Nat.cast_add_one_ne_zero l h

theorem exists_bound {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ c : O, ‖algebraMap O K c‖ < 1 → ‖algebraMap O K c‖ ≤ ρ := by
  have : IsNoetherianRing O := isNoetherian_of_tower ℤ_[l] inferInstance
  let m : Ideal O :=
    { carrier := {c | ‖algebraMap O K c‖ < 1}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_add (f := _)] at *
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx hy)
      zero_mem' := by simp
      smul_mem' := fun r x hx => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at *
        exact (mul_le_of_le_one_left (norm_nonneg _) (norm_algebraMap_le r)).trans_lt hx }
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian m : m.FG)
  refine ⟨(s.sup fun g => ‖algebraMap O K g‖₊ : NNReal), NNReal.coe_nonneg _, ?_, fun c hc => ?_⟩
  · have : s.sup (fun g => ‖algebraMap O K g‖₊) < 1 := by
      refine (Finset.sup_lt_iff zero_lt_one).2 fun g hg => ?_
      have : g ∈ m := hs ▸ Ideal.subset_span hg
      exact (by exact_mod_cast this : ‖algebraMap O K g‖ < 1)
    exact_mod_cast this
  · have key : ∀ c ∈ Submodule.span O (s : Set O),
        ‖algebraMap O K c‖ ≤ (s.sup fun g => ‖algebraMap O K g‖₊ : NNReal) := by
      intro c hc'
      induction hc' using Submodule.span_induction with
      | mem x hx =>
        exact_mod_cast Finset.le_sup (f := fun g => ‖algebraMap O K g‖₊) hx
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add (f := _)]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
      | smul r x _ hx =>
        rw [smul_eq_mul, map_mul, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (norm_algebraMap_le r)).trans hx
    exact key c (by rw [hs]; exact hc)

end GlobalTheory.ResidueUnitCoeff

namespace GlobalTheory.ResidueUnitCoeff

theorem norm_coeff_pow_le {K : Type} [NormedField K] [IsUltrametricDist K] {f : K⟦X⟧} {ρ : ℝ}
    (h0 : 0 ≤ ρ) (hf : ∀ n, ‖coeff n f‖ ≤ ρ) (m n : ℕ) : ‖coeff n (f ^ m)‖ ≤ ρ ^ m := by
  induction m generalizing n with
  | zero => rw [pow_zero, pow_zero, coeff_one]; split_ifs <;> simp
  | succ m ih =>
    rw [pow_succ, pow_succ]
    simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp)
      (pow_nonneg h0 m) h0 (f := f ^ m) (g := f) (by simpa using ih) (by simpa using hf) n

theorem exists_norm_coeff_eq_one : ∀ {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {S : Type} [Fintype S] (y : S → ZMod a → A O K) (c : S → OW l O) (h : ∑ s, c s * inclO l O (ϖ.iTot t K (y s)) = 1) (τ : ZMod a), ∃ s k, ‖coeff k (y s τ : K⟦X⟧)‖ = 1 := by
  intro l _ a _ e O K _ _ _ _ _ _ _ _ _ t ϖ S _ y c h τ
  have := neZero_of_piSys ϖ
  by_contra hne
  push_neg at hne
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := exists_bound (l := l) (O := O) (K := K)
  have hco : ∀ s k, ‖coeff k (y s τ : K⟦X⟧)‖ ≤ ρ := fun s k => by
    obtain ⟨o, ho⟩ := (IsUnitBall.mem_range_iff (O := O) _).2 (mem_A.1 (y s τ).2 k)
    have h1 : ‖coeff k (y s τ : K⟦X⟧)‖ < 1 := lt_of_le_of_ne (mem_A.1 (y s τ).2 k) (hne s k)
    rw [← ho] at h1 ⊢
    exact hρ o h1
  have hl0 : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] K)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hlpos : 0 < ‖(l : K)‖ := norm_pos_iff.2 hl0
  obtain ⟨N0, hN0⟩ := exists_pow_lt_of_lt_one hlpos hρ1
  set N := N0 + 1 with hN
  have hρN : ρ ^ N ≤ ‖(l : K)‖ :=
    (pow_le_pow_of_le_one hρ0 hρ1.le (Nat.le_succ N0)).trans hN0.le
  have hzmem : ∀ s, C (l : K)⁻¹ * (y s τ : K⟦X⟧) ^ N ∈ A O K := fun s n => by
    rw [coeff_C_mul, norm_mul, norm_inv, inv_mul_le_iff₀ hlpos, mul_one]
    exact (norm_coeff_pow_le hρ0 (hco s) N n).trans hρN
  let z : S → A O K := fun s => ⟨_, hzmem s⟩
  have hz : ∀ s, y s τ ^ N = (l : A O K) * z s := fun s => Subtype.ext (by
    simp only [SubmonoidClass.coe_pow, MulMemClass.coe_mul, SubringClass.coe_natCast, z]
    rw [← map_natCast (C : K →+* K⟦X⟧), ← mul_assoc, ← map_mul, mul_inv_cancel₀ hl0, map_one, one_mul])
  let ε : ZMod a → A O K := Pi.single τ 1
  have hpow : ∀ s, (ε * y s) ^ N = (l : ZMod a → A O K) * Pi.single τ (z s) := fun s => by
    funext σ
    rcases eq_or_ne σ τ with rfl | hσ
    · simp [ε, hz]
    · simp [ε, hσ, hN]
  obtain ⟨Φ, hΦi, hΦ⟩ : ∃ Φ : (ZMod a → A O K) →ₐ[O] OW l O, Function.Injective Φ ∧
      ∀ s, inclO l O (ϖ.iTot t K (y s)) = Φ (y s) :=
    ⟨(inclO l O).comp (ϖ.iTot t K), inclO_injective.comp (ϖ.iTot_injective t K), fun _ => rfl⟩
  simp only [hΦ] at h
  have hidem : IsIdempotentElem (Φ ε) := by
    show Φ ε * Φ ε = Φ ε
    rw [← map_mul]
    congr 1
    simp only [ε, ← Pi.single_mul, one_mul]
  have hne0 : Φ ε ≠ 0 := fun h0 => by
    have h1 := congrFun (hΦi (h0.trans (map_zero Φ).symm)) τ
    simp [ε] at h1
  let I : Ideal (OW l O) := Ideal.span {((l : ℕ) : OW l O)}
  have hnil : ∀ s, IsNilpotent (Ideal.Quotient.mk I (Φ ε * Φ (y s))) := fun s => by
    refine ⟨N, ?_⟩
    rw [← map_pow, ← map_mul, ← map_pow, hpow, map_mul, map_natCast, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hsum : Φ ε = ∑ s, c s * (Φ ε * Φ (y s)) := by
    calc Φ ε = Φ ε * ∑ s, c s * Φ (y s) := by rw [h, mul_one]
      _ = ∑ s, c s * (Φ ε * Φ (y s)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring
  have hmk : Ideal.Quotient.mk I (Φ ε) = 0 := by
    refine IsIdempotentElem.eq_zero_of_isNilpotent ?_ ?_
    · show _ * _ = _
      rw [← map_mul, hidem.eq]
    · set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum]
      refine isNilpotent_sum fun s _ => ?_
      rw [map_mul]
      exact (Commute.all _ _).isNilpotent_mul_left (hnil s)
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hmk)
  have hdvd : ∀ n, Φ ε ∈ Ideal.span {((l : ℕ) : OW l O) ^ n} := fun n => by
    rw [Ideal.mem_span_singleton]
    cases n with
    | zero => exact one_dvd _
    | succ n =>
      rw [← hidem.pow_succ_eq n, ← hx, mul_pow]
      exact dvd_mul_left _ _
  have hcpl := GlobalTheory.HWL.TensorWitt.complete_tensor (Module.Free.chooseBasis ℤ_[l] O) ((l : ℕ) : WCb l)
  have e1 : (1 : O) ⊗ₜ[ℤ_[l]] ((l : ℕ) : WCb l) = ((l : ℕ) : OW l O) :=
    map_natCast (Algebra.TensorProduct.includeRight : WCb l →ₐ[ℤ_[l]] OW l O) l
  rw [e1] at hcpl
  exact hne0 (GlobalTheory.Per.AinfComplete.eq_zero_of_haus ((l : ℕ) : OW l O) (Φ ε) hdvd)

end GlobalTheory.ResidueUnitCoeff
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrysFrobCoord

theorem span_range_eq_top {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) :
    Submodule.span B (Set.range u) = ⊤ := by
  set S := Submodule.span B (Set.range u)
  obtain ⟨w, -, hu⟩ := h (N ⧸ S) 0
  have h1 := hu S.mkQ (fun x => by
    simpa using (Submodule.Quotient.mk_eq_zero S).2 (Submodule.subset_span ⟨x, rfl⟩))
  have h2 := hu 0 (fun x => by simp)
  rw [eq_top_iff]
  intro y _
  have : S.mkQ y = 0 := by rw [h1, ← h2]; rfl
  exact (Submodule.Quotient.mk_eq_zero S).1 this

theorem frac_indep {A M B : Type} [CommRing A] [AddCommGroup M] [Module A M] [CommRing B] [IsDomain B]
    (d : A) (J : A →+* B) (hd : J d ≠ 0) (lam : M →+ B) (hlam : ∀ r y, lam (r • y) = J r * lam y)
    {z : LocalizedModule (Submonoid.powers d) M} {n n' : M} {k k' : ℕ} (h : IsFrac d z n k)
    (h' : IsFrac d z n' k') {b : B} (hb : lam n' = J d ^ k' * b) : lam n = J d ^ k * b := by
  unfold IsFrac at h h'
  obtain ⟨⟨_, s, rfl⟩, hs⟩ := LocalizedModule.mk_eq.1 (h.symm.trans h')
  have h2 := congrArg lam hs
  simp only [Submonoid.smul_def, hlam, map_pow, hb] at h2
  have h3 := mul_left_cancel₀ (pow_ne_zero s hd) h2
  refine mul_left_cancel₀ (pow_ne_zero k' hd) ?_
  rw [h3]; ring

theorem frac_formula {A M B : Type} [CommRing A] [AddCommGroup M] [Module A M] [CommRing B] [IsDomain B]
    (d : A) (φ : A →+* A)
    (Φ : M →ₛₗ[(algebraMap A (Localization.Away d)).comp φ] LocalizedModule (Submonoid.powers d) M)
    (J : A →+* B) (hd : J d ≠ 0) (lam : M →+ B) (hlam : ∀ r y, lam (r • y) = J r * lam y)
    (F : M →+ B) (hF : ∀ r y, F (r • y) = J (φ r) * F y) (S : Set M) (hS : Submodule.span A S = ⊤)
    (h0 : ∀ y ∈ S, ∀ n k, IsFrac d (Φ y) n k → lam n = J d ^ k * F y) (y n : M) (k : ℕ)
    (h : IsFrac d (Φ y) n k) : lam n = J d ^ k * F y := by
  have key : ∀ y ∈ Submodule.span A S, ∃ n k, IsFrac d (Φ y) n k ∧ lam n = J d ^ k * F y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨n, k, hn⟩ := exists_isFrac d (Φ y)
      exact ⟨n, k, hn, h0 y hy n k hn⟩
    | zero => exact ⟨0, 0, by simp [IsFrac], by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨n, k, hn, en⟩ := hx
      obtain ⟨m, j, hm, em⟩ := hy
      refine ⟨d ^ j • n + d ^ k • m, k + j, ?_, ?_⟩
      · unfold IsFrac at hn hm ⊢
        rw [map_add (f := _), hn, hm, LocalizedModule.mk_add_mk]
        congr 1
        exact Subtype.ext (pow_add d k j).symm
      · rw [map_add (f := _), hlam, hlam, en, em, map_add (f := _), map_pow, map_pow]; ring
    | smul r x _ hx =>
      obtain ⟨n, k, hn, en⟩ := hx
      refine ⟨φ r • n, k, ?_, ?_⟩
      · unfold IsFrac at hn ⊢
        rw [map_smulₛₗ, hn, RingHom.comp_apply, algebraMap_smul, LocalizedModule.smul'_mk]
      · rw [hlam, hF, en]; ring
  obtain ⟨n', k', h', e'⟩ := key y (hS ▸ Submodule.mem_top)
  exact frac_indep d J hd lam hlam h h' e'

section Maps

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (t : Wq l a →ₐ[ℤ_[l]] O) (e : ℕ)

theorem frob_toAc (x : (Wq l a)⟦X⟧) (τ : ZMod a) :
    frob K l (toAc t K x (τ - 1) : K⟦X⟧) = (toAc t K (frobS l a x) τ : K⟦X⟧) := by
  ext n
  have : coeff n (frobS l a x) = if l ∣ n then sigma l a (coeff (n / l) x) else 0 := by
    simp only [frobS, RingHom.comp_apply, coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coeff_expand]
    split_ifs <;> simp
  rw [coeff_frob, coeff_toAc, coeff_toAc, this]
  split_ifs
  · rw [emb_sigma]
  · simp

theorem coe_toAc_eis (τ : ZMod a) : (toAc t K (eis l a e) τ : K⟦X⟧) = E K l e := by
  have hX : toAc t K X = fun _ => uIn (A O K) :=
    funext fun τ => Subtype.ext ((congrArg (PowerSeries.map _) (PowerSeries.map_X _)).trans
      (PowerSeries.map_X _))
  rw [eis, map_add (f := _), map_pow, hX, map_natCast]
  simp [E]

end Maps

theorem frob_in_coordinates : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → (∀ (x m : EE.M (ϖ.prism a)) (k : ℕ), IsFrac (A := (ϖ.prism a).A) (eis l a e) (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x) m k → c m = fun τ i => E K l e ^ k * P.phi (c x) τ i) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (hl : (l : PP.A) ∈ PP.I) (p : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (J : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (g : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ τ (w : (Wq l a)⟦X⟧), J τ (p.f w) = g (toAc t K (frobS l a w) τ : K⟦X⟧)) → (∀ τ y, J τ (PP.D.φ y) = φ₂ (J (τ - 1) y)) → (∀ f, φ₂ (g f) = g (frob K l f)) → Function.Injective g → ∀ lam : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧), (∀ (r : PP.A) (y : EE.M PP) τ i, lam (r • y) τ i = J τ r * lam y τ i) → (∀ x τ i, lam (EE.tr p x) τ i = g (frob K l (c x (τ - 1) i))) → ∀ (y n : EE.M PP) (k : ℕ), IsFrac (l : PP.A) (EE.Φ PP ⟨l, hl⟩ y) n k → ∀ τ i, lam n τ i = (l : K⟦X⟧⟦X⟧) ^ k * (((P.mx (τ - 1)).map (frob K l)).map g *ᵥ fun j => φ₂ (lam y (τ - 1) j)) i := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P EE c _ hc PP hl p J g φ₂ hJp hJφ hφg hg lam hlam hlamtr y n k h τ i
  have hK : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hl1 : (l : K⟦X⟧) ≠ 0 := fun h => hl0 (by simpa using congrArg constantCoeff h)
  have hl2 : (l : K⟦X⟧⟦X⟧) ≠ 0 := fun h => hl1 (by simpa using congrArg constantCoeff h)
  have hE : E K l e ≠ 0 := fun h => hl0 (by
    simpa [E, NeZero.ne e] using congrArg constantCoeff h)
  have hJE : J τ (p.f (eis l a e)) = g (frob K l (E K l e)) := by
    rw [hJp, ← frob_toAc, coe_toAc_eis]
  have hJE0 : g (frob K l (E K l e)) ≠ 0 := by
    rw [map_ne_zero_iff _ hg, map_ne_zero_iff _ (frob_injective l)]; exact hE
  let lam' : EE.M PP →+ K⟦X⟧⟦X⟧ :=
    { toFun := fun y => lam y τ i, map_zero' := by simp, map_add' := by simp }
  let F : EE.M PP →+ K⟦X⟧⟦X⟧ :=
    { toFun := fun y => (((P.mx (τ - 1)).map (frob K l)).map g *ᵥ fun j => φ₂ (lam y (τ - 1) j)) i
      map_zero' := by simp [Matrix.mulVec, dotProduct]
      map_add' := by simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib] }
  have hJl : J τ (l : PP.A) = l := map_natCast _ _
  have := frac_formula (l : PP.A) PP.D.φ (EE.Φ PP ⟨l, hl⟩) (J τ) (hJl ▸ hl2) lam'
    (fun r y => hlam r y τ i) F ?_ _ (span_range_eq_top (EE.tr_bc p)) ?_ y n k h
  · rw [hJl] at this; exact this
  · intro r y
    simp only [F, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mulVec, dotProduct, hlam, map_mul, hJφ,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  · rintro _ ⟨x, rfl⟩ n k h
    obtain ⟨m', k', hm'⟩ := exists_isFrac (A := (ϖ.prism a).A) (eis l a e)
      (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x)
    obtain ⟨r, hr⟩ := EE.Φ_nat p ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ ⟨l, hl⟩ x m' k' n k hm' h
    have h1 := congrArg (fun y => lam y τ i) hr
    simp only [hlam, map_sub, Pi.sub_apply, map_zero, Pi.zero_apply, map_pow, map_mul, hJl, hJE] at h1
    have h2 := sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ (mul_ne_zero hJE0 hl2)))
    rw [hlamtr, hc x m' k' hm'] at h2
    rw [hJl]
    refine mul_left_cancel₀ (pow_ne_zero k' hJE0) ?_
    change _ * lam n τ i = _
    rw [← h2]

    simp only [F, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mulVec, dotProduct, hlamtr, hφg,
    PhiMod.phi_apply, frobV_apply, map_mul, map_pow, map_sum, Matrix.map_apply]
    ring

end GlobalTheory.CrysFrobCoord
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.TameCoeff

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a], e + 1 = l ^ a → ¬ l ∣ a → ∀ LL : FinExt l,
    (∃ LL' : FinExt l, LL.1 ≤ LL'.1 ∧ HasUnr a LL') ∧ (HasUnr a LL → TameDescentExponentData ↥LL.1 l e a) := by
  intro l _ a e _ h1 h2 LL
  refine ⟨?_, fun hU => ?_⟩
  · have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
    have : FiniteDimensional ℚ_[l] ↥(Kunr l a) := (unrExt l a).2
    exact ⟨⟨LL.1 ⊔ Kunr l a, inferInstance⟩, le_sup_left, ⟨le_sup_right⟩⟩
  · obtain ⟨_, ω, hω, -, -⟩ := exists_gen l a
    have hlt := one_lt_pow_l l a
    have hmem : ω ∈ LL.1 := HasUnr.le (a := a) (IntermediateField.subset_adjoin _ _ (show ω ^ l ^ a = ω by
      rw [← Nat.sub_add_cancel hlt.le, pow_succ, hω.pow_eq_one, one_mul]))
    have he : e = l ^ a - 1 := by omega
    exact
      { succ_eq := h1
        not_dvd := h2
        finite := LL.2
        prim := ⟨⟨ω, hmem⟩, he ▸ (IsPrimitiveRoot.map_iff_of_injective (f := LL.1.val)
          Subtype.val_injective).1 hω⟩ }

end GlobalTheory.TameCoeff
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK.CoordInv

section Gen

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem E_pow_mem_RpiE (N : ℕ) : E K l e ^ N ∈ RpiE O K l e :=
  le_away _ _ (A_le_Rpi l e (pow_mem (E_mem l e (A O K)) N))

theorem E_mem_RpiE : E K l e ∈ RpiE O K l e :=
  le_away _ _ (A_le_Rpi l e (E_mem l e (A O K)))

theorem hat_E_pow (N : ℕ) :
    hat O l e (E K l e ^ N) = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ N := by
  induction N with
  | zero => simpa using (hat_coe (O := O) (K := K) l e 1).trans (map_one _)
  | succ n ih =>
    rw [pow_succ, hat_mul l e (E_pow_mem_RpiE n) E_mem_RpiE, ih, hat_E, pow_succ]

theorem main [NeZero a] (P : PhiMod O K l e a ι) :
    ∃ (β : ℕ) (y : ZMod a → ι → ι → Ahat O K l e), ∀ τ j i,
      algebraMap (Ahat O K l e) (AhatE O K l e) (y τ j i) =
        algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ β * hat O l e (P.mxInv τ j i) := by
  choose n hn using fun p : ZMod a × ι × ι => mem_away.1 (P.mxInv_mem p.1 p.2.1 p.2.2)
  have hN : ∀ p : ZMod a × ι × ι, E K l e ^ Finset.univ.sup n * P.mxInv p.1 p.2.1 p.2.2 ∈ A O K := by
    intro p
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ p))
    rw [hc, pow_add, mul_assoc]
    exact mul_mem (pow_mem (E_mem l e _) c) (by simpa using hn p)
  refine ⟨Finset.univ.sup n, fun τ j i => ofA O K l e ⟨_, hN (τ, j, i)⟩, fun τ j i => ?_⟩
  rw [← hat_coe_A, hat_mul l e (E_pow_mem_RpiE _) (invE_A_le_RpiE l e (P.mxInv_mem τ j i)), hat_E_pow]

end Gen

end GlobalTheory.BK.CoordInv

open GlobalTheory.BK.CoordInv in
theorem GlobalTheory.BK.coordE_mxInv : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι), ∃ (β : ℕ) (y : ZMod a → ι → ι → Ahat ↥(OL LL) ↥LL.1 l e), ∀ τ j i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (y τ j i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ β * hat ↥(OL LL) l e (P.mxInv τ j i) := by
  intro l _ a e _ _ _ LL _ _ ι _ _ P
  exact _root_.GlobalTheory.BK.CoordInv.main P
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal Matrix

namespace GlobalTheory.FrobIntO

theorem frobenius_integrality_vec_O : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] (ι : Type) [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι (OA l O)) (w : ι → OA l O) (z : ι → OW l O), (fun i => frobOW l O (z i)) = (Y.map (inclO l O)) *ᵥ z + (fun i => inclO l O (w i)) → ∀ i, z i ∈ (inclO l O).range := by
  intro l _ O _ _ _ _ ι _ _ Y w z h i
  classical
  have key := GlobalTheory.FrobIntegralCoeff.integrality_baseChange (R := ℤ_[l]) (O := O) (inclWA l) (frobW l)
    (fun p q _ _ Z S S' Y h => GlobalTheory.FrobInt.frobenius_integrality l p q Z S S' Y h) ι Unit
    (Matrix.of fun j (_ : Unit) => z j) Y 1 (Matrix.of fun j (_ : Unit) => w j) (by
      rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
      refine Matrix.ext fun j u => ?_
      have := congrFun h j
      simp only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mulVec,
        dotProduct, Fintype.sum_unique, Pi.add_apply] at this ⊢
      exact this) i ()
  exact key

end GlobalTheory.FrobIntO
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKReal.SESExact

theorem homW_exact_middle : ∀ {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {G : Type} [Group G] [TopologicalSpace G] {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] {P₀ : PhiMod O K l e a ι} {P₁ : PhiMod O K l e a κ} {P₂ : PhiMod O K l e a μ} {T₀ T₁ T₂ : LocLat G ℚ_[l] K O} {I₀ : Ident t ϖ P₀ T₀} {I₁ : Ident t ϖ P₁ T₁} {I₂ : Ident t ϖ P₂ T₂} {f : LatHom T₀.L T₁.L} {g : LatHom T₁.L T₂.L} {F : GlobalTheory.BK.Hom P₀ P₁} {H : GlobalTheory.BK.Hom P₁ P₂} (hS : IsSESLat (Qp := ℚ_[l]) f g) (hF : IsMapOf I₀ I₁ f F) (hH : IsMapOf I₁ I₂ g H), ∀ v : κ → OW l O, homW t ϖ H v = 0 → ∃ w, homW t ϖ F w = v := by
  intro l _ a _ e _ O K _ _ _ _ _ _ _ _ _ t ϖ G _ _ ι κ μ _ _ _ _ _ _ P₀ P₁ P₂ T₀ T₁ T₂ I₀ I₁ I₂ f g F H hS hF hH v hv
  obtain ⟨-, -, hOnto, hker, hsat⟩ := hS
  set f₁ := (f.f.restrictScalars O).restrict f.T_le with hf₁
  set g₁ := (g.f.restrictScalars O).restrict g.T_le with hg₁
  have hgs : Function.Surjective g₁ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := hOnto y hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hex : Function.Exact f₁ g₁ := by
    rintro ⟨y, hy⟩
    constructor
    · intro h0
      have h0' : g.f y = 0 := congrArg Subtype.val h0
      obtain ⟨z, hz⟩ := (hker y).1 h0'
      have hzT : z ∈ T₀.L.T := hsat z (hz ▸ hy)
      exact ⟨⟨z, hzT⟩, Subtype.ext hz⟩
    · rintro ⟨⟨z, hzT⟩, hz⟩
      apply Subtype.ext
      have hz' : f.f z = y := congrArg Subtype.val hz
      exact (hker y).2 ⟨z, hz'⟩
  have hT := lTensor_exact (OW l O) hex hgs
  have h1 : latW g (I₁.j v) = 0 := by
    rw [← hH v, hv, map_zero]
  obtain ⟨z, hz⟩ := (hT (I₁.j v)).1 h1
  refine ⟨I₀.j.symm z, I₁.j.injective ?_⟩
  rw [hF, LinearEquiv.apply_symm_apply]
  exact hz

end GlobalTheory.BKReal.SESExact
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem _root_.GlobalTheory.T.witt_twist_invariant_basis_change : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ (E : WEt I) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (q : ℕ) (x : Fin q → TW (RW LL) T) (A : Matrix (Fin q) (Fin q) R.EE), IsUnit A → (∀ g : ↥(GK K), P.χQ (g : GQ l) = 1 → ∀ i, TWact (AI.gRW LL (g : GQ l)) T g (x i) = x i) → (∀ j, TWmap (φRW LL) T (x j) = ∑ i, TensorProduct.map (LinearMap.mulLeft ↥(OL LL) (I.ioE (A i j) : RW LL)) (LinearMap.id : ↥T.L.T →ₗ[↥(OL LL)] ↥T.L.T) (x i)) → ∀ i, x i ∈ Set.range (E.jD T) := by
  first | exact @GlobalTheory.HWL.EtMem.fixed_mem_range | exact GlobalTheory.HWL.EtMem.fixed_mem_range | (intros; apply GlobalTheory.HWL.EtMem.fixed_mem_range <;> assumption)
end
