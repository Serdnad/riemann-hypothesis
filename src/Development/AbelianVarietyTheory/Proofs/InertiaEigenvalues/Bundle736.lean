module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle587
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle634
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle635
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle721
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle205
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle686
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle722
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle723
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle521
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle724
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.breuilKisin_mu_pow_smul_frobenius_mem_ainf : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (α β : ℕ), (∀ m ∈ P.L, E K l e ^ α • m ∈ P.M) → (∀ m ∈ P.M, E K l e ^ β • m ∈ P.L) → ∀ ε δ : OCb l, IsEps ε → δ ^ l = ε → ∀ (y : ME P), y.1 ∈ P.EM α → ∀ m₀, phiW t ϖ P m₀ - m₀ = toW t ϖ P y → inclO l O (1 ⊗ₜ (muOf δ ^ (β + α))) • m₀ ∈ MA P ∧ inclO l O (1 ⊗ₜ (muOf ε ^ (β + α))) • phiW t ϖ P m₀ ∈ LA t ϖ P := by
  first | exact @GlobalTheory.BKGal.LiftStep.mu_pow_smul_mem | exact GlobalTheory.BKGal.LiftStep.mu_pow_smul_mem | (intros; apply GlobalTheory.BKGal.LiftStep.mu_pow_smul_mem <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP



theorem l_dvd_of_galois_sections : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)) (κ : Type) [Fintype κ] (x : κ → En.Q.A) (c : κ → κ → En.Q.A) (h : ℕ), (∀ j, En.inl.f (bk.ev bk.E) ^ h * x j = ∑ i, En.Q.D.φ (x i) * c i j) → (∀ (g : ↥(GK K)) (s : Hom En.Q (ainfObj K)), s.comp En.inl = Hom.id _ → s.comp En.inr = (ainfHom K g).comp bk.ι → ∀ j, ((l : ℕ) : (ainfObj K).A) ∣ s.f (x j)) → ∀ j, ((l : ℕ) : En.Q.A) ∣ x j := by
  intro l _ K bk En κ _ x c h hx hs
  obtain ⟨-, -, -, -, -, -, hA7⟩ := GlobalTheory.T.ainf_divisibility_breuilKisin_facts l K bk
  obtain ⟨-, hM2, hM3⟩ := GlobalTheory.T.ainf_envelope_mod_prime_properties l K bk En
  let I : Ideal En.Q.A := Ideal.span {((l : ℕ) : En.Q.A)}
  let π : En.Q.A →+* En.Q.A ⧸ I := Ideal.Quotient.mk I
  have hπ : ∀ y, π y = 0 ↔ ((l : ℕ) : En.Q.A) ∣ y := fun y =>
    Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton
  have hl0 : ((l : ℕ) : En.Q.A ⧸ I) = 0 := by
    rw [← map_natCast π]; exact (hπ _).2 dvd_rfl
  have hreg : π (En.inl.f (bk.ev X)) ∈ nonZeroDivisors (En.Q.A ⧸ I) := by
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have : π (En.inl.f (bk.ev X) * y) = 0 := by rw [map_mul, mul_comm]; exact hy
    exact (hπ _).2 (hM2 y ((hπ _).1 this))
  have hE : π (En.inl.f (bk.ev bk.E)) = π (En.inl.f (bk.ev X)) ^ bk.Ep.natDegree := by
    let ι : Ainf l →+* En.Q.A := En.inl.f
    have h1 : ((l : ℕ) : En.Q.A) ∣ ι (bk.ev bk.E - bk.ev X ^ bk.Ep.natDegree) := by
      have := map_dvd ι hA7
      rwa [map_natCast] at this
    have h2 := (hπ _).2 h1
    rw [map_sub, map_pow, map_sub, map_pow, sub_eq_zero] at h2
    exact h2
  have hl1 : π ((l : ℕ) : En.Q.A) = 0 := (hπ _).2 dvd_rfl
  have hφ : ∀ y, π (En.Q.D.φ y) = π y ^ l := fun y => by
    have e : π (En.Q.D.φ y - y ^ l) = 0 := (hπ _).2 ⟨En.Q.D.δ y, by rw [En.Q.D.φ_eq y]; ring⟩
    rwa [map_sub, map_pow, sub_eq_zero] at e
  have heq : ∀ j, π (En.inl.f (bk.ev X)) ^ (bk.Ep.natDegree * h) * π (x j) =
      ∑ i, π (x i) ^ l * π (c i j) := fun j => by
    have := congrArg π (hx j)

    rw [map_mul π, map_pow π, hE, ← pow_mul, map_sum π] at this
    rw [this]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul π, hφ]
  have hpts : ∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l]
      (f : En.Q.A ⧸ I →+* O), f (π (En.inl.f (bk.ev X))) ≠ 0 → ¬ IsUnit (f (π (En.inl.f (bk.ev X)))) →
      IsAdicComplete (Ideal.span {f (π (En.inl.f (bk.ev X)))}) O → ∀ j, f (π (x j)) = 0 := by
    intro O _ _ _ _ _ f hf0 hfu hfc j
    obtain ⟨g, s, ψ, h1, h2, h3⟩ := GlobalTheory.T.breuilKisinEnvelope_point_factors_through_section l K bk En O (f.comp π) hf0 hfu hfc
    obtain ⟨z, hz⟩ := hs g s h1 h2 j
    have e := h3 (x j)
    rw [RingHom.comp_apply] at e
    rw [e, hz]
    have : WittVector.coeff (p := l) (R := OCb l) (((l : ℕ) : (ainfObj K).A) * z) 0 = 0 := by
      rw [mul_comm]; exact WittVector.mul_charP_coeff_zero (p := l) (R := OCb l) z
    rw [this, map_zero]
  have key := GlobalTheory.T.dvd_all_pow_of_frobenius_eq_killed_by_perfect_points l (En.Q.A ⧸ I) (π (En.inl.f (bk.ev X))) hl0 hreg κ (fun i => π (x i))
    (fun i j => π (c i j)) (bk.Ep.natDegree * h) heq (fun O _ _ _ _ _ f hf0 hfu hfc j => hpts O f hf0 hfu hfc j)
  intro j
  refine hM3 (x j) fun m => ?_
  obtain ⟨w, hw⟩ := key m j
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
  refine ⟨z, (hπ _).1 ?_⟩
  change π (x j) = π (En.inl.f (bk.ev X)) ^ m * π z at hw
  rw [map_sub π, map_mul π, map_pow π, hw, sub_self]

end GlobalTheory.BSP
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace BridgeWittDvd

section Witt
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

theorem dvd_iff (x : WittVector p k) : (p : WittVector p k) ∣ x ↔ x.coeff 0 = 0 := by
  rw [← Ideal.mem_span_singleton]
  exact WittVector.mem_span_p_iff_coeff_zero_eq_zero x

theorem exists_limit (w : ℕ → WittVector p k) (h : ∀ n, (p : WittVector p k) ^ n ∣ w (n + 1) - w n) :
    ∃ z : WittVector p k, ∀ n, (p : WittVector p k) ^ n ∣ z - w n := by
  have hc : IsAdicComplete (Ideal.span {(p : WittVector p k)}) (WittVector p k) := inferInstance
  have key : ∀ (n : ℕ) (x y : WittVector p k),
      x ≡ y [SMOD (Ideal.span {(p : WittVector p k)} ^ n • ⊤ : Submodule (WittVector p k) (WittVector p k))] ↔
        (p : WittVector p k) ^ n ∣ x - y := by
    intro n x y
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have step : ∀ m d : ℕ, (p : WittVector p k) ^ m ∣ w (m + d) - w m := by
    intro m d
    induction d with
    | zero => simp
    | succ d ih =>
      have e : w (m + (d + 1)) - w m = (w (m + d + 1) - w (m + d)) + (w (m + d) - w m) := by
        rw [← add_assoc]; ring
      rw [e]
      exact dvd_add ((pow_dvd_pow _ (Nat.le_add_right m d)).trans (h _)) ih
  obtain ⟨z, hz⟩ := hc.toIsPrecomplete.prec (f := w) (fun {m n} hmn => by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [key, ← dvd_neg, neg_sub]
    exact step m d)
  refine ⟨z, fun n => ?_⟩
  rw [← dvd_neg, neg_sub]
  exact (key n _ _).1 (hz n)

theorem series_dvd (s : (WittVector p k)⟦X⟧)
    (h : PowerSeries.map (WittVector.constantCoeff (p := p) (R := k)) s = 0) :
    (p : (WittVector p k)⟦X⟧) ∣ s := by
  have hd : ∀ n, ∃ c, PowerSeries.coeff n s = (p : WittVector p k) * c := by
    intro n
    apply (dvd_iff _).2
    have := congrArg (PowerSeries.coeff n) h
    simpa using this
  choose c hc using hd
  refine ⟨PowerSeries.mk c, ?_⟩
  ext1 n
  rw [← map_natCast (PowerSeries.C (R := WittVector p k)) p, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc]

theorem decomp (w : WittVector p k) (h0 : w ≠ 0) :
    ∃ (n : ℕ) (v : WittVector p k), IsUnit v ∧ w = (p : WittVector p k) ^ n * v := by
  obtain ⟨n, v, e⟩ := WittVector.exists_eq_pow_p_mul' w h0
  exact ⟨n, v, v.isUnit, e⟩
end Witt

theorem perfect_frac (p : ℕ) [Fact p.Prime] (R F : Type) [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [CharP R p] [CharP F p] [PerfectRing R p] : PerfectRing F p := by
  refine PerfectRing.ofSurjective F p fun x => ?_
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  obtain ⟨a', rfl⟩ := (bijective_frobenius R p).2 a
  obtain ⟨b', rfl⟩ := (bijective_frobenius R p).2 b
  exact ⟨algebraMap R F a' / algebraMap R F b', by simp [frobenius_def, div_pow]⟩

end BridgeWittDvd

theorem Bridge.kisin_reduction_unit_at_uniformizer : ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (K : Formalism.BasicNotions.Loc.FinExt l) (bk : GlobalTheory.BSP.BK K), (∀ w ∈ bk.OE, l.cast ∣ w → ∃ v ∈ bk.OE, w = l.cast * v) ∧ (∃ w ∈ bk.OE, HMul.hMul (α := Formalism.BasicNotions.Loc.WCb l) (DFunLike.coe (β := fun (x : bk.S) ↦ Formalism.BasicNotions.Loc.WCb l) bk.evW PowerSeries.X : Formalism.BasicNotions.Loc.WCb l) w = OfNat.ofNat 1) ∧ (∀ (s : bk.S), ¬l.cast ∣ s → ∃ w ∈ bk.OE, HMul.hMul (α := Formalism.BasicNotions.Loc.WCb l) (DFunLike.coe (β := fun (x : bk.S) ↦ Formalism.BasicNotions.Loc.WCb l) bk.evW s : Formalism.BasicNotions.Loc.WCb l) w = OfNat.ofNat 1) ∧ (∀ w ∈ bk.OE, w ≠ OfNat.ofNat 0 → ∃ (k : ℕ) (v : Formalism.BasicNotions.Loc.WCb l) (v' : Formalism.BasicNotions.Loc.WCb l), v ∈ bk.OE ∧ v' ∈ bk.OE ∧ v * v' = OfNat.ofNat 1 ∧ w = HPow.hPow (α := Formalism.BasicNotions.Loc.WCb l) l.cast k * v) ∧ (∀ (w : ℕ → Formalism.BasicNotions.Loc.WCb l), (∀ (n : ℕ), w n ∈ bk.OE) → (∀ (n : ℕ), HPow.hPow (α := Formalism.BasicNotions.Loc.WCb l) l.cast n ∣ w (n + OfNat.ofNat 1) - w n) → ∃ z ∈ bk.OE, ∀ (n : ℕ), HPow.hPow (α := Formalism.BasicNotions.Loc.WCb l) l.cast n ∣ z - w n) ∧ (∀ (g : ↥(Formalism.BasicNotions.Loc.GK K)), bk.FixFlat g → ∀ w ∈ bk.OE, DFunLike.coe (F := Formalism.BasicNotions.Loc.WCb l ≃ₐ[ℤ_[l]] Formalism.BasicNotions.Loc.WCb l) (β := fun (x : Formalism.BasicNotions.Loc.WCb l) ↦ Formalism.BasicNotions.Loc.WCb l) (DFunLike.coe (F := Formalism.BasicNotions.Loc.GQ l →* Formalism.BasicNotions.Loc.WCb l ≃ₐ[ℤ_[l]] Formalism.BasicNotions.Loc.WCb l) (β := fun (x : Formalism.BasicNotions.Loc.GQ l) ↦ Formalism.BasicNotions.Loc.WCb l ≃ₐ[ℤ_[l]] Formalism.BasicNotions.Loc.WCb l) (GlobalTheory.Prism.galW l) (g.val (p := fun (x : Formalism.BasicNotions.Loc.GQ l) ↦ x ∈ Formalism.BasicNotions.Loc.GK K)) : Formalism.BasicNotions.Loc.WCb l ≃ₐ[ℤ_[l]] Formalism.BasicNotions.Loc.WCb l) w = w) ∧ ∀ w ∈ bk.OE, Membership.mem (α := Formalism.BasicNotions.Loc.WCb l) bk.OE (DFunLike.coe (F := Formalism.BasicNotions.Loc.WCb l →ₐ[ℤ_[l]] Formalism.BasicNotions.Loc.WCb l) (β := fun (x : Formalism.BasicNotions.Loc.WCb l) ↦ Formalism.BasicNotions.Loc.WCb l) (Formalism.BasicNotions.Loc.frobW l) w : Formalism.BasicNotions.Loc.WCb l) := by
  intro l _ K bk
  haveI : PerfectRing (Cb l) l := BridgeWittDvd.perfect_frac l (OCb l) (Cb l)
  obtain ⟨ek, -, hek, hinj, -, -⟩ := GlobalTheory.T.exists_residueTilt_injective_retract l K bk
  obtain ⟨-, hS, hX, -, -⟩ := GlobalTheory.T.breuilKisin_OE_mod_prime_laurent_field l K bk
  obtain ⟨hsat, hcl, hφ, hgal, hunit⟩ := GlobalTheory.T.breuilKisin_OE_stability_properties l K bk
  have hsatn : ∀ (n : ℕ) (v : WCb l), ((l : ℕ) : WCb l) ^ n * v ∈ bk.OE → v ∈ bk.OE := by
    intro n
    induction n with
    | zero => intro v hv; simpa using hv
    | succ n ih =>
      intro v hv
      rw [pow_succ, mul_assoc] at hv
      exact hsat v (ih _ hv)
  refine ⟨?_, hunit _ (hS _) hX, ?_, ?_, ?_, hgal, hφ⟩
  · rintro w hw ⟨v, rfl⟩
    exact ⟨v, hsat v hw, rfl⟩
  · intro s hs
    refine hunit _ (hS s) (WittVector.isUnit_of_coeff_zero_ne_zero _ fun h0 => hs ?_)
    apply BridgeWittDvd.series_dvd
    apply hinj
    rw [hek, map_zero]
    have e : (bk.evW s).coeff 0 = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0) := rfl
    rw [e] at h0
    exact (FaithfulSMul.algebraMap_injective (OCb l) (Cb l)) (h0.trans (map_zero _).symm)
  · intro w hw h0
    obtain ⟨n, v, hv, e⟩ := BridgeWittDvd.decomp (p := l) (k := Cb l) w h0
    have hvO : v ∈ bk.OE := hsatn n v (e ▸ hw)
    obtain ⟨v', hv', e'⟩ := hunit v hvO hv
    exact ⟨n, v, v', hvO, hv', e', e⟩
  · intro w hw h
    obtain ⟨z, hz⟩ := BridgeWittDvd.exists_limit (p := l) (k := Cb l) w h
    exact ⟨z, hcl z fun n => ⟨w n, hw n, hz n⟩, hz⟩

namespace GlobalTheory.OEDvr

variable {l : ℕ} [hl : Fact l.Prime]

theorem perfectRing_Cb : PerfectRing (Cb l) l := by
  refine PerfectRing.ofSurjective _ _ fun x => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  refine ⟨algebraMap _ _ ((frobeniusEquiv (OCb l) l).symm a) /
    algebraMap _ _ ((frobeniusEquiv (OCb l) l).symm b), ?_⟩
  rw [frobenius_def, div_pow, ← map_pow (algebraMap (OCb l) (Cb l)),
    ← map_pow (algebraMap (OCb l) (Cb l)), frobeniusEquiv_symm_pow_p,
    frobeniusEquiv_symm_pow_p]

variable {K : FinExt l} (bk : BK K)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ w ∈ bk.OE, ((l : ℕ) : WCb l) ∣ w → ∃ v ∈ bk.OE, w = (l : WCb l) * v) ∧ (∃ w ∈ bk.OE, bk.evW X * w = 1) ∧ (∀ s : bk.S, ¬ (l : bk.S) ∣ s → ∃ w ∈ bk.OE, bk.evW s * w = 1) ∧ (∀ w ∈ bk.OE, w ≠ 0 → ∃ (k : ℕ) (v v' : WCb l), v ∈ bk.OE ∧ v' ∈ bk.OE ∧ v * v' = 1 ∧ w = (l : WCb l) ^ k * v) ∧ (∀ w : ℕ → WCb l, (∀ n, w n ∈ bk.OE) → (∀ n, (l : WCb l) ^ n ∣ w (n + 1) - w n) → ∃ z ∈ bk.OE, ∀ n, (l : WCb l) ^ n ∣ z - w n) ∧ (∀ g : ↥(GK K), bk.FixFlat g → ∀ w ∈ bk.OE, galW l (g : GQ l) w = w) ∧ (∀ w ∈ bk.OE, frobW l w ∈ bk.OE) :=
  Bridge.kisin_reduction_unit_at_uniformizer

end GlobalTheory.OEDvr
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DescentStep

variable {l : ℕ} [Fact l.Prime]

theorem perfectRing_Cb : PerfectRing (Cb l) l := by
  refine PerfectRing.ofSurjective _ _ fun x => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  obtain ⟨a, rfl⟩ := (bijective_frobenius (OCb l) l).2 a
  obtain ⟨b, rfl⟩ := (bijective_frobenius (OCb l) l).2 b
  exact ⟨algebraMap _ _ a / algebraMap _ _ b, by simp [frobenius_def]⟩

theorem constantCoeff_frobW (w : WCb l) :
    WittVector.constantCoeff (p := l) (R := Cb l) (frobW l w) =
      WittVector.constantCoeff (p := l) (R := Cb l) w ^ l := by
  rw [WittVector.constantCoeff_apply, WittVector.constantCoeff_apply]
  change (WittVector.map (frobenius (Cb l) l) w).coeff 0 = _
  rw [WittVector.map_coeff, frobenius_def]

theorem constantCoeff_galW (g : GQ l) (w : WCb l) :
    WittVector.constantCoeff (p := l) (R := Cb l) (galW l g w) =
      autCb l (galTilt l g) (WittVector.constantCoeff (p := l) (R := Cb l) w) := by
  rw [WittVector.constantCoeff_apply, WittVector.constantCoeff_apply]
  change (WittVector.map (autCb l (galTilt l g)).toRingHom w).coeff 0 = _
  rw [WittVector.map_coeff]
  rfl

end GlobalTheory.BSP.DescentStep


open GlobalTheory.BSP.DescentStep in
theorem GlobalTheory.BSP.BK.descent_step : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (κ : Type) [Fintype κ] (x b : κ → WCb l) (c : κ → κ → WCb l), (∀ i j, c i j ∈ bk.OE) → (∀ j, b j ∈ bk.OE) → (∀ j, x j = ∑ i, frobW l (x i) * c i j + b j) → (∀ g : ↥(GK K), bk.FixFlat g → ∀ j, galW l (g : GQ l) (x j) = x j) → ∃ v x' b' : κ → WCb l, (∀ j, v j ∈ bk.OE) ∧ (∀ j, b' j ∈ bk.OE) ∧ (∀ j, x j = v j + ((l : ℕ) : WCb l) * x' j) ∧ (∀ j, x' j = ∑ i, frobW l (x' i) * c i j + b' j) ∧ ∀ g : ↥(GK K), bk.FixFlat g → ∀ j, galW l (g : GQ l) (x' j) = x' j := by
  intro l _ K bk κ _ x b c hc hb hx hg
  haveI : PerfectRing (Cb l) l := perfectRing_Cb
  obtain ⟨sat, -, hφ, hfix, -⟩ := GlobalTheory.T.breuilKisin_OE_stability_properties l K bk
  set cc := WittVector.constantCoeff (p := l) (R := Cb l) with hcc
  have hmemc : ∀ w ∈ bk.OE, cc w ∈ bk.OE.map cc := fun w hw => Subring.mem_map.2 ⟨w, hw, rfl⟩
  have key : ∀ j, cc (x j) ∈ bk.OE.map cc := by
    refine GlobalTheory.T.tilt_invariant_mem_reduction_of_frobenius_equation l K bk κ (fun j => cc (x j)) ?_ ?_
    · intro g hgf j
      have h1 := congrArg cc (hg g hgf j)
      rw [constantCoeff_galW] at h1
      exact h1
    · intro T _ i₁ i₂ h12
      refine ⟨fun i j => i₁ (cc (c i j)), fun j => ?_⟩
      have e1 : ∀ i' : Cb l →+* T,
          i' (cc (x j)) = ∑ i, i' (cc (x i)) ^ l * i' (cc (c i j)) + i' (cc (b j)) := by
        intro i'
        conv_lhs => rw [hx j]

        rw [RingHom.map_add cc, map_sum cc, RingHom.map_add i', map_sum i']
        refine congrArg (· + _) (Finset.sum_congr rfl fun i _ => ?_)
        rw [RingHom.map_mul cc, RingHom.map_mul i', constantCoeff_frobW, RingHom.map_pow i']
      have e2 : ∀ i, i₂ (cc (c i j)) = i₁ (cc (c i j)) := fun i => (h12 _ (hmemc _ (hc i j))).symm
      rw [e1 i₁, e1 i₂, ← h12 _ (hmemc _ (hb j))]
      simp_rw [e2]
      rcases subsingleton_or_nontrivial T with hT | hT
      · exact Subsingleton.elim _ _
      · haveI : CharP T l := charP_of_injective_ringHom i₁.injective l
        simp_rw [sub_pow_char, sub_mul, Finset.sum_sub_distrib]
        ring
  choose v hv hvx using fun j => Subring.mem_map.1 (key j)
  have hker : ∀ j, x j - v j ∈ RingHom.ker cc := fun j => by
    rw [RingHom.mem_ker, map_sub, hvx j, sub_self]
  rw [hcc, WittVector.ker_constantCoeff] at hker
  choose x' hx' using fun j => Ideal.mem_span_singleton'.1 (hker j)

  set b' : κ → WCb l := fun j => x' j - ∑ i, frobW l (x' i) * c i j with hb'
  have hlb : ∀ j, ((l : ℕ) : WCb l) * b' j = b j - v j + ∑ i, frobW l (v i) * c i j := by
    intro j
    have h3 : ∀ i, ((l : ℕ) : WCb l) * (frobW l (x' i) * c i j) = (frobW l (x i) - frobW l (v i)) * c i j := by
      intro i
      rw [← map_sub, ← hx' i, map_mul, map_natCast]
      ring
    simp only [hb', mul_sub, Finset.mul_sum, h3]
    rw [mul_comm, hx' j]
    conv_lhs => rw [hx j]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have hb'mem : ∀ j, b' j ∈ bk.OE := fun j => sat _ (by
    rw [hlb j]
    refine bk.OE.add_mem (bk.OE.sub_mem (hb j) (hv j)) (bk.OE.sum_mem fun i _ => bk.OE.mul_mem (hφ _ (hv i)) (hc i j)))
  refine ⟨v, x', b', hv, hb'mem, fun j => ?_, fun j => ?_, fun g hgf j => ?_⟩
  · linear_combination (hx' j).symm
  · simp only [hb']
    ring
  · have h5 : galW l (g : GQ l) (x' j * ((l : ℕ) : WCb l)) = x' j * ((l : ℕ) : WCb l) := by
      rw [hx' j, map_sub, hg g hgf j, hfix g hgf _ (hv j)]
    rw [map_mul, map_natCast] at h5
    have h4 : (galW l (g : GQ l) (x' j) - x' j) * ((l : ℕ) : WCb l) = 0 := by
      linear_combination h5
    exact sub_eq_zero.1 (WittVector.eq_zero_of_p_mul_eq_zero _ h4)
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem _root_.GlobalTheory.T.ainf_closedDisc_linearDisjoint_over_powerSeries : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (sA : bk.S →+* A) (ι : Type) (TB : TopBasis sA bk.J ι) (j : bk.DS bk.ρ₀ →+* Disc l (sA X) bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) sA j → ∀ (x y : A) (f g : bk.DS bk.ρ₀), g ≠ 0 → y ≠ 0 → toDisc l (sA X) bk.ρ₀ x * j g = toDisc l (sA X) bk.ρ₀ y * j f → ∃ δ a : bk.S, δ ≠ 0 ∧ sA δ * x = sA a * y := by
  first | exact @GlobalTheory.BSP.linDisjoint_disc | exact GlobalTheory.BSP.linDisjoint_disc | (intros; apply GlobalTheory.BSP.linDisjoint_disc <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem _root_.GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → IsUnit (inclW l τ) ∧ bk.iA τ ≠ 0 ∧ τ ≠ 0 ∧ ∀ g : GQ l, IsUnit (inclW l (Per.σA g τ)) := by
  first | exact @GlobalTheory.BSP.isUnit_inclW_of_isPer | exact GlobalTheory.BSP.isUnit_inclW_of_isPer | (intros; apply GlobalTheory.BSP.isUnit_inclW_of_isPer <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem _root_.GlobalTheory.T.discPeriods_map_frobenius_eq_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → ((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) • s.W.map Φ = s.W * (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS := by
  first | exact @GlobalTheory.BSP.Seed.crystallineDiscPeriods_frobenius_eq_mul | exact GlobalTheory.BSP.Seed.crystallineDiscPeriods_frobenius_eq_mul | (intros; apply GlobalTheory.BSP.Seed.crystallineDiscPeriods_frobenius_eq_mul <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.eisenstein_div_closedDisc_of_topBasis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ ρ : ℝ≥0, bk.ρ₀ ≤ ρ → ρ < 1 → (∀ y : Disc l (s X) ρ, ‖toDisc l (s X) ρ (s bk.E) * y‖ = (ρ : ℝ) ^ bk.Ep.natDegree * ‖y‖) ∧ ∀ R : Disc l (s X) ρ →+* Disc l (s X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R → ∀ (h : ℕ) (y : Disc l (s X) ρ), toDisc l (s X) bk.ρ₀ (s bk.E) ^ h ∣ R y → toDisc l (s X) ρ (s bk.E) ^ h ∣ y := by
  first | exact @GlobalTheory.BSP.div_E_of_topBasis | exact GlobalTheory.BSP.div_E_of_topBasis | (intros; apply GlobalTheory.BSP.div_E_of_topBasis <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_base_eq_of_closedDisc_extends_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ ρ : ℝ≥0, 0 < ρ → ρ < 1 → ∀ y : Disc l (s X) ρ, (∀ ρ₁ : ℝ≥0, ρ₁ < 1 → ∃ (ρ' : ℝ≥0) (R : Disc l (s X) ρ' →+* Disc l (s X) ρ) (y' : Disc l (s X) ρ'), ρ₁ ≤ ρ' ∧ ρ ≤ ρ' ∧ ρ' < 1 ∧ IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R ∧ R y' = y ∧ ‖y'‖ ≤ 1) → ∃ a, toDisc l (s X) ρ a = y := by
  first | exact @GlobalTheory.BSP.exists_toDisc_eq_of_extends_norm_le_one | exact GlobalTheory.BSP.exists_toDisc_eq_of_extends_norm_le_one | (intros; apply GlobalTheory.BSP.exists_toDisc_eq_of_extends_norm_le_one <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_framedStratifiedCrystalBasis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (M : FCrys l ↥(OL K)), ∃ (d : ℕ) (S : Strat bk d) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e := by
  first | exact @GlobalTheory.BSP.exists_framed | exact GlobalTheory.BSP.exists_framed | (intros; apply GlobalTheory.BSP.exists_framed <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LFun (IsSplitChart IsInertChart KGL)
open GlobalTheory.AdelicU


theorem _root_.GlobalTheory.T.selfDualLatticeIndex_inertPlace_eq_localIndex : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → ∀ g : GlobalTheory.FinZeta.Gv T v, latIndex T (GlobalTheory.FinZeta.embV T v g) = GlobalTheory.LocKerMod.idxAt T w h g := by
  first | exact @GlobalTheory.LocKerMod.latIndex_embV_inert | exact GlobalTheory.LocKerMod.latIndex_embV_inert | (intros; apply GlobalTheory.LocKerMod.latIndex_embV_inert <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LFun (IsSplitChart IsInertChart KGL)
open GlobalTheory.AdelicU


theorem _root_.GlobalTheory.T.selfDualLatticeIndex_splitPlace_eq_mul : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w w' : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (h' : w'.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → w ≠ w' → ∀ g : GlobalTheory.FinZeta.Gv T v, latIndex T (GlobalTheory.FinZeta.embV T v g) = GlobalTheory.LocKerMod.idxAt T w h g * GlobalTheory.LocKerMod.idxAt T w' h' g := by
  first | exact @GlobalTheory.SplitLatIdx.latIndex_split | exact GlobalTheory.SplitLatIdx.latIndex_split | (intros; apply GlobalTheory.SplitLatIdx.latIndex_split <;> assumption)
end
