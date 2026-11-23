module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesVecReduceModUMulVec
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsEqMulAddOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle058
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle199
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle166
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle111
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle169
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiltrationEstimateExpansionTensorBdRComponent
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle009
public import Formalism.CharacterColumnKernels.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle202
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle203
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot

@[expose] public section

section

noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology Matrix

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K]

open PowerSeries Filter Topology Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
omit [IsUltrametricDist K] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
private lemma coeff_eq_add_of_X_pow_succ_dvd_sub {f s g : K⟦X⟧} {c : K} {n : ℕ}
    (h : (X : K⟦X⟧) ^ (n + 1) ∣ f - (s + c • g)) :
    coeff n f = coeff n s + c * coeff n g := by
  have h0 := (PowerSeries.X_pow_dvd_iff.mp h) n (Nat.lt_succ_self n)
  rw [map_sub, map_add (f := _), PowerSeries.coeff_smul, smul_eq_mul, sub_eq_zero] at h0
  exact h0

open PowerSeries Filter Topology Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
private lemma norm_add_mul_mul_le_max {x y c : K} {w : ℝ} (hw : 0 ≤ w) :
    ‖x + c * y‖ * w ≤ max (‖x‖ * w) (‖c‖ * (‖y‖ * w)) := by
  calc ‖x + c * y‖ * w ≤ max ‖x‖ ‖c * y‖ * w :=
        mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) hw
    _ = max (‖x‖ * w) (‖c‖ * (‖y‖ * w)) := by
        rw [max_mul_of_nonneg _ _ hw, norm_mul, mul_assoc]

open PowerSeries Filter Topology Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
omit [IsUltrametricDist K] in
private lemma norm_natCast_prime_lt_one_inertia_eigenvalues : ‖(l : K)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] K), norm_algebraMap']
  exact Padic.norm_p_lt_one


open PowerSeries Filter Topology Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
theorem _root_.GlobalTheory.BK.mem_S_of_approx {f : K⟦X⟧}
    (h : ∀ k : ℕ, ∃ s ∈ _root_.GlobalTheory.BK.S O K e, ∀ m : ℕ,
      ∃ g ∈ _root_.GlobalTheory.BK.S O K e,
        (X : K⟦X⟧) ^ m ∣ f - (s + (l : K) ^ k • g)) : f ∈ _root_.GlobalTheory.BK.S O K e := by
  rw [_root_.GlobalTheory.BK.mem_S]
  have hw := _root_.GlobalTheory.BK.wS_nonneg (K := K) e
  refine ⟨fun n => ?_, ?_⟩
  · obtain ⟨s, hs, hm⟩ := h 0
    obtain ⟨g, hg, hdvd⟩ := hm (n + 1)
    rw [coeff_eq_add_of_X_pow_succ_dvd_sub hdvd]
    refine (norm_add_mul_mul_le_max (hw n)).trans (max_le ((_root_.GlobalTheory.BK.mem_S.mp hs).1 n) ?_)
    rw [pow_zero, norm_one, one_mul]
    exact (_root_.GlobalTheory.BK.mem_S.mp hg).1 n
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (norm_natCast_prime_lt_one_inertia_eigenvalues (K := K) (l := l))
    obtain ⟨s, hs, hm⟩ := h k
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (_root_.GlobalTheory.BK.mem_S.mp hs).2 ε hε
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨g, hg, hdvd⟩ := hm (n + 1)
    have hsn := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (norm_nonneg _) (hw n))] at hsn ⊢
    rw [coeff_eq_add_of_X_pow_succ_dvd_sub hdvd]
    refine (norm_add_mul_mul_le_max (hw n)).trans_lt (max_lt hsn ?_)
    calc ‖(l : K) ^ k‖ * (‖coeff n g‖ * _root_.GlobalTheory.BK.wS K e n)
        ≤ ‖(l : K) ^ k‖ * 1 :=
          mul_le_mul_of_nonneg_left ((_root_.GlobalTheory.BK.mem_S.mp hg).1 n)
            (norm_nonneg _)
      _ < ε := by rw [mul_one, norm_pow]; exact hk

namespace PhiMod

variable (P : PhiMod O K l e a ι)

open PowerSeries Filter Topology Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
variable (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) in
omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
theorem _root_.GlobalTheory.BK.PhiMod.l_pow_smul_mem_MM (n : ℕ) {v : _root_.GlobalTheory.BK.Vec K a ι} (hv : v ∈ P.MM) :
    (l : K) ^ n • v ∈ P.MM := by
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hv _

open PowerSeries Filter Topology Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
variable (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) in
omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
theorem _root_.GlobalTheory.BK.PhiMod.smul_mem_MM {f : K⟦X⟧}
    (hf : f ∈ _root_.GlobalTheory.BK.S O K e) {v : _root_.GlobalTheory.BK.Vec K a ι}
    (hv : v ∈ P.MM) : f • v ∈ P.MM :=
  Submodule.smul_mem _ (⟨f, hf⟩ : _root_.GlobalTheory.BK.S O K e) hv

variable [NeZero e]


open PowerSeries Filter Topology Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
variable (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) in
variable [NeZero e] in
theorem _root_.GlobalTheory.BK.PhiMod.l_pow_smul_phi_mem_MM {k : ℕ} {v : _root_.GlobalTheory.BK.Vec K a ι}
    (hv : _root_.GlobalTheory.BK.E K l e ^ k • v ∈
      P.Mext (_root_.GlobalTheory.BK.S O K e)) :
    (l : K) ^ k • P.phi v ∈ P.MM := by
  obtain ⟨c, hc, hcE⟩ :=
    _root_.GlobalTheory.BK.exists_mul_frob_E (O := O) (K := K) l e
  set F := _root_.GlobalTheory.BK.frob K l with hF
  set E := _root_.GlobalTheory.BK.E K l e with hE
  have hw : ∀ τ i, (E ^ k • v) τ i ∈ _root_.GlobalTheory.BK.S O K e := by
    intro τ i
    unfold _root_.GlobalTheory.BK.PhiMod.Mext at hv
    rw [_root_.GlobalTheory.BK.mem_tot] at hv
    exact _root_.GlobalTheory.BK.mem_vecs.mp (hv τ) i
  have hmem : P.phi (E ^ k • v) ∈ P.MM := by
    unfold _root_.GlobalTheory.BK.PhiMod.MM
    rw [_root_.GlobalTheory.BK.PhiMod.ext, _root_.GlobalTheory.BK.mem_tot]
    intro τ
    rw [_root_.GlobalTheory.BK.PhiMod.mem_extc]
    refine ⟨_root_.GlobalTheory.BK.frobV l ((E ^ k • v) (τ - 1)), ?_, _root_.GlobalTheory.BK.PhiMod.phi_apply _ _ _⟩
    rw [_root_.GlobalTheory.BK.mem_vecs]
    intro i
    rw [_root_.GlobalTheory.BK.frobV_apply]
    exact _root_.GlobalTheory.BK.frob_mem_S l (hw _ i)
  have heq : (l : K) ^ k • P.phi v =
      ((⟨c, hc⟩ : _root_.GlobalTheory.BK.S O K e) ^ k) •
        P.phi (E ^ k • v) := by
    funext τ i
    have hvec : _root_.GlobalTheory.BK.frobV l ((E ^ k • v) (τ - 1)) =
        F E ^ k • _root_.GlobalTheory.BK.frobV l (v (τ - 1)) := by
      funext j
      simp only [Pi.smul_apply, _root_.GlobalTheory.BK.frobV_apply, smul_eq_mul, map_mul, map_pow, hF]
    change (l : K) ^ k • P.phi v τ i =
      (c ^ k) • P.phi (E ^ k • v) τ i
    rw [_root_.GlobalTheory.BK.PhiMod.phi_apply, _root_.GlobalTheory.BK.PhiMod.phi_apply, hvec, Matrix.mulVec_smul, Pi.smul_apply, smul_smul, ← mul_pow, hcE,
      ← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [heq]
  exact Submodule.smul_mem _ _ hmem

variable {η : ℕ} (hη : ∀ v ∈ P.MM, (l : K) ^ η • P.phi v ∈ P.MM)

include hη

end PhiMod

namespace BKDat

variable [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ} (D : BKDat O K l e a ι η H)

end BKDat

end GlobalTheory.BK
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.PartialInv

def intLat (F : Type) [NormedField F] [IsUltrametricDist F] (r : ℕ) : AddSubgroup (Fin r → F) where
  carrier := Set.univ.pi fun _ => Metric.closedBall (0 : F) 1
  zero_mem' := by intro i _; simp
  add_mem' := by
    intro a b ha hb i _
    have h1 := ha i trivial
    have h2 := hb i trivial
    simp only [mem_closedBall_zero_iff] at h1 h2 ⊢
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)
  neg_mem' := by
    intro a ha i _
    have h1 := ha i trivial
    simpa using h1

theorem mem_intLat {F : Type} [NormedField F] [IsUltrametricDist F] {r : ℕ} (x : Fin r → F) :
    x ∈ intLat F r ↔ ∀ i, ‖x i‖ ≤ 1 := by
  change x ∈ Set.univ.pi (fun _ => Metric.closedBall (0 : F) 1) ↔ _
  simp [Set.mem_pi]

theorem isTest_slice {F : Type} [NormedField F] {r : ℕ} {f : Gl r F → ℂ} (hf : IsTest f)
    (A : Matrix (Fin r) (Fin r) F) (c : Fin r → F) (l : F) : IsTest fun v : Fin r → F => f (A, v, c, l) := by
  have hc : Continuous fun v : Fin r → F => ((A, v, c, l) : Gl r F) := by fun_prop
  refine ⟨hf.1.comp_continuous hc, ?_⟩
  have he : IsClosedEmbedding fun v : Fin r → F => ((A, v, c, l) : Gl r F) := by
    refine Function.LeftInverse.isClosedEmbedding (f := fun Y : Gl r F => Y.2.1) (fun _ => rfl) (by fun_prop) hc
  exact hf.2.comp_isClosedEmbedding he

theorem selfDual_pi (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    letI := M.mF
    SelfDual (Measure.pi fun _ : Fin r => M.μF) (fun x y : Fin r → F => ψ (x ⬝ᵥ y)) := by
  letI := M.mF
  haveI := M.bF
  haveI := M.haarF
  haveI : IsUltrametricDist F := Unram.ultraF E
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  have hcond := ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).2.2.1
  have hsymm : LinearMap.BilinForm.IsSymm (dotProductBilin F F : LinearMap.BilinForm F (Fin r → F)) :=
    ⟨fun x y => by simp [dotProduct_comm]⟩
  have hnd : LinearMap.BilinForm.Nondegenerate (dotProductBilin F F : LinearMap.BilinForm F (Fin r → F)) := by
    constructor
    · intro x hx
      ext i
      simpa using hx (Pi.single i 1)
    · intro x hx
      ext i
      simpa using hx (Pi.single i 1)
  have hopen : IsOpen (intLat F r : Set (Fin r → F)) :=
    isOpen_set_pi Set.finite_univ fun _ _ => IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hcpt : IsCompact (intLat F r : Set (Fin r → F)) :=
    isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hvol : (Measure.pi fun _ : Fin r => M.μF) (intLat F r : Set (Fin r → F)) = 1 := by
    change (Measure.pi fun _ : Fin r => M.μF) (Set.univ.pi fun _ => Metric.closedBall (0 : F) 1) = 1
    rw [Measure.pi_pi]
    simp [M.volF]
  have hdual : {y : Fin r → F | ∀ x ∈ intLat F r,
      ψ ((dotProductBilin F F : LinearMap.BilinForm F (Fin r → F)) x y) = 1} = (intLat F r : Set (Fin r → F)) := by
    ext y
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, mem_intLat, dotProductBilin_apply_apply]
    constructor
    · intro h i
      refine (hcond (y i)).1 fun e he => ?_
      have := h (Pi.single i e) (fun j => by
        by_cases hj : j = i
        · subst hj; simpa using he
        · simp [hj])
      simpa using this
    · intro h x hx
      refine hψ.1 _ ?_
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
      rw [norm_mul]
      exact mul_le_one₀ (hx i) (norm_nonneg _) (h i)
  have key := ((GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ (Fin r → F) (dotProductBilin F F) hsymm hnd
    (Measure.pi fun _ : Fin r => M.μF) inferInstance).1 (intLat F r) hopen hcpt).1
  rw [hdual, hvol] at key
  exact key.2 (mul_one 1)

theorem ptrB_ptrB (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ)
    (f : Gl r F → ℂ) (hf : IsTest f) : WeilMix.ptrB M ψ (WeilMix.ptrB M ψ f) = WeilMix.negB f := by
  funext Y
  exact (selfDual_pi F E r M ψ hψ).2 _ (isTest_slice hf Y.1 Y.2.2.1 Y.2.2.2) Y.2.1

end GlobalTheory.JR.PartialInv
end
end

section

noncomputable section

namespace GlobalTheory.UnitLemma.Unr.Dual

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr

theorem val_mul (K : UQ) {x y : K.E} (hx : x ≠ 0) (hy : y ≠ 0) :
    val K.O (x * y) = val K.O x + val K.O y := by
  unfold val
  rw [map_mul, WithZero.log_mul (by simpa using hx) (by simpa using hy)]
  ring

theorem val_inv (K : UQ) (x : K.E) : val K.O x⁻¹ = - val K.O x := by
  unfold val
  rw [map_inv₀, WithZero.log_inv]

theorem deg_pos {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E} (hU : IsUnrExt K K' d φ) : 0 < d := by
  rcases Nat.eq_zero_or_pos d with h | h
  · exfalso
    have h1 := K'.card_res
    rw [hU.1, h, pow_zero, one_pow] at h1
    have : 1 < Nat.card (IsLocalRing.ResidueField K'.O) := Finite.one_lt_card
    omega
  · exact h

theorem herm_eq_trace {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E} (hU : IsUnrExt K K' d φ) (B : InvAlg K)
    (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e))
    (x y z : B.A) :
    B.herm x y z = @Algebra.trace K.E K'.E _ _ φ.toAlgebra ((overExt φ B ψ hψ hσ).herm x y z) := by
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K'.E B.A := ψ.toAlgebra
  haveI : IsScalarTower K.E K'.E B.A := IsScalarTower.of_algebraMap_eq fun e => (hψ e).symm
  haveI : Module.Finite K.E K'.E := Module.finite_of_finrank_pos
    (by rw [show Module.finrank K.E K'.E = d from hU.2.2.2.2]; exact deg_pos hU)
  haveI : Module.Finite K'.E B.A := Module.Finite.of_restrictScalars_finite K.E K'.E B.A
  show Algebra.trace K.E B.A (x * y * B.σ z) = Algebra.trace K.E K'.E (Algebra.trace K'.E B.A (x * y * B.σ z))
  exact (Algebra.trace_trace _).symm

theorem herm_smul {K K' : UQ} {φ : K.E →+* K'.E} (B : InvAlg K)
    (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e))
    (x y z : B.A) (m : K'.E) (y₀ : K'.O) (hcm : K'.c (algebraMap K'.O K'.E y₀) = m) :
    (overExt φ B ψ hψ hσ).herm x y (y₀ • (show (overExt φ B ψ hψ hσ).A from z)) =
      m * (overExt φ B ψ hψ hσ).herm x y z := by
  letI : Algebra K'.E B.A := ψ.toAlgebra
  have hs : B.σ (ψ (algebraMap K'.O K'.E y₀) * z) = ψ m * B.σ z := by
    rw [map_mul, hσ, hcm]
  show Algebra.trace K'.E B.A (x * y * B.σ (ψ (algebraMap K'.O K'.E y₀) * z)) =
    m * Algebra.trace K'.E B.A (x * y * B.σ z)
  rw [hs, show x * y * (ψ m * B.σ z) = m • (x * y * B.σ z) by
    rw [Algebra.smul_def]; show _ = ψ m * _; ring, LinearMap.map_smul, smul_eq_mul]

end GlobalTheory.UnitLemma.Unr.Dual


open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.Dual in
theorem GlobalTheory.UnitLemma.Unr.dual_iff : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (L : Submodule K'.O (overExt φ B ψ hψ hσ).A) (x y : B.A), (∀ z ∈ L, (overExt φ B ψ hψ hσ).herm x y z ∈ (algebraMap K'.O K'.E).range) ↔ (∀ z ∈ L, B.herm x y z ∈ (algebraMap K.O K.E).range) := by
  intro K K' d φ hU B ψ hψ hσ L x y
  letI : Algebra K.E K'.E := φ.toAlgebra
  have hT : ∀ z, B.herm x y z = Algebra.trace K.E K'.E ((overExt φ B ψ hψ hσ).herm x y z) :=
    fun z => herm_eq_trace hU B ψ hψ hσ x y z
  constructor
  · intro h z hz
    obtain ⟨b, hb⟩ := h z hz
    obtain ⟨a, ha⟩ := GlobalTheory.T.exists_integral_trace_unramifiedQuadraticLocalExt K K' d φ hU b
    refine ⟨a, ?_⟩
    calc algebraMap K.O K.E a = Algebra.trace K.E K'.E (algebraMap K'.O K'.E b) := ha.symm
      _ = Algebra.trace K.E K'.E ((overExt φ B ψ hψ hσ).herm x y z) := by rw [hb]
      _ = B.herm x y z := (hT z).symm
  · intro h z₀ hz₀
    by_contra hw
    have hv : val K'.O ((overExt φ B ψ hψ hσ).herm x y z₀) < 0 := by
      by_contra hle
      push_neg at hle
      obtain ⟨b, hb⟩ := mem_range_of_val_nonneg K' _ hle
      exact hw ⟨b, hb⟩
    have hw0 : (overExt φ B ψ hψ hσ).herm x y z₀ ≠ 0 := by
      intro h0
      exact hw ⟨0, by rw [h0, map_zero]⟩
    obtain ⟨u, a, ha, hua⟩ := GlobalTheory.T.exists_unit_trace_unramifiedInvolutionFieldExt K K' d φ hU
    obtain ⟨π, hπ⟩ := (IsDiscreteValuationRing.maximalIdeal K.O).valuation_exists_uniformizer K.E
    have hπv : val K.O π = 1 := by
      unfold val
      rw [hπ, WithZero.log_exp]
      norm_num
    have hπ0 : π ≠ 0 := by
      rintro rfl
      simp [val] at hπv
    have hφπ : φ π ≠ 0 := (map_ne_zero φ).2 hπ0
    set w := (overExt φ B ψ hψ hσ).herm x y z₀ with hwdef
    set m : K'.E := algebraMap K'.O K'.E u * w⁻¹ * (φ π)⁻¹ with hm
    have hm_int : 0 ≤ val K'.O m := by
      by_cases hu0 : algebraMap K'.O K'.E u = 0
      · rw [hm, hu0, zero_mul, zero_mul]
        simp [val]
      · rw [hm, val_mul K' (mul_ne_zero hu0 (inv_ne_zero hw0)) (inv_ne_zero hφπ),
          val_mul K' hu0 (inv_ne_zero hw0), val_inv, val_inv, hU.2.2.1, hπv]
        have := val_algebraMap_nonneg K' u
        omega
    obtain ⟨m₀, hm₀⟩ := mem_range_of_val_nonneg K' m hm_int
    obtain ⟨y₀, hy₀⟩ := K'.c_int m₀
    have hz₁ : y₀ • z₀ ∈ L := L.smul_mem y₀ hz₀
    have key : (overExt φ B ψ hψ hσ).herm x y (y₀ • z₀) = m * w :=
      herm_smul B ψ hψ hσ x y z₀ m y₀ (by rw [← hy₀, K'.c_c, hm₀])
    obtain ⟨b, hb⟩ := h _ hz₁
    have hb' := hb.trans (hT _)
    rw [key] at hb'
    have hmw : m * w = π⁻¹ • algebraMap K'.O K'.E u := by
      rw [Algebra.smul_def, hm]
      show _ = φ π⁻¹ * _
      rw [map_inv₀]
      field_simp
    rw [hmw, LinearMap.map_smul, hua, smul_eq_mul] at hb'
    have ha0 : algebraMap K.O K.E a ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap K.O K.E), (IsFractionRing.injective K.O K.E).eq_iff]
      exact ha.ne_zero
    have h1 := val_algebraMap_nonneg K b
    rw [hb', val_mul K (inv_ne_zero hπ0) ha0, val_inv, hπv, GlobalTheory.UnitLemma.Orbit.val_unit a ha] at h1
    omega
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp

theorem _root_.GlobalTheory.T.filtration_estimate_expansion_tensorBdR_component : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]  (T : LocLat G Qp LL O) (ι : LL →ₐ[Qp] BdR) (tS pk : BdR), IsUnit tS → tS ∈ PD.Fil 1 → ∀ (r w : ℕ) (z : T.V ⊗[Qp] BdR) (D : Fin r → T.V ⊗[Qp] BdR) (b : Fin r → BdR) (e : Fin r → PowerSeries LL) (L : ℤ → T.V ⊗[Qp] BdR), mulVR T (tS ^ w) z - ∑ j, mulVR T (b j) (D j) ∈ compKer T ι → (∀ (j : Fin r) (m : ℕ), b j - ∑ k ∈ Finset.range m, ι (PowerSeries.coeff k (e j)) * tS ^ k ∈ PD.Fil (m : ℤ)) → (∀ k : ℤ, L k - ∑ j, cz (e j) (k + (w : ℤ)) • D j ∈ compKer T ι) → ∀ a : ℕ, (∀ k : ℤ, k < -(a : ℤ) → L k = 0) → ∃ c : ℤ, ∀ M : ℕ, mulVR T (tS ^ a) (mulVR T pk z) - mulVR T pk (∑ k ∈ Finset.range M, mulVR T (tS ^ k) (L ((k : ℤ) - (a : ℤ)))) ∈ compKer T ι ⊔ FilV PD (LL := LL) (V := T.V) ((M : ℤ) - c) := by
  first | exact @GlobalTheory.HWL.Cmp.filt_expansion_component | exact GlobalTheory.HWL.Cmp.filt_expansion_component | (intros; apply GlobalTheory.HWL.Cmp.filt_expansion_component <;> assumption)
end

section

open ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.card_H2_level_rep_one_le : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)},
    FiniteDimensional ℚ_[p] K → ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] {ϖ : O}, Irreducible ϖ → ∀ {M : Type} [AddCommGroup M] [Module O M],
    (M ≃ₗ[O] Formalism.NG.KO O) → ∀ (ρ : Representation O (Formalism.GaloisCohomology.GK p K) M)
    (h : ((p : O) ^ 1) ∈ Ideal.span {ϖ ^ 1}),
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p 1 h
    ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p 1 h ρ) →
    Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p 1 h ρ)) ≤ Nat.card (IsLocalRing.ResidueField O) := by
  first | exact @GlobalTheory.ShapeNeg.card_H2_level_rep_le | exact GlobalTheory.ShapeNeg.card_H2_level_rep_le | (intros; apply GlobalTheory.ShapeNeg.card_H2_level_rep_le <;> assumption)
end

section

open Formalism.GaloisCohomology ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.finite_H1_H2_local : LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] K → ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation (ZMod (l ^ r)) (GK l K) M), 0 < r → ContAction rho → Finite (H1 rho) ∧ Finite (H2 rho) := by
  first | exact @GlobalTheory.finite_H1_H2_of_localTateDuality | exact GlobalTheory.finite_H1_H2_of_localTateDuality | (intros; apply GlobalTheory.finite_H1_H2_of_localTateDuality <;> assumption)
end
