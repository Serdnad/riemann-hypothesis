module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle001
public import Mathlib.Algebra.Order.PUnit
public import Mathlib.Data.Nat.Prime.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle057
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle040
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle041
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle051
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle072
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle096
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle075
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
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
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.TwCok

theorem pow_torsion_bounded {W : Type} [CommRing W] [IsNoetherianRing W] (r : W) (T : Type 1)
    [AddCommGroup T] [Module W T] [Module.Finite W T] :
    ∃ c : ℕ, ∀ (k : ℕ) (t : T), r ^ k • t = 0 → r ^ c • t = 0 := by
  haveI := isNoetherian_of_isNoetherianRing_of_finite W T
  let f : ℕ →o Submodule W T :=
    ⟨fun k => LinearMap.ker ((r ^ k) • LinearMap.id : T →ₗ[W] T), fun a b hab t ht => by
      simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at ht ⊢
      obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
      rw [pow_add, mul_comm, mul_smul, ht, smul_zero]⟩
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance f
  refine ⟨n, fun k t ht => ?_⟩
  rcases le_total k n with hkn | hnk
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hkn
    rw [pow_add, mul_comm, mul_smul, ht, smul_zero]
  · have h1 : t ∈ f k := by
      simp only [f, OrderHom.coe_mk, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
      exact ht
    rw [← hn k hnk] at h1
    have h2 : t ∈ LinearMap.ker ((r ^ n) • LinearMap.id : T →ₗ[W] T) := h1
    rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at h2
    exact h2

variable {W : Type} [CommRing W] {l : ℕ} {S S' : Sys.{1} W}

def conn (Q : LSeq l S S') (n : ℕ) (x : S.M n) : S'.lim :=
  ⟨fun a => Q.δ n a x, fun a => Q.δ_r n a x⟩

theorem conn_smul (Q : LSeq l S S') (n : ℕ) (s : W) (x : S.M n) :
    s • conn Q n x = conn Q n (s • x) := by
  apply Subtype.ext
  funext a
  simp [conn]

theorem conn_kill (Q : LSeq l S S') (n : ℕ) (x : S.M n) : ((l : W) ^ n) • conn Q n x = 0 := by
  rw [conn_smul, Q.kill n x]
  apply Subtype.ext
  funext a
  simp [conn]

theorem lift_of_conn_zero (Q : LSeq l S S') (hA : ∀ n, IsArtinian W (S.M n)) (n : ℕ) (x : S.M n)
    (h : ∀ a, Q.δ n a x = 0) : ∃ y : S.lim, y.1 n = x := by
  classical
  have hy : ∀ m, n ≤ m → ∃ u : S.M m, Q.ρ m n u = x := fun m hm =>
    Q.ex₂ (m - n) n m (by omega) x (h _)
  let y : ∀ m, S.M m := fun m => if hm : n ≤ m then (hy m hm).choose else 0
  have hyx : ∀ m (hm : n ≤ m), Q.ρ m n (y m) = x := by
    intro m hm
    simp only [y, dif_pos hm]
    exact (hy m hm).choose_spec
  let N : ∀ m, Submodule W (S.M m) := fun m => if n ≤ m then LinearMap.ker (Q.ρ m n) else ⊤
  have hN : ∀ m (hm : n ≤ m), N m = LinearMap.ker (Q.ρ m n) := fun m hm => if_pos hm
  have hN' : ∀ m (hm : ¬ n ≤ m), N m = ⊤ := fun m hm => if_neg hm
  have hNr : ∀ m, ∀ u ∈ N (m + 1), S.r m u ∈ N m := by
    intro m u hu
    by_cases hm : n ≤ m
    · rw [hN (m + 1) (by omega), LinearMap.mem_ker] at hu
      rw [hN m hm, LinearMap.mem_ker, ← Q.ρ_succ m n hm]
      exact hu
    · rw [hN' m hm]
      exact Submodule.mem_top
  have hyr : ∀ m, S.r m (y (m + 1)) - y m ∈ N m := by
    intro m
    by_cases hm : n ≤ m
    · rw [hN m hm, LinearMap.mem_ker, map_sub, ← Q.ρ_succ m n hm, hyx (m + 1) (by omega), hyx m hm,
        sub_self]
    · rw [hN' m hm]
      exact Submodule.mem_top
  obtain ⟨z, hz⟩ := GlobalTheory.T.artinian_limit_lift_of_compatible W S hA N y hNr hyr
  refine ⟨z, ?_⟩
  have h1 := hz n
  rw [hN n le_rfl, LinearMap.mem_ker, map_sub, Q.ρ_self, Q.ρ_self, sub_eq_zero] at h1
  have h2 := hyx n le_rfl
  rw [Q.ρ_self] at h2
  rw [← h2]
  exact h1

theorem lim_cokernel_bounded : ∀ (W : Type) [CommRing W] [IsNoetherianRing W] (l : ℕ) (S S' : Sys.{1} W)
    (_ : LSeq l S S'), (∀ n, IsArtinian W (S.M n)) → Module.Finite W S'.lim →
    ∃ c : ℕ, ∀ n (x : S.M n), ∃ y : S.lim, y.1 n = ((l : W) ^ c) • x := by
  intro W _ _ l S S' Q hA hF
  obtain ⟨c, hc⟩ := pow_torsion_bounded ((l : W)) S'.lim
  refine ⟨c, fun n x => lift_of_conn_zero Q hA n _ (fun a => ?_)⟩
  have h0 : conn Q n ((l : W) ^ c • x) = 0 := by
    rw [← conn_smul]
    exact hc n _ (conn_kill Q n x)
  have h3 := congrArg (fun v : S'.lim => (v : ∀ m, S'.M m) a) h0
  simpa [conn] using h3

end GlobalTheory.CompanionTheory.TwCok
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Dblock.AmiExact

theorem pf_punit (p : ℕ) : Pf p PUnit :=
  ⟨Subsingleton.elim _ _, ⟨fun _ _ _ => Subsingleton.elim _ _, fun b => ⟨b, Subsingleton.elim _ _⟩⟩⟩

theorem tensor_punit_eq_zero {A C : Type} [CommRing A] [AddCommGroup C] [Module A C]
    (w : C ⊗[A] PUnit) : w = 0 := by
  induction w using TensorProduct.induction_on with
  | zero => rfl
  | tmul c u => rw [Subsingleton.elim u 0, TensorProduct.tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

theorem almost_injective {p : ℕ} {A : Type} [CommRing A] {B : Type} [CommRing B] [Algebra A B]
    {r : ℕ → A} (hCov : Cov p r B) (K₀ : Type) [CommRing K₀] [Algebra A K₀] (hK : Pf p K₀)
    (z : K₀) (hz : (1 : B) ⊗ₜ[A] z = 0) (k : ℕ) : r k • z = 0 := by
  have good : Good p r (0 : PUnit →ₗ[A] K₀) := by
    intro C _ _ _ w _ k
    exact ⟨0, (tensor_punit_eq_zero _).trans (tensor_punit_eq_zero _).symm⟩
  have h := hCov PUnit K₀ (pf_punit p) hK 0 good z
    ⟨0, by rw [map_zero, hz]⟩ k
  simpa using h

theorem ker_zero {p : ℕ} {A : Type} [CommRing A] {B : Type} [CommRing B] [Algebra A B]
    {r : ℕ → A} (hCov : Cov p r B) (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)]
    (d : ∀ n, K n →ₗ[A] K (n + 1)) (H : ∀ n, K (n + 1) →ₗ[A] B ⊗[A] K n)
    (hK : ∀ n, Pf p (K n)) (h0 : ∀ z, H 0 (d 0 z) = (1 : B) ⊗ₜ[A] z)
    (z : K 0) (hz : d 0 z = 0) (k : ℕ) : r k • z = 0 :=
  almost_injective hCov (K 0) (hK 0) z (by rw [← h0, hz, map_zero]) k

theorem exact_of_good {p : ℕ} {A : Type} [CommRing A] {B : Type} [CommRing B] [Algebra A B]
    {r : ℕ → A} (hCov : Cov p r B) (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)]
    (d : ∀ n, K n →ₗ[A] K (n + 1)) (H : ∀ n, K (n + 1) →ₗ[A] B ⊗[A] K n)
    (hK : ∀ n, Pf p (K n))
    (hS : ∀ n z, (d n).lTensor B (H n z) + H (n + 1) (d (n + 1) z) = (1 : B) ⊗ₜ[A] z)
    (n : ℕ) (hG : Good p r (d n)) (z : K (n + 1)) (hz : d (n + 1) z = 0) (k : ℕ) :
    r k • z ∈ LinearMap.range (d n) :=
  hCov (K n) (K (n + 1)) (hK n) (hK (n + 1)) (d n) hG z
    ⟨H n z, by simpa [hz] using hS n z⟩ k

theorem lTensor_sq_zero {A C : Type} [CommRing A] [AddCommGroup C] [Module A C]
    {K : ℕ → Type} [∀ n, AddCommGroup (K n)] [∀ n, Module A (K n)]
    (d : ∀ n, K n →ₗ[A] K (n + 1)) (dd : ∀ n z, d (n + 1) (d n z) = 0)
    (n : ℕ) (z : C ⊗[A] K n) : (d (n + 1)).lTensor C ((d n).lTensor C z) = 0 := by
  have h : d (n + 1) ∘ₗ d n = 0 := LinearMap.ext (dd n)
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h, LinearMap.lTensor_zero,
    LinearMap.zero_apply]

theorem exact_succ {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] {B : Type} [CommRing B]
    [Algebra A B] {r : ℕ → A} (hA : Pf p A) (hCov : Cov p r B) (n : ℕ) :
    ∀ (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)]
      (d : ∀ n, K n →ₗ[A] K (n + 1)) (H : ∀ n, K (n + 1) →ₗ[A] B ⊗[A] K n),
      (∀ n, Pf p (K n)) → (∀ n z, d (n + 1) (d n z) = 0) →
      ((∀ z, H 0 (d 0 z) = (1 : B) ⊗ₜ[A] z) ∧
        ∀ n z, (d n).lTensor B (H n z) + H (n + 1) (d (n + 1) z) = (1 : B) ⊗ₜ[A] z) →
      ∀ z, d (n + 1) z = 0 → ∀ k, r k • z ∈ LinearMap.range (d n) := by
  induction n with
  | zero =>
    intro K _ _ d H hK _ hH
    refine exact_of_good hCov K d H hK hH.2 0 ?_
    intro C _ _ hC w hw k
    obtain ⟨H₁, h0', _⟩ := GlobalTheory.CompanionTheory.Dblock.AmiBc.contraction_lTensor A B C K d H hH
    have hz : r k • w = 0 :=
      ker_zero hCov (fun n => C ⊗[A] K n) (fun n => (d n).lTensor C) H₁
        (fun n => GlobalTheory.T.perfect_tensor_product p A C (K n) hA hC (hK n)) h0' w hw k
    rw [hz]
    exact zero_mem _
  | succ n ih =>
    intro K _ _ d H hK dd hH
    refine exact_of_good hCov K d H hK hH.2 (n + 1) ?_
    intro C _ _ hC w hw k
    obtain ⟨H₁, h0', hS'⟩ := GlobalTheory.CompanionTheory.Dblock.AmiBc.contraction_lTensor A B C K d H hH
    obtain ⟨v, hv⟩ := ih (fun n => C ⊗[A] K n) (fun n => (d n).lTensor C) H₁
      (fun n => GlobalTheory.T.perfect_tensor_product p A C (K n) hA hC (hK n))
      (fun n z => lTensor_sq_zero d dd n z) ⟨h0', hS'⟩ w hw k
    refine ⟨((d n).codRestrict (LinearMap.ker (d (n + 1))) (fun z => dd n z)).lTensor C v, ?_⟩
    rw [← hv, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    rfl

theorem exact_of_contraction :
    ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (r : ℕ → A), Pf p A → Cov p r B → ∀ (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (d : ∀ n, K n →ₗ[A] K (n + 1)) (H : ∀ n, K (n + 1) →ₗ[A] B ⊗[A] K n), (∀ n, Pf p (K n)) → (∀ n z, d (n + 1) (d n z) = 0) → ((∀ z, H 0 (d 0 z) = (1 : B) ⊗ₜ[A] z) ∧ ∀ n z, (d n).lTensor B (H n z) + H (n + 1) (d (n + 1) z) = (1 : B) ⊗ₜ[A] z) → (∀ z, d 0 z = 0 → ∀ k, r k • z = 0) ∧ ∀ n z, d (n + 1) z = 0 → ∀ k, r k • z ∈ LinearMap.range (d n) := by
  intro p _ A _ B _ _ r hA hCov K _ _ d H hK dd hH
  exact ⟨fun z hz k => ker_zero hCov K d H hK hH.1 z hz k,
    fun n z hz k => exact_succ hA hCov n K d H hK dd hH z hz k⟩

end GlobalTheory.CompanionTheory.Dblock.AmiExact
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem pq_baseChange : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](S : Type) [CommRing S] [Algebra A S] (B : Type) [CommRing B] [Algebra A B] (K : Type) [CommRing K] [Algebra A K](S₁ : Type) [CommRing S₁] (i : S →ₐ[A] B) (I : Ideal S) (κ : K →+* S₁) (j : S →+* S₁) (i₁ : S₁ →+* B ⊗[A] K), Pf p A → Pf p K → PQ p (i : S →+* B) I → κ.comp (algebraMap A K) = j.comp (algebraMap A S) → Subring.closure (Set.range κ ∪ Set.range j) = ⊤ → (∀ a, i₁ (κ a) = (1 : B) ⊗ₜ[A] a) → (∀ s, i₁ (j s) = i s ⊗ₜ[A] (1 : K)) → PQ p i₁ (I.map j) := by
  intro p _ A _ S _ _ B _ _ K _ _ S₁ _ i I κ j i₁ hA hK hQ hcomm hgen hκ hj
  have hT : Pf p (B ⊗[A] K) := GlobalTheory.T.perfect_tensor_product p A B K hA hQ.pf hK
  obtain ⟨-, hred, -, -, -⟩ := pf_facts p _ hT
  have hpS : (p : S₁) = 0 := by
    have h := congrArg κ hK.char
    simpa using h
  have addT : ∀ (k : ℕ) (a b : B ⊗[A] K), (a + b) ^ p ^ k = a ^ p ^ k + b ^ p ^ k := by
    intro k a b
    obtain ⟨F, hF⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p (B ⊗[A] K) hT.char k
    rw [← hF, ← hF, ← hF, map_add (f := _)]
  have hkill : ∀ x ∈ I.map j, i₁ x = 0 := by
    have hle : I.map j ≤ RingHom.ker i₁ := by
      refine Ideal.map_le_iff_le_comap.2 fun s hs => ?_
      have h0 : (i : S →+* B) s = 0 := (hQ.ker s).2 ⟨0, by simpa using hs⟩
      have h1 : i s = 0 := h0
      rw [Ideal.mem_comap, RingHom.mem_ker, hj, h1, TensorProduct.zero_tmul]
    exact fun x hx => hle hx
  refine ⟨hT, ?_, ?_⟩
  · intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul b a =>
      obtain ⟨k, s, hs⟩ := hQ.pow b
      have hs' : b ^ p ^ k = i s := hs
      refine ⟨k, j s * κ (a ^ p ^ k), ?_⟩
      rw [map_mul, hj, hκ, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_pow, hs']
      simp
    | add y y' h h' =>
      obtain ⟨k, x, hx⟩ := h
      obtain ⟨k', x', hx'⟩ := h'
      refine ⟨k + k', x ^ p ^ k' + x' ^ p ^ k, ?_⟩
      rw [addT, map_add (f := _), map_pow, map_pow, ← hx, ← hx', ← pow_mul, ← pow_mul, ← pow_add, ← pow_add,
        Nat.add_comm k' k]
  · intro x
    constructor
    · intro hx
      obtain ⟨T', _, i', hQ'⟩ := GlobalTheory.CompanionTheory.PerfClos.exists_PQ p S₁ (I.map j) hpS
      have hφ : ∀ s ∈ I, (i'.comp j) s = 0 := fun s hs =>
        (hQ'.ker (j s)).2 ⟨0, by simpa using Ideal.mem_map_of_mem j hs⟩
      obtain ⟨ψ, hψ, -⟩ := pq_lift p S B T' (i : S →+* B) I (i'.comp j) hQ hQ'.pf hφ
      have hψs : ∀ s, ψ (i s) = i' (j s) := fun s => by
        have h := RingHom.congr_fun hψ s
        simpa using h
      letI : Algebra A T' := ((i'.comp κ).comp (algebraMap A K)).toAlgebra
      have hal : ∀ a, algebraMap A T' a = i' (κ (algebraMap A K a)) := fun a => rfl
      let ψA : B →ₐ[A] T' :=
        { ψ with
          commutes' := fun a => by
            have h1 : algebraMap A B a = i (algebraMap A S a) := (i.commutes a).symm
            have h2 := RingHom.congr_fun hcomm a
            simp only [RingHom.comp_apply] at h2
            change ψ (algebraMap A B a) = _
            rw [h1, hψs, hal, h2] }
      let κA : K →ₐ[A] T' :=
        { i'.comp κ with
          commutes' := fun a => rfl }
      let ρ : B ⊗[A] K →ₐ[A] T' := Algebra.TensorProduct.productMap ψA κA
      have hρ : ((ρ : B ⊗[A] K →+* T').comp i₁) = i' := by
        refine RingHom.eq_of_eqOn_set_dense hgen ?_
        rintro y (⟨a, rfl⟩ | ⟨s, rfl⟩)
        · change ρ (i₁ (κ a)) = i' (κ a)
          rw [hκ]
          simp [ρ, κA]
        · change ρ (i₁ (j s)) = i' (j s)
          rw [hj]
          simp [ρ, ψA, hψs]
      have h0 : i' x = 0 := by
        rw [← hρ, RingHom.comp_apply, hx, map_zero]
      exact (hQ'.ker x).1 h0
    · rintro ⟨k, hk⟩
      have h := hkill _ hk
      rw [map_pow] at h
      exact hred _ _ h

end GlobalTheory.CompanionTheory.PerfectRing
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.CovRoot

theorem exists_retraction {A : Type} [CommRing A] (P : Polynomial A) (hP : P.Monic)
    (hd : 0 < P.natDegree) : ∃ ρ : AdjoinRoot P →ₗ[A] A, ρ 1 = 1 := by
  let b := AdjoinRoot.powerBasis' hP
  have h0 : 0 < b.dim := by simpa [b] using hd
  refine ⟨b.basis.coord ⟨0, h0⟩, ?_⟩
  have h1 : b.basis ⟨0, h0⟩ = 1 := by simp
  change b.basis.repr 1 ⟨0, h0⟩ = 1
  rw [← h1, b.basis.repr_self]
  simp

theorem cov_root : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A)
    (P : Polynomial A), Pf p A → P.Monic → 0 < P.natDegree →
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧
      ∃ x : B, Polynomial.aeval x P = 0 := by
  intro p _ A _ r P hA hP hd
  have hpS : (p : AdjoinRoot P) = 0 := by
    have := congrArg (algebraMap A (AdjoinRoot P)) hA.char
    simpa using this
  obtain ⟨T, _, i, hq⟩ := GlobalTheory.CompanionTheory.PerfClos.exists_PQ p (AdjoinRoot P) ⊥ hpS
  letI : Algebra A T := (i.comp (algebraMap A (AdjoinRoot P))).toAlgebra
  let i' : AdjoinRoot P →ₐ[A] T := { i with commutes' := fun _ => rfl }
  have hq' : PQ p (i' : AdjoinRoot P →+* T) ⊥ := hq
  refine ⟨T, inferInstance, inferInstance, hq.pf, ?_, i' (AdjoinRoot.root P), ?_⟩
  · refine GlobalTheory.CompanionTheory.CovCmp.cov_of_solv p A T r fun m n a c hs => ?_
    refine ⟨A, inferInstance, inferInstance, GlobalTheory.CompanionTheory.CovMono.cov_self p A r, ?_⟩
    obtain ⟨k, s, hs'⟩ := GlobalTheory.T.frobenius_power_solution_lift p A (AdjoinRoot P) T i' ⊥ m n a c hA.char hq' hs
    refine GlobalTheory.T.perfect_frobenius_root_solution p A A m n k a c hA ?_
    obtain ⟨ρ, hρ⟩ := exists_retraction P hP hd
    have hρa : ∀ x : A, ρ (algebraMap A (AdjoinRoot P) x) = x := fun x => by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, hρ, smul_eq_mul, mul_one]
    refine ⟨fun j => ρ (s j), fun t => ?_⟩
    have h := sub_eq_zero.mp ((Ideal.mem_bot).mp (hs' t))
    have h2 := congrArg ρ h

    rw [map_sum, hρa] at h2
    simpa using h2
  · rw [Polynomial.aeval_algHom_apply]
    have : Polynomial.aeval (AdjoinRoot.root P) P = 0 := by
      simp [AdjoinRoot.aeval_eq]
    rw [this, map_zero]

end GlobalTheory.CompanionTheory.CovRoot
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.EtaleLift

theorem lift_hom_existsUnique {O R Λ : Type} [CommRing O] [CommRing R] [CommRing Λ] (a : O →+* R) {d : ℕ}
    (T : Fin d → R) (I : Ideal Λ) (κ : O →+* Λ ⧸ I) (𝓛 : Lift a T Λ I κ) {B : Type} [CommRing B]
    (J : Ideal B) : EtLift J → ∀ (h : Λ →+* B) (g : R →+* B ⧸ J) (u : Fin d → B), I ≤ J.comap h →
    (∀ o x, Ideal.Quotient.mk I x = κ o → g (a o) = Ideal.Quotient.mk J (h x)) →
    (∀ k, Ideal.Quotient.mk J (u k) = g (T k)) →
    ∃! f : 𝓛.D →+* B, f.comp 𝓛.i = h ∧ (∀ k, f (𝓛.t k) = u k) ∧
      ∀ r z, Ideal.Quotient.mk _ z = 𝓛.j r → Ideal.Quotient.mk J (f z) = g r := by
  intro hEt h g u hIJ hg hu
  obtain ⟨g0, ⟨hg0i, hg0j⟩, hg0u⟩ := 𝓛.univ (B ⧸ J) ((Ideal.Quotient.mk J).comp h) g
    (fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ hx)) (fun o x hx => hg o x hx)
  have hcomm : g0.comp (MvPolynomial.eval₂Hom 𝓛.i 𝓛.t) =
      (Ideal.Quotient.mk J).comp (MvPolynomial.eval₂Hom h u) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      exact RingHom.congr_fun hg0i c
    · intro k
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      rw [hu k]
      exact hg0j (T k) (𝓛.t k) (𝓛.hT k).symm
  obtain ⟨F, ⟨hFψ, hFg⟩, hFu⟩ :=
    hEt _ _ (MvPolynomial.eval₂Hom 𝓛.i 𝓛.t) 𝓛.et (MvPolynomial.eval₂Hom h u) g0 hcomm
  refine ⟨F, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact RingHom.ext fun c => by simpa using RingHom.congr_fun hFψ (MvPolynomial.C c)
  · exact fun k => by simpa using RingHom.congr_fun hFψ (MvPolynomial.X k)
  · intro r z hz
    rw [← hg0j r z hz]
    exact RingHom.congr_fun hFg z
  · rintro f' ⟨hf'i, hf't, hf'j⟩
    apply hFu
    refine ⟨?_, ?_⟩
    · apply MvPolynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
        exact RingHom.congr_fun hf'i c
      · intro k
        simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
        exact hf't k
    · apply hg0u
      refine ⟨?_, ?_⟩
      · rw [RingHom.comp_assoc, hf'i]
      · intro r z hz
        exact hf'j r z hz

end GlobalTheory.CompanionTheory.EtaleLift
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.ThickSub

theorem subThick_onto {O : Type} [CommRing O] {F : Fn O} (V : F.Sub) (b : Base) (ht : b.t = 1)
    (κ : O →+* b.R ⧸ b.I) : Onto (subThick V b ht κ) fun T => V.In T.y.1.2 := by
  refine ⟨⟨fun {T T'} f => ⟨{
      φ := f.φ, u := f.u, comm := f.comm, dp := f.dp, hle := f.hle,
      pt := Subtype.ext (Prod.ext (congrArg (fun z => z.1.1) f.pt)
        (Subtype.ext (congrArg (fun z => z.1.2) f.pt))),
      hx := fun j => j.elim, hs := f.hs, hv := fun j => j.elim }, rfl⟩⟩,
    ⟨fun {T T'} f g h => Thick.Hom.ext (congrArg (fun m => m.φ) h) (funext fun j => j.elim)⟩,
    fun T => T.y.1.2.2, fun T h => ?_⟩
  refine ⟨{ B := T.B, i := T.i, J := T.J, δ := T.δ, adm := T.adm, compat := T.compat, α := (),
            y := ⟨(T.y.1.1, ⟨T.y.1.2, h⟩), T.y.2⟩, inα := trivial, w := T.w, x := T.x, v := T.v, s := T.s,
            hx := fun j => j.elim, hs := T.hs, hv := T.hv }, ⟨eqToIso rfl⟩⟩

end GlobalTheory.CompanionTheory.ThickSub
end

section

open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Casselman

theorem exists_mem_inf_conj_of_isDom : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : PositivityTheory.SphericalProduct.CassData G), ∀ t : D.T, D.IsDom t → ∀ y ∈ D.J,
      ∃ a ∈ D.J ⊓ D.N, a⁻¹ * y ∈ D.J ⊓ D.J.map (MulAut.conj (t : G)).toMonoidHom := by
  intro G _ _ _ D t ht y hy
  obtain ⟨c, hc, b, hb, a, ha, rfl⟩ := D.fact_up y hy
  have hb' : b ∈ D.J := (Subgroup.mem_inf.1 hb).1
  have ha' : a ∈ D.J := (Subgroup.mem_inf.1 ha).1
  have hbt : (t : G)⁻¹ * b * t ∈ D.J := (Subgroup.mem_inf.1 (ht.2.2 b hb).2).1
  have hat : (t : G)⁻¹ * a * t ∈ D.J := (Subgroup.mem_inf.1 (ht.2.1 a ha)).1
  have he : c⁻¹ * (c * b * a) = b * a := by group
  refine ⟨c, hc, Subgroup.mem_inf.2 ⟨?_, ?_⟩⟩
  · rw [he]
    exact D.J.mul_mem hb' ha'
  · rw [he, Subgroup.mem_map]
    refine ⟨((t : G)⁻¹ * b * t) * ((t : G)⁻¹ * a * t), D.J.mul_mem hbt hat, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

end GlobalTheory.CompanionTheory.Casselman
end
