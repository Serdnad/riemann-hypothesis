module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle082
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle088
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle085
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle011

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.MomT.CocInt

variable {X : Fields} (A : Amb X) {a b : ℕ}

theorem hv_apply {ι : Type} [Fintype ι] (sc : ℝ) (z w : VV ι a b) :
    HV sc z w = (sc : ℂ) * ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) := rfl

theorem hv_swap {ι : Type} [Fintype ι] (sc : ℝ) (z w : VV ι a b) :
    HV sc w z = (starRingEnd ℂ) (HV sc z w) := by

  simp only [hv_apply, map_mul, map_sum, Complex.conj_ofReal, Complex.conj_conj]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem emb_apply (x : HomE X.E a b) (τ : X.Tau) (i : Fin b) (j : Fin a) :
    emb A x τ i j = A.δ * X.embC A.σ₀ τ (x (Pi.single j 1) i) := rfl

theorem hv_smul (hX : X.Ok) (r : X.E) (x y : HomE X.E a b) :
    HV A.sc (emb A (r • x)) (emb A y) = HV A.sc (emb A x) (emb A (star r • y)) := by
  rw [hv_apply, hv_apply]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [emb_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, hX.conjE, Complex.conj_conj]
  ring

theorem emb_add (x y : HomE X.E a b) : emb A (x + y) = emb A x + emb A y := map_add (embH _ _) x y

theorem coc_add_left (x y z : HomE X.E a b) : coc A (x + y) z = coc A x z + coc A y z := by
  simp only [coc, imH, altE, emb_add, map_add (f := _), LinearMap.add_apply, Complex.add_re, Complex.add_im]
  ring

theorem coc_zero_left (z : HomE X.E a b) : coc A 0 z = 0 := by
  have := coc_add_left A 0 0 z
  rw [add_zero] at this
  linarith

theorem emb_injective (hX : X.Ok) (hδ : A.δ ≠ 0) : Function.Injective (emb A : HomE X.E a b → _) := by
  intro x y h
  obtain ⟨τ⟩ : Nonempty X.Tau := Fintype.card_pos_iff.1 hX.f_pos
  refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
  funext i
  have := congrFun (congrFun (congrFun h τ) i) j
  rw [emb_apply, emb_apply] at this
  simpa using (X.embC A.σ₀ τ).injective (mul_left_cancel₀ hδ this)

variable {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)}

theorem emb_mem {x : HomE X.E a b} (hx : x ∈ per A N N') : emb A x ∈ LamC (X.embC A.σ₀) A.δ A.AA N N' :=
  ⟨x, hx, rfl⟩

theorem mem_per_iff (hX : X.Ok) (hδ : A.δ ≠ 0) (hL : LaFacts (X.embC A.σ₀) A.δ A.d A.sc A.AA N N') (x : HomE X.E a b) :
    x ∈ per A N N' ↔ ∀ y ∈ per A N N', ∃ n : ℤ, imH A x y = n := by
  constructor
  · intro hx y hy
    have h1 := emb_mem A hx
    rw [← hL.1] at h1
    exact h1 _ (emb_mem A hy)
  · intro h
    have h1 : emb A x ∈ dualLat (HV A.sc) (LamC (X.embC A.σ₀) A.δ A.AA N N') := by
      rintro _ ⟨y, hy, rfl⟩
      exact h y hy
    rw [hL.1] at h1
    obtain ⟨x', hx', e⟩ := h1
    rwa [← emb_injective A hX hδ (a₁ := x') e]

theorem coc_int (hX : X.Ok) (hδ : A.δ ≠ 0) (hL : LaFacts (X.embC A.σ₀) A.δ A.d A.sc A.AA N N') {x y : HomE X.E a b}
    (hx : x ∈ per A N N') (hy : y ∈ per A N N') : ∃ n : ℤ, coc A x y = n := by
  obtain ⟨m, hm⟩ := (mem_per_iff A hX hδ hL x).1 hx y hy
  have h := hL.2.2 _ (emb_mem A hx) _ (emb_mem A hy)
  simp only [alV, alphaQ, Formalism.L2.Th1.H.qOf] at h
  rw [← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨n, hn⟩ := h
  refine ⟨n + m, ?_⟩
  have h2 := congrArg Complex.im hn
  have h3 : (HV A.sc (emb A y) (emb A x)).re = (HV A.sc (emb A x) (emb A y)).re := by
    rw [hv_swap]; simp
  simp only [imH] at hm
  simp only [map_add (f := _), LinearMap.add_apply, Complex.add_re, h3, hm] at h2
  simp at h2
  simp only [coc, imH, hm]
  push_cast
  apply mul_left_cancel₀ Real.pi_ne_zero
  linarith

theorem cocycle_integral : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), X.Ok → A.δ ≠ 0 → LaFacts (X.embC A.σ₀) A.δ A.d A.sc A.AA N N' → (∀ (r : X.E) (x y : HomE X.E a b), coc A (r • x) y = coc A x (star r • y) ∧ imH A (r • x) y = imH A x (star r • y)) ∧ (∀ x : HomE X.E a b, x ∈ per A N N' ↔ ∀ y ∈ per A N N', ∃ n : ℤ, imH A x y = n) ∧ ∀ x y : HomE X.E a b, (∀ Q : HeightOneSpectrum (𝓞 X.E), ∃ k : X.E, k ≠ 0 ∧ k⁻¹ • x ∈ localization₂ Q.asIdeal (per A N N') ∧ star k • y ∈ localization₂ (conjPrime₂ Q).asIdeal (per A N N')) → ∃ n : ℤ, coc A x y = n := by
  intro X A a b N N' hX hδ hL
  have h1 : ∀ (r : X.E) (x y : HomE X.E a b), coc A (r • x) y = coc A x (star r • y) ∧ imH A (r • x) y = imH A x (star r • y) := by
    intro r x y
    simp only [coc, imH, altE, hv_smul A hX, and_self]
  refine ⟨h1, mem_per_iff A hX hδ hL, fun x y h => ?_⟩
  let I : Ideal (𝓞 X.E) :=
    { carrier := {r | ∀ s : 𝓞 X.E, ∃ n : ℤ, coc A ((s * r) • x) y = n}
      zero_mem' := fun s => ⟨0, by simp [coc_zero_left]⟩
      add_mem' := fun {r r'} hr hr' s => by
        obtain ⟨n, hn⟩ := hr s
        obtain ⟨m, hm⟩ := hr' s
        exact ⟨n + m, by rw [mul_add, add_smul, coc_add_left, hn, hm, Int.cast_add]⟩
      smul_mem' := fun c r hr s => by
        rw [smul_eq_mul, ← mul_assoc]
        exact hr _ }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    let Q : HeightOneSpectrum (𝓞 X.E) :=
      ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField X.E)⟩
    obtain ⟨k, hk, hx, hy⟩ := h Q
    obtain ⟨u, hu, hx⟩ := (mem_locP _ _ _).1 hx
    obtain ⟨v, hv, hy⟩ := (mem_locP _ _ _).1 hy
    have hmem : u * cO X.E v ∈ I := by
      intro s
      obtain ⟨n, hn⟩ := coc_int A hX hδ hL (Submodule.smul_mem _ s hx) hy
      refine ⟨n, ?_⟩
      rw [← hn]
      have e1 : (s * (u * cO X.E v)) • x = (star (algebraMap (𝓞 X.E) X.E v) * k) • (s • u • k⁻¹ • x) := by
        rw [← algebraMap_smul X.E s, ← algebraMap_smul X.E u, ← algebraMap_smul X.E (s * _), smul_smul, smul_smul, smul_smul,
          map_mul, map_mul, algebraMap_cO]
        congr 1
        field_simp
      rw [e1, (h1 _ _ _).1, star_mul', star_star, mul_smul, algebraMap_smul]
    rcases hM.isPrime.mem_or_mem (hle hmem) with h' | h'
    · exact hu h'
    · exact hv h'
  have : (1 : 𝓞 X.E) ∈ I := hI ▸ Submodule.mem_top
  simpa using this 1

end GlobalTheory.MomT.CocInt
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.CommonRef

section

variable {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module (𝓞 E) W] [Module E W] [IsScalarTower (𝓞 E) E W]

theorem exists_nat_mul_integral (a : E) : ∃ n : ℕ, 0 < n ∧ ∃ r : 𝓞 E, (n : E) * a = algebraMap (𝓞 E) E r := by
  have ha : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hint⟩ := ha.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  have h2 : IsIntegral ℤ ((y.natAbs : E) * a) := by
    rw [zsmul_eq_mul] at hint
    rcases Int.natAbs_eq y with h | h
    · have := congrArg (Int.cast : ℤ → E) h
      rw [Int.cast_natCast] at this
      rwa [this] at hint
    · have := congrArg (Int.cast : ℤ → E) h
      rw [Int.cast_neg, Int.cast_natCast] at this
      rw [this, neg_mul] at hint
      simpa using hint.neg
  exact ⟨⟨_, h2⟩, rfl⟩

theorem full_of_span {M : Submodule (𝓞 E) W} (hM : Submodule.span E (M : Set W) = ⊤) : Full M := by
  intro x
  have hx : x ∈ Submodule.span E (M : Set W) := hM ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, Nat.one_pos, by simpa using hx⟩
  | zero => exact ⟨1, Nat.one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hx⟩ := hx
    obtain ⟨m, hm, hy⟩ := hy
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [Nat.cast_mul, mul_comm, mul_smul]; exact M.smul_mem _ hx
    · rw [Nat.cast_mul, mul_smul]; exact M.smul_mem _ hy
  | smul a x _ hx =>
    obtain ⟨n, hn, hx⟩ := hx
    obtain ⟨m, hm, r, hr⟩ := exists_nat_mul_integral a
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have : ((n * m : ℕ) : 𝓞 E) • a • x = r • (n : 𝓞 E) • x := by
      simp only [← algebraMap_smul E (_ : 𝓞 E), smul_smul, map_natCast, ← hr]
      congr 1
      push_cast
      ring
    rw [this]
    exact M.smul_mem _ hx

omit [Module E W] [IsScalarTower (𝓞 E) E W] in
theorem exists_nat_smul_le {M N : Submodule (𝓞 E) W} (hM : Full M) (hN : N.FG) :
    ∃ m : ℕ, 0 < m ∧ ∀ x ∈ N, (m : 𝓞 E) • x ∈ M := by
  first
  | exact @_root_.GlobalTheory.FinitelyGeneratedNatMultiple.exists_nat_smul_mem_of_fg
  | exact _root_.GlobalTheory.FinitelyGeneratedNatMultiple.exists_nat_smul_mem_of_fg
  | (apply _root_.GlobalTheory.FinitelyGeneratedNatMultiple.exists_nat_smul_mem_of_fg <;> assumption)
  | (intros; apply _root_.GlobalTheory.FinitelyGeneratedNatMultiple.exists_nat_smul_mem_of_fg <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FinitelyGeneratedNatMultiple.exists_nat_smul_mem_of_fg <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FinitelyGeneratedNatMultiple.exists_nat_smul_mem_of_fg ..)

theorem smul_mem_locP {M N : Submodule (𝓞 E) W} {m : ℕ} (h : ∀ x ∈ N, (m : 𝓞 E) • x ∈ M) (Q : HeightOneSpectrum (𝓞 E))
    {x : W} (hx : x ∈ localization₂ Q.asIdeal N) : (m : E) • x ∈ localization₂ Q.asIdeal M := by
  obtain ⟨s, hs, hx⟩ := hx
  refine ⟨s, hs, ?_⟩
  have := h _ hx
  rwa [smul_comm, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E] at this

theorem mem_localization_of_inv_smul_mem {M N : Submodule (𝓞 E) W} {m : ℕ} (hm : 0 < m) (h : ∀ x ∈ N, (m : 𝓞 E) • x ∈ M)
    (Q : HeightOneSpectrum (𝓞 E)) {x : W} (hx : (m : E)⁻¹ • x ∈ localization₂ Q.asIdeal N) : x ∈ localization₂ Q.asIdeal M := by
  have hmE : (m : E) ≠ 0 := by exact_mod_cast hm.ne'
  have := smul_mem_locP h Q hx
  rwa [smul_smul, mul_inv_cancel₀ hmE, one_smul] at this

theorem dom_twO [StarRing E] (S : Finset (HeightOneSpectrum (𝓞 E))) {M N : Submodule (𝓞 E) W} {m : ℕ} (hm : 0 < m)
    (h₁ : ∀ x ∈ N, (m : 𝓞 E) • x ∈ M) (h₂ : ∀ x ∈ M, (m : 𝓞 E) • x ∈ N)
    (hQ : ∀ Q : HeightOneSpectrum (𝓞 E), Q ∉ S → conjPrime₂ Q ∉ S → localization₂ Q.asIdeal M = localization₂ Q.asIdeal N) :
    Dom S M (twist₂ N m (expS S)) ∧ Dom S (twist₂ N m fun Q => -expS S Q) M := by
  have hb := expS_bound S
  have hb' : ∀ Q, -1 ≤ -expS S Q ∧ -expS S Q ≤ 1 := fun Q => by have := hb Q; omega
  refine ⟨⟨fun P hP x hx => ?_, fun Q hS x hx => ?_⟩, fun P hP x hx => ?_, fun Q hS x hx => ?_⟩
  · rw [mem_localization_twist N hm hb] at hx
    have e : expS S P = 1 := by simp [expS, hP]
    rw [e, zpow_one] at hx
    exact mem_localization_of_inv_smul_mem hm h₁ P hx
  · rw [mem_localization_twist N hm hb]
    by_cases hc : conjPrime₂ Q ∈ S
    · have e : expS S Q = -1 := by simp [expS, hS, hc]
      rw [e, zpow_neg_one, inv_inv]
      exact smul_mem_locP h₂ Q hx
    · have e : expS S Q = 0 := by simp [expS, hS, hc]
      rw [e, zpow_zero, inv_one, one_smul, ← hQ Q hS hc]
      exact hx
  · rw [mem_localization_twist N hm hb']
    have e : expS S P = 1 := by simp [expS, hP]
    rw [e, zpow_neg_one, inv_inv]
    exact smul_mem_locP h₂ P hx
  · rw [mem_localization_twist N hm hb'] at hx
    by_cases hc : conjPrime₂ Q ∈ S
    · have e : expS S Q = -1 := by simp [expS, hS, hc]
      rw [e, neg_neg, zpow_one] at hx
      exact mem_localization_of_inv_smul_mem hm h₁ Q hx
    · have e : expS S Q = 0 := by simp [expS, hS, hc]
      rw [e, neg_zero, zpow_zero, inv_one, one_smul, ← hQ Q hS hc] at hx
      exact hx

end

theorem common_refinement : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (M₁ M₂ : Submodule (𝓞 E) (Sp E n)) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ P ∈ S, conjPrime₂ P ∉ S) → IsSdLat M₁ → IsSdLat M₂ → (∀ Q : HeightOneSpectrum (𝓞 E), Q ∉ S → conjPrime₂ Q ∉ S → localization₂ Q.asIdeal M₁ = localization₂ Q.asIdeal M₂) → ∃ F G : Submodule (𝓞 E) (Sp E n), IsSdLat F ∧ IsSdLat G ∧ Dom S M₁ F ∧ Dom S M₂ F ∧ Dom S G M₁ ∧ Dom S G M₂ := by
  intro E _ _ _ n M₁ M₂ S hS h₁ h₂ hQ
  have hfull (L : Submodule (𝓞 E) (Sp E n)) (hL : IsSdLat L) : Full L := by
    apply full_of_span
    let W := Submodule.span E (L : Set (Sp E n))
    change W = ⊤
    by_contra h
    let e : Sp E n ≃ₗ⋆[E] Sp E n := starLinearEquiv E
    let g : Sp E n →ₗ[E] Module.Dual E W :=
      (LinearMap.domRestrict' W).comp ((hStd E n).comp e.toLinearMap)
    have hdim : Module.finrank E (Module.Dual E W) < Module.finrank E (Sp E n) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt h
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    have hsmul (a : E) : a • e x ∈ L := by
      rw [← hL.2, dualBasic_mem_dual]
      intro y hy
      apply hStd_mem_one_symm
      have hxy : hStd E n (e x) y = 0 :=
        congrArg (fun f : Module.Dual E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
      simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hxy]
    let i : E →ₗ[𝓞 E] L :=
      ((LinearMap.toSpanSingleton E _ (e x)).restrictScalars (𝓞 E)).codRestrict L hsmul
    let : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hL.1.fg
    let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  obtain ⟨a, ha, hA⟩ := exists_nat_smul_le (hfull M₁ h₁) h₂.1.fg
  obtain ⟨b, hb, hB⟩ := exists_nat_smul_le (hfull M₂ h₂) h₁.1.fg
  have hm : 0 < a * b := Nat.mul_pos ha hb
  have hA' : ∀ x ∈ M₂, ((a * b : ℕ) : 𝓞 E) • x ∈ M₁ := fun x hx => by
    rw [Nat.cast_mul, mul_comm, mul_smul]; exact M₁.smul_mem _ (hA x hx)
  have hB' : ∀ x ∈ M₁, ((a * b : ℕ) : 𝓞 E) • x ∈ M₂ := fun x hx => by
    rw [Nat.cast_mul, mul_smul]; exact M₂.smul_mem _ (hB x hx)
  have hC : ∀ x ∈ M₂, ((a * b : ℕ) : 𝓞 E) • x ∈ M₂ := fun x hx => M₂.smul_mem _ hx
  obtain ⟨hF, hG⟩ := GlobalTheory.ThetaMove.TwistSd.isSdLat_twO_expS E n M₂ (a * b) S hS h₂ hm
  obtain ⟨d₁, d₂⟩ := dom_twO S hm hA' hB' hQ
  obtain ⟨d₃, d₄⟩ := dom_twO S hm hC hC fun _ _ _ => rfl
  exact ⟨_, _, hF, hG, d₁, d₃, d₂, d₄⟩

end GlobalTheory.ThetaMove.CommonRef
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.VolumePos

section Index

variable {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module (𝓞 E) W]

theorem relIndex_ne_zero {M₀ M : Submodule (𝓞 E) W} (h₀ : Full M₀) (hM : M.FG) :
    M₀.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 := by
  haveI : Module.Finite (𝓞 E) M := Module.Finite.iff_fg.2 hM
  haveI : Module.Finite ℤ M := Module.Finite.trans (𝓞 E) M
  haveI : AddGroup.FG M.toAddSubgroup := Module.Finite.iff_addGroup_fg.1 ‹Module.Finite ℤ M›
  have : Finite (M.toAddSubgroup ⧸ M₀.toAddSubgroup.addSubgroupOf M.toAddSubgroup) := by
    apply AddCommGroup.finite_of_fg_torsion
    intro q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨n, hn, hx⟩ := h₀ x
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    rw [Nat.cast_smul_eq_nsmul] at hx
    exact hx
  exact AddSubgroup.index_ne_zero_of_finite

theorem relIndex_localized_ne_zero (P : HeightOneSpectrum (𝓞 E)) {M₀ M : Submodule (𝓞 E) W} (h₀ : Full M₀) (h : Full M) (hM : M.FG) :
    (localization₂ P.asIdeal M₀).toAddSubgroup.relIndex (localization₂ P.asIdeal M).toAddSubgroup ≠ 0 := by
  intro h0
  have hle : (localization₂ P.asIdeal M).toAddSubgroup ≤ M.toAddSubgroup ⊔ (localization₂ P.asIdeal M₀).toAddSubgroup := by
    intro x hx
    obtain ⟨t, h1, h2⟩ := (h.inf h₀).approx {P} x
    have h3 := h1 P (Finset.mem_singleton_self P)
    have ht : t ∈ M := mem_of_locP fun Q => by
      by_cases hQ : Q = P
      · subst hQ
        have := (localization₂ Q.asIdeal M).add_mem (localization_mono Q inf_le_left h3) hx
        rwa [sub_add_cancel] at this
      · exact localization_mono Q inf_le_left (h2 Q (by simpa using hQ))
    have : x = t - (t - x) := by abel
    rw [this]
    exact sub_mem (AddSubgroup.mem_sup_left ht) (AddSubgroup.mem_sup_right (localization_mono P inf_le_right h3))
  have h4 := AddSubgroup.relIndex_eq_zero_of_le_right hle h0
  rw [AddSubgroup.relIndex_sup_right] at h4
  exact relIndex_ne_zero h₀ hM
    (AddSubgroup.relIndex_eq_zero_of_le_left (fun x hx => mem_localization_of_mem P hx) h4)

end Index

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem homO_fg {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} (hN : N.FG) (hN' : N'.FG)
    (hs : Submodule.span E (N : Set (Sp E a)) = ⊤) : (homO N N').FG := by
  obtain ⟨T, rfl⟩ := hN
  let φ : HomE E a b →ₗ[𝓞 E] (T → Sp E b) :=
    { toFun := fun x y => x y.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := by
    intro x y hxy
    rw [Submodule.span_span_of_tower] at hs
    exact LinearMap.ext_on hs fun v hv => congrFun hxy ⟨v, hv⟩
  refine Submodule.fg_of_fg_map_injective φ hφ ?_
  refine Submodule.FG.of_le (Submodule.fg_pi (p := fun _ : T => N') fun _ => hN') ?_
  rintro _ ⟨x, hx, rfl⟩ y _
  exact hx _ (Submodule.subset_span y.2)

theorem perO_fg {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} (hA : AA.FG)
    (hH : (homO N N').FG) : (perO AA N N').FG := by
  let B : E →ₗ[𝓞 E] HomE E a b →ₗ[𝓞 E] HomE E a b :=
    LinearMap.mk₂ (𝓞 E) (fun r x => r • x) (fun _ _ _ => add_smul _ _ _) (fun _ _ _ => smul_assoc _ _ _)
      (fun _ _ _ => smul_add _ _ _) (fun _ _ _ => smul_comm _ _ _)
  refine Submodule.FG.of_le (Submodule.FG.map₂ B hA hH) (Submodule.span_le.2 ?_)
  rintro _ ⟨r, hr, x, hx, rfl⟩
  exact Submodule.apply_mem_map₂ B hr hx

theorem volC_pos : Formalism.L2.Ker.VolCPos := by
  intro E _ _ _ a b AA S N N' hN hN' hs hs' hA hA0
  have la : Submodule.IsLattice E (Formalism.L2.Col.stdLat E a) := Formalism.L2.Col.stdLat_lattice
  have lb : Submodule.IsLattice E (Formalism.L2.Col.stdLat E b) := Formalism.L2.Col.stdLat_lattice
  have hspan (n : ℕ) : Submodule.span E (Formalism.L2.Col.stdLat E n : Set (Sp E n)) = ⊤ := by
    rw [Formalism.L2.Col.stdLat_eq_span, Submodule.span_span_of_tower]
    have hbasis : (fun i : Fin n => (Pi.single i (1 : E) : Sp E n)) =
        ⇑(Pi.basisFun E (Fin n)) :=
      funext fun i => (Pi.basisFun_apply E (Fin n) i).symm
    rw [hbasis, (Pi.basisFun E (Fin n)).span_eq]
  have full₀ : Submodule.IsFullLattice E (Formalism.L2.Col.stdLat E b) :=
    { toIsLattice := lb, span_eq_top := hspan b }
  have full₁ : Submodule.IsFullLattice E N' :=
    { toIsLattice := Submodule.IsLattice.of_fg E hN', span_eq_top := hs' }
  have f₀ := PeriodComp.full AA (Formalism.L2.Col.stdLat E a)
    (Formalism.L2.Col.stdLat E b) la.fg full₀ hA0
  have f₁ := PeriodComp.full AA N N' hN full₁ hA0
  have g₀ := perO_fg hA (homO_fg la.fg lb.fg (hspan a))
  have g₁ := perO_fg hA (homO_fg hN hN' hs)
  refine Finset.prod_pos fun P _ => div_pos ?_ ?_
  · exact Nat.cast_pos.2 (Nat.pos_of_ne_zero (relIndex_localized_ne_zero P f₀ f₁ g₁))
  · exact Nat.cast_pos.2 (Nat.pos_of_ne_zero (relIndex_localized_ne_zero P f₁ f₀ g₀))

end GlobalTheory.ThetaMove.VolumePos
end
