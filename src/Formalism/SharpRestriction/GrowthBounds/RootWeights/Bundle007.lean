module

public import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle001
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
public import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Basic.PEquiv
public import Mathlib.Data.Matrix.PEquiv

@[expose] public section

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem monomial_exponent_le_multidegree {ι : Type*} {n : ℕ} (m : ι × Fin n →₀ ℕ) (l : ι) (a : Fin n) : m (l, a) ≤ multideg m l := by
  exact Finset.single_le_sum (f := fun c => m (l, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

theorem polynomial_weight_difference_le {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι) (d : ι → ℕ)
    (m m' : ι × Fin n →₀ ℕ) (hm : ∀ i, multideg m i = d i) (hm' : ∀ i, multideg m' i = d i) (a b : Fin n) :
    wtS LL S m a - wtS LL S m' b ≤ (degIn d S : ℤ) := by
  unfold wtS degIn
  rw [← Finset.sum_sub_distrib]
  push_cast
  refine Finset.sum_le_sum fun l _ => ?_
  have h1 := monomial_exponent_le_multidegree m l a
  have h2 := monomial_exponent_le_multidegree m' l b
  rw [hm l] at h1
  rw [hm' l] at h2
  split_ifs <;> omega

theorem prime_pow_smul_cast {O : Type} [CommRing O] [IsDomain O] {σ : Type} (p k : ℕ) (y : MvPolynomial σ (KK O)) :
    ((p : O) ^ k) • y = ((p : KK O) ^ k) • y := by
  rw [← algebraMap_smul (KK O) ((p : O) ^ k) y, map_pow, map_natCast]

theorem isotypic_projector_lattice_scaling (D : Formalism.BasicNotions.D7) (hDom : HighestWeightDominant) (hRes : SubrepRestrictionRep) (hPol : PolynomialGLRepresentation) (h13 : IsotypicProjectorTheoremField D)
    (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (S0 : UniformizedDVR p O)
    (hG : AdmissibleDVR p n' O) [CharZero (KK O)] (n : ℕ) (ι : Type) [Fintype ι] (LL : Letters ι) (S : Set ι)
    (d : ι → ℕ) (lam : Fin n → ℤ) (e : Module.End (KK O) (MvPolynomial (ι × Fin n) (KK O)))
    (he : IsIsoProj (glOps (KK O) n LL S) lam e) :
    (∀ F ∈ Pol (KK O) n d, e F ∈ Pol (KK O) n d) ∧
    ∀ L : Submodule O (MvPolynomial (ι × Fin n) (KK O)),
      (∀ u ∈ UZgens (glOps (KK O) n LL S), ∀ F ∈ L, u F ∈ L) → (latticeMultidegreePart L d).FG →
      MQ (K := KK O) (latticeMultidegreePart L d) = ⊤ →
      ∀ F ∈ Pol (KK O) n d, F ∈ L →
        ((p : KK O) ^ (N0 n * Nat.log p (2 * degIn d S + n - 1))) • e F ∈ L := by
  obtain ⟨hRep, -, -, hStab, hFD, hWt, -⟩ := hPol (KK O) ι n LL
  have hStabS : ∀ a b, ∀ x ∈ Pol (KK O) n d, glOps (KK O) n LL S a b x ∈ Pol (KK O) n d :=
    fun a b x hx => hStab S d a b x hx
  obtain ⟨hResRep, hResWt, hResDiv, hResBin, hResProj, hResZero⟩ :=
    hRes (KK O) (MvPolynomial (ι × Fin n) (KK O)) n (glOps (KK O) n LL S) (hRep S) (Pol (KK O) n d) hStabS
  obtain ⟨e', he'P, he'eq⟩ := hResProj lam e he
  have hPres : ∀ F ∈ Pol (KK O) n d, e F ∈ Pol (KK O) n d := by
    intro F hF
    have h := (e' ⟨F, hF⟩).2
    rwa [he'eq ⟨F, hF⟩] at h
  refine ⟨hPres, ?_⟩
  intro L hLst hFG hMQ F hF hFL
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hid : e F = F := by
      by_cases h0 : F = 0
      · rw [h0, map_zero]
      · apply he.1
        apply Submodule.subset_span
        refine ⟨1, Submonoid.one_mem _, F, ⟨h0, ?_, fun a => a.elim0⟩, by simp⟩
        simp [weightSp]
    rw [hid]
    simpa [N0] using hFL
  · have : NeZero n := ⟨hn.ne'⟩
    have : FiniteDimensional (KK O) (Pol (KK O) n d) := hFD d

    have hwt : ∀ (mu : Fin n → ℤ) (x : Pol (KK O) n d), x ≠ 0 →
        x ∈ weightSp (restrictStableOperators (glOps (KK O) n LL S) (Pol (KK O) n d) hStabS) mu →
        ∃ m : ι × Fin n →₀ ℕ, (∀ i, multideg m i = d i) ∧ wtS LL S m = mu := by
      intro mu x hx0 hx
      have hxV := (hResWt mu x).mp hx
      have hne : (x : MvPolynomial (ι × Fin n) (KK O)) ≠ 0 := by simpa using hx0
      obtain ⟨m, hm⟩ : (x : MvPolynomial (ι × Fin n) (KK O)).support.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr (by rwa [Ne, MvPolynomial.support_eq_empty])
      refine ⟨m, ?_, hWt S mu _ hxV m hm⟩
      have hx2 : (x : MvPolynomial (ι × Fin n) (KK O)) ∈
          MvPolynomial.restrictSupport (KK O) {m : ι × Fin n →₀ ℕ | ∀ i, multideg m i = d i} := x.2
      exact (show ((x : MvPolynomial (ι × Fin n) (KK O)).support : Set (ι × Fin n →₀ ℕ)) ⊆
        {m : ι × Fin n →₀ ℕ | ∀ i, multideg m i = d i} from hx2) hm
    by_cases hhw : ∃ v : Pol (KK O) n d,
        IsHWV (restrictStableOperators (glOps (KK O) n LL S) (Pol (KK O) n d) hStabS) lam v
    · have hdom : Dominant lam := by
        obtain ⟨v, hv⟩ := hhw
        exact hDom (KK O) (Pol (KK O) n d) n _ hResRep lam v hv
      have hWtBound : ellWt lam ≤ degIn d S := by
        obtain ⟨v, hv⟩ := hhw
        obtain ⟨m, hmd, hmw⟩ := hwt lam v hv.1 hv.2.1
        have h := polynomial_weight_difference_le LL S d m m hmd hmd 0 (lastIdx n)
        rw [hmw] at h
        unfold ellWt
        omega
      have hEllBound : ellOf (restrictStableOperators (glOps (KK O) n LL S) (Pol (KK O) n d) hStabS) ⊤ ≤ degIn d S := by
        unfold ellOf
        apply csSup_le'
        rintro k ⟨mu, hmu, nu, hnu, a, b, hab, hk⟩
        obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp (by simpa [wtsOf] using hmu)
        obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).mp (by simpa [wtsOf] using hnu)
        obtain ⟨m, hmd, hmw⟩ := hwt mu x hx0 hx
        obtain ⟨m', hmd', hmw'⟩ := hwt nu y hy0 hy
        have e1 := congrFun hk a
        have e2 := congrFun hk b
        simp [rootW, hab, Ne.symm hab] at e1 e2
        have d1 := polynomial_weight_difference_le LL S d m m hmd hmd a b
        have d2 := polynomial_weight_difference_le LL S d m' m' hmd' hmd' b a
        rw [hmw] at d1
        rw [hmw'] at d2
        omega
      have hLat : UZLattice (O := O) (restrictStableOperators (glOps (KK O) n LL S) (Pol (KK O) n d) hStabS)
          (latticeMultidegreePart L d) := by
        refine ⟨?_, hFG⟩
        intro u hu x hx
        rw [latticeMultidegreePart, Submodule.mem_comap] at hx ⊢
        rcases hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
        · change ((divPowE _ a b k x : Pol (KK O) n d) : MvPolynomial (ι × Fin n) (KK O)) ∈ L
          rw [hResDiv a b k x]
          exact hLst _ (Or.inl ⟨a, b, k, hab, rfl⟩) _ hx
        · change ((binomE _ a k x : Pol (KK O) n d) : MvPolynomial (ι × Fin n) (KK O)) ∈ L
          rw [hResBin a k x]
          exact hLst _ (Or.inr ⟨a, k, rfl⟩) _ hx
      have key := h13 p n' O S0 hG n (Pol (KK O) n d) _ hResRep (latticeMultidegreePart L d) hLat hMQ {lam}
        (by simpa using hdom) (fun _ => e') (by simpa using he'P) ⟨F, hF⟩ hFL
      simp only [Finset.sup_singleton, Finset.sum_singleton, hMQ] at key
      rw [latticeMultidegreePart, Submodule.mem_comap] at key
      have key' : ((p : O) ^ (N0 n * deF p n (ellOf (restrictStableOperators (glOps (KK O) n LL S) (Pol (KK O) n d) hStabS) ⊤
          + ellWt lam))) • e F ∈ L := by
        simpa [he'eq] using key
      have hle : N0 n * deF p n (ellOf (restrictStableOperators (glOps (KK O) n LL S) (Pol (KK O) n d) hStabS) ⊤ + ellWt lam)
          ≤ N0 n * Nat.log p (2 * degIn d S + n - 1) := by
        unfold deF
        exact Nat.mul_le_mul_left _ (Nat.log_mono_right (by omega))
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hle
      rw [hj, ← prime_pow_smul_cast p _ (e F), pow_add, mul_comm, mul_smul]
      exact L.smul_mem _ key'
    · have h0 : e F = 0 := hResZero lam e he hhw F hF
      rw [h0, smul_zero]
      exact L.zero_mem

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem det_mem_subalgebra_of_entries {R P : Type*} [CommRing R] [CommRing P] [Algebra R P] (T : Subalgebra R P) {n : ℕ}
    (N : Matrix (Fin n) (Fin n) P) (h : ∀ i j, N i j ∈ T) : N.det ∈ T := by
  let M : Matrix (Fin n) (Fin n) T := Matrix.of fun i j => ⟨N i j, h i j⟩
  have hM : (T.val.toRingHom).mapMatrix M = N := by ext i j; rfl
  rw [← hM, ← RingHom.map_det]
  exact M.det.2

theorem divisor_supported_of_supported {R σ : Type*} [CommRing R] [IsDomain R] {s : Set σ} {f q : MvPolynomial σ R}
    (hf : f ≠ 0) (hs : f ∈ supported R s) (hq : q ∣ f) : q ∈ supported R s := by
  rw [mem_supported] at hs ⊢
  obtain ⟨g, rfl⟩ := hq
  have hq0 : q ≠ 0 := by rintro rfl; simp at hf
  have hg0 : g ≠ 0 := by rintro rfl; simp at hf
  intro v hv
  by_contra hvs
  have h1 : degreeOf v (q * g) = degreeOf v q + degreeOf v g := degreeOf_mul_eq hq0 hg0
  have h2 : degreeOf v (q * g) = 0 := by
    rw [degreeOf_eq_sup]
    refine Nat.le_zero.mp (Finset.sup_le fun m hm => ?_)
    by_contra hmv
    exact hvs (hs ((mem_vars_iff_mem_support v).mpr ⟨m, hm, Finsupp.mem_support_iff.mpr (by omega)⟩))
  have h3 : degreeOf v q ≠ 0 := mem_vars_iff_degreeOf_ne_zero.mp hv
  omega

theorem algHom_fixes_supported_polynomials {R σ : Type*} [CommRing R] {s : Set σ} (φ : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (h : ∀ v ∈ s, φ (X v) = X v) {q : MvPolynomial σ R} (hq : q ∈ supported R s) : φ q = q := by
  rw [supported_eq_adjoin_X] at hq
  have hle : Algebra.adjoin R (X '' s) ≤ AlgHom.equalizer φ (AlgHom.id R _) := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨v, hv, rfl⟩
    exact h v hv
  exact hle hq

def cofactorMatrix (R : Type) [CommRing R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι) (a : Fin r) :
    Matrix (Fin r) (Fin r) (MvPolynomial (ι × Fin r) R) :=
  (matA R A).updateRow (lastIdx r) (Pi.single a 1)

def cofactorMatrixColumnCleared (R : Type) [CommRing R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι) (a : Fin r) :
    Matrix (Fin r) (Fin r) (MvPolynomial (ι × Fin r) R) :=
  Matrix.of fun i j => if i = lastIdx r then (if j = a then 1 else 0) else (if j = a then 0 else X (A i, j))

theorem adjugate_last_row_eq_cofactor_det (R : Type) [CommRing R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι) (a : Fin r) :
    (matA R A).adjugate a (lastIdx r) = (cofactorMatrix R A a).det := by
  rw [Matrix.adjugate_apply]; rfl

theorem cofactor_det_eq_cleared_det (R : Type) [CommRing R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι) (a : Fin r) :
    (cofactorMatrix R A a).det = (cofactorMatrixColumnCleared R A a).det := by
  symm
  classical
  refine Matrix.det_eq_of_forall_row_eq_smul_add_const
    (fun i => if i = lastIdx r then 0 else -X (A i, a)) (lastIdx r) (by simp) ?_
  intro i j
  by_cases hi : i = lastIdx r
  · subst hi
    simp [cofactorMatrix, cofactorMatrixColumnCleared, Matrix.updateRow_self, Pi.single_apply]
  · by_cases hj : j = a
    · subst hj
      simp [cofactorMatrix, cofactorMatrixColumnCleared, hi, Matrix.updateRow_ne hi, Matrix.updateRow_self, matA]
    · simp [cofactorMatrix, cofactorMatrixColumnCleared, hi, hj, Matrix.updateRow_ne hi, Matrix.updateRow_self, matA, Pi.single_apply]

def cofactorVariables {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι) (a : Fin r) : Set (ι × Fin r) :=
  {v | (∃ i, i ≠ lastIdx r ∧ v.1 = A i) ∧ v.2 ≠ a}

theorem cofactor_last_row_supported (R : Type) [CommRing R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι) (a : Fin r) :
    (matA R A).adjugate a (lastIdx r) ∈ supported R (cofactorVariables A a) := by
  rw [adjugate_last_row_eq_cofactor_det, cofactor_det_eq_cleared_det]
  apply det_mem_subalgebra_of_entries
  intro i j
  simp only [cofactorMatrixColumnCleared, Matrix.of_apply]
  split_ifs with h1 h2 h3
  · exact Subalgebra.one_mem _
  · exact Subalgebra.zero_mem _
  · exact Subalgebra.zero_mem _
  · rw [supported_eq_adjoin_X]
    exact Algebra.subset_adjoin ⟨_, ⟨⟨i, h1, rfl⟩, h3⟩, rfl⟩


open Classical in
theorem adjugate_last_row_ne_zero (R : Type) [CommRing R] [Nontrivial R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι)
    (hA : Function.Injective A) (a : Fin r) : (matA R A).adjugate a (lastIdx r) ≠ 0 := by
  rw [adjugate_last_row_eq_cofactor_det, cofactor_det_eq_cleared_det]
  intro h0
  set σ : Equiv.Perm (Fin r) := Equiv.swap a (lastIdx r) with hσ
  let g : ι × Fin r → R := fun v => if ∃ i, v = (A i, σ i) then 1 else 0
  have hmap : (eval g).mapMatrix (cofactorMatrixColumnCleared R A a) = σ.permMatrix R := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, cofactorMatrixColumnCleared, Matrix.of_apply,
      Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
      Option.some.injEq]
    by_cases hi : i = lastIdx r
    · subst hi
      by_cases hj : j = a
      · subst hj; simp [hσ, Equiv.swap_apply_right]
      · have : σ (lastIdx r) ≠ j := by rw [hσ, Equiv.swap_apply_right]; exact Ne.symm hj
        simp [hj, this]
    · have hσi : σ i ≠ a := by
        intro h
        apply hi
        have := congrArg σ h
        rwa [hσ, Equiv.swap_apply_self, Equiv.swap_apply_left] at this
      have key : (∃ i', A i = A i' ∧ j = σ i') ↔ σ i = j := by
        constructor
        · rintro ⟨i', h1, h2⟩
          rw [hA h1]; exact h2.symm
        · intro h; exact ⟨i, rfl, h.symm⟩
      by_cases hj : j = a
      · subst hj; simp [hi, hσi]
      · simp [hi, hj, g, key]
  have hdet := congrArg (eval g) h0
  rw [RingHom.map_det, hmap, Matrix.det_permutation, map_zero] at hdet
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs] at hdet


open Classical in
def lastRowSubstitution (R : Type) [CommRing R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι) (a : Fin r) :
    MvPolynomial (ι × Fin r) R →ₐ[R] MvPolynomial (ι × Fin r) R :=
  aeval fun v => if v.1 = A (lastIdx r) then (if v.2 = a then 1 else 0) else X v

theorem substitution_det_eq_adjugate (R : Type) [CommRing R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι)
    (hA : Function.Injective A) (a : Fin r) :
    lastRowSubstitution R A a (detA (R := R) A) = (matA R A).adjugate a (lastIdx r) := by
  rw [adjugate_last_row_eq_cofactor_det]
  unfold detA
  rw [AlgHom.map_det]
  congr 1
  ext i j
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, cofactorMatrix, lastRowSubstitution, aeval_X, matA]
  by_cases hi : i = lastIdx r
  · subst hi
    simp [Matrix.updateRow_self, Pi.single_apply]
  · have : A i ≠ A (lastIdx r) := hA.ne hi
    simp [this, Matrix.updateRow_ne hi, matA]

theorem hCop_proved : HCop := by
  intro R _ ι r _ A hA
  have hC := adjugate_last_row_ne_zero R A hA (lastIdx r)
  refine ⟨hC, ?_⟩
  intro d hd1 hd2
  have hd0 : d ≠ 0 := by rintro rfl; exact hC (zero_dvd_iff.mp hd2)
  have hsL : d ∈ supported R (cofactorVariables A (lastIdx r)) :=
    divisor_supported_of_supported hC (cofactor_last_row_supported R A _) hd2
  have hall : ∀ a, d ∈ supported R (cofactorVariables A a) := by
    intro a
    have hfix : lastRowSubstitution R A a d = d := by
      refine algHom_fixes_supported_polynomials _ ?_ hsL
      rintro v ⟨⟨i, hi, hv⟩, -⟩
      have : v.1 ≠ A (lastIdx r) := by rw [hv]; exact hA.ne hi
      simp [lastRowSubstitution, this]
    have hdv : d ∣ (matA R A).adjugate a (lastIdx r) := by
      rw [← substitution_det_eq_adjugate R A hA a, ← hfix]; exact map_dvd _ hd1
    exact divisor_supported_of_supported (adjugate_last_row_ne_zero R A hA a) (cofactor_last_row_supported R A a) hdv
  have hsub : (d.vars : Set (ι × Fin r)) ⊆ ∅ := by
    intro v hv
    exact ((mem_supported.mp (hall v.2)) hv).2 rfl
  have h0 : d ∈ supported R (∅ : Set (ι × Fin r)) := mem_supported.mpr hsub
  rw [supported_empty, Algebra.mem_bot] at h0
  obtain ⟨c, rfl⟩ := h0
  have hc : c ≠ 0 := by rintro rfl; exact hd0 (map_zero _)
  exact (IsUnit.mk0 c hc).map (algebraMap R _)

end Formalism.MainNotions.G.GLWeightTheory
end
end
