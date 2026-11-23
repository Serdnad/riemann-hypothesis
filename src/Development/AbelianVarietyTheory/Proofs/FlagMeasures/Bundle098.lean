module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.CoreDefs
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.CapelliHighestWeightConjugated
public import Formalism.RealPlaceAnalysis.Bundle005
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle046
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle091
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory

private theorem list_prod_ofFn_sum_eq_sum_prod {A : Type*} [Semiring A] {ι : Type*} [Fintype ι] :
    ∀ {t : ℕ} (f : Fin t → ι → A),
      (List.ofFn fun k => ∑ i, f k i).prod = ∑ c : Fin t → ι, (List.ofFn fun k => f k (c k)).prod
  | 0, f => by simp
  | t + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, list_prod_ofFn_sum_eq_sum_prod (fun k => f k.succ), Finset.sum_mul_sum,
      ← (Fin.consEquiv fun _ => ι).sum_comp, Fintype.sum_prod_type]
    simp [Fin.consEquiv, List.ofFn_succ]

private theorem list_prod_ofFn_smul_eq_prod_smul {A : Type*} [Semiring A] [Algebra ℂ A] :
    ∀ {t : ℕ} (r : Fin t → ℂ) (x : Fin t → A),
      (List.ofFn fun k => r k • x k).prod = (∏ k, r k) • (List.ofFn x).prod
  | 0, r, x => by simp
  | t + 1, r, x => by
    rw [List.ofFn_succ, List.prod_cons, list_prod_ofFn_smul_eq_prod_smul (fun k => r k.succ) (fun k => x k.succ),
      smul_mul_smul_comm, Fin.prod_univ_succ, List.ofFn_succ (f := x), List.prod_cons]

private theorem Tm_conj_eq_sum_conj_Tm {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (v : ℂ) (a b : Fin n) :
    Formalism.REAL.Tm (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) v a b =
      ∑ c, ∑ d, (P c a * Q b d) • Formalism.REAL.Tm E v c d := by
  have h1 : ∑ c, P c a * Q b c = if a = b then 1 else 0 := by
    have := congrFun (congrFun hQP b) a
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [show (∑ c, P c a * Q b c) = ∑ c, Q b c * P c a from
      Finset.sum_congr rfl fun c _ => mul_comm _ _, this]
    by_cases h : a = b <;> simp [h, eq_comm]
  simp only [Formalism.REAL.Tm, smul_add, Finset.sum_add_distrib, smul_ite, smul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  congr 1
  rw [← Finset.sum_smul, h1]
  by_cases h : a = b <;> simp [h]

private theorem sum_sign_mul_prod_eq_zero_of_not_bijective {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (r : Fin n → Fin n)
    (hr : ¬ Function.Bijective r) :
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, P (r k) (σ k) = 0 := by
  have := Matrix.det_mul_aux (M := Pᵀ) (N := Matrix.of fun _ _ => (1 : ℂ)) hr
  simpa [Matrix.transpose_apply] using this

private theorem sum_sign_mul_prod_perm_eq_sign_mul_det {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (τ : Equiv.Perm (Fin n)) :
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, P (τ k) (σ k) =
      ((Equiv.Perm.sign τ : ℤ) : ℂ) * Matrix.det P := by
  rw [← Matrix.det_transpose, Matrix.det_apply', Finset.mul_sum]
  conv_lhs => rw [← Equiv.sum_comp (Equiv.mulRight τ)]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  simp only [Equiv.coe_mulRight, Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul, Equiv.Perm.coe_mul,
    Function.comp_apply, Matrix.transpose_apply]
  rw [show (∏ k, P (τ k) (ρ (τ k))) = ∏ j, P j (ρ j) from Equiv.prod_comp τ (fun j => P j (ρ j))]
  ring

private theorem sum_fun_eq_sum_perm_of_eq_zero_of_not_bijective {M : Type*} [AddCommMonoid M] {n : ℕ} (g : (Fin n → Fin n) → M)
    (h : ∀ r, ¬ Function.Bijective r → g r = 0) :
    ∑ r, g r = ∑ τ : Equiv.Perm (Fin n), g τ := by
  let e : Equiv.Perm (Fin n) ↪ (Fin n → Fin n) := ⟨fun τ => τ, DFunLike.coe_injective⟩
  rw [show (∑ τ : Equiv.Perm (Fin n), g τ) = ∑ r ∈ Finset.univ.map e, g r from
    (Finset.sum_map Finset.univ e g).symm]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro r _ hr
  apply h r
  intro hb
  exact hr (Finset.mem_map.2 ⟨Equiv.ofBijective r hb, Finset.mem_univ _, rfl⟩)

private theorem qminor_eq_zero_of_not_bijective {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (hE : Formalism.REAL.GlRel E) (u : ℂ) (s : Fin n → Fin n) (hs : ¬ Function.Bijective s) :
    Formalism.REAL.qminor E id s u = 0 := by
  have hni : ¬ Function.Injective s := fun hi => hs (Finite.injective_iff_bijective.mp hi)
  obtain ⟨p, q, hsq, hpq⟩ : ∃ p q, s p = s q ∧ p ≠ q := by
    simp only [Function.Injective, not_forall] at hni
    obtain ⟨p, q, h1, h2⟩ := hni
    exact ⟨p, q, h1, h2⟩
  have hsw : s ∘ Equiv.swap p q = s := by
    funext i
    simp only [Function.comp_apply]
    rcases eq_or_ne i p with rfl | hip
    · simp [hsq]
    rcases eq_or_ne i q with rfl | hiq
    · simp [hsq]
    · rw [Equiv.swap_apply_of_ne_of_ne hip hiq]
  have h := Formalism.REAL.qSkewCol A n n E hE id s (Equiv.swap p q) u
  rw [hsw, Equiv.Perm.sign_swap hpq] at h
  set x := Formalism.REAL.qminor E id s u
  have h2 : x + x = 0 := by
    nth_rewrite 2 [h]
    simp
  calc x = (1 / 2 : ℂ) • (x + x) := by rw [← two_smul ℂ x, smul_smul]; norm_num
    _ = 0 := by rw [h2, smul_zero]

private theorem qdet_conj_eq_qdet_of_mul_eq_one {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (hE : Formalism.REAL.GlRel E) (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (hPQ : P * Q = 1)
    (u : ℂ) :
    Formalism.REAL.qdet (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) u = Formalism.REAL.qdet E u := by
  classical
  have hsg : ∀ (z : ℤ) (x : A), (z : A) * x = (z : ℂ) • x := fun z x => by
    rw [Algebra.smul_def, map_intCast]
  have ha : ∀ σ : Equiv.Perm (Fin n),
      (List.ofFn fun k : Fin n => Formalism.REAL.Tm (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d)
        (u - (k : ℂ)) (id (σ k)) (id k)).prod =
        ∑ r : Fin n → Fin n, ∑ s : Fin n → Fin n, (∏ k, (P (r k) (σ k) * Q k (s k))) •
          (List.ofFn fun k : Fin n => Formalism.REAL.Tm E (u - (k : ℂ)) (r k) (s k)).prod := by
    intro σ
    simp only [id, Tm_conj_eq_sum_conj_Tm E P Q hQP]
    rw [list_prod_ofFn_sum_eq_sum_prod (fun k c => ∑ d, (P c (σ k) * Q k d) • Formalism.REAL.Tm E (u - (k : ℂ)) c d)]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [list_prod_ofFn_sum_eq_sum_prod (fun k d => (P (r k) (σ k) * Q k d) • Formalism.REAL.Tm E (u - (k : ℂ)) (r k) d)]
    refine Finset.sum_congr rfl fun s _ => ?_
    exact list_prod_ofFn_smul_eq_prod_smul (fun k => P (r k) (σ k) * Q k (s k))
      (fun k => Formalism.REAL.Tm E (u - (k : ℂ)) (r k) (s k))
  have hq : ∀ s : Fin n → Fin n, Formalism.REAL.qminor E id s u =
      ∑ τ : Equiv.Perm (Fin n), ((Equiv.Perm.sign τ : ℤ) : ℂ) •
        (List.ofFn fun k : Fin n => Formalism.REAL.Tm E (u - (k : ℂ)) (τ k) (s k)).prod := by
    intro s
    unfold Formalism.REAL.qminor
    exact Finset.sum_congr rfl fun τ _ => hsg _ _
  have hs : ∀ s : Fin n → Fin n,
      ∑ r : Fin n → Fin n, (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ k, (P (r k) (σ k) * Q k (s k))) •
          (List.ofFn fun k : Fin n => Formalism.REAL.Tm E (u - (k : ℂ)) (r k) (s k)).prod =
        (∏ k, Q k (s k)) • (Matrix.det P • Formalism.REAL.qminor E id s u) := by
    intro s
    have hD : ∀ r : Fin n → Fin n, (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ k, (P (r k) (σ k) * Q k (s k))) =
          (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, P (r k) (σ k)) *
            ∏ k, Q k (s k) := by
      intro r
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun σ _ => by rw [Finset.prod_mul_distrib, mul_assoc]
    simp_rw [hD]
    rw [sum_fun_eq_sum_perm_of_eq_zero_of_not_bijective _ (fun r hr => by rw [sum_sign_mul_prod_eq_zero_of_not_bijective P r hr, zero_mul, zero_smul])]
    simp_rw [sum_sign_mul_prod_perm_eq_sign_mul_det P]
    rw [hq s, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [smul_smul, smul_smul]
    congr 1
    ring
  have hL : Formalism.REAL.qdet (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) u =
      ∑ s : Fin n → Fin n, (∏ k, Q k (s k)) • (Matrix.det P • Formalism.REAL.qminor E id s u) := by
    have step : Formalism.REAL.qdet (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) u =
        ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : A) *
          ∑ r : Fin n → Fin n, ∑ s : Fin n → Fin n, (∏ k, (P (r k) (σ k) * Q k (s k))) •
            (List.ofFn fun k : Fin n => Formalism.REAL.Tm E (u - (k : ℂ)) (r k) (s k)).prod := by
      unfold Formalism.REAL.qdet Formalism.REAL.qminor
      exact Finset.sum_congr rfl fun σ _ => by rw [ha σ]
    rw [step]
    simp_rw [← hs]
    simp only [Finset.sum_smul, Finset.mul_sum, Finset.smul_sum, hsg, smul_smul]
    first
      | exact Finset.sum_comm
      | exact Eq.trans Finset.sum_comm (Finset.sum_congr rfl fun r _ => Finset.sum_comm)
      | exact Eq.trans Finset.sum_comm (Eq.trans (Finset.sum_congr rfl fun r _ => Finset.sum_comm) Finset.sum_comm)
  have hperm : ∀ τ : Equiv.Perm (Fin n),
      Formalism.REAL.qminor E id τ u = ((Equiv.Perm.sign τ : ℤ) : ℂ) • Formalism.REAL.qdet E u := by
    intro τ
    have h := Formalism.REAL.qSkewCol A n n E hE id id τ u
    rw [hsg] at h
    exact h
  have hdetQ : ∑ τ : Equiv.Perm (Fin n), ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ k, Q k (τ k) =
      Matrix.det Q := by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    rfl
  have hscal : ∑ τ : Equiv.Perm (Fin n), (∏ k, Q k (τ k)) *
      (Matrix.det P * ((Equiv.Perm.sign τ : ℤ) : ℂ)) = 1 := by
    rw [show (1 : ℂ) = Matrix.det P * Matrix.det Q by rw [← Matrix.det_mul, hPQ, Matrix.det_one],
      ← hdetQ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ _ => by ring
  rw [hL, sum_fun_eq_sum_perm_of_eq_zero_of_not_bijective _ (fun s hs => by rw [qminor_eq_zero_of_not_bijective E hE u s hs, smul_zero, smul_zero])]
  simp_rw [hperm, smul_smul]
  rw [← Finset.sum_smul, hscal, one_smul]

theorem capelli_transport_conj : PI.UnitaryGroupMassFormula.CapelliEig.CapTransport := by
  intro n ε E _ _ H P Q F u g hQP hPQ hH hF hg
  have hx : Formalism.REAL.inUJ ε (P * g * Q) := Formalism.QuantumDeterminants.ioh_inUJ ε H P Q g hPQ hH hg
  obtain ⟨x₀, hx₀⟩ := Formalism.QuantumDeterminants.io_rep_mk (ε := ε) (E := E) hF
  have hA := Formalism.QuantumDeterminants.ioh_qminor_rep (Formalism.QuantumDeterminants.ioh_repr (ε := ε) (E := E) P Q) id id u hx₀
  have hB := Formalism.QuantumDeterminants.io_qminor_rep (ε := ε) id id u hx₀
  have hkey : Formalism.REAL.qminor (Formalism.QuantumDeterminants.iohE ε E P Q) id id u =
      Formalism.REAL.qminor (Formalism.QuantumDeterminants.ioE ε E) id id u :=
    qdet_conj_eq_qdet_of_mul_eq_one (Formalism.QuantumDeterminants.ioE ε E) (Formalism.QuantumDeterminants.io_gl ε E) P Q hQP hPQ u
  have h1 := Formalism.QuantumDeterminants.ioh_qminor ε H P Q hQP hPQ hH (id : Fin n → Fin n) id u F g
  show Formalism.QuantumDeterminants.qminorOp (Formalism.QuantumDeterminants.EabH H) id id u F g =
    Formalism.QuantumDeterminants.qminorOp (Formalism.REAL.EabV ε) id id u (fun x => F (Q * x * P)) (P * g * Q)
  rw [h1, hA _ hx, hB _ hx, hkey]

end GlobalTheory
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.LatUniq

theorem datum_of_lattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (d d' : LocNG.Datum P) (τ τ' : Term V M r), LocNG.IsTermOver P d τ → LocNG.IsTermOver P d' τ' → τ.abelian₂ = τ'.abelian₂ → d = d' := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hk hP d d' τ τ' hτ hτ' hL
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hk hP
  have h1 := ((GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P S c).1 d τ hτ).1
  have h2 := ((GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P S c).1 d' τ' hτ').1
  rw [← hL] at h2
  have e := (GlobalTheory.HL.TermBasic.term_basic M.L r k S (c.dat d) (c.lat τ.abelian₂) h1).2.2.2.2.2.2.2 (c.dat d') h2
  exact ((GlobalTheory.HL.CoordDatum.transport M hM H r k P S c).1 e).symm

end GlobalTheory.HL.LatUniq
end

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory
namespace LowKProj

section General
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem fix_of_mem {E : H →L[ℂ] H} {S : Submodule ℂ H} (hE : IsOrthProjOnto E S) :
    ∀ x ∈ S, E x = x := by
  intro x hx
  obtain ⟨hidem, -, hrange⟩ := hE
  rw [← hrange] at hx
  obtain ⟨y, rfl⟩ := hx
  change E (E y) = E y
  rw [← ContinuousLinearMap.comp_apply, hidem]

theorem apply_mem {E : H →L[ℂ] H} {S : Submodule ℂ H} (hE : IsOrthProjOnto E S) (x : H) :
    E x ∈ S := by
  rw [← hE.2.2]
  exact ⟨x, rfl⟩

theorem norm_le_one {E : H →L[ℂ] H} {S : Submodule ℂ H} (hE : IsOrthProjOnto E S) :
    ‖E‖ ≤ 1 := by
  obtain ⟨hidem, hsym, -⟩ := hE
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  have hEE : E (E x) = E x := by rw [← ContinuousLinearMap.comp_apply, hidem]
  have hsq : ‖E x‖ ^ 2 ≤ ‖x‖ * ‖E x‖ := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hsym, hEE]
    exact re_inner_le_norm x (E x)
  have h0 : 0 ≤ ‖x‖ := norm_nonneg x
  have h1 : 0 ≤ ‖E x‖ := norm_nonneg (E x)
  nlinarith

theorem exists_proj (S : Submodule ℂ H) [FiniteDimensional ℂ S] :
    ∃ E : H →L[ℂ] H, IsOrthProjOnto E S := by
  have : CompleteSpace S := FiniteDimensional.complete ℂ S
  refine ⟨S.starProjection, ?_, ?_, ?_⟩
  · exact S.isIdempotentElem_starProjection
  · exact S.inner_starProjection_left_eq_right
  · exact S.range_starProjection

theorem comm_of_stable {E A B : H →L[ℂ] H} {S : Submodule ℂ H} (hE : IsOrthProjOnto E S)
    (hAB : ∀ x y, ⟪A x, y⟫_ℂ = ⟪x, B y⟫_ℂ) (hA : ∀ v ∈ S, A v ∈ S) (hB : ∀ v ∈ S, B v ∈ S) :
    E ∘L A = A ∘L E := by
  have hfix := fix_of_mem hE
  have hmem := apply_mem hE
  have hsym := hE.2.1
  ext x
  simp only [ContinuousLinearMap.comp_apply]
  refine ext_inner_right ℂ fun y => ?_

  calc ⟪E (A x), y⟫_ℂ = ⟪A x, E y⟫_ℂ := hsym _ _
    _ = ⟪x, B (E y)⟫_ℂ := hAB _ _
    _ = ⟪x, E (B (E y))⟫_ℂ := by rw [hfix _ (hB _ (hmem y))]
    _ = ⟪E x, B (E y)⟫_ℂ := (hsym _ _).symm
    _ = ⟪A (E x), E y⟫_ℂ := (hAB _ _).symm
    _ = ⟪E (A (E x)), y⟫_ℂ := (hsym _ _).symm
    _ = ⟪A (E x), y⟫_ℂ := by rw [hfix _ (hA _ (hmem x))]

end General

theorem mem_UJset_of_Kset {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) : k ∈ UJset ε := by
  obtain ⟨hu, hc⟩ := hk
  have h2 : star k * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hu
  show kᴴ * Jm ε * k = Jm ε
  rw [← Matrix.star_eq_conjTranspose, Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, h2, Matrix.one_mul]

private lemma star_mem_Kset {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) : star k ∈ Kset ε := by
  obtain ⟨hu, hc⟩ := hk
  have h1 : k * star k = 1 := (Matrix.mem_unitaryGroup_iff).1 hu
  have h2 : star k * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hu
  refine ⟨(Matrix.mem_unitaryGroup_iff).2 (by rw [star_star]; exact h2), ?_⟩
  calc star k * Jm ε = star k * Jm ε * (k * star k) := by rw [h1, Matrix.mul_one]
    _ = star k * (Jm ε * k) * star k := by simp only [Matrix.mul_assoc]
    _ = star k * (k * Jm ε) * star k := by rw [hc]
    _ = (star k * k) * Jm ε * star k := by simp only [Matrix.mul_assoc]
    _ = Jm ε * star k := by rw [h2, Matrix.one_mul]

theorem inner_adj {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (x y : H) :
    ⟪σ k x, y⟫_ℂ = ⟪x, σ (star k) y⟫_ℂ := by
  obtain ⟨⟨h1, hmul⟩, hiso, -⟩ := hσ
  have hkU := mem_UJset_of_Kset hk
  have hsU := mem_UJset_of_Kset (star_mem_Kset hk)
  have hks : k * star k = 1 := (Matrix.mem_unitaryGroup_iff).1 hk.1

  let L : H →ₗᵢ[ℂ] H := ⟨(σ k : H →ₗ[ℂ] H), fun v => hiso k hkU v⟩
  have hy : σ k (σ (star k) y) = y := by
    rw [← ContinuousLinearMap.comp_apply, ← hmul k hkU (star k) hsU, hks, h1]
    rfl
  calc ⟪σ k x, y⟫_ℂ = ⟪L x, L (σ (star k) y)⟫_ℂ := by
        change ⟪σ k x, y⟫_ℂ = ⟪σ k x, σ k (σ (star k) y)⟫_ℂ
        rw [hy]
    _ = ⟪x, σ (star k) y⟫_ℂ := L.inner_map_map _ _

theorem lowKSub_stable {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    IsKStableOn ε σ (lowKSub ε lam σ) := by
  intro g hg v hv

  have hle : lowKSub ε lam σ ≤ (lowKSub ε lam σ).comap (σ g : H →ₗ[ℂ] H) :=
    sSup_le fun S hS w hw => le_sSup hS (hS.2.1 g hg w hw)
  exact hle hv

theorem lowK_projection : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ → (∃ w, IsHighestUnit ε lam σ w) ∧ IsKStableOn ε σ (lowKSub ε lam σ) ∧ (FiniteDimensional ℂ (lowKSub ε lam σ) → ∃ E : H →L[ℂ] H, IsOrthProjOnto E (lowKSub ε lam σ)) ∧ ∀ E : H →L[ℂ] H, IsOrthProjOnto E (lowKSub ε lam σ) → ‖E‖ ≤ 1 ∧ (∀ x ∈ lowKSub ε lam σ, E x = x) ∧ ∀ k ∈ Kset ε, E ∘L σ k = σ k ∘L E ∧ ‖σ k‖ ≤ 1 := by
  intro n ε lam H _ _ _ σ hDS
  obtain ⟨-, -, hrep, -, -, ⟨S, hS⟩, -⟩ := hDS
  refine ⟨?_, lowKSub_stable ε lam σ, fun _ => exists_proj _, ?_⟩
  ·
    obtain ⟨v, hvS, hv0, hwt⟩ := hS.2.2.2.1
    have hn : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hv0
    refine ⟨((‖v‖ : ℂ)⁻¹) • v, ?_, ?_, ?_⟩
    · rw [norm_smul, norm_inv, Complex.norm_real, norm_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0)
    · have hle : S ≤ lowKSub ε lam σ :=
        le_sSup (show S ∈ {S | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S} from hS)
      exact Submodule.smul_mem _ _ (hle hvS)
    · intro θ hθ
      rw [map_smul, hwt θ hθ, smul_comm]
  · intro E hE
    refine ⟨norm_le_one hE, fix_of_mem hE, fun k hk => ⟨?_, ?_⟩⟩
    · exact comm_of_stable hE (inner_adj hrep hk) (fun v hv => lowKSub_stable ε lam σ k hk v hv)
        (fun v hv => lowKSub_stable ε lam σ (star k) (star_mem_Kset hk) v hv)
    · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
        rw [hrep.2.1 k (mem_UJset_of_Kset hk) x, one_mul]

end LowKProj
end GlobalTheory
end

section

open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory.LeadMinorTri

theorem sum_fin_eq_sum_castLE_of_vanish {n l : ℕ} (hl : l ≤ n) (f : Fin n → ℂ)
    (hf : ∀ k : Fin n, l ≤ k.val → f k = 0) :
    ∑ k, f k = ∑ k : Fin l, f (Fin.castLE hl k) := by
  symm
  refine Finset.sum_of_injOn (Fin.castLE hl) ((Fin.castLE_injective hl).injOn) (by simp) ?_ (by simp)
  intro k _ hk
  apply hf
  by_contra h
  exact hk ⟨⟨k.val, by omega⟩, by simp, rfl⟩

theorem leadBlock_lower_mul {n l : ℕ} (hl : l ≤ n) (c z : Matrix (Fin n) (Fin n) ℂ)
    (hc : ∀ i j, i < j → c i j = 0) :
    (c * z).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      c.submatrix (Fin.castLE hl) (Fin.castLE hl) * z.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  refine sum_fin_eq_sum_castLE_of_vanish hl (fun k => c (Fin.castLE hl i) k * z k (Fin.castLE hl j)) ?_
  intro k hk
  rw [hc _ k (by rw [Fin.lt_def]; have := i.isLt; simp only [Fin.val_castLE]; omega), zero_mul]

theorem leadBlock_mul_upper {n l : ℕ} (hl : l ≤ n) (z c : Matrix (Fin n) (Fin n) ℂ)
    (hc : ∀ i j, j < i → c i j = 0) :
    (z * c).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      z.submatrix (Fin.castLE hl) (Fin.castLE hl) * c.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  refine sum_fin_eq_sum_castLE_of_vanish hl (fun k => z (Fin.castLE hl i) k * c k (Fin.castLE hl j)) ?_
  intro k hk
  rw [hc k _ (by rw [Fin.lt_def]; have := j.isLt; simp only [Fin.val_castLE]; omega), mul_zero]

theorem leadMinor_lower_mul_mul_upper :
    ∀ (n : ℕ) (c z c' : Matrix (Fin n) (Fin n) ℂ), (∀ i j, i < j → c i j = 0) → (∀ i j, j < i → c' i j = 0) → ∀ (l : ℕ) (hl : l ≤ n), leadMinor (c * z * c') l hl = (∏ i : Fin l, c (Fin.castLE hl i) (Fin.castLE hl i) * c' (Fin.castLE hl i) (Fin.castLE hl i)) * leadMinor z l hl := by
  intro n c z c' hc hc' l hl
  have h1 : (c.submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      ∏ i : Fin l, c (Fin.castLE hl i) (Fin.castLE hl i) := by
    apply Matrix.det_of_lowerTriangular
    intro i j hij
    exact hc _ _ (show i < j from hij)
  have h2 : (c'.submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      ∏ i : Fin l, c' (Fin.castLE hl i) (Fin.castLE hl i) := by
    apply Matrix.det_of_upperTriangular
    intro i j hij
    exact hc' _ _ (show j < i from hij)
  change ((c * z * c').submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
    _ * (z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det
  rw [leadBlock_mul_upper hl _ _ hc', leadBlock_lower_mul hl _ _ hc, Matrix.det_mul, Matrix.det_mul,
    h1, h2, Finset.prod_mul_distrib]
  ring

end GlobalTheory.LeadMinorTri
end

section

namespace GlobalTheory.UpperUnipotentMulFlagMeasures

theorem isUpUni_mul {N : ℕ} {K : Type} [inst : Field K] {A B : Matrix (Fin N) (Fin N) K}
    (hA : Formalism.MainNotions.S.IsUpUni A) (hB : Formalism.MainNotions.S.IsUpUni B) : Formalism.MainNotions.S.IsUpUni (A * B) := by
  intro i j
  refine ⟨fun hji => ?_, fun hij => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with hk | hk
    · rw [(hA i k).1 hk, zero_mul]
    · rw [(hB k j).1 (lt_of_lt_of_le hji hk), mul_zero]
  · subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(hA i i).2 rfl, (hB i i).2 rfl, mul_one]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [(hA i k).1 h, zero_mul]
      · rw [(hB k i).1 h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h

end GlobalTheory.UpperUnipotentMulFlagMeasures
end
