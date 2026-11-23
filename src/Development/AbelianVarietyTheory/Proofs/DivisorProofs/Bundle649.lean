module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle630
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle605
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle139
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle608
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle609
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle262
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle610
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLogDiff

theorem restr_inL_inR {R : Type} [CommRing R] {d : ℕ} (f : MvPowerSeries (Fin d) R) (i : Fin d) :
    subst (Sum.elim (fun j => (X j : MvPowerSeries (Fin d) R)) (fun _ => 0))
        (pderiv (R := R) (Sum.inr i) (inL f)) = 0 ∧
    subst (Sum.elim (fun j => (X j : MvPowerSeries (Fin d) R)) (fun _ => 0))
        (pderiv (R := R) (Sum.inr i) (inR f)) = C (lin f i) := by
  classical
  have hl : ∀ s : Fin d, constantCoeff (X (Sum.inl s) : MvPowerSeries (Fin d ⊕ Fin d) R) = 0 :=
    fun s => by simp
  have hr : ∀ s : Fin d, constantCoeff (X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) R) = 0 :=
    fun s => by simp
  have hρ : HasSubst (Sum.elim (fun j => (X j : MvPowerSeries (Fin d) R)) (fun _ : Fin d => 0)) :=
    hasSubst_of_constantCoeff_zero (fun s => by cases s <;> simp)
  constructor
  · unfold inL
    have hchain := GlobalTheory.PSChain.pderiv_subst_chain _ hl f (Sum.inr i)
    rw [hchain,
      Finset.sum_eq_zero (fun j _ => by rw [pderiv_X_of_ne (by simp), mul_zero]),
      ← substAlgHom_apply hρ, map_zero]
  · unfold inR
    have hchain := GlobalTheory.PSChain.pderiv_subst_chain _ hr f (Sum.inr i)
    rw [hchain, Finset.sum_eq_single i
      (fun j _ hj => by rw [pderiv_X_of_ne (by simpa using hj), mul_zero]) (by simp),
      pderiv_X_self, mul_one, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hr) hρ]
    have e : (fun s : Fin d => subst (Sum.elim (fun j => (X j : MvPowerSeries (Fin d) R))
        (fun _ : Fin d => 0)) (X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) R)) = 0 := by
      funext s; simp [subst_X hρ]
    rw [e, subst_zero_eq_C_constantCoeff, Algebra.algebraMap_self, map_id, RingHom.id_apply,
      ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add]
    simp [lin]

end GlobalTheory.QLogDiff

namespace GlobalTheory.QLogDiff

theorem pderiv_map_eq {R S σ : Type} [CommRing R] [CommRing S] (h : R →+* S)
    (f : MvPowerSeries σ R) (i : σ) :
    pderiv (R := S) i (map h f) = map h (pderiv (R := R) i f) := by
  ext n; simp [coeff_pderiv, coeff_map]

theorem in_add {B Q σ : Type} [CommRing B] [CommRing Q] [Algebra B Q] {N : Ideal B}
    {f g : MvPowerSeries σ Q} (hf : In N f) (hg : In N g) : In N (f + g) := fun α => by
  obtain ⟨a, ha, ea⟩ := hf α
  obtain ⟨b, hb, eb⟩ := hg α
  exact ⟨a + b, N.add_mem ha hb, by rw [map_add (f := _), ea, eb, map_add (f := _)]⟩

theorem coeff_inr_of_unit {B : Type} [CommRing B] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B)
    (hu : op μ (fun i => (X i : MvPowerSeries (Fin d) B)) (fun _ => 0) = fun i => X i)
    (hc : ∀ i, swap (μ i) = μ i) (i j : Fin d) :
    coeff (Finsupp.single (Sum.inr i) 1) (μ j) = if i = j then 1 else 0 := by
  classical
  have hs : HasSubst (Sum.elim (fun _ : Fin d => (0 : MvPowerSeries (Fin d) B)) (fun i : Fin d => X i)) :=
    hasSubst_of_constantCoeff_zero (fun s => by cases s <;> simp)
  have hw : HasSubst (Sum.elim (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) B))
      (fun i => X (Sum.inl i))) :=
    hasSubst_of_constantCoeff_zero (fun s => by cases s <;> simp)
  have key : subst (Sum.elim (fun _ : Fin d => (0 : MvPowerSeries (Fin d) B)) (fun i : Fin d => X i)) (μ j) = X j := by
    have h1 := congrFun hu j
    simp only [op, at2] at h1
    rw [← hc j, swap, at2, subst_comp_subst_apply hw hs]
    have e : (fun s => subst (Sum.elim (fun _ : Fin d => (0 : MvPowerSeries (Fin d) B)) (fun i : Fin d => X i))
        (Sum.elim (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) B))
          (fun i => X (Sum.inl i)) s)) = Sum.elim (fun i => X i) (fun _ => 0) := by
      funext s; cases s <;> simp [subst_X hs]
    rw [e]; exact h1
  have := (GlobalTheory.T.coeff_subst_restrict_sum_variables (μ j)).2 (Finsupp.single i 1)
  rw [key, Finsupp.mapDomain_single] at this
  rw [← this, coeff_X]
  simp [Finsupp.single_left_inj one_ne_zero]

theorem dIn_of_QL : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O]
    [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B),
    IsLift θ μ → ∀ (N : Ideal B) (f : MvPowerSeries (Fin d) Q), QL μ N f → DIn N f := by
  intro p _ B O Q _ _ _ _ θ _ d μ hμ N f hf
  classical
  obtain ⟨-, hlin, hcob⟩ := hf
  have hμ0 : ∀ j, constantCoeff (up Q μ j) = 0 := fun j => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      hμ.const j, map_zero]
  have haμ : HasSubst (up Q μ) := hasSubst_of_constantCoeff_zero hμ0
  obtain ⟨ρ, hρe⟩ : ∃ ρ : Fin d ⊕ Fin d → MvPowerSeries (Fin d) Q,
    ρ = Sum.elim (fun j => (X j : MvPowerSeries (Fin d) Q)) (fun _ => 0) := ⟨_, rfl⟩
  obtain ⟨ρB, hρBe⟩ : ∃ ρ : Fin d ⊕ Fin d → MvPowerSeries (Fin d) B,
    ρ = Sum.elim (fun j => (X j : MvPowerSeries (Fin d) B)) (fun _ => 0) := ⟨_, rfl⟩
  have hρ : HasSubst ρ := hasSubst_of_constantCoeff_zero (fun s => by cases s <;> simp [hρe])
  have hρB : HasSubst ρB := hasSubst_of_constantCoeff_zero (fun s => by cases s <;> simp [hρBe])
  have hmapρ : (fun s => map (algebraMap B Q) (ρB s)) = ρ := by
    funext s; cases s <;> simp [hρe, hρBe]
  have hmapsub : ∀ g : MvPowerSeries (Fin d ⊕ Fin d) B,
      map (algebraMap B Q) (subst ρB g) = subst ρ (map (algebraMap B Q) g) := by
    intro g; rw [map_subst hρB, hmapρ]
  have hunit : ∀ j, subst ρ (up Q μ j) = X j := by
    intro j
    have h1 := congrFun hμ.unit j
    simp only [op, at2] at h1
    rw [← hρBe] at h1
    have h2 := congrArg (map (algebraMap B Q)) h1
    rw [hmapsub, map_X] at h2
    exact h2
  let M : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) B) :=
    fun j i => subst ρB (pderiv (R := B) (Sum.inr i) (μ j))
  have hM : ∀ j i, constantCoeff (M j i) = if j = i then 1 else 0 := by
    intro j i
    have h2 := (GlobalTheory.T.coeff_subst_restrict_sum_variables (R := B) (pderiv (R := B) (Sum.inr i) (μ j))).1 0
    rw [← hρBe] at h2
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp only [M]
    rw [h2, Finsupp.mapDomain_zero, coeff_pderiv, zero_add, coeff_inr_of_unit μ hμ.unit hμ.comm i j]
    simp [eq_comm]
  let g : Fin d → MvPowerSeries (Fin d) Q :=
    fun i => subst ρ (pderiv (R := Q) (Sum.inr i) (subst (up Q μ) f))
  have hvg : ∀ i, ∑ j, pderiv (R := Q) j f * map (algebraMap B Q) (M j i) = g i := by
    intro i
    simp only [g, M]
    have hchain := GlobalTheory.PSChain.pderiv_subst_chain (up Q μ) hμ0 f (Sum.inr i)

    rw [hchain, ← substAlgHom_apply hρ, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, substAlgHom_apply, substAlgHom_apply, subst_comp_subst_apply haμ hρ, hmapsub]
    have e : (fun s => subst ρ (up Q μ s)) = X := funext hunit
    rw [e, subst_self, id, up, pderiv_map_eq]
  have hg : ∀ i, In N (g i) := by
    intro i
    have hsplit : subst (up Q μ) f = cob1 (up Q μ) f + inL f + inR f := by
      unfold cob1; abel
    have l4 := restr_inL_inR f i
    rw [← hρe] at l4
    simp only [g]
    rw [hsplit, map_add (f := _), map_add (f := _), ← substAlgHom_apply hρ, map_add (f := _), map_add (f := _)]
    simp only [substAlgHom_apply]
    rw [l4.1, l4.2, add_zero]
    refine in_add ?_ ?_
    · intro α
      have h2 := (GlobalTheory.T.coeff_subst_restrict_sum_variables (R := Q)
        (pderiv (R := Q) (Sum.inr i) (cob1 (up Q μ) f))).1 α
      rw [← hρe] at h2
      rw [h2, coeff_pderiv]
      obtain ⟨b, hb, e⟩ := hcob (Finsupp.mapDomain Sum.inl α + Finsupp.single (Sum.inr i) 1)
      refine ⟨b, hb, ?_⟩
      rw [e, Finsupp.mapDomain_of_notMem_range _ _ (by simp), Nat.cast_zero, zero_add, mul_one]
    · intro α
      obtain ⟨b, hb, e⟩ := hlin i
      by_cases h0 : α = 0
      · exact ⟨b, hb, by rw [h0, coeff_zero_C, e]⟩
      · exact ⟨0, N.zero_mem, by rw [coeff_C, ite_eq_right h0, map_zero]⟩
  have hv := GlobalTheory.T.coeffsInIdeal_solution_of_unipotent_series_matrix N M hM
    (fun j => pderiv (R := Q) j f) g hvg hg
  intro α i
  by_cases hi : α i = 0
  · exact ⟨0, N.zero_mem, by rw [hi, Nat.cast_zero, zero_mul, map_zero]⟩
  · have hle : Finsupp.single i 1 ≤ α := by
      rw [Finsupp.single_le_iff]; omega
    obtain ⟨b, hb, e⟩ := hv i (α - Finsupp.single i 1)
    refine ⟨b, hb, ?_⟩
    rw [← e, coeff_pderiv, tsub_add_cancel_of_le hle, Finsupp.tsub_apply, Finsupp.single_eq_same,
      mul_comm, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hi), Nat.cast_one, sub_add_cancel]

end GlobalTheory.QLogDiff
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem quasiInt_of_cob1_int_of_lin_int : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ f : MvPowerSeries (Fin d) (Fr p k), (∀ i, ∃ w : WittVector p k, lin f i = algebraMap (WittVector p k) (Fr p k) w) → cob1 (fun i => Katz.lift p (μ i)) f ∈ intBy p k _ 1 → f ∈ quasiInt p k (Fin d) := by
  intro p _ k _ _ _ d μ hμ f hlin hcob
  have key : ∀ N, ∀ α : Fin d →₀ ℕ, α.degree = N → ∀ i, ∃ w : WittVector p k,
      (α i : Fr p k) * coeff α f = algebraMap (WittVector p k) (Fr p k) w := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro α hα i
      rcases Nat.lt_or_ge N 2 with hN | hN
      · interval_cases N
        · have h0 : α = 0 := (Finsupp.degree_eq_zero_iff α).1 hα
          subst h0
          exact ⟨0, by simp⟩
        · by_cases hi : α i = 0
          · exact ⟨0, by simp [hi]⟩
          · have hα' : α ∈ Set.range (fun a : Fin d ↦ Finsupp.single a 1) := by
              rw [Finsupp.range_single_one]; exact hα
            obtain ⟨a, rfl⟩ := hα'
            have hai : a = i := by
              by_contra hne
              exact hi (Finsupp.single_eq_of_ne (Ne.symm hne))
            subst hai
            obtain ⟨w, hw⟩ := hlin a
            refine ⟨w, ?_⟩
            simp only [Finsupp.single_eq_same, Nat.cast_one, one_mul]
            exact hw
      · let g : MvPowerSeries (Fin d) (Fr p k) := fun β => if β.degree < N then coeff β f else 0
        have hg : ∀ β, coeff β g = if β.degree < N then coeff β f else 0 := fun β => rfl
        have hgq : g ∈ quasiInt p k (Fin d) := by
          show ∀ (β : Fin d →₀ ℕ) (j : Fin d), ∃ w : WittVector p k,
            (β j : Fr p k) * coeff β g = algebraMap _ (Fr p k) w
          intro β j
          by_cases hβ : β.degree < N
          · obtain ⟨w, hw⟩ := ih β.degree hβ β rfl j
            refine ⟨w, ?_⟩
            rw [hg, if_pos hβ]; exact hw
          · exact ⟨0, by rw [hg, if_neg hβ]; simp⟩
        have hh : ∀ β : Fin d →₀ ℕ, β.degree < N → coeff β (f - g) = 0 := by
          intro β hβ
          rw [map_sub, hg, if_pos hβ, sub_self]
        have hc : ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree = N → ∃ w : WittVector p k,
            coeff γ (cob1 (fun i => Katz.lift p (μ i)) (g + (f - g))) =
              algebraMap (WittVector p k) (Fr p k) w := by
          intro γ _
          rw [add_sub_cancel]
          obtain ⟨w, hw⟩ := hcob γ
          exact ⟨1 * w, hw⟩
        obtain ⟨w, hw⟩ := GlobalTheory.T.degree_part_integralDifferential_of_coboundary p k d μ hμ N g (f - g) hN hgq hh hc α i hα
        refine ⟨w, ?_⟩
        have hfα : coeff α (f - g) = coeff α f := by
          rw [map_sub, hg, if_neg (by omega), sub_zero]
        rw [← hfα]; exact hw
  show ∀ (α : Fin d →₀ ℕ) (i : Fin d), ∃ w : WittVector p k,
    (α i : Fr p k) * coeff α f = algebraMap _ (Fr p k) w
  intro α i
  exact key _ α rfl i

end GlobalTheory.Katz
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap : ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A], (∀ (τ : Type) [Finite τ] (φ : MvPowerSeries τ k →ₐ[k] A), (∀ t, IsNilpotent (φ (X t))) → ∀ a : σ → MvPowerSeries τ k, (∀ i, constantCoeff (a i) = 0) → ∀ (y : σ → A) (hy : ∀ i, IsNilpotent (y i)), (∀ i, φ (a i) = y i) → ∀ f : MvPowerSeries σ k, φ (subst a f) = evA k y hy f) ∧ ∀ (B : Type) [CommRing B] [Algebra k B] (g : A →ₐ[k] B) (x : σ → A) (hx : ∀ i, IsNilpotent (x i)) (y : σ → B) (hy : ∀ i, IsNilpotent (y i)), (∀ i, g (x i) = y i) → ∀ f : MvPowerSeries σ k, g (evA k x hx f) = evA k y hy f := by
  first | exact @GlobalTheory.evA_subst_and_map | exact GlobalTheory.evA_subst_and_map | (intros; apply GlobalTheory.evA_subst_and_map <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.exists_integral_coboundaryOne_congr_frobenius : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ (c : MvPowerSeries (Fin d ⊕ Fin d) O) (t : MvPowerSeries (Fin d) O), (∀ α : Fin d →₀ ℕ, (∃ i, ¬ p ∣ α i) → ¬IsUnit (coeff α t)) → (∀ β : Fin d ⊕ Fin d →₀ ℕ, ¬IsUnit (coeff (p • β) (cob1 μ t) - coeff β c ^ p)) → ∃ u : MvPowerSeries (Fin d) O, ∀ α, ¬IsUnit (coeff α c - coeff α (cob1 μ u)) := by
  first | exact @GlobalTheory.SmallSecondRoot.exists_integral_cob1_congr_of_frobenius_congr | exact GlobalTheory.SmallSecondRoot.exists_integral_cob1_congr_of_frobenius_congr | (intros; apply GlobalTheory.SmallSecondRoot.exists_integral_cob1_congr_of_frobenius_congr <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem coh_coprod_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U), IsColimit (Cofan.mk U j) → ∀ n : ℤ, Function.Bijective (fun (x : H R (sch.obj U) F n) (i : ι) => pull R (sch.map (j i)) F n x) := by
  intro R _ F U ι V j hc n
  refine GlobalTheory.T.etaleSpaceCohomology_levelwise_coproduct_bijective R F (sch.obj U) ι (fun i => sch.obj (V i)) (fun i => sch.map (j i)) ?_ n
  intro k
  exact GlobalTheory.T.freeEtaleSheaf_presheaf_over_coproduct_eq_sum R U ι V j hc (yoneda.obj U) (𝟙 _) (fun i => yoneda.obj (V i)) (fun i => yoneda.map (j i))
    (fun _ => 𝟙 _) (fun i => IsPullback.of_vert_isIso (by simp))

end GlobalTheory
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.isAlgClosed_fractionRing_of_monic_polynomials_have_roots : ∀ (A : Type) [CommRing A] [IsDomain A], AIC A → IsAlgClosed (FractionRing A) := by
  first | (exact @GlobalTheory.isAlgClosed_fractionRing_of_AIC) | (exact GlobalTheory.isAlgClosed_fractionRing_of_AIC) | (intros; apply GlobalTheory.isAlgClosed_fractionRing_of_AIC  <;> assumption)
end

section

open GlobalTheory.EtC

namespace GlobalTheory.ClosedFibre
open Polynomial
open scoped TensorProduct

theorem mem_range_of_eval₂ {K D : Type} [Field K] [IsAlgClosed K] [CommRing D] [IsDomain D]
    (ψ : K →+* D) (f : K[X]) (hf : f ≠ 0) (τ : D) (h : f.eval₂ ψ τ = 0) : ∃ r, ψ r = τ := by
  letI : Algebra K D := ψ.toAlgebra
  have hK : AIC K := fun p _ hd => IsAlgClosed.exists_root p (natDegree_pos_iff_degree_pos.mp hd).ne'
  have hm : (f * C f.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hf
  exact GlobalTheory.AICIff.root_mem_range hK _ _ hm rfl τ (by
    rw [aeval_def, eval₂_mul]
    change eval₂ ψ τ f * _ = 0
    rw [h, zero_mul])

theorem mem_range_of_etale {R K E D : Type} [CommRing R] [Field K] [IsAlgClosed K] [CommRing E]
    [CommRing D] [IsDomain D] [Algebra R K] [Algebra R E] [Algebra.Etale R E] [Algebra R D]
    (ψ : K →ₐ[R] D) (Φ : E →ₐ[R] D) (u : E) : ∃ r, ψ r = Φ u := by
  haveI : Algebra.Etale K (K ⊗[R] E) := Algebra.Etale.baseChange R E K
  haveI : Module.Finite K (K ⊗[R] E) := Algebra.FormallyUnramified.finite_of_free _ _
  haveI : Algebra.IsIntegral K (K ⊗[R] E) := Algebra.IsIntegral.of_finite _ _
  obtain ⟨f, hfm, hf⟩ := Algebra.IsIntegral.isIntegral (R := K) ((1 : K) ⊗ₜ[R] u)
  let Θ : K ⊗[R] E →ₐ[R] D := Algebra.TensorProduct.productMap ψ Φ
  have hΘ : (Θ : K ⊗[R] E →+* D).comp (algebraMap K (K ⊗[R] E)) = (ψ : K →+* D) := by
    ext k
    simp [Θ, Algebra.TensorProduct.algebraMap_apply]
  refine mem_range_of_eval₂ (ψ : K →+* D) f hfm.ne_zero (Φ u) ?_
  have h2 := congrArg (Θ : K ⊗[R] E →+* D) hf
  rw [hom_eval₂, hΘ, map_zero] at h2
  simpa [Θ] using h2

end GlobalTheory.ClosedFibre

namespace GlobalTheory.ClosedFibre
open Polynomial

theorem isMaximal_of_mem : ∀ (T : Type) [CommRing T] [IsDomain T], AIC T → ∀ (O : Type) [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) → ∀ P : Ideal (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))), P.IsPrime → ∀ g : Polynomial T, g ≠ 0 → algebraMap (Polynomial T) (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) g ∈ P → P.IsMaximal ∧ ∀ x : Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)), ∃ c d : T, d ≠ 0 ∧ algebraMap T (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) d * x - algebraMap T (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) c ∈ P := by
  intro T _ _ hT O _ _ _ _ hO P hP g hg hgP
  let L := Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
  let K := FractionRing T
  haveI : IsAlgClosed K := GlobalTheory.isAlgClosed_fractionRing_of_AIC T hT
  haveI := hP
  let mk : L →+* L ⧸ P := Ideal.Quotient.mk P
  have hunitL : ∀ t : T, t ≠ 0 → IsUnit (algebraMap T L t) := by
    intro t ht
    have := IsLocalization.map_units L (⟨algebraMap T O t, ⟨t, mem_nonZeroDivisors_of_ne_zero ht, rfl⟩⟩ :
      Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
    rwa [IsScalarTower.algebraMap_apply T O L]
  have hunit : ∀ y : nonZeroDivisors T, IsUnit ((mk.comp (algebraMap T L)) y) :=
    fun y => (hunitL y (nonZeroDivisors.ne_zero y.2)).map mk
  let ψ : K →+* L ⧸ P := IsLocalization.lift (M := nonZeroDivisors T) (S := K) hunit
  have hψ : ψ.comp (algebraMap T K) = mk.comp (algebraMap T L) := IsLocalization.lift_comp hunit
  let τ : L ⧸ P := mk (algebraMap (Polynomial T) L X)
  have hpoly : mk.comp (algebraMap (Polynomial T) L) = eval₂RingHom (mk.comp (algebraMap T L)) τ := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_C]
      rw [IsScalarTower.algebraMap_apply T (Polynomial T) L, Polynomial.algebraMap_apply]
      rfl
    · simp [τ]
  obtain ⟨a, ha⟩ : ∃ a, ψ a = τ := by
    refine mem_range_of_eval₂ ψ (g.map (algebraMap T K))
      ((Polynomial.map_ne_zero_iff (IsFractionRing.injective T K)).2 hg) τ ?_
    rw [eval₂_map, hψ, ← coe_eval₂RingHom, ← hpoly, RingHom.comp_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hgP
  letI : Algebra (Polynomial T) K := (eval₂RingHom (algebraMap T K) a).toAlgebra
  let ψA : K →ₐ[Polynomial T] L ⧸ P :=
    { ψ with
      commutes' := fun p => by
        change ψ (eval₂ (algebraMap T K) a p) = mk (algebraMap (Polynomial T) L p)
        rw [hom_eval₂, hψ, ha, ← RingHom.comp_apply mk, hpoly, coe_eval₂RingHom] }
  have key : ∀ o : O, ∃ r, ψ r = mk (algebraMap O L o) := by
    intro o
    obtain ⟨ι, _, _, _, Si, -, hcov, hE⟩ := hO
    obtain ⟨i, hi⟩ := hcov o
    obtain ⟨E, _, _, _, Q, _, ⟨e⟩⟩ := hE i
    let Φ0 : Localization.AtPrime Q →ₐ[Polynomial T] L ⧸ P :=
      (Ideal.Quotient.mkₐ (Polynomial T) P).comp
        ((IsScalarTower.toAlgHom (Polynomial T) O L).comp ((Si i).val.comp e.toAlgHom))
    let Φ : E →ₐ[Polynomial T] L ⧸ P :=
      Φ0.comp (IsScalarTower.toAlgHom (Polynomial T) E (Localization.AtPrime Q))
    obtain ⟨⟨u, s⟩, hus⟩ := IsLocalization.mk'_surjective Q.primeCompl (e.symm ⟨o, hi⟩)
    obtain ⟨r1, h1⟩ := mem_range_of_etale ψA Φ u
    obtain ⟨r2, h2⟩ := mem_range_of_etale ψA Φ s
    have hsu : IsUnit (Φ s) := (IsLocalization.map_units (Localization.AtPrime Q) s).map Φ0
    have ho : Φ0 (e.symm ⟨o, hi⟩) = mk (algebraMap O L o) := by
      change Ideal.Quotient.mk P (algebraMap O L ((e (e.symm ⟨o, hi⟩) : Si i) : O)) = mk (algebraMap O L o)
      rw [AlgEquiv.apply_symm_apply]
    have hmul : Φ0 (e.symm ⟨o, hi⟩) * Φ s = Φ u := by
      rw [← hus]
      simp only [Φ, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
      rw [← map_mul, IsLocalization.mk'_spec]
    have h1' : ψA r1 = ψ r1 := rfl
    have h2' : ψA r2 = ψ r2 := rfl
    rw [h1'] at h1
    rw [h2'] at h2
    have hr2 : r2 ≠ 0 := by
      rintro rfl
      rw [map_zero] at h2
      exact hsu.ne_zero h2.symm
    refine ⟨r1 * r2⁻¹, ?_⟩
    have hne : ψ r2 ≠ 0 := h2 ▸ hsu.ne_zero
    apply mul_right_cancel₀ hne
    rw [← map_mul, inv_mul_cancel_right₀ hr2, h1, ← ho, h2, hmul]
  have hall : ∀ x : L, ∃ r, ψ r = mk x := by
    intro x
    obtain ⟨⟨o, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) x
    obtain ⟨t, ht, hts⟩ := s.2
    obtain ⟨r, hr⟩ := key o
    have ht0 : t ≠ 0 := nonZeroDivisors.ne_zero ht
    have hk : ψ (algebraMap T K t) = mk (algebraMap O L s) := by
      rw [← RingHom.comp_apply ψ, hψ, RingHom.comp_apply, IsScalarTower.algebraMap_apply T O L, ← hts]
    have hne : ψ (algebraMap T K t) ≠ 0 := by
      rw [hk]
      exact ((IsLocalization.map_units L s).map mk).ne_zero
    have hk0 : algebraMap T K t ≠ 0 := fun h => hne (by rw [h, map_zero])
    refine ⟨r * (algebraMap T K t)⁻¹, ?_⟩
    apply mul_right_cancel₀ hne
    rw [← map_mul, inv_mul_cancel_right₀ hk0, hr, hk, ← map_mul, IsLocalization.mk'_spec]
  have hfield : IsField (L ⧸ P) := by
    refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {y} hy => ?_⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨r, hr⟩ := hall x
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hy (by rw [← hr, map_zero])
    exact ⟨ψ r⁻¹, by rw [← hr, ← map_mul, mul_inv_cancel₀ hr0, map_one]⟩
  refine ⟨Ideal.Quotient.maximal_of_isField P hfield, fun x => ?_⟩
  obtain ⟨r, hr⟩ := hall x
  obtain ⟨⟨c, d⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors T) r
  refine ⟨c, d, nonZeroDivisors.ne_zero d.2, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul]
  have h1 : ψ (IsLocalization.mk' K c d) * ψ (algebraMap T K d) = ψ (algebraMap T K c) := by
    rw [← map_mul, IsLocalization.mk'_spec]
  have hd : ψ (algebraMap T K d) = Ideal.Quotient.mk P (algebraMap T L d) := by
    rw [← RingHom.comp_apply ψ, hψ]; rfl
  have hc : ψ (algebraMap T K c) = Ideal.Quotient.mk P (algebraMap T L c) := by
    rw [← RingHom.comp_apply ψ, hψ]; rfl
  rw [← hd, ← hc, ← h1, ← hr, mul_comm]
  exact sub_self _

end GlobalTheory.ClosedFibre
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleSpaceCohomology_presheaf_classes_as_cocycles : ∀ (R : Type) [CommRing R] (F : Shv R), ∃ cl : ∀ (P : PSh) (n : ℤ) (t : (free R).obj P ⟶ (res R F).X n), t ≫ (res R F).d n (n + 1) = 0 → H R (disc.obj P) F n, (∀ P n x, ∃ t ht, cl P n t ht = x) ∧ (∀ P n t ht t' ht', cl P n t ht = cl P n t' ht' ↔ ∃ y : (free R).obj P ⟶ (res R F).X (n - 1), t = t' + y ≫ (res R F).d (n - 1) n) ∧ (∀ P n, cl P n 0 zero_comp = 0) ∧ ∀ (P P' : PSh) (f : P ⟶ P') n t ht, ∃ h, pull R (disc.map f) F n (cl P' n t ht) = cl P n ((free R).map f ≫ t) h := by
  first | (exact @GlobalTheory.EtC.disc_elt_cls) | (exact GlobalTheory.EtC.disc_elt_cls) | (intros; apply GlobalTheory.EtC.disc_elt_cls <;> assumption)
end
