module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle866
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSubInOfCob2In
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle800
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle858
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle609
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle798
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle857
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle623
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle506
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle557
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle649
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle799
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle512
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle860
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.formValueOnTangentVector_eq_zero_of_globalForm_zero : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) (v : epsR R ⟶ A) (f : Form (A.hom ≫ 𝟙 (Sp R))), GlobalTheory.CechDR.cmpForm (A.hom ≫ 𝟙 (Sp R)) f = 0 → tanVal v f = 0 := by
  first | exact @GlobalTheory.TanVanish.tanVal_eq_zero_of_cmpForm_eq_zero | exact GlobalTheory.TanVanish.tanVal_eq_zero_of_cmpForm_eq_zero | (intros; apply GlobalTheory.TanVanish.tanVal_eq_zero_of_cmpForm_eq_zero <;> assumption)
end

section

set_option autoImplicit false

open Filter Topology TopologicalSpace CategoryTheory GlobalTheory.AnPer GlobalTheory.CatCoh GlobalTheory.Cris TensorProduct

namespace GlobalTheory.AnPer

theorem dpExp_eq_one_add_of_sq {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {C : Type}
    [CommRing C] {J : Ideal C} (δ : DividedPowers J) (ρ : Hol W →+* C) {x : C} (hx : x ∈ J)
    (hx2 : x * x = 0) : dpExp δ x = 1 + x := by
  have hv : ∀ n, 2 ≤ n → δ.dpow n x = 0 := by
    intro n hn
    have hu : IsUnit ((n.factorial : ℕ) : C) := by
      have h1 : IsUnit ((n.factorial : ℕ) : Hol W) := by
        rw [← map_natCast (algebraMap ℂ (Hol W))]
        exact (IsUnit.mk0 _ (by exact_mod_cast (Nat.factorial_ne_zero n))).map _
      simpa using h1.map ρ
    have hp : x ^ n = 0 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [pow_add, sq, hx2, zero_mul]
    have := δ.factorial_mul_dpow_eq_pow hx (n := n)
    rw [hp] at this
    exact (hu.mul_right_eq_zero).1 this
  rw [dpExp_eq_sum_range_of_vanish δ x 2 hv]
  simp [Finset.sum_range_succ, δ.dpow_zero hx, δ.dpow_one hx]

theorem step_exp {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {C : Type} [CommRing C]
    {J : Ideal C} {ρ ρ' : Hol W →+* C} (s : Step J ρ ρ') (e l : Hol W)
    (he : ∀ a, dw a e = dw a l * e) :
    ρ' l - ρ l ∈ J ∧ (ρ' l - ρ l) * (ρ' l - ρ l) = 0 ∧ ρ' e = ρ e * (1 + (ρ' l - ρ l)) := by
  obtain ⟨n, h1, h2, h3⟩ := s
  have hx : ρ' l - ρ l = ∑ a, ρ (dw a l) * n a := by rw [h3 l]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hx]; exact J.sum_mem fun a _ ↦ J.mul_mem_left _ (h1 a)
  · rw [hx, Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun b _ ↦ ?_
    rw [mul_mul_mul_comm, h2, mul_zero]
  · rw [hx, h3 e, mul_add, mul_one, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [he, map_mul]; ring

theorem close_exp : ∀ {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {C : Type} [CommRing C]
    (J : Ideal C) (δ : DividedPowers J), IsNilDP δ → ∀ (ρ₁ ρ₂ : Hol W →+* C) (e l : Hol W),
    (∀ a, dw a e = dw a l * e) → Close J ρ₁ ρ₂ → ρ₂ e = ρ₁ e * dpExp δ (ρ₂ l - ρ₁ l) := by
  intro I _ g W C _ J δ hδ ρ₁ ρ₂ e l he hc
  induction hc with
  | refl => rw [sub_self, dpExp_zero, mul_one]
  | @tail ρ ρ' hc' s ih =>
    obtain ⟨hxJ, hx2, hρ'⟩ := step_exp s e l he
    have hyJ : ρ l - ρ₁ l ∈ J := Close.sub_mem hc' l
    rw [show ρ' l - ρ₁ l = (ρ l - ρ₁ l) + (ρ' l - ρ l) by ring,
      hδ.dpExp_add_eq_mul hyJ hxJ, dpExp_eq_one_add_of_sq δ ρ₁ hxJ hx2, hρ', ih, mul_assoc]

end GlobalTheory.AnPer
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

theorem _root_.GlobalTheory.T.hasVal_log_eval_of_hasVal_formalLog : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ E : MvPowerSeries σ B →ₐ[B] B, IsEval p z E → ∀ (g : MvPowerSeries σ B) (q : Q), constantCoeff g = 1 → HasVal p z (formalLog (map (algebraMap B Q) g)) q → HasVal p (fun _ : Unit => E g - 1) (PowerSeries.log Q : MvPowerSeries Unit Q) q := by
  first | exact @GlobalTheory.QLog.hasVal_log_of_hasVal_formalLog | exact GlobalTheory.QLog.hasVal_log_of_hasVal_formalLog | (intros; apply GlobalTheory.QLog.hasVal_log_of_hasVal_formalLog <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem QLog.Chart.existsUnique_isLie : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E), QL c.μ ⊤ f → ∃! l : G.dual.Lie, c.IsLie f l := by
  intro p _ O E _ _ _ hF G d c f hf
  haveI : IsAdicComplete (Ideal.span {(p : O)}) O := hF.complete
  have hinj : Function.Injective (MvPowerSeries.map (σ := Fin d) (algebraMap O E)) := by
    intro s t h
    ext α
    have := congrArg (MvPowerSeries.coeff α) h
    simp only [MvPowerSeries.coeff_map] at this
    exact hF.inj this
  obtain ⟨hex, hcomp⟩ := GlobalTheory.QLog.defect_compat p O E hF G d c f hf
  choose s hs _ using fun n : ℕ => hex (p ^ n)
  have hadd := GlobalTheory.QLog.cobOne_ev_defect_dvd p O E hF G d c f hf
  obtain ⟨l, hl, huniq⟩ := GlobalTheory.LieOfAdditive.existsUnique_lie_of_additive p O G (fun n => c.ev n (s n))
    (fun n => hadd n (s n) (hs n)) (fun n => hcomp n (s n) (s (n + 1)) (hs n) (hs (n + 1)))
  refine ⟨l, ⟨fun n => In.top_iff.2 ⟨s n, hs n⟩, ?_⟩, ?_⟩
  · intro n w φ t hφ ht
    have : t = s n := hinj (ht.trans (hs n).symm)
    subst this
    exact hl n w φ hφ
  · intro l' hl'
    exact huniq l' fun n w φ hφ => hl'.2 n w φ (s n) hφ (hs n)

end GlobalTheory
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.swap_sub_in_of_cob2_in : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N J : Ideal B), N ≤ J → ∀ c : MvPowerSeries (Fin d ⊕ Fin d) Q, (IsLaw μ ∨ DIn N c) → constantCoeff c = 0 → (∀ α, ∃ k : ℕ, ∃ b ∈ J, (p : Q) ^ k * coeff α c = algebraMap B Q b) → In N (cob2 (up Q μ) c) → In N (swap c - c) → ∃ g : MvPowerSeries (Fin d) Q, constantCoeff g = 0 ∧ lin g = 0 ∧ (∀ α, ∃ k : ℕ, ∃ b ∈ J, (p : Q) ^ k * coeff α g = algebraMap B Q b) ∧ In N (c - cob1 (up Q μ) g) := by
  first | exact @GlobalTheory.symmetric_cocycle_is_coboundary_mod | exact GlobalTheory.symmetric_cocycle_is_coboundary_mod | (intros; apply GlobalTheory.symmetric_cocycle_is_coboundary_mod <;> assumption)
end

section

set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem isHom_map_of_semiHom_ev (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k')
    (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e)
    (s : SemiHom σ G' G) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k)
    (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k') (φ : Fin d → MvPowerSeries (Fin e) k')
    (hμ : c.IsLawOf μ) (hν : c'.IsLawOf ν) (hφ : ∀ n j, c'.ev n (φ j) = s.app n (c.x n j))
 :
    IsHom ν (fun i => MvPowerSeries.map σ (μ i)) φ := by
  have hL := (GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k' e G' c').2 ν hν
  have h2 := GlobalTheory.T.semilinearPDivGroupHom_eval_two_variable_series p k k' σ d e G G' c c' s φ hφ
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have h0 := (GlobalTheory.Katz.counit_dUnit_evA k' e (G'.A 0) (c'.x 0) (c'.nil 0) (c'.aug 0) (φ j)).1
    change Coalgebra.counit (R := k') (c'.ev 0 (φ j)) = _ at h0
    rw [← h0, hφ 0 j, (s.app 0).counit_map, c.aug 0 j, map_zero]
  · let z : ∀ n, G'.A n ⊗[k'] G'.A n := fun n => Coalgebra.comul (R := k') (s.app n (c.x n j))
    have hz : ∀ n, pullbackTwo (G'.res n) (z (n + 1)) = z n := fun n => by
      simp only [z]
      rw [pullTwo_comul, s.res_app, c.res]
    have hl : ∀ n, c'.ev₂ n (subst ν (φ j)) = z n := fun n => by
      rw [(hL.2 n (φ j)).1, hφ n j]
    have hr : ∀ n, c'.ev₂ n (pull2 φ (MvPowerSeries.map σ (μ j))) = z n := fun n => by
      rw [h2 n (μ j), hμ n j, SemiBialgHom.two_comul]
    exact ((GlobalTheory.T.chart_square_coordinates_present_levels p k' e G' c').2 z hz).unique hl hr

end GlobalTheory.Katz
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz.LazardModP

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]

theorem algebraMap_pow_ne_zero (m : ℕ) :
    algebraMap (WittVector p k) (Fr p k) ((p : WittVector p k) ^ m) ≠ 0 := fun h =>
  pow_ne_zero m (WittVector.p_nonzero p k)
    (IsFractionRing.injective (WittVector p k) (Fr p k) (by rw [h, map_zero]))

theorem coeff_wsmul {σ : Type} (w : WittVector p k) (f : MvPowerSeries σ (Fr p k))
    (α : σ →₀ ℕ) : coeff α (w • f) = algebraMap (WittVector p k) (Fr p k) w * coeff α f := by
  rw [← Algebra.smul_def]; rfl

theorem mem_one_of_p_smul {σ : Type} (f : MvPowerSeries σ (Fr p k))
    (hf : (p : WittVector p k) • f ∈ intBy p k σ (p : WittVector p k)) : f ∈ intBy p k σ 1 := by
  intro α
  obtain ⟨w, hw⟩ := hf α
  refine ⟨w, ?_⟩
  rw [coeff_wsmul, map_mul] at hw
  rw [one_mul]
  have h0 := algebraMap_pow_ne_zero p k 1
  rw [pow_one] at h0
  exact mul_left_cancel₀ h0 hw

theorem exists_pow_smul_mem {d N : ℕ} (e : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k))
    (he : ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ e = 0) :
    ∃ m : ℕ, ((p : WittVector p k) ^ m) • e ∈ intBy p k _ (p : WittVector p k) := by
  classical
  have hfin := Finsupp.finite_of_degree_le (σ := Fin d ⊕ Fin d) N
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors (WittVector p k)) (hfin.toFinset.image fun γ => coeff γ e)
  have hb0 : (b : WittVector p k) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  obtain ⟨n, u, hu⟩ := WittVector.exists_eq_pow_p_mul' (b : WittVector p k) hb0
  refine ⟨n + 1, fun γ => ?_⟩
  by_cases hγ : γ.degree = N
  · have hmem : coeff γ e ∈ hfin.toFinset.image fun γ => coeff γ e :=
      Finset.mem_image.2 ⟨γ, by simp [hγ], rfl⟩
    obtain ⟨w, hw⟩ := hb _ hmem
    refine ⟨((u⁻¹ : (WittVector p k)ˣ) : WittVector p k) * w, ?_⟩
    have hw' : algebraMap (WittVector p k) (Fr p k) w =
        algebraMap (WittVector p k) (Fr p k) (b : WittVector p k) * coeff γ e := by
      rw [hw, Algebra.smul_def]
    have hu1 : algebraMap (WittVector p k) (Fr p k) ((u⁻¹ : (WittVector p k)ˣ) : WittVector p k) *
        algebraMap (WittVector p k) (Fr p k) (u : WittVector p k) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [hu, map_mul, map_pow] at hw'
    rw [coeff_wsmul, map_mul, map_mul, map_pow, pow_succ]
    linear_combination (-algebraMap (WittVector p k) (Fr p k) (p : WittVector p k) *
      algebraMap (WittVector p k) (Fr p k) ((u⁻¹ : (WittVector p k)ˣ) : WittVector p k)) * hw' +
      (-algebraMap (WittVector p k) (Fr p k) (p : WittVector p k) ^ n *
        algebraMap (WittVector p k) (Fr p k) (p : WittVector p k) * coeff γ e) * hu1
  · refine ⟨0, ?_⟩
    rw [coeff_wsmul, he γ hγ]
    simp

theorem lift_addLaw (d : ℕ) :
    (fun i => Katz.lift p (addLaw k d i)) = addLaw (Fr p k) d := by
  funext i
  ext γ
  rw [coeff_lift]
  simp only [addLaw, map_add (f := _), coeff_X]
  by_cases h1 : γ = Finsupp.single (Sum.inl i) 1
  · have h2 : γ ≠ Finsupp.single (Sum.inr i) 1 := by
      rw [h1]; intro h; exact Sum.inl_ne_inr ((Finsupp.single_left_inj one_ne_zero).1 h)
    simp only [if_pos h1, if_neg h2, add_zero, map_one, map_one]
  · by_cases h2 : γ = Finsupp.single (Sum.inr i) 1
    · simp only [if_neg h1, if_pos h2, zero_add, map_one, map_one]
    · simp only [if_neg h1, if_neg h2, add_zero, WittVector.teichmuller_zero, map_zero]

end GlobalTheory.Katz.LazardModP

namespace GlobalTheory.Katz.LazardModP

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]

theorem step (d N : ℕ) (hN : 2 ≤ N) (m : ℕ) : ∀ e : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k),
    (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ e = 0) →
    cob2 (addLaw (Fr p k) d) e ∈ intBy p k _ (p : WittVector p k) →
    swap e - e ∈ intBy p k _ (p : WittVector p k) →
    ((p : WittVector p k) ^ m) • e ∈ intBy p k _ (p : WittVector p k) →
    ∃ h : MvPowerSeries (Fin d) (Fr p k), (∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α h = 0) ∧
      e - cob1 (addLaw (Fr p k) d) h ∈ intBy p k _ (p : WittVector p k) := by
  have hconst : ∀ i, constantCoeff (addLaw (Fr p k) d i) = 0 := fun i => by simp [addLaw]
  have hA := GlobalTheory.T.formalGroupLawCoboundaryTwo_coboundaryOne (Fr p k) d (addLaw (Fr p k) d) hconst 0
  have hlaw : IsLaw (addLaw (Fr p k) d) := hA.2.2.2.2.1
  have hcob0 : cob1 (addLaw (Fr p k) d) 0 = 0 := by
    have := formalCoboundary_smul hconst 0 0
    rwa [zero_smul, zero_smul] at this
  have hR := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ Fin d)
  have hR3 := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ (Fin d ⊕ Fin d))
  have hRC := GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d (addLaw k d) (fun i => by simp [addLaw])
  rw [lift_addLaw] at hRC
  induction m with
  | zero =>
    intro e _ _ _ hm
    refine ⟨0, fun _ _ => by simp, ?_⟩
    rw [hcob0, sub_zero]
    simpa using hm
  | succ m ih =>
    intro e he hcb hsw hm
    have hsm : ∀ {σ : Type} (x : MvPowerSeries σ (Fr p k)), ((p : WittVector p k) ^ m) • x =
        algebraMap (WittVector p k) (Fr p k) ((p : WittVector p k) ^ m) • x :=
      fun x => (algebraMap_smul (Fr p k) _ x).symm
    have hQ := algebraMap_pow_ne_zero p k m
    rw [pow_succ', mul_smul] at hm
    have he' := mem_one_of_p_smul p k _ hm
    obtain ⟨c, hc⟩ := (hR.1 _).1 he'
    have hcb' : cob2 (addLaw (Fr p k) d) (((p : WittVector p k) ^ m) • e) ∈
        intBy p k _ (p : WittVector p k) := by
      rw [hsm, (hA.2.2.2.1 _ e).1, ← hsm]
      exact Submodule.smul_mem _ _ hcb
    have hsw' : swap (((p : WittVector p k) ^ m) • e) - ((p : WittVector p k) ^ m) • e ∈
        intBy p k _ (p : WittVector p k) := by
      rw [hsm, (hA.2.2.2.1 _ e).2, ← smul_sub, ← hsm]
      exact Submodule.smul_mem _ _ hsw
    obtain ⟨hr2, hrs⟩ := hRC.1 _ _ hc
    have hc2 : cob2 (addLaw k d) c = 0 := hR3.2.1 _ _ _ hr2 ((hR3.2.2.2.2.2.1 _).1 hcb')
    have hcs : swap c = c := sub_eq_zero.1
      (hR.2.1 _ _ _ (hR.2.2.2.1 _ _ _ _ hrs hc).2 ((hR.2.2.2.2.2.1 _).1 hsw'))
    have hch : ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ c = 0 := by
      intro γ hγ
      obtain ⟨w, hw1, hw2⟩ := hc γ
      rw [coeff_wsmul, he γ hγ, mul_zero] at hw1
      have hw0 : w = 0 := IsFractionRing.injective (WittVector p k) (Fr p k) (by rw [← hw1, map_zero])
      rw [← hw2, hw0, map_zero]
    obtain ⟨h', hh', hred⟩ := GlobalTheory.T.homogeneous_cocycle_additiveLaw_reduction_coboundary p k d N c hN ⟨hc2, hcs⟩ hch
    have hdiff : ((p : WittVector p k) ^ m) • e - cob1 (addLaw (Fr p k) d) h' ∈
        intBy p k _ (p : WittVector p k) := by
      have := (hR.2.2.2.1 _ _ _ _ hc hred).2
      rw [sub_self] at this
      exact (hR.2.2.2.2.2.1 _).2 this
    have hcobh1 : ((p : WittVector p k) ^ m) • cob1 (addLaw (Fr p k) d)
        ((algebraMap (WittVector p k) (Fr p k) ((p : WittVector p k) ^ m))⁻¹ • h') =
        cob1 (addLaw (Fr p k) d) h' := by
      rw [hsm, ← formalCoboundary_smul hconst, smul_smul, mul_inv_cancel₀ hQ, one_smul]
    have hh1 : ∀ α : Fin d →₀ ℕ, α.degree ≠ N →
        coeff α ((algebraMap (WittVector p k) (Fr p k) ((p : WittVector p k) ^ m))⁻¹ • h') = 0 := by
      intro α hα
      rw [coeff_smul, hh' α hα, mul_zero]
    have hcoc := (GlobalTheory.T.formalGroupLawCoboundaryTwo_coboundaryOne (Fr p k) d (addLaw (Fr p k) d) hconst
      ((algebraMap (WittVector p k) (Fr p k) ((p : WittVector p k) ^ m))⁻¹ • h')).2.2.2.2.2 hlaw
    obtain ⟨h2, hh2, hfin⟩ := ih (e - cob1 (addLaw (Fr p k) d)
        ((algebraMap (WittVector p k) (Fr p k) ((p : WittVector p k) ^ m))⁻¹ • h'))
      (fun γ hγ => by
        rw [map_sub, he γ hγ, (GlobalTheory.T.additive_formal_group_coboundary_homogeneous (Fr p k) d N).1 _ hh1 γ hγ, sub_zero])
      (by rw [((hA.2.2.1) e _).2.1, hcoc.1, sub_zero]; exact hcb)
      (by
        rw [((hA.2.2.1) e _).2.2, hcoc.2]
        convert hsw using 1
        abel)
      (by rw [smul_sub, hcobh1]; exact hdiff)
    refine ⟨(algebraMap (WittVector p k) (Fr p k) ((p : WittVector p k) ^ m))⁻¹ • h' + h2,
      fun α hα => by rw [map_add (f := _), hh1 α hα, hh2 α hα, add_zero], ?_⟩
    rw [formalCoboundary_add hconst]
    convert hfin using 1
    abel

end GlobalTheory.Katz.LazardModP

namespace GlobalTheory.Katz

theorem lazard_mod_p_frac : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (d N : ℕ) (e : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k)), 2 ≤ N →
    (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ e = 0) →
    cob2 (addLaw (Fr p k) d) e ∈ intBy p k _ p → swap e - e ∈ intBy p k _ p →
    ∃ h : MvPowerSeries (Fin d) (Fr p k), (∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α h = 0) ∧
      e - cob1 (addLaw (Fr p k) d) h ∈ intBy p k _ p := by
  intro p _ k _ _ _ d N e hN he hcb hsw
  obtain ⟨m, hm⟩ := LazardModP.exists_pow_smul_mem p k e he
  exact LazardModP.step p k d N hN m e he hcb hsw hm

end GlobalTheory.Katz
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz

theorem Chart.ev_X {p : ℕ} {k : Type} [CommRing k] {d : ℕ} {G : PDivGroup p k} (c : Chart G d)
    (n : ℕ) (i : Fin d) : c.ev n (X i) = c.x n i := by
  have hs : HasSubst (fun i => (C (c.x n i) : MvPowerSeries Empty (G.A n))) :=
    hasSubst_of_constantCoeff_nilpotent fun i => by simpa using c.nil n i
  show constantCoeff (substAlgHom (R := k) hs (X i)) = c.x n i
  rw [coe_substAlgHom, subst_X hs, constantCoeff_C]

theorem Chart.isMapOf_add : ∀ (p : ℕ) (k : Type) [CommRing k] (d e : ℕ) (G H : PDivGroup p k)
    (c : Chart G d) (c' : Chart H e), ∀ (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k)
    (f g : G ⟶ H) (φ ψ : Fin e → MvPowerSeries (Fin d) k), c'.IsLawOf ν → c.IsMapOf c' f φ →
    c.IsMapOf c' g ψ → c.IsMapOf c' (f + g) (op ν φ ψ) := by
  intro p k _ d e G H c c' ν f g φ ψ hν hf hg n j
  have hφ := ((GlobalTheory.T.connectedPDivGroupHom_coordinates_existsUnique p k d e G H c c' f).2 φ hf).1
  have hψ := ((GlobalTheory.T.connectedPDivGroupHom_coordinates_existsUnique p k d e G H c c' g).2 ψ hg).1
  let L : H.A n ⊗[k] H.A n →ₐ[k] G.A n := Algebra.TensorProduct.lift
    (f.app n : H.A n →ₐ[k] G.A n) (g.app n : H.A n →ₐ[k] G.A n) (fun _ _ => Commute.all _ _)
  have hadd : ∀ a, (f + g).app n a = L (Coalgebra.comul a) := fun a => by
    have h := congrArg (fun u => u.ofConv a) (map_mul toPts (f.conv n) (g.conv n))
    simp only [toPts_ofConv] at h
    exact h.trans (AlgHom.convMul_apply _ _ a)
  have hy : ∀ i, IsNilpotent (L (c'.x₂ n i)) := fun i => (c'.nil₂ n i).map L
  have ha : ∀ i, constantCoeff (Sum.elim φ ψ i) = 0 := fun i => by
    cases i with
    | inl i => exact hφ i
    | inr i => exact hψ i
  have hnil : ∀ t, IsNilpotent (c.ev n (X t)) := fun t => by
    rw [Chart.ev_X]; exact c.nil n t
  have h1 : ∀ i, c.ev n (Sum.elim φ ψ i) = L (c'.x₂ n i) := fun i => by
    cases i with
    | inl i =>
      change c.ev n (φ i) = L (c'.x n i ⊗ₜ 1)
      rw [hf, Algebra.TensorProduct.lift_tmul, map_one, mul_one]; rfl
    | inr i =>
      change c.ev n (ψ i) = L (1 ⊗ₜ c'.x n i)
      rw [hg, Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl
  have e1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin e ⊕ Fin e) (G.A n)).1 (Fin d) (c.ev n) hnil (Sum.elim φ ψ) ha
    (fun i => L (c'.x₂ n i)) hy h1 (ν j)
  have e2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin e ⊕ Fin e) (H.A n ⊗[k] H.A n)).2 (G.A n) L (c'.x₂ n)
    (c'.nil₂ n) (fun i => L (c'.x₂ n i)) hy (fun _ => rfl) (ν j)
  change c.ev n (subst (Sum.elim φ ψ) (ν j)) = _
  rw [e1, ← e2, hadd]
  exact congrArg L (hν n j)

end GlobalTheory.Katz
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem eq_zero_of_cob1_eq_zero : ∀ (p : ℕ) (k : Type) [CommRing k] (h : (p : k) = 0) (d : ℕ)
    (G : PDivGroup p k) (c : Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k),
    c.IsLawOf μ → ∀ b, cob1 μ b = 0 → b = 0 := by
  intro p k _ h d G c μ hμ b hb
  obtain ⟨hres, -, huniq⟩ := GlobalTheory.T.functions_eq_series_in_chart p k d G c
  have hlaw := ((GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k d G c).2 μ hμ).2
  let B : G.funs := ⟨fun n => c.ev n b, fun n => hres n b⟩
  have hB : G.cob B = 0 := by
    refine Subtype.ext (funext fun n => ?_)
    change cobOne k (G.A n) (c.ev n b) = 0
    rw [← (hlaw n b).2, hb, map_zero]
  have hB0 := G.eq_zero_of_cob_eq_zero h hB
  have hb0 : ∀ n, c.ev n b = 0 := fun n => congrArg (fun B : G.funs => B.1 n) hB0
  obtain ⟨f, -, hf⟩ := huniq (fun _ => 0) (fun n => map_zero _)
  exact (hf b hb0).trans (hf 0 fun n => map_zero _).symm

end GlobalTheory.Katz
end

section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.exists_semilinear_action_dualWeylTensor : ∀ (R : Type) [CommRing R] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (mu : ι → ℕ → ℕ) (g : R ≃+* R), ∃ Φ : NablaT R N mu →+ NablaT R N mu, Function.Injective Φ ∧ (∀ (c : R) x, Φ (c • x) = g c • Φ x) ∧ ∀ (h : ι → GL (Fin N) R), (∀ τ a b, g ((h τ : Matrix (Fin N) (Fin N) R) a b) = (h τ : Matrix (Fin N) (Fin N) R) a b) → ∀ x, Φ (grp R N mu h x) = grp R N mu h (Φ x) := by
  first | exact @GlobalTheory.semilinear_transport | exact GlobalTheory.semilinear_transport | (intros; apply GlobalTheory.semilinear_transport <;> assumption)
end
