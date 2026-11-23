module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle251
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle088
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle079
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle131
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle132
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle133
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle134
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN.WpSep

theorem main : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (x y : Fin 2 → ZMod N), x ≠ 0 → y ≠ 0 →
    wp N x τ = wp N y τ → x = y ∨ x = -y := by
  intro N _ τ x y hx hy h1
  obtain ⟨hsub, hadd, hmem, -, -⟩ := GlobalTheory.WpFam.TorsMem.main N τ
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have hz : tors N τ x ∉ (tauPair τ).lattice := fun h => hx ((hmem x).1 h)
  have hw : tors N τ y ∉ (tauPair τ).lattice := fun h => hy ((hmem y).1 h)
  rw [wp, wp, div_left_inj' (pow_ne_zero _ hc)] at h1
  rcases (Formalism.L2.Th1.F.pInjective (tauPair τ) _ _ hz hw).1 h1 with h | h
  · exact Or.inl ((hsub x y).1 h)
  · right
    have h2 := (tauPair τ).lattice.add_mem (hadd x y) h
    rw [sub_add_cancel] at h2
    have h3 := (hmem (x + y)).1 h2
    exact eq_neg_of_add_eq_zero_left h3

end GlobalTheory.FN.WpSep
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem kummer_moves : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime →
    ∀ F : Subfield L, ApproxRoot p v F → 0 < v (p : L) → v (p : L) < 1 →
    ∀ (G : Type) [Group G] [MulSemiringAction G L] (σ : G), (∀ x ∈ F, σ • x = x) →
    ∀ ζ α : L, IsPrimitiveRoot ζ p → α ≠ 0 → α ^ p ∈ F → σ • α = ζ * α → Moves v ⊤ σ := by
  intro L _ v p hp F hF hp0 hp1 G _ _ σ hσ ζ α hζ hα hαp hσα r hr
  obtain ⟨t, hrt, ht1⟩ := exists_between hr
  have ht0 : 0 < t := lt_of_le_of_lt (zero_le') hrt
  set s : ℝ≥0 := t⁻¹ with hs_def
  have hs1 : 1 < s := by rw [hs_def]; exact one_lt_inv₀ ht0 |>.mpr ht1
  have hs0 : 0 < s := lt_trans zero_lt_one hs1
  have hrs : r * s < 1 := by
    rw [hs_def, ← div_eq_mul_inv]; exact (div_lt_one ht0).mpr hrt
  obtain ⟨y, hyF, hy⟩ := GlobalTheory.T.kummer_generator_approx_critical_radius L v p hp F hF hp1 α hαp hp0 s hs1
  have hz := GlobalTheory.T.valuation_primitiveRoot_sub_one_pow_pred_eq L v p hp ζ hζ
  have hp2 : 2 ≤ p := hp.two_le
  have hpn : p - 1 ≠ 0 := by omega
  set β := α - y with hβ_def
  have hσβ : σ • β - β = (ζ - 1) * α := by
    rw [hβ_def, smul_sub, hσα, hσ y hyF]; ring
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  have hne : σ • β - β ≠ 0 := by
    rw [hσβ]; exact mul_ne_zero (sub_ne_zero.mpr hζ1) hα
  have hβ0 : β ≠ 0 := by
    intro h; apply hne; rw [h, smul_zero, sub_zero]

  have hvβ : v β ≤ s * v (σ • β - β) := by
    have h1 : v β ^ (p - 1) ≤ (s * v (σ • β - β)) ^ (p - 1) := by
      rw [hσβ, map_mul, mul_pow, mul_pow, hz]
      calc v β ^ (p - 1) ≤ s * v (p : L) * v α ^ (p - 1) := hy
        _ ≤ s ^ (p - 1) * v (p : L) * v α ^ (p - 1) := by
          gcongr
          exact le_self_pow₀ hs1.le hpn
        _ = s ^ (p - 1) * (v (p : L) * v α ^ (p - 1)) := by ring
    exact le_of_pow_le_pow_left₀ hpn (zero_le') h1
  obtain ⟨d, hdF, hd0, hdlo, hdhi⟩ := GlobalTheory.T.exists_pth_power_scale_thin_shell L v p hp F hF hp0 hp1 (r * s) hrs β hβ0
  refine ⟨β * d ^ p, Subfield.mem_top _, hdhi, ?_⟩
  have hσx : σ • (β * d ^ p) - β * d ^ p = d ^ p * (σ • β - β) := by
    rw [smul_mul', smul_pow', hσ d hdF]; ring
  rw [hσx]
  have hvx : v (β * d ^ p) ≤ s * v (d ^ p * (σ • β - β)) := by
    rw [map_mul, map_mul]
    calc v β * v (d ^ p) ≤ s * v (σ • β - β) * v (d ^ p) := by gcongr
      _ = s * (v (d ^ p) * v (σ • β - β)) := by ring
  have : r * s < s * v (d ^ p * (σ • β - β)) := lt_of_lt_of_le hdlo hvx
  rw [mul_comm] at this
  exact lt_of_mul_lt_mul_left this (zero_le')

end GlobalTheory.AlmostEt
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem translate_mem_aug_of_not_intertwine {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    (J : Set G) (θ : G → ℂ) (u : V) (hu : IsEig π J θ u) (y j : G) (hj : j ∈ J) (hc : y * j * y⁻¹ ∈ J)
    (hne : θ j ≠ θ (y * j * y⁻¹)) : π y u ∈ aug π J θ := by
  have h1 : π (y * j * y⁻¹) (π y u) = θ j • π y u := by
    have : π (y * j * y⁻¹) (π y u) = π y (π j u) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      simp
    rw [this, hu j hj, map_smul]
  have h2 : (θ j - θ (y * j * y⁻¹)) • π y u ∈ aug π J θ := by
    apply Submodule.subset_span
    exact ⟨_, hc, π y u, by rw [h1, sub_smul]⟩
  exact (Submodule.smul_mem_iff _ (sub_ne_zero.mpr hne)).mp h2

theorem eig_eq_zero_of_mem_aug_of_not_intertwine : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (J N : Set G) (θ : G → ℂ), Datum J θ →
    Datum N (fun _ => 1) → (∀ y ∈ N, (y ∈ J ∧ θ y = 1) ∨ ∃ j ∈ J, y * j * y⁻¹ ∈ J ∧ θ j ≠ θ (y * j * y⁻¹)) →
    ∀ u ∈ aug π N (fun _ => 1), IsEig π J θ u → u = 0 := by
  intro G V _ _ _ _ _ π hπ J N θ hJ hN hy u hu he
  classical
  obtain ⟨R, h1, hR, hs⟩ := GlobalTheory.T.character_average_twistedSpan_eq_zero G V π hπ N _ hN u hu
  simp only [inv_one, one_smul] at hs
  refine (GlobalTheory.T.characterEigenspace_isCompl_principalSeriesTwistedSpan G V π hπ J θ hJ).1 u ?_ he
  rw [← Finset.sum_filter_add_sum_filter_not R (fun y => y ∈ J ∧ θ y = 1)] at hs
  have hA : ∑ y ∈ R.filter (fun y => y ∈ J ∧ θ y = 1), π y u
      = ((R.filter (fun y => y ∈ J ∧ θ y = 1)).card : ℂ) • u := by
    rw [Finset.sum_congr rfl (g := fun _ => u), Finset.sum_const, Nat.cast_smul_eq_nsmul]
    intro y hy'
    obtain ⟨_, a, b⟩ := Finset.mem_filter.mp hy'
    rw [he y a, b, one_smul]
  have hB : ∑ y ∈ R.filter (fun y => ¬ (y ∈ J ∧ θ y = 1)), π y u ∈ aug π J θ := by
    refine Submodule.sum_mem _ fun y hy' => ?_
    obtain ⟨a, b⟩ := Finset.mem_filter.mp hy'
    obtain ⟨j, hj, hc, hne⟩ := (hy y (hR y a)).resolve_left b
    exact translate_mem_aug_of_not_intertwine π J θ u he y j hj hc hne
  have hc : ((R.filter (fun y => y ∈ J ∧ θ y = 1)).card : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Finset.card_ne_zero]
    exact ⟨1, Finset.mem_filter.mpr ⟨h1, hJ.one, hJ.val_one⟩⟩
  rw [← Submodule.smul_mem_iff _ hc, ← hA, eq_neg_of_add_eq_zero_left hs]
  exact Submodule.neg_mem _ hB

end GlobalTheory.PsType
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

theorem rootOfUnity_pow {Ω K : Type} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Field K] [Algebra Ω K]
    (l : ℕ) (hl : 0 < l) (ζ : Kˣ) (hζ : ζ ^ l = 1) (m : ℕ) (hm : 0 < m) : ∃ η : Kˣ, ζ = η ^ m := by
  haveI : NeZero l := ⟨hl.ne'⟩
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  have hω' : IsPrimitiveRoot (algebraMap Ω K ω) l := hω.map_of_injective (algebraMap Ω K).injective
  have hζK : (ζ : K) ^ l = 1 := by rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one]
  obtain ⟨i, -, hi⟩ := hω'.eq_pow_of_pow_eq_one hζK
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (ω ^ i) hm
  have hz0 : algebraMap Ω K z ≠ 0 := by
    intro h0
    have : (ζ : K) = 0 := by rw [← hi, ← map_pow, ← hz, map_pow, h0, zero_pow hm.ne']
    exact ζ.ne_zero this
  refine ⟨Units.mk0 _ hz0, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, ← map_pow, hz, map_pow, hi]

theorem khat_l_smul_eq_zero {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    [IsAlgClosed Ω] (x : X.Khat l) (hx : (l : ℤ_[l]) • x = 0) : x = 0 := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  suffices hn : ∀ n, AdicCompletion.eval (idl l) (X.Kl l) n x = 0 by
    apply AdicCompletion.ext
    intro n
    rw [← AdicCompletion.eval_apply, ← AdicCompletion.eval_apply, hn, map_zero]
  intro n
  obtain ⟨hsurj, -, -, -, -, -, -⟩ := GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l (n + 1)
  obtain ⟨-, hker, hmul, hone, -, -, -⟩ := GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l (n + 1)
  obtain ⟨-, hker0, -, hone0, -, -, -⟩ := GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l n
  obtain ⟨-, -, -, -, -, -, hred⟩ := GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l n
  obtain ⟨f, hf⟩ := hsurj (AdicCompletion.eval (idl l) (X.Kl l) (n + 1) x)
  have hpow : ∀ k : ℕ, X.cls l (n + 1) (f ^ k) = k • X.cls l (n + 1) f := by
    intro k
    induction k with
    | zero => simp [hone]
    | succ k ih => rw [pow_succ f k, hmul, ih, succ_nsmul]
  have h1 : X.cls l (n + 1) (f ^ l) = X.cls l (n + 1) 1 := by
    rw [hpow, hone, hf, ← Nat.cast_smul_eq_nsmul ℤ_[l], ← map_smul, hx, map_zero]
  obtain ⟨g, hg⟩ := (hker _ _).1 h1
  rw [one_mul] at hg
  set ζ : X.Kˣ := f * (g ^ (l ^ n))⁻¹ with hζdef
  have hζ : ζ ^ l = 1 := by
    rw [hζdef, mul_pow, hg, inv_pow, ← pow_mul, ← pow_succ, mul_inv_cancel]
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨η, hη⟩ := rootOfUnity_pow (Ω := Ω) l hl ζ hζ (l ^ n) (pow_pos hl n)
  have hf' : f = 1 * (η * g) ^ (l ^ n) := by
    rw [one_mul, mul_pow, ← hη, hζdef, inv_mul_cancel_right]
  rw [hred x f hf.symm, ← hone0]
  exact (hker0 _ _).2 ⟨_, hf'⟩

theorem khat_torsionFree (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    [IsAlgClosed Ω] (c : ℤ_[l]) (x : X.Khat l) (hc : c ≠ 0) (hcx : c • x = 0) : x = 0 := by
  have key : ∀ k : ℕ, ∀ y : X.Khat l, ((l : ℤ_[l]) ^ k) • y = 0 → y = 0 := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      apply khat_l_smul_eq_zero X l
      apply ih
      rw [smul_smul, ← pow_succ]; exact hy
  apply key c.valuation
  have h := PadicInt.unitCoeff_spec hc
  have : ((PadicInt.unitCoeff hc)⁻¹ : ℤ_[l]ˣ) • (c • x) = 0 := by rw [hcx, smul_zero]
  rw [Units.smul_def, smul_smul] at this
  nth_rw 2 [h] at this
  rwa [← mul_assoc, Units.inv_mul, one_mul] at this

end GlobalTheory.KZ.H3
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.eichlerShimuraPotential_submodule_and_base_change : ∀ (R : Type) [CommRing R] (w : ℕ) (Γ : Subgroup SL(2, ℤ)), (∀ F G, F ∈ Pot R w Γ → G ∈ Pot R w Γ → F + G ∈ Pot R w Γ) ∧ (0 ∈ Pot R w Γ) ∧ (∀ (c : R) F, F ∈ Pot R w Γ → c • F ∈ Pot R w Γ) ∧ (∀ F G, F ∈ Triv R w Γ → G ∈ Triv R w Γ → F + G ∈ Triv R w Γ) ∧ (∀ (c : R) F, F ∈ Triv R w Γ → c • F ∈ Triv R w Γ) ∧ (∀ (S : Type) [CommRing S] (f : R →+* S) F, F ∈ Pot R w Γ → (fun z => MvPolynomial.map f (F z)) ∈ Pot S w Γ) ∧ (∀ (S : Type) [CommRing S] (f : R →+* S) F, F ∈ Triv R w Γ → (fun z => MvPolynomial.map f (F z)) ∈ Triv S w Γ) := by
  first | exact @GlobalTheory.KZ.pot_triv_lin | exact GlobalTheory.KZ.pot_triv_lin | (intros; apply GlobalTheory.KZ.pot_triv_lin <;> assumption)
end

section

open GlobalTheory.Col PowerSeries

theorem _root_.GlobalTheory.T.ev_normOp_eq_nrm_ev_succ : ∀ (R : Type) [CommRing R] (p m : ℕ) [hp : Fact p.Prime] (hm : 1 ≤ m), IsAdicComplete (Ideal.span {(p : R)}) R → ∀ h : PowerSeries R, ev R p m (normOp p h) = nrm p m hm (ev R p (m + 1) h) := by
  first | exact @GlobalTheory.Col.ev_normOp_eq_nrm | exact GlobalTheory.Col.ev_normOp_eq_nrm | (intros; apply GlobalTheory.Col.ev_normOp_eq_nrm <;> assumption)
end

section

open GlobalTheory.Col PowerSeries

theorem _root_.GlobalTheory.T.normOp_congr_mod_pow_succ : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ → ∀ (h₁ h₂ r : PowerSeries R) (k : ℕ), 1 ≤ k → IsUnit h₂ → h₁ = h₂ + (p : PowerSeries R) ^ k * r → ∃ r' : PowerSeries R, normOp p h₁ = normOp p h₂ + (p : PowerSeries R) ^ (k + 1) * r' := by
  first | exact @GlobalTheory.Col.normOp_congr | exact GlobalTheory.Col.normOp_congr | (intros; apply GlobalTheory.Col.normOp_congr <;> assumption)
end

section

open GlobalTheory.Col PowerSeries

theorem _root_.GlobalTheory.T.normOp_eq_smap_add_mul : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ → ∀ h : PowerSeries R, ∃ r : PowerSeries R, normOp p h = smap σ h + (p : PowerSeries R) * r := by
  first | exact @GlobalTheory.Col.normOp_frob | exact GlobalTheory.Col.normOp_frob | (intros; apply GlobalTheory.Col.normOp_frob <;> assumption)
end
