module

public import Formalism.SharpRestriction.GlobalSchurBounds.MainIn
public import Formalism.SharpRestriction.GlobalSchurBounds.TopDensityNGeSixteen
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle001
public import Formalism.GL3MeanSquares.HookFormulaTorsion.Bundle004
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.SharpRestriction.GlobalSchurBounds.FirstClaimLemmaTwoFourOfLemmaTwoThree
public import Formalism.SharpRestriction.GlobalSchurBounds.JointsL
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle003
import Formalism.LocalRingCardinality.Lemmas
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions

theorem Closed.of_all {𝒞 : FamClass} {P : ∀ {eps : ℝ}, FamP eps → ℝ → Prop}
    (h : ∀ {eps : ℝ} (Fm : FamP eps) (CH : ℝ), P Fm CH) : Closed 𝒞 P :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => h Fm CH⟩⟩

theorem logNE_le_of_rows (D : D7) {Y x eps : ℝ} (he : 0 < eps) (h1 : 1 < Y) (hY : Y ≤ x) (h : QDRows_at D Y eps) :
    Real.log (GlobalTheoryTheory.NE D) ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hlog⟩ := h
  have hY0 : 0 < Y := by linarith
  have hNE : Real.log (GlobalTheoryTheory.NE D) ≤ 2 * Y ^ (eps / 5) * Real.log Y ^ 2 := by
    first
      | (unfold GlobalTheoryTheory.NE; push_cast; exact hlog)
      | simpa [GlobalTheoryTheory.NE] using hlog
  have ha : Y ^ (eps / 5) ≤ x ^ (eps / 5) := Real.rpow_le_rpow hY0.le hY (by linarith)
  have hl0 : 0 ≤ Real.log Y := Real.log_nonneg h1.le
  have hl : Real.log Y ≤ Real.log x := Real.log_le_log hY0 hY
  have hsq : Real.log Y ^ 2 ≤ Real.log x ^ 2 := by nlinarith
  have hp : 0 ≤ Y ^ (eps / 5) := Real.rpow_nonneg hY0.le _
  have hm : Y ^ (eps / 5) * Real.log Y ^ 2 ≤ x ^ (eps / 5) * Real.log x ^ 2 :=
    mul_le_mul ha hsq (by positivity) (le_trans hp ha)
  linarith

theorem one_lt_of_win {eps : ℝ} (Fm : FamP eps) {x Y : ℝ} (hx : 1 < x) (h : x ^ (1 / Fm.J) ≤ Y) : 1 < Y := by
  obtain ⟨i⟩ := Fm.Ix_zero
  have hJ : 1 ≤ Fm.J := by
    have h0 := (Fm.L 0 i).sc.one_le_J
    rwa [Fm.L_J 0 i] at h0
  have hp : 0 < 1 / Fm.J := one_div_pos.mpr (by linarith)
  exact lt_of_lt_of_le (Real.one_lt_rpow hx hp) h

theorem eps_pos_of_fam {eps : ℝ} (Fm : FamP eps) : 0 < eps := by
  obtain ⟨i⟩ := Fm.Ix_zero
  have h0 := (Fm.L 0 i).sc.eps_pos
  rwa [Fm.L_eps 0 i] at h0

theorem pair_and_box_hypothesis_of_congruence_data_and_boxes {eps : ℝ} (Fm : FamP eps) (hR : QDRowsF Fm) (hB : BoxesF Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      (∃ Y : ℝ, 1 < Y ∧ Y ≤ x ∧ ShortIntervalPrimes.PairAt Y eps (Fm.D x i).host.q (Fm.D x i).host.d) ∧ ShortIntervalPrimes.PropTwoSixBoxHypothesis (Fm.D x i) x eps := by
  obtain ⟨xR, hR⟩ := hR
  obtain ⟨xB, hB⟩ := hB
  refine ⟨max (max xR xB) 2, fun x hx i => ?_⟩
  have hxR : xR ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxB : xB ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx1 : 1 < x := by linarith [le_max_right (max xR xB) 2]
  obtain ⟨Y, ⟨hY1, hY2⟩, hQ⟩ := hR x hxR i
  obtain ⟨Y', ⟨hY1', hY2'⟩, -, hE⟩ := hB x hxB i
  have hY : 1 < Y := one_lt_of_win Fm hx1 hY1
  have hY' : 1 < Y' := one_lt_of_win Fm hx1 hY1'
  have hlog := logNE_le_of_rows (Fm.D x i) (eps_pos_of_fam Fm) hY hY2 hQ
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, -⟩ := hQ
  exact ⟨⟨Y, hY, hY2, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩, ⟨Y', hY', hY2', hE⟩, hlog⟩

def LitThin : Prop :=
  (∃ C1 c : ℝ, 0 < C1 ∧ 0 < c ∧ ∀ D : D7, ShortIntervalPrimes.adm6 D C1 c) ∧ (∃ C : ℝ, 0 < C ∧ ∀ D : D7, ShortIntervalPrimes.adm7 D C) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ D : D7, ShortIntervalPrimes.adm11 D C

theorem prop_two_six_congruence_family_of_literature {eps : ℝ} (Fm : FamP eps) (hL : LitThin) : ShortIntervalPrimes.FamilyPropTwoSixCongruenceForm Fm := by
  obtain ⟨⟨C1, c, hC1, hc, h6⟩, ⟨C7, hC7, h7⟩, C11, hC11, h11⟩ := hL
  exact ShortIntervalPrimes.proposition_six_norm_family_of_admitted Fm ⟨C1, c, hC1, hc, fun _ _ _ => h6 _⟩ ⟨C7, hC7, fun _ _ _ => h7 _⟩ ⟨C11, hC11, fun _ _ _ => h11 _⟩

theorem chosenThin_of_boxesN {eps : ℝ} (Fm : FamP eps) (hL : LitThin) (hB : BoxesF Fm) (hR : QDRowsF Fm) :
    ∃ c6 : ℝ, 0 < c6 ∧ ChosenThin Fm c6 := by
  obtain ⟨c, hc, x0, -, h⟩ := prop_two_six_congruence_family_of_literature Fm hL
  obtain ⟨xa, ha⟩ := pair_and_box_hypothesis_of_congruence_data_and_boxes Fm hR hB
  refine ⟨c, hc, max x0 xa, fun x hx i => ?_⟩
  have h1 : x0 ≤ x := le_trans (le_max_left _ _) hx
  have h2 : xa ≤ x := le_trans (le_max_right _ _) hx
  have hn := h x h1 i
  unfold ShortIntervalPrimes.PropTwoSixThinScales at hn
  exact hn (ha x h2 i).2

theorem chosenThin_closed (𝒞 : FamClass) (hL : LitThin) :
    Closed 𝒞 (fun Fm _ => BoxesF Fm → QDRowsF Fm → (∃ C5 : ℝ, 0 < C5 ∧ ChosenQD Fm C5) →
      ∃ c6 : ℝ, 0 < c6 ∧ ChosenThin Fm c6) :=
  Closed.of_all fun Fm _ hB hR _ => chosenThin_of_boxesN Fm hL hB hR

section Proviso

variable {D : D7}

theorem proviso_e (L : SizeData₂ D) (h4f : LinkB.RankM D) (hDu : StandardLattice.FactDuStar D) (hDs : StandardLattice.FactDstar D) :
    ChProviso_at L (Real.exp 1) := by
  intro u
  have hΓ : 1 < (D.mem u).A.GamP := (D.mem u).A.one_lt_gammaP
  have hΓ0 : 0 < (D.mem u).A.GamP := lt_trans one_pos hΓ
  have hD : 0 < StandardLattice.DstarD D := by rw [← hDs, ← D.Dstar_eq u]; exact (D.mem u).A.Dstar_pos
  have hd : 0 < StandardLattice.duStarU D u := by rw [← hDu u]; exact_mod_cast (D.mem u).A.duStar_pos
  have hk := D.R.k_ge
  have hf : 1 ≤ D.R.f := by
    have hm : D.R.m ≤ D.R.f := D.R.m_le_f
    have hm2 := D.R.two_le_m
    omega
  have hfk : 2 * D.R.f ≤ 2 ^ D.R.k := by
    have h1 : D.R.f ≤ D.R.k := D.R.f_le_k
    have h2 : D.R.k - 1 < 2 ^ (D.R.k - 1) := Nat.lt_two_pow_self
    have h3 : 2 ^ D.R.k = 2 * 2 ^ (D.R.k - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  have hfR : (0 : ℝ) < D.R.f := by exact_mod_cast hf
  have hkR : (0 : ℝ) < D.R.k := by exact_mod_cast (by omega : 0 < D.R.k)
  have hX : Real.exp (StandardLattice.logXuD D u) ^ (D.R.f * D.R.k) = StandardLattice.DstarD D / StandardLattice.duStarU D u := by
    rw [← Real.exp_nat_mul]
    unfold StandardLattice.logXuD StandardLattice.logXu
    push_cast
    rw [show (D.R.f : ℝ) * D.R.k * (1 / ((D.R.f : ℝ) * D.R.k) * Real.log (StandardLattice.DstarD D / StandardLattice.duStarU D u)) =
      Real.log (StandardLattice.DstarD D / StandardLattice.duStarU D u) by field_simp]
    exact Real.exp_log (div_pos hD hd)
  have hT : (2 : ℝ) ≤ ((D.mem u).A.T : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.two_le
  have hw := D.T_win u
  have hXe := LinkB.exp_logXu hDu hDs u
  have h1 : Real.exp (StandardLattice.logXuD D u) * (D.mem u).A.GamP ^ (-(2 : ℝ) / (D.R.f * D.R.k)) =
      (D.mem u).A.Tstar := by rw [hXe]; rfl
  obtain ⟨c1, c2, -, -⟩ := Formalism.HermitianLattices.GenusMassVolumes.mass_corollary D.R.f D.R.k ((D.mem u).A.T : ℝ)
    (Real.exp (StandardLattice.logXuD D u)) (D.mem u).A.GamP (StandardLattice.DstarD D) (StandardLattice.duStarU D u) (D.duS u : ℝ)
    (StandardLattice.logXuD D u) (StandardLattice.logXuD D u) hf (by omega) hfk hT (Real.exp_pos _) hΓ.le hD hd hX
    (by rw [h1]; exact hw.1) (by rw [h1, mul_comm]; exact hw.2) (h4f u)
    (by rw [Real.log_exp]) (by rw [Real.log_exp])
  rw [LinkB.gamL_eq L u, hDs]
  have hG2 : 0 ≤ (D.mem u).A.GamP ^ 2 := by positivity
  constructor
  · have he : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    refine (inv_anti₀ (by norm_num) he).trans ?_
    rw [le_div_iff₀ hD]
    calc (2 : ℝ)⁻¹ * StandardLattice.DstarD D = StandardLattice.DstarD D * ((D.mem u).A.GamP⁻¹) ^ 2 / 2 * (D.mem u).A.GamP ^ 2 := by
          field_simp
      _ ≤ (D.duS u : ℝ) * (D.mem u).A.GamP ^ 2 := mul_le_mul_of_nonneg_right c1 hG2
  · rw [div_le_iff₀ hD]
    calc (D.duS u : ℝ) * (D.mem u).A.GamP ^ 2
        ≤ Real.exp 1 * (StandardLattice.DstarD D * ((D.mem u).A.GamP⁻¹) ^ 2) * (D.mem u).A.GamP ^ 2 :=
          mul_le_mul_of_nonneg_right c2 hG2
      _ = Real.exp 1 * StandardLattice.DstarD D := by field_simp

end Proviso

def RankTiesF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (∀ j, StandardLattice.SplitsF (Fm.D x i) ((Fm.D x i).host.g j)) ∧
    ∀ u : (Fm.D x i).what₂.Word, StandardLattice.SplitsF (Fm.D x i) ((Fm.D x i).mem u).A.T ∧ StandardLattice.Mu0Tie (Fm.D x i) u

theorem rankHypF_of {eps : ℝ} (Fm : FamP eps) (h : RankTiesF Fm) : LinkB.RankHypF Fm := by
  obtain ⟨x0, h⟩ := h
  unfold LinkB.RankHypF
  refine ⟨max (max x0 3) (Fm.x1 + 1), fun x hx i => ?_⟩
  have h0 : x0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have h3 : 3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have h1 : Fm.x1 < x := by linarith [le_max_right (max x0 3) (Fm.x1 + 1)]
  obtain ⟨hg, hu⟩ := h x h0 i
  unfold LinkB.RankHyp
  exact ⟨GlobalTheoryTheory.JDB.gBig_fam Fm x h3 h1 i, hg, hu⟩

end Formalism.MainNotions

end
end

section

section Commens

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.MainNotions.Lnk

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory

section General

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]

theorem mem_of_locally (M : Submodule (𝓞 K) V) (x : V)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), ∃ s : 𝓞 K, s ∉ v.asIdeal ∧ s • x ∈ M) : x ∈ M := by
  let I : Ideal (𝓞 K) := M.comap (LinearMap.toSpanSingleton (𝓞 K) V x)
  have hI : ∀ a : 𝓞 K, a ∈ I ↔ a • x ∈ M := fun a => Iff.rfl
  have htop : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I hne
    have hm0 : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)
    obtain ⟨s, hs, hsx⟩ := h ⟨m, hm.isPrime, hm0⟩
    exact hs (hle ((hI s).2 hsx))
  have h1 : (1 : 𝓞 K) ∈ I := by rw [htop]; trivial
  have h2 := (hI 1).1 h1
  rwa [one_smul] at h2

theorem exists_common_mul (M N : Submodule (𝓞 K) V) (hM : M.FG)
    (h : ∀ y ∈ M, ∃ s : 𝓞 K, s ≠ 0 ∧ s • y ∈ N) : ∃ c : 𝓞 K, c ≠ 0 ∧ ∀ y ∈ M, c • y ∈ N := by
  classical
  obtain ⟨S, hS⟩ := hM
  have hSM : ∀ y ∈ S, y ∈ M := fun y hy => by rw [← hS]; exact Submodule.subset_span hy
  let f : V → 𝓞 K := fun y => if hy : y ∈ M then (h y hy).choose else 1
  have hf0 : ∀ y, f y ≠ 0 := by
    intro y
    by_cases hy : y ∈ M
    · simp only [f, dif_pos hy]; exact (h y hy).choose_spec.1
    · simp only [f, dif_neg hy]; exact one_ne_zero
  have hfN : ∀ y ∈ M, f y • y ∈ N := by
    intro y hy
    simp only [f, dif_pos hy]; exact (h y hy).choose_spec.2
  refine ⟨∏ y ∈ S, f y, Finset.prod_ne_zero_iff.2 (fun y _ => hf0 y), ?_⟩
  have hle : Submodule.span (𝓞 K) (S : Set V) ≤ N.comap (LinearMap.lsmul (𝓞 K) V (∏ y ∈ S, f y)) := by
    rw [Submodule.span_le]
    intro y hy
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem f hy
    show (∏ y ∈ S, f y) • y ∈ N
    rw [hk, mul_comm, mul_smul]
    exact N.smul_mem _ (hfN y (hSM y hy))
  intro y hy
  rw [← hS] at hy
  exact hle hy

end General

theorem locLe_zero {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    {w : HeightOneSpectrum (𝓞 K)} {A B : Submodule (𝓞 K) V} (h : DV.LocLe w 0 A B) :
    ∀ x ∈ A, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ B := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := h x hx
  rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul] at hsx
  exact ⟨s, hs, hsx⟩

theorem place_over' (D : D7) (p : ℕ) (hp : p.Prime) : ∃ w : D.what₂.places.Pl, D.what₂.places.resChar w = p := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  obtain ⟨P, hP, hlo⟩ :=
    (inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.what₂.LL)))
  have hpP : ((p : ℕ) : 𝓞 D.what₂.LL) ∈ P := by
    have h1 : (p : ℤ) ∈ Ideal.span {(p : ℤ)} := Ideal.mem_span_singleton_self _
    rw [hlo.over, Ideal.mem_comap] at h1
    simpa using h1
  have hne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpP
    exact hp.ne_zero (by exact_mod_cast hpP)
  refine ⟨D.plEq.symm ⟨P, hP, hne⟩, ?_⟩
  set w := D.plEq.symm ⟨P, hP, hne⟩ with hw
  have hr := J.resChar_mem D w
  rw [hw, Equiv.apply_symm_apply] at hr
  rw [← hw] at hr
  by_contra hcon
  have hco : Nat.Coprime (D.what₂.places.resChar w) p :=
    (Nat.coprime_primes (D.what₂.places.resChar_prime w) hp).2 hcon
  have hb := Nat.gcd_eq_gcd_ab (D.what₂.places.resChar w) p
  rw [hco] at hb
  have h1 : (1 : 𝓞 D.what₂.LL) = ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) *
      ((Nat.gcdA (D.what₂.places.resChar w) p : ℤ) : 𝓞 D.what₂.LL) +
      ((p : ℕ) : 𝓞 D.what₂.LL) * ((Nat.gcdB (D.what₂.places.resChar w) p : ℤ) : 𝓞 D.what₂.LL) := by
    have := congrArg (fun z : ℤ => (z : 𝓞 D.what₂.LL)) hb
    simpa using this
  exact hP.ne_top ((Ideal.eq_top_iff_one P).2 (by
    rw [h1]; exact P.add_mem (P.mul_mem_right _ hr) (P.mul_mem_right _ hpP)))

def NuAtT (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ u w, D.what₂.places.resChar w = (D.mem u).A.T → DV.LocLe (D.plEq w) 0 (L.NuLat u) (DV.MramL D u)

theorem nuAtT_of {D : D7} {L : SizeData₂ D} (hAtT : NuAtTDef D L)
    (h5 : ∀ u w, D.what₂.places.resChar w = (D.mem u).A.T → LT.Nlam D u w ≤ LT.Sram D u w) : NuAtT D L := by
  intro u w hw x hx
  have h1 : InLoc (D.plEq w) (L.NuLat u) x :=
    ⟨1, fun h => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h), by rwa [one_smul]⟩
  have h2 : D.nuIn u x ∈ LT.Nlam D u w := (hAtT u w hw x).mp h1
  have h3 : D.nuIn u x ∈ (D.fm u).S 0 w := (h5 u w hw h2).1
  obtain ⟨s, hs, hsx⟩ := D.locSpan u w _ h3
  refine ⟨s, hs, ?_⟩
  rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
  show (D.nuIn u).restrictScalars (𝓞 D.what₂.LL) (s • x) ∈ ((D.fm u).lat 0).L
  rw [map_smul]
  exact hsx

theorem nu_le_mram {D : D7} {L : SizeData₂ D} (hNu : DV.NuDef D L) (hT : NuAtT D L) (u : D.what₂.Word) :
    L.NuLat u ≤ DV.MramL D u := by
  intro x hx
  refine mem_of_locally _ x (fun v => ?_)
  have hv : D.plEq (D.plEq.symm v) = v := Equiv.apply_symm_apply _ _
  by_cases hw : D.what₂.places.resChar (D.plEq.symm v) = (D.mem u).A.T
  · have := locLe_zero (hT u _ hw) x hx
    rwa [hv] at this
  · have := locLe_zero (hNu.1 u _ hw) x hx
    rwa [hv] at this

theorem exists_free_prime (D : D7) (u : D.what₂.Word) :
    ∃ p : ℕ, p.Prime ∧ p ≠ (D.mem u).A.T ∧ ¬ DV.InertK D p := by
  have hq2 : D.host.q ≠ 2 := by
    have := D.host.hyp.2.2.1
    omega
  by_cases hT : (D.mem u).A.T = 2
  · refine ⟨D.host.q, D.host.hyp.1, by rw [hT]; exact hq2, ?_⟩
    unfold DV.InertK Host.cls primeClass
    rw [if_neg D.host.q_notMem_small, if_pos rfl]
    simp
  · refine ⟨2, Nat.prime_two, fun h => hT h.symm, ?_⟩
    unfold DV.InertK Host.cls primeClass
    rw [if_pos D.host.two_mem_small]
    simp

theorem nuCommens_of {D : D7} {L : SizeData₂ D} (hNu : DV.NuDef D L) (hT : NuAtT D L) : NuCommens D L := by
  intro u
  have hle := nu_le_mram hNu hT u
  constructor
  · have : Module.Finite (𝓞 D.what₂.LL) (DV.MramL D u) := Module.Finite.iff_fg.2 (D.MramL_fg u)
    have : IsNoetherian (𝓞 D.what₂.LL) (DV.MramL D u) := inferInstance
    have h2 := (IsNoetherian.noetherian ((L.NuLat u).comap (DV.MramL D u).subtype)).map (DV.MramL D u).subtype
    rw [Submodule.map_comap_subtype, inf_eq_right.2 hle] at h2
    exact h2
  · obtain ⟨p, hp, hpT, hin⟩ := exists_free_prime D u
    obtain ⟨w, hw⟩ := place_over' D p hp
    have hEq := hNu.2.1 u w (by rw [hw]; exact hpT) (Or.inr (by rw [hw]; exact hin))
    refine exists_common_mul _ _ (D.MramL_fg u) (fun y hy => ?_)
    obtain ⟨s, hs, hsy⟩ := locLe_zero hEq.2 y hy
    exact ⟨s, fun h0 => hs (by rw [h0]; exact Ideal.zero_mem _), hsy⟩

theorem nuCommensF_of {eps : ℝ} (Fm : FamP eps) (crystallineComparison : ℝ) (h10 : product_first_zeroth_parts.ConclusionOnFamily Fm crystallineComparison) (hS : SettingEventually Fm) :
    NuCommensF Fm := by
  obtain ⟨a0, h10⟩ := h10
  obtain ⟨a1, hS⟩ := hS
  refine ⟨max (max a0 a1) (Fm.x1 + 1), fun x hx i => ?_⟩
  have e0 : a0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have e1 : a1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have e2 : Fm.x1 < x := by have := le_trans (le_max_right (max a0 a1) (Fm.x1 + 1)) hx; linarith
  exact nuCommens_of (Fm.nuDef x e2 i) (nuAtT_of (Fm.ex x e2 i).lat.atT
    (fun u w hw => ((h10 x e0 i u (hS x e1 e2 i u)).2.2.2.2.1 w hw).1))

end Formalism.MainNotions.Lnk

end

end Commens

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory


end Formalism.MainNotions

end
end
