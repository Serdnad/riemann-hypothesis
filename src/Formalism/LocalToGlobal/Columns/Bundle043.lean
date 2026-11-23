module

public import Formalism.LocalToGlobal.Columns.Bundle038
public import Formalism.PeriodIntegrals.TwistedEisensteinNonvanishing
import Formalism.LocalToGlobal.Columns.Bundle033
public import Formalism.LocalToGlobal.Columns.Bundle041
import Formalism.LocalToGlobal.Columns.ChainTwPsi
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle015
public import Formalism.LocalToGlobal.Columns.TiedLv
import Formalism.LocalToGlobal.Columns.CoefColLemmas
import Formalism.LocalToGlobal.Columns.RowFormsAdelic
public import Formalism.LocalToGlobal.Columns.Bundle042
public import Formalism.LocalToGlobal.Columns.Bundle019
public import Formalism.LocalToGlobal.Columns.Bundle017
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

def toTwistedEisensteinRanks (R : Ranks) : PI.TwistedEisensteinNonvanishing.Ranks :=
  { ord := R.ord, k := R.k, m := R.m, t := R.t, k_even := R.k_even, m_even := R.m_even, t_odd := R.t_odd, two_le_m := R.two_le_m,
    m_add_three_le_k := R.m_add_three_le_k, rank_add_five_le := R.rank_add_five_le, three_m_lt_t := R.three_m_lt_t,
    m_le_f := R.m_le_f, f_le_k := R.f_le_k, m_sq_le_N := R.m_sq_le_N }

section Br

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}

theorem doubleCosetDatum_psi_ok (G : ChGlob X R.m) (P : rowSG Pr sel mu)
    (hadd : ∀ x y : X.E, IntAt P.1 ((qOf P.1 : X.E) ^ (2 * R.m) * x) → IntAt P.1 ((qOf P.1 : X.E) ^ (2 * R.m) * y) →
      twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) (x + y) = twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) x * twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) y)
    (hint : ∀ x : X.E, IntAt P.1 x → twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) x = 1) :
    PI.TwistedEisensteinNonvanishing.PsiOk (2 * (toTwistedEisensteinRanks R).m) P.1 (twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m)) := by
  refine ⟨fun x y hx hy => hadd x y hx hy, fun x hx => hint x hx, fun x hx => ?_⟩
  unfold twPsiQ
  rw [dite_eq_right]
  rintro ⟨b, hb, -⟩
  exact hx hb

theorem twistedMultiplier_ne_zero (G : ChGlob X R.m) (i : ℕ) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) : twMuq Ch sel mu G (i + 1) P ≠ 0 := by
  unfold twMuq
  rw [if_neg hP]
  split_ifs
  · exact Units.ne_zero _
  · exact one_ne_zero

theorem squareRoot_norm_ne_zero (P : rowSG Pr sel mu) (hq : (Ideal.absNorm P.1.asIdeal).Prime) (hsq : twSqrt P.1 ^ 2 = (qOf P.1 : X.K)) :
    twSqrt (X := X) P.1 ≠ 0 := by
  intro h0
  rw [h0, zero_pow two_ne_zero] at hsq
  have : (qOf P.1 : X.K) ≠ 0 := by exact_mod_cast hq.ne_zero
  exact this hsq.symm

theorem firstUnfolding_eq_doubleCosetDatum (G : ChGlob X R.m) (i : ℕ) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) (A' B' : ℕ) (hal : AutY X R i) (h : AutY X R (i + 1)) :
    E1at Ch sel mu { twCst Ch sel mu G with A := A', B := B' } i P hal h =
      PI.TwistedEisensteinNonvanishing.TwistedEisensteinCoefficient (toTwistedEisensteinRanks R) P.1 (twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m)) (twSqrt P.1) (twMuq Ch sel mu G (i + 1) P)
        (resChar (mu : Chr X.F X.E X.K) P.1) A' B' i hal h := by
  unfold E1at omPhi muAt PhiAt
  simp only [twCst, if_neg hP]
  rfl

theorem doubleCosetDatum_hypotheses (H : PI.TwistedEisensteinNonvanishing.TwistedEisensteinNonvanishing) (G : ChGlob X R.m) {i : ℕ} (hi : i + 3 ≤ R.m) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (hq : (Ideal.absNorm P.1.asIdeal).Prime) (hu : ((Ideal.absNorm P.1.asIdeal : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal ^ 2)
    (hadd : ∀ x y : X.E, IntAt P.1 ((qOf P.1 : X.E) ^ (2 * R.m) * x) → IntAt P.1 ((qOf P.1 : X.E) ^ (2 * R.m) * y) →
      twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) (x + y) = twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) x * twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) y)
    (hint : ∀ x : X.E, IntAt P.1 x → twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) x = 1) (hsq : twSqrt P.1 ^ 2 = (qOf P.1 : X.K))
    (hal : AutY X R i) (h h' : AutY X R (i + 1)) (hbal : TwBdd (Pr := Pr) i P.1 hal) (hb : TwBdd (Pr := Pr) (i + 1) P.1 h)
    (hb' : TwBdd (Pr := Pr) (i + 1) P.1 h') (hdc : SameDC (Pr := Pr) true (i + 1) P.1 h h')
    (hne : FiniteSumNonzeroLargeDepth Ch sel mu (twCst Ch sel mu G) i P hal h) : FiniteSumNonzeroLargeDepth Ch sel mu (twCst Ch sel mu G) i P hal h' := by
  have hL : ∀ j, lamYat (Pr := Pr) (R := R) j P.1 = LocE.lamY P.1 (qOf P.1) (R.N j) (cOf R j) 0 := fun j => by
    unfold lamYat; rw [if_neg hP]
  have hJ : ∀ j, Jat (Pr := Pr) (R := R) true j P.1 = LocE.JQ P.1 (qOf P.1) (R.k + j) (R.N j) (cOf R j) := fun j => by
    unfold Jat; rw [if_neg hP]
  have bdd : ∀ j (g : AutY X R j), TwBdd (Pr := Pr) j P.1 g → PI.TwistedEisensteinNonvanishing.BddL (toTwistedEisensteinRanks R) P.1 j g := fun j g hg x hx => by
    have := hg x (by rw [hL]; exact hx)
    rw [hL] at this
    exact this
  obtain ⟨A₀, B₀, hAB⟩ := hne
  have := H X.E X.K (toTwistedEisensteinRanks R) P.1 hq hu (twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m)) (twSqrt P.1) (twMuq Ch sel mu G (i + 1) P)
    (resChar (mu : Chr X.F X.E X.K) P.1) (doubleCosetDatum_psi_ok G P hadd hint) (squareRoot_norm_ne_zero P hq hsq) (twistedMultiplier_ne_zero G i P hP) i hi hal h h'
    (bdd i hal hbal) (bdd (i + 1) h hb) (bdd (i + 1) h' hb')
    (by obtain ⟨r, hr, κ, hκ, e⟩ := hdc; exact ⟨r, hr, κ, by rw [hJ] at hκ; exact hκ, e⟩)
    ⟨A₀, B₀, fun A' B' hA hB => by rw [← firstUnfolding_eq_doubleCosetDatum G i P hP]; exact hAB A' B' hA hB⟩
  obtain ⟨A₁, B₁, h1⟩ := this
  exact ⟨A₁, B₁, fun A' B' hA hB => by rw [firstUnfolding_eq_doubleCosetDatum G i P hP]; exact h1 A' B' hA hB⟩

theorem unfoldingNonvanishingDoubleCoset_holds (G : ChGlob X R.m) {m2 : ℕ} (hm : R.m = m2 + 2) (hK : TwCstQ (Pr := Pr) sel mu G) :
    UnfoldingNonvanishingDoubleCoset Ch sel mu (twCst Ch sel mu G) m2 := by
  intro i hi P hP hd hal h h' hbal hb hb' hs hne
  exact doubleCosetDatum_hypotheses _root_.TwistedEisensteinNonvanishing G (by omega) P hP hd.1 hd.2 (hK.psi_add P hP) (hK.psi_int P hP) (hK.sq_sq P hP)
    hal h h' hbal hb hb' hs hne

theorem twIdx_ok_closed (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (h4 : ∀ w ∈ Pr.vGs, qOf w % 4 = 1) (G : ChGlob X R.m)
    {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} (hT : Ch.Tied G.σ₀ e G.mu0 eta) (hW : Ch.WeilTied G.σ₀ G.xi0)
    (hval : ∀ (j : Fin R.m) (w : HeightOneSpectrum (𝓞 X.E)), w ∈ Pr.vGs →
      ∃ y : X.K, G.σ₀ y = ((((G.mu0 j).locK w (ciQU w)) : ℂˣ) : ℂ)⁻¹)
    {m2 : ℕ} (hm : R.m = m2 + 2) (hQG : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs)
    (hd : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1)
    (hz : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs →
      ∃ z : X.K, G.σ₀ z = Complex.exp (2 * Real.pi * Complex.I / ((qOf P.1 ^ (2 * R.m) : ℕ) : ℂ)))
    (hs : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∃ z : X.K, z ^ 2 = (qOf P.1 : X.K))
    (hxi : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → IntAt P.1 G.xi0 ∧ redP P.1 G.xi0 ≠ 0) :
    (twIdx Ch sel mu (twCst Ch sel mu G) m2).Ok Ch sel mu (twCst Ch sel mu G) G m2 := by
  have hK := twCstQ_of hd hz hs hxi
  have hc := twCst_ok hPr hCh h4 hK
  exact twistedIndex_firstUnfolding_ok hX hPr hCh h4 G hT hW hval hm hQG hd hz hs hxi (unfoldingNonvanishingDoubleCoset_holds G hm hK) (characterNonvanishing_holds hm hc)

end Br

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem lastVector_eq_single (n : ℕ) (p : E) : z0 E n p = (Pi.single (lastIdx (n + 1)) p : Fin (n + 1) → E) := by
  have hl : lastIdx (n + 1) = Fin.last n := Fin.ext (by simp [lastIdx])
  rw [hl]
  funext j
  simp [z0, eLast, Pi.single_apply]

theorem xp_tilH_f {N n : ℕ} (hN : N = n + 1) [NeZero N] {ST SG : Finset (Pl E)} (d : DecoSet (E := E) (n := n) (ST := ∅) (SG := SG)) {pi : 𝓞 E}
    (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG, pi ∉ w.1.asIdeal) {b : 𝓞 E} (hb : SepElt ST b) (P : ST)
    (y : Sp E N) (hy : y ∈ (DecoSet.tilH (ST := ST) hN pi d).1.Lsh) (r : 𝓞 E)
    (hr : algebraMap (𝓞 E) E r = hStd E N (Pi.single (lastIdx N) (algebraMap (𝓞 E) E pi)) y) :
    (DecoSet.tilH (ST := ST) hN pi d).1.f P y = Ideal.Quotient.mk P.1.asIdeal r := by
  subst hN
  have hy' : y ∈ (DecoSet.til (ST := ST) pi d).1.Lsh := hy
  have h1 : y ∈ localization₂ P.1.asIdeal (DecoSet.til (ST := ST) pi d).1.N := by
    rw [← (DecoSet.til (ST := ST) pi d).2.locP_Lsh hb P]
    exact le_locP _ _ hy'
  show (DecoSet.til (ST := ST) pi d).1.f P y = _
  rw [DecoSet.til_val d hT hG] at h1 ⊢
  have h2 : (d.1.til (ST := ST) pi).f P y = redP P.1 (hStd E (n + 1) (z0 E n (algebraMap (𝓞 E) E pi)) y) := if_pos h1
  rw [h2, lastVector_eq_single, ← hr, reduction_coe]

theorem xp_til_f_core {N n : ℕ} (hN : N = n + 1) [NeZero N] {ST SG SG' : Finset (Pl E)} (hSG : SG ⊆ SG') {H : Subgroup (GLG (E := E) (n := N) (SG := SG))}
    (d : DecoSet (E := E) (n := n) (ST := ∅) (SG := SG')) {pi : 𝓞 E} (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG', pi ∉ w.1.asIdeal) {b : 𝓞 E}
    (hb : SepElt ST b) (g : UF E N × H) (e : DecoSet (E := E) (n := N) (ST := ST) (SG := SG)) (hge : g • e = (DecoSet.tilH (ST := ST) hN pi d).res hSG) (P : ST)
    (x : Sp E N) (hx : x ∈ e.1.Lsh) (r : 𝓞 E)
    (hr : algebraMap (𝓞 E) E r = hStd E N (Pi.single (lastIdx N) (algebraMap (𝓞 E) E pi)) (g.1.1 x)) :
    e.1.f P x = Ideal.Quotient.mk P.1.asIdeal r := by
  have h1 : e.1.f P x = (g • e).1.f P (g.1.1 x) := by
    show _ = e.1.f P (g.1.1.symm (g.1.1 x))
    rw [LinearEquiv.symm_apply_apply]
  have h2 : g.1.1 x ∈ (g • e).1.Lsh := by
    rw [rlc_smul_val, Deco.Lsh_act _ g.1.2]
    exact Submodule.mem_map_of_mem hx
  rw [h1]
  rw [hge] at h2 ⊢
  exact xp_tilH_f hN d hT hG hb P _ h2 r hr

end Gen

section GenJ

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem xp_hform_one (hc : CMData F E) {N : ℕ} (x y : Fin N → E) :
    hform (hc.sig : E →+* E) (1 : Matrix (Fin N) (Fin N) E) x y = hStd E N x y := by
  unfold hform
  rw [hStd_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, mul_one]
    rfl
  · intro j _ hj
    simp only [Matrix.one_apply_ne' hj, mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem xp_til_f_coreJ (hc : CMData F E) {N n : ℕ} (hN : N = n + 1) [NeZero N] {ST SG SG' : Finset (Pl E)} (hSG : SG ⊆ SG')
    {H : Subgroup (GLG (E := E) (n := N) (SG := SG))} (d : DecoSet (E := E) (n := n) (ST := ∅) (SG := SG')) {pi : 𝓞 E} (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal)
    (hG : ∀ w : SG', pi ∉ w.1.asIdeal) {b : 𝓞 E} (hb : SepElt ST b) (g : UF E N × H) (e : DecoSet (E := E) (n := N) (ST := ST) (SG := SG))
    (hge : g • e = (DecoSet.tilH (ST := ST) hN pi d).res hSG) (P : ST) (x : Sp E N) (hx : x ∈ e.1.Lsh) (r : 𝓞 E)
    {J : Matrix (Fin N) (Fin N) E} (hJ : J = 1)
    (hr : algebraMap (𝓞 E) E r = hform (hc.sig : E →+* E) J (Pi.single (lastIdx N) (algebraMap (𝓞 E) E pi))
      ((((ratEquiv hc N).symm g.1 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x)) :
    e.1.f P x = Ideal.Quotient.mk P.1.asIdeal r := by
  subst hJ
  refine xp_til_f_core hN hSG d hT hG hb g e hge P x hx r ?_
  rw [hr, xp_hform_one, ← rlc_ratHom_apply hc N]
  have : ratHom hc N ((ratEquiv hc N).symm g.1) = g.1 := (ratEquiv hc N).apply_symm_apply g.1
  rw [this]

end GenJ

section GenQ

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)

section Step

variable (c₀ : DiaG (E := X.E) (ST := Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := Pr.vGs))
  (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
  (Q : StepCrd Pr σ₀ n fun c => (s c).1.L)

theorem xp_clsG_U : (clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).lev.U = levU hc n (Pr.vT u) Pr.vGs Λ.grp := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  rfl

theorem xp_clsG_y (c : DecoCl n (Pr.vT u) Pr.vGs Λ.grp) :
    ((clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).y c).1 = (ptOfD hc n (Pr.vT u) Pr.vGs c₀ (s c)).1 := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  rfl

end Step

section P

variable (s : DecoCl n (∅ : Finset (Pl X.E)) Pr.vGs Λ.grp → DecoSet (E := X.E) (n := n) (ST := (∅ : Finset (Pl X.E))) (SG := Pr.vGs))
  (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c)
  (Q : StepCrd Pr σ₀ n fun c => (s c).1.N)

theorem xp_clsPG_y (c : DecoCl n (∅ : Finset (Pl X.E)) Pr.vGs Λ.grp) :
    ((clsPG hc σ₀ Λ s hS hs Q).y c).1 = (ptOfD hc n ∅ Pr.vGs 1 (s c)).1 := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  rfl

end P

end GenQ

section Rec

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d)

abbrev ColDat.tilC (d : ColDat) (u : d.what₂.Word) (c : PCl d) : StCl (Pr := d.Pr) d.W d.lev u d.R.m :=
  tilCl (Pr := d.Pr) d.W d.lev (Finset.Subset.refl _) d.levP u c


include hS hH in

theorem xp_Ld_eq (u : d.what₂.Word) (c : StCl (Pr := d.Pr) d.W d.lev u d.R.m) :
    CF.Ld (d.colRec a) u d.R.m le_rfl c = (d.repr u d.R.m c).1.Lsh :=
  tie_Ld_eq (X := d.X) (Pr := d.Pr) d.sp.cm d.σ₀ u (d.repr u d.R.m) (stepCrd a hS hH u d.R.m le_rfl) c

variable (hP : PtSurjP d)



def tildeLatticeAgreement (u : d.what₂.Word) :
    CF.TilTied (D := d.colRec a) u (atTTied a hH u) (parabolicClassAgreement a hS hH hP u) (levelAgreement a hS hH u d.R.m le_rfl) where
  z0 := d.z0 u
  lastCoordinateUniformizerVector_spans_orthogonal_line := lastCoordinateUniformizerVector_spans_orthogonal_line a hS u
  hermitianForm_lastCoordinateUniformizerVector_self := hermitianForm_lastCoordinateUniformizerVector_self a hS u
  ga := tieGa a hS u
  til_lat := til_lat a hS u
  til_fv := fun v c x r hr =>
    (tie_fv d.sp.cm d.hPr d.σ₀ u (d.repr u d.R.m) (stepCrd a hS hH u d.R.m le_rfl) v (d.tilC u c) x).trans
      (xp_til_f_coreJ d.sp.cm (N_m_succ d.R) (Finset.Subset.refl _) (d.reprP c) (fun P => conj_piT_notMem d.hPr u P)
        (a.piT_off u) (sepElt_of_ok d.hPr u) (d.tilMv u c) _ (tilMv_smul u c) v x.1 ((xp_Ld_eq a hS hH u (d.tilC u c)).le x.2) r
        (gramN_eq a hS d.R.m le_rfl) hr)

def TilMove (u : d.what₂.Word) : Prop :=
  ∀ c : PCl d, ∃ κ : levU d.sp.cm (d.R.N d.R.m) (d.Pr.vT u) d.Pr.vGs (d.lev d.R.m).grp,
    levRed d.sp.cm (d.R.N d.R.m) (d.Pr.vT u) d.Pr.vGs (d.lev d.R.m).grp κ = (d.tilMv u c).2 ∧
    ∀ g : GL (Fin (d.R.N d.R.m)) (d.host.E ⊗[d.host.F] FiniteAdeleRing (𝓞 d.host.F) d.host.F),
      CF.IsExt (d.colRec a) (d.z0 u) (inclE (F := d.host.F) (FiniteAdeleRing (𝓞 d.host.F) d.host.F))
        (ptOfD d.sp.cm (d.R.N d.R.m - 1) ∅ d.Pr.vGs 1 (d.reprP c)).1.1 g.1 →
      bc (inclE (F := d.host.F) (FiniteAdeleRing (𝓞 d.host.F) d.host.F)) (d.tilGa u c).1 *
        (ptOfD d.sp.cm (d.R.N d.R.m) (d.Pr.vT u) d.Pr.vGs (colDia (X := d.X) (Pr := d.Pr) d.R u d.R.m)
          (d.repr u d.R.m (d.tilC u c))).1 = g * κ.1

variable (hQ : PtSurj d)

def tilAd (u : d.what₂.Word) (hM : TilMove a u) :
    CF.TilAd (tildeLatticeAgreement a hS hH hP u) (classAgreement a hS hH hQ u d.R.m le_rfl) where
  ka := fun c => ⟨(hM c).choose.1, (Subgroup.ext_iff.1 (xp_clsG_U d.sp.cm d.hX d.hPr d.σ₀ u (d.lev d.R.m)
    (colDia (X := d.X) (Pr := d.Pr) d.R u d.R.m) (d.repr u d.R.m) (hQ u d.R.m)
    (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u d.R.m).outSec.spec c) (stepCrd a hS hH u d.R.m le_rfl)) _).2 (hM c).choose.2⟩
  til_ad := fun c g hg => by
    have h1 := xp_clsPG_y d.sp.cm d.σ₀ d.levP.inv d.reprP hP (fun c => (ptGSD (Pr := d.Pr) d.W d.levP).outSec.spec c)
      (crdPr a hS hH) c
    have h2 := xp_clsG_y d.sp.cm d.hX d.hPr d.σ₀ u (d.lev d.R.m) (colDia (X := d.X) (Pr := d.Pr) d.R u d.R.m) (d.repr u d.R.m)
      (hQ u d.R.m) (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u d.R.m).outSec.spec c) (stepCrd a hS hH u d.R.m le_rfl) (d.tilC u c)
    have hg' : CF.IsExt (d.colRec a) (d.z0 u) (inclE (F := d.host.F) (FiniteAdeleRing (𝓞 d.host.F) d.host.F))
        (ptOfD d.sp.cm (d.R.N d.R.m - 1) ∅ d.Pr.vGs 1 (d.reprP c)).1.1 g.1 := by
      rw [← h1]; exact hg
    have h3 := (hM c).choose_spec.2 g hg'
    exact (congrArg (fun t => bc (inclE (F := d.host.F) (FiniteAdeleRing (𝓞 d.host.F) d.host.F)) (d.tilGa u c).1 * t) h2).trans h3

end Rec

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {d : ColDat} (a : ColArgs d)

theorem th_gram_eq (hS : SpStd d.toColBase) (i : ℕ) (hi : i ≤ d.R.m) : (d.sp.X i).gram = 1 := by
  refine Matrix.ext fun x y => ?_
  show (d.sp.X i).hT ((d.sp.X i).frame x) ((d.sp.X i).frame y) = _
  rw [hS.X_on i hi, Matrix.one_apply]

theorem th_gram0_eq (hS : SpStd d.toColBase) : d.sp.gram0 = 1 := by
  refine Matrix.ext fun x y => ?_
  show (d.sp.X 0).hT ((d.sp.X 0).frame _) ((d.sp.X 0).frame _) = _
  rw [hS.X_on 0 (Nat.zero_le _), Matrix.one_apply]
  simp only [EmbeddingLike.apply_eq_iff_eq]

theorem th_crdLat_eq (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) (c : StCl (Pr := d.Pr) d.W d.lev u i) :
    Formalism.L2.Herm.crdLat (d.sp.X i) (d.clsLat u i c) = Formalism.L2.Forms.reL (d.sp.X_rank i hi).symm (d.repr u i c).1.L := by
  unfold Formalism.L2.Herm.crdLat ColDat.clsLat Formalism.L2.Forms.reL
  rw [dite_eq_left hi, ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  funext j
  show (d.sp.X i).frame.equivFun ((d.crd i hi).symm x) j = _
  unfold ColDat.crd
  rw [LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

theorem th_crdLat0_eq (u : d.what₂.Word) (c : StCl (Pr := d.Pr) d.W d.lev u 0) :
    d.sp.crdLat0 (d.clsLat u 0 c) = Formalism.L2.Forms.reL (Formalism.L2.Forms.rank_eq_first_level d.R).symm (d.repr u 0 c).1.L := by
  unfold Spaces.crdLat0 ColDat.clsLat Formalism.L2.Forms.reL
  rw [dite_eq_left (Nat.zero_le _), ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  funext j
  show d.sp.crd0 ((d.crd 0 (Nat.zero_le _)).symm x) j = _
  unfold ColDat.crd Spaces.crd0
  rw [LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

def hCrd (hS : SpStd d.toColBase) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) :
    HCrd d.Pr (d.R.N i) fun c : StCl (Pr := d.Pr) d.W d.lev u i => (d.repr u i c).1.L where
  n' := (d.sp.X i).rank
  hn := d.sp.X_rank i hi
  J := (d.sp.X i).gram
  hJ := th_gram_eq hS i hi
  f := d.R.f
  hf := d.f_eq.symm
  bad := plUnder d.X.F d.Pr.vGs
  hbad := rfl
  lat := fun c => Formalism.L2.Herm.crdLat (d.sp.X i) (d.clsLat u i c)
  hlat := fun c => th_crdLat_eq u i hi c

def hCrd0 (hS : SpStd d.toColBase) (u : d.what₂.Word) :
    HCrd d.Pr (d.R.N 0) fun c : StCl (Pr := d.Pr) d.W d.lev u 0 => (d.repr u 0 c).1.L where
  n' := d.R.k
  hn := Formalism.L2.Forms.rank_eq_first_level d.R
  J := d.sp.gram0
  hJ := th_gram0_eq hS
  f := d.R.f
  hf := d.f_eq.symm
  bad := plUnder d.X.F d.Pr.vGs
  hbad := rfl
  lat := fun c => d.sp.crdLat0 (d.clsLat u 0 c)
  hlat := fun c => th_crdLat0_eq u c

def LocalLevelIsKOneEverywhere (d : ColDat) : Prop := ∀ (u : d.what₂.Word) (i : ℕ), LocalLevelIsKOneAtT d.sp.cm u (d.lev i)

def IwAll (d : ColDat) (S : GSplit (Pr := d.Pr) d.sp.cm) : Prop := ∀ u : d.what₂.Word, IwLoc d.sp.cm u (d.lev 0) S.sp

def hermPack (hS : SpStd d.toColBase) (hP : PtSurj d) (hK : LocalLevelIsKOneEverywhere d) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) :=
  levPack d.sp.cm d.hX d.hPr d.σ₀ u (d.lev i) (colDia (X := d.X) (Pr := d.Pr) d.R u i) (d.repr u i) (hP u i)
    (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.spec c) (hK u i) (hCrd hS u i hi)

def hermPack0 (hS : SpStd d.toColBase) (hP : PtSurj d) (hK : LocalLevelIsKOneEverywhere d) (u : d.what₂.Word) :=
  levPack d.sp.cm d.hX d.hPr d.σ₀ u (d.lev 0) (colDia (X := d.X) (Pr := d.Pr) d.R u 0) (d.repr u 0) (hP u 0)
    (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u 0).outSec.spec c) (hK u 0) (hCrd0 hS u)

def hermLev0 (hS : SpStd d.toColBase) (hP : PtSurj d) (hK : LocalLevelIsKOneEverywhere d) (S : GSplit (Pr := d.Pr) d.sp.cm) (hI : IwAll d S)
    (u : d.what₂.Word) :
    ColLevel d.R d.host.F d.host.E d.sp d.host.g (d.chain a u) (d.atT a u) (fun i c => d.clsLat u i c) :=
  LevPack.toCol (sp := d.sp) (C := d.chain a u) (A := d.atT a u) (clsLat := fun i c => d.clsLat u i c)
    (hermPack0 hS hP hK u) S.sp S.sp_sig
    (levPack_iw d.sp.cm d.hX d.hPr d.σ₀ u (d.lev 0) S.sp _ _ _ _ _ (hI u) (hCrd0 hS u))
    (exists_place_over_first_prime d.hX d.hPr).choose (exists_place_over_first_prime d.hX d.hPr).choose_spec

def hermCols (hS : SpStd d.toColBase) (hP : PtSurj d) (hK : LocalLevelIsKOneEverywhere d) (S : GSplit (Pr := d.Pr) d.sp.cm) (hI : IwAll d S) :
    CH.HermCols (d.colRec a) where
  lev0 := fun u => hermLev0 a hS hP hK S hI u
  lev := fun u i _ hm => LevPack.toStep (S := d.sp.X i) (lat := d.clsLat u i) (hermPack hS hP hK u i hm)
  cls := fun u i _ hm => LevPack.toCls (S := d.sp.X i) (lat := d.clsLat u i) (hermPack hS hP hK u i hm)
  vT := fun u => tieEV d.sp.cm d.hX d.hPr u
  Fv := fun u v => tieFv d.sp.cm d.hX d.hPr u v

end Formalism.L2.Col
end
end
