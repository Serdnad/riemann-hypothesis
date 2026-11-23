module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle172
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle307
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle133
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle138
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle158
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle191
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle173
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle283
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle308
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle117
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle116
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle140
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle310
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle233
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle216
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle309
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
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

noncomputable section

namespace GlobalTheory.KZ.H3.KumPot

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem cast_of_dvd {d M : ℕ} (h : d ∣ M) {x y : ℤ} (hxy : (x : ZMod M) = y) : (x : ZMod d) = y :=
  (ZMod.intCast_eq_intCast_iff _ _ _).2
    (Int.ModEq.of_dvd (Int.natCast_dvd_natCast.2 h) ((ZMod.intCast_eq_intCast_iff _ _ _).1 hxy))

theorem gamma_le {d M : ℕ} (h : d ∣ M) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma d := by
  intro γ hγ
  obtain ⟨a, b, c, e⟩ := CongruenceSubgroup.Gamma_mem.1 hγ
  refine CongruenceSubgroup.Gamma_mem.2 ⟨?_, ?_, ?_, ?_⟩
  · simpa using cast_of_dvd h (x := γ 0 0) (y := 1) (by simpa using a)
  · simpa using cast_of_dvd h (x := γ 0 1) (y := 0) (by simpa using b)
  · simpa using cast_of_dvd h (x := γ 1 0) (y := 0) (by simpa using c)
  · simpa using cast_of_dvd h (x := γ 1 1) (y := 1) (by simpa using e)

theorem gamma_le_gam {N l M : ℕ} (hN : N ∣ M) (hl : l ∣ M) : CongruenceSubgroup.Gamma M ≤ Gam N l := by
  intro γ hγ
  obtain ⟨a, -, c, e⟩ := CongruenceSubgroup.Gamma_mem.1 (gamma_le hN hγ)
  obtain ⟨-, -, c', -⟩ := CongruenceSubgroup.Gamma_mem.1 (gamma_le hl hγ)
  exact ⟨(CongruenceSubgroup.Gamma1_mem N γ).2 ⟨a, e, c⟩, CongruenceSubgroup.Gamma0_mem.2 c'⟩

theorem polySlash_eq_self_of_mem_Gamma (l n : ℕ) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma (l ^ n))
    (p : MvPolynomial (Fin 2) (ZMod (l ^ n))) : slP (δ : Matrix (Fin 2) (Fin 2) ℤ) p = p := by
  obtain ⟨a, b, c, e⟩ := CongruenceSubgroup.Gamma_mem.1 hδ
  rw [GlobalTheory.KZ.SlPLaws.polySlash_congr _ 1 p, GlobalTheory.KZ.SlPLaws.polySlash_one']
  intro i j
  fin_cases i <;> fin_cases j <;> simp [a, b, c, e]

theorem toZModPow_eval (l : ℕ) [Fact l.Prime] (n : ℕ) (u : Fin 2 → ℤ_[l]) (p : MvPolynomial (Fin 2) ℤ_[l]) :
    PadicInt.toZModPow n (MvPolynomial.eval u p) =
      MvPolynomial.eval (fun i => PadicInt.toZModPow n (u i)) (MvPolynomial.map (PadicInt.toZModPow n) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem kum_sum (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) {ι : Type} (s : Finset ι) (x : ι → X.Khat l)
    (χ : ι → SL(2, ℤ) → ZMod (l ^ n)) (h : ∀ i ∈ s, Kum X l n (x i) (χ i)) :
    Kum X l n (∑ i ∈ s, x i) (∑ i ∈ s, χ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n).2.1
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n).1 _ _ _ _ (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end GlobalTheory.KZ.H3.KumPot

namespace GlobalTheory.KZ.H3.KumPot

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem bset_rel (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] [IsAlgClosed Ω] (hJ : JHol X) (N w : ℕ) (hN : 4 ≤ N)
    (hl2 : l ≠ 2) (hlN : ¬ l ∣ N) (hw : Odd w) (b : X.Fn l) (hb : b ∈ X.BSet N l w) :
    ∃ F ∈ Pot ℤ_[l] w (Gam N l), Rel X l b F := by
  obtain ⟨⟨c, hcA, hbc⟩, hinv⟩ := hb
  have hcoef := fun γ hγ i => GlobalTheory.T.binaryForm_coeff_of_gamma1CapGamma0_invariant Ω ε X l N w b c hbc γ hγ (hinv γ hγ) i
  obtain ⟨Φ, hΦ, hK⟩ := GlobalTheory.T.kummerCharacters_invariant_compatible_family Ω ε X l hJ N w c hcA hcoef
  obtain ⟨z, hz, hzΦ⟩ := GlobalTheory.T.exists_padic_cocycle_of_compatible_poly_family N l w (by omega) hl2 hlN hw Φ hΦ
  obtain ⟨F, hF, hFz⟩ := GlobalTheory.T.exists_eichlerShimuraPotential_of_homogeneousPolyCocycle ℤ_[l] w N l hN z hz
  refine ⟨F, hF, fun u n => ⟨fun δ => MvPolynomial.eval (fun i => PadicInt.toZModPow n (u i)) (Φ n δ), ?_, ?_⟩⟩
  · have hsum := kum_sum X l n (Finset.univ : Finset (Fin (w + 1))) (fun (i : Fin (w + 1)) => (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i)
      (fun (i : Fin (w + 1)) δ => PadicInt.toZModPow n (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) *
        AddMonoidAlgebra.coeff (Φ n δ) (Finsupp.single 0 (i : ℕ) + Finsupp.single 1 (w - (i : ℕ))))
      (fun i _ => GlobalTheory.T.isKummerCharacterAtLevel_padicInt_smul Ω ε X l n _ _ _ (hK n i))
    rw [← hbc u] at hsum
    convert hsum using 1
    funext δ
    rw [Finset.sum_apply]
    have MX := GlobalTheory.T.binaryMonomialDegree_subst_expansion (ZMod (l ^ n)) w
    conv_lhs => rw [MX.2.1 (Φ n δ) (hΦ.1 n δ)]

    simp only [map_sum, map_mul, MvPolynomial.eval_C, MX.2.2.2.1, map_pow]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · obtain ⟨M1, hM1, hM1'⟩ := hzΦ n
    have hl : 0 < l := (Fact.out : l.Prime).pos
    refine ⟨N * l ^ (n + 1) * M1, by positivity, fun δ hδ τ hτ => ?_⟩
    have hδG : δ ∈ Gam N l := gamma_le_gam (l := l) ⟨l ^ (n + 1) * M1, by ring⟩
      ⟨N * l ^ n * M1, by ring⟩ hδ
    have hδn : δ ∈ CongruenceSubgroup.Gamma (l ^ n) := gamma_le ⟨N * l * M1, by ring⟩ hδ
    have hδ1 : δ ∈ CongruenceSubgroup.Gamma M1 := gamma_le ⟨N * l ^ (n + 1), by ring⟩ hδ
    have e1 := hFz δ hδG τ hτ
    have e2 : MvPolynomial.map (PadicInt.toZModPow n) (z δ) = Φ n δ := hM1' δ hδ1
    have e3 : MvPolynomial.map (PadicInt.toZModPow n) (F (mob (ofSL δ) τ)) =
        MvPolynomial.map (PadicInt.toZModPow n) (slP (δ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL δ) τ))) := by
      rw [GlobalTheory.KZ.SlPLaws.map_slP, polySlash_eq_self_of_mem_Gamma l n hδn]
    rw [map_sub, toZModPow_eval, toZModPow_eval, e3, ← map_sub, ← map_sub, e1, e2]

end GlobalTheory.KZ.H3.KumPot

theorem GlobalTheory.KZ.H3.exists_pot_rel : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ)
    [Fact l.Prime], [IsAlgClosed Ω] → JHol X → ∀ (N w : ℕ), 4 ≤ N → l ≠ 2 → ¬ l ∣ N → Odd w →
    ∀ b ∈ X.B N l w, ∃ F ∈ Pot ℤ_[l] w (Gam N l), Rel X l b F := by
  intro Ω _ _ ε X l _ _ hJ N w hN hl2 hlN hw b hb
  have RO := GlobalTheory.T.kummerPotentialRelation_linear_hecke_stable Ω ε X l
  have PL := GlobalTheory.T.eichlerShimuraPotential_submodule_and_base_change ℤ_[l] w (Gam N l)
  induction hb using Submodule.span_induction with
  | mem b hb => exact KumPot.bset_rel X l hJ N w hN hl2 hlN hw b hb
  | zero => exact ⟨0, PL.2.1, RO.2.1⟩
  | add b b' _ _ ih ih' =>
    obtain ⟨F, hF, hR⟩ := ih
    obtain ⟨F', hF', hR'⟩ := ih'
    exact ⟨F + F', PL.1 _ _ hF hF', RO.1 _ _ _ _ hR hR'⟩
  | smul a b _ ih =>
    obtain ⟨F, hF, hR⟩ := ih
    exact ⟨a • F, PL.2.2.1 a F hF, RO.2.2.1 a b F hR⟩
end
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.DlEx

variable {Ω : Type} [Field Ω]

def Sp (L : ℕ) (x : HahnSeries ℚ Ω) : Prop := ∀ r : ℚ, x.coeff r ≠ 0 → (r * L).den = 1

lemma den_add {a b : ℚ} (ha : a.den = 1) (hb : b.den = 1) : (a + b).den = 1 := by
  rw [Rat.den_eq_one_iff] at ha hb
  rw [← ha, ← hb, ← Int.cast_add]; simp

lemma exists_of_coeff_mul_ne {x y : HahnSeries ℚ Ω} {r : ℚ} (h : (x * y).coeff r ≠ 0) :
    ∃ r₁ r₂, r₁ + r₂ = r ∧ x.coeff r₁ ≠ 0 ∧ y.coeff r₂ ≠ 0 := by
  rw [HahnSeries.coeff_mul] at h
  obtain ⟨ij, hij, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [Finset.mem_antidiagonal] at hij
  exact ⟨ij.1, ij.2, hij.2.2, left_ne_zero_of_mul hne, right_ne_zero_of_mul hne⟩

lemma sp_mul {L : ℕ} {x y : HahnSeries ℚ Ω} (hx : Sp L x) (hy : Sp L y) : Sp L (x * y) := by
  intro r hr
  obtain ⟨r₁, r₂, rfl, h1, h2⟩ := exists_of_coeff_mul_ne hr
  rw [add_mul]; exact den_add (hx _ h1) (hy _ h2)

lemma sp_sub {L : ℕ} {x y : HahnSeries ℚ Ω} (hx : Sp L x) (hy : Sp L y) : Sp L (x - y) := by
  intro r hr
  rw [HahnSeries.coeff_sub] at hr
  by_cases h : x.coeff r = 0
  · exact hy r (by intro h'; apply hr; rw [h, h', sub_zero])
  · exact hx r h

variable [Algebra ℚ Ω]

lemma sp_theta {L : ℕ} (s : ℚ) {x : HahnSeries ℚ Ω} (hx : Sp L x) : Sp L (theta s x) := by
  intro r hr
  exact hx r (fun h => hr (by simp [theta, h]))

lemma intA_mul (A : ValuationSubring Ω) {x y : HahnSeries ℚ Ω} (hx : ∀ r, x.coeff r ∈ A)
    (hy : ∀ r, y.coeff r ∈ A) (r : ℚ) : (x * y).coeff r ∈ A := by
  rw [HahnSeries.coeff_mul]
  exact Subring.sum_mem A.toSubring (fun ij _ => mul_mem (hx _) (hy _))

lemma intA_sub (A : ValuationSubring Ω) {x y : HahnSeries ℚ Ω} (hx : ∀ r, x.coeff r ∈ A)
    (hy : ∀ r, y.coeff r ∈ A) (r : ℚ) : (x - y).coeff r ∈ A := by
  rw [HahnSeries.coeff_sub]; exact sub_mem (hx r) (hy r)

lemma intA_theta (A : ValuationSubring Ω) {L : ℕ} {x : HahnSeries ℚ Ω} (hx : ∀ r, x.coeff r ∈ A)
    (hs : Sp L x) (r : ℚ) : (theta (L : ℚ) x).coeff r ∈ A := by
  show algebraMap ℚ Ω ((L : ℚ) * r) * x.coeff r ∈ A
  by_cases h : x.coeff r = 0
  · rw [h, mul_zero]; exact zero_mem A
  · have hd := hs r h
    rw [Rat.den_eq_one_iff] at hd
    rw [mul_comm (L : ℚ) r, ← hd, map_intCast]
    exact mul_mem (intCast_mem A _) (hx r)

end GlobalTheory.DlEx


open GlobalTheory.DlEx in
theorem GlobalTheory.dl_exists : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n L : ℕ) (f : X.K), 0 < L → f ≠ 0 → f ∈ KT X L → ∃ φ : HahnSeries ℚ Ω, IsDl X A l n L f φ ∧ ∀ r : ℚ, φ.coeff r ≠ 0 → (r * L).den = 1 := by
  intro Ω _ _ _ ε X hj l _ A hl n L f hL hf hfK
  obtain ⟨a, b, κ, S, hκ, hfb, ha, hb, hbinv, -⟩ := GlobalTheory.T.exists_primitive_expansion_quotient_level_one ε X hj l A hl f hf
  have hbK : b ∈ KT X L := (RingHom.mem_eqLocusField).2 (hbinv _)
  have hcK : algebraMap Ω X.K κ ∈ KT X L := (RingHom.mem_eqLocusField).2 ((X.sl _).commutes κ)
  have haK : a ∈ KT X L := by
    have e : a = (algebraMap Ω X.K κ)⁻¹ * (f * b) := by
      rw [hfb, ← mul_assoc, inv_mul_cancel₀ ((map_ne_zero _).2 hκ), one_mul]
    rw [e]; exact (KT X L).mul_mem ((KT X L).inv_mem hcK) ((KT X L).mul_mem hfK hbK)
  have hsa : Sp L (X.exp a) := (GlobalTheory.T.mem_translationInvariantSubfield_iff_exponents ε X L hL a).1 haK
  have hsb : Sp L (X.exp b) := (GlobalTheory.T.mem_translationInvariantSubfield_iff_exponents ε X L hL b).1 hbK
  have hP : Prim A (X.exp a * X.exp b) := GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss A _ _ ha hb
  obtain ⟨Q, hQA, hQs, hQP⟩ := GlobalTheory.T.primitive_hahnSeries_invertible_mod_prime_pow l A hl n L (X.exp a * X.exp b) hL hP (sp_mul hsa hsb)
  have hDA : ∀ r, (theta (L:ℚ) (X.exp a) * X.exp b - X.exp a * theta (L:ℚ) (X.exp b)).coeff r ∈ A :=
    intA_sub A (intA_mul A (intA_theta A ha.1 hsa) hb.1) (intA_mul A ha.1 (intA_theta A hb.1 hsb))
  have hDs : Sp L (theta (L:ℚ) (X.exp a) * X.exp b - X.exp a * theta (L:ℚ) (X.exp b)) :=
    sp_sub (sp_mul (sp_theta _ hsa) hsb) (sp_mul hsa (sp_theta _ hsb))
  refine ⟨Q * (theta (L:ℚ) (X.exp a) * X.exp b - X.exp a * theta (L:ℚ) (X.exp b)),
    ⟨intA_mul A hQA hDA, a, b, κ, hκ, hfb, ha, hb, ?_⟩, sp_mul hQs hDs⟩
  intro r
  generalize theta (L:ℚ) (X.exp a) * X.exp b - X.exp a * theta (L:ℚ) (X.exp b) = D at hDA ⊢
  choose z hzA hz using hQP
  have e : (Q * D * X.exp a * X.exp b).coeff r - D.coeff r = (D * (Q * (X.exp a * X.exp b) - 1)).coeff r := by
    rw [show Q * D * X.exp a * X.exp b = D * (Q * (X.exp a * X.exp b)) by ring, mul_sub, mul_one,
      HahnSeries.coeff_sub]
  refine ⟨∑ ij ∈ Finset.addAntidiagonal D.isPWO_support (Q * (X.exp a * X.exp b) - 1).isPWO_support r,
    D.coeff ij.1 * z ij.2, Subring.sum_mem A.toSubring (fun ij _ => mul_mem (hDA _) (hzA _)), ?_⟩
  rw [e, HahnSeries.coeff_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ij _ => ?_)
  rw [HahnSeries.coeff_sub, hz ij.2]; ring
end

section

noncomputable section

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

namespace GlobalTheory.LFun.HeckeScalar

open GlobalTheory.LFun.SatCompare GlobalTheory.LocGL

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ G V} {K : Subgroup G}

theorem heckeVec_dosetInd_eq_idem (hπ : GlobalTheory.LGrp.IsIrrSmooth π) (hc : IsCompact (K : Set G)) (hK : IsCommensurated K)
    (g : G) {z : V} (hz : z ∈ fixed π K) :
    ∃ N : ℂ, N ≠ 0 ∧ heckeVec π K (dosetInd ℂ K g) z = N • idem hπ.1 hc (π g z) := by
  classical
  have hm := Final.DosetIndMem G K ℂ g
  have hfin := Formalism.UG.P.finite_support_cosets hK hm.2
  have hS : ∀ c : G ⧸ K, c ∈ hfin.toFinset ↔ c.out ∈ DoubleCoset.doubleCoset g (K : Set G) K := fun c => by
    simp [dosetInd]
  refine ⟨hfin.toFinset.card, ?_, ?_⟩
  · refine Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨(g : G ⧸ K), (hS _).2 ?_⟩)
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    exact DoubleCoset.mem_doubleCoset.2 ⟨1, K.one_mem, k, k.2, by rw [hk, one_mul]⟩

  · rw [← idem_of_mem hπ.1 hc (heckeVec_mem_fixed hK hm hz), heckeVec,
    finsum_eq_sum_of_support_subset (s := hfin.toFinset), map_sum, Nat.cast_smul_eq_nsmul, ← Finset.sum_const]
    · refine Finset.sum_congr rfl fun c hcS => ?_
      have h1 := (hS c).1 hcS
      obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.1 h1
      rw [dosetInd, Set.indicator_of_mem h1, e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        GlobalTheory.LGrp.mem_fixed.1 hz b hb]
      simpa using idem_apply_mem hπ.1 hc ha (π g z)
    · intro c hc'
      refine Finset.mem_coe.2 ((hS c).2 ?_)
      by_contra h0
      exact hc' (by simp [dosetInd, h0])

theorem exists_scalar : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ G V) (K : Subgroup G), IsCompact (K : Set G) → IsCommensurated K →
    (∀ f₁ ∈ Hecke ℂ K, ∀ f₂ ∈ Hecke ℂ K, conv K f₁ f₂ = conv K f₂ f₁) → GlobalTheory.LGrp.IsIrrSmooth π →
    FiniteDimensional ℂ (fixed π K) → ∀ h ∈ Hecke ℂ K, ∃ c : ℂ, ∀ x ∈ fixed π K, heckeVec π K h x = c • x := by
  intro G V _ _ _ _ _ π K hc hK hcomm hπ hfd h hh
  by_cases hb : fixed π K = ⊥
  · refine ⟨0, fun x hx => ?_⟩
    have := heckeVec_mem_fixed hK hh hx
    rw [hb] at this
    simpa using this
  haveI : Nontrivial (fixed π K) := Submodule.nontrivial_iff_ne_bot.2 hb
  let A : Module.End ℂ (fixed π K) := (heckeLin hK hh π).restrict fun x hx => heckeVec_mem_fixed hK hh hx
  obtain ⟨c, hcA⟩ := Module.End.exists_eigenvalue A
  obtain ⟨⟨x₀, hx₀⟩, hv⟩ := hcA.exists_hasEigenvector
  have h0 : x₀ ≠ 0 := fun e => hv.2 (Subtype.ext e)
  have he : heckeVec π K h x₀ = c • x₀ := congrArg Subtype.val hv.apply_eq_smul
  have key : ∀ g, heckeLin hK hh π (idem hπ.1 hc (π g x₀)) = c • idem hπ.1 hc (π g x₀) := fun g => by
    obtain ⟨N, hN, e⟩ := heckeVec_dosetInd_eq_idem hπ hc hK g hx₀
    have hm := Final.DosetIndMem G K ℂ g
    refine smul_right_injective V hN ?_
    show N • _ = N • _
    rw [← map_smul, smul_comm N c, ← e, heckeLin_apply, ← heckeVec_conv hK hh hm hx₀, hcomm _ hh _ hm,
      heckeVec_conv hK hm hh hx₀, he, heckeVec_smul hK hm]
  refine ⟨c, fun x hx => ?_⟩
  have all : ∀ w : MonoidAlgebra ℂ G, heckeLin hK hh π (idem hπ.1 hc (orbitMap π x₀ w)) =
      c • idem hπ.1 hc (orbitMap π x₀ w) := fun w => by
    induction w using MonoidAlgebra.induction_on with
    | of g =>
      have : orbitMap π x₀ (MonoidAlgebra.of ℂ G g) = π g x₀ := by
        show π.asAlgebraHom (MonoidAlgebra.of ℂ G g) x₀ = _
        simp
      rw [this]; exact key g
    | add a b ha hb =>
      have : orbitMap π x₀ (a + b) = orbitMap π x₀ a + orbitMap π x₀ b := map_add _ _ _
      rw [this, map_add (f := _), map_add (f := _), ha, hb, smul_add]
    | smul r a ha =>
      have : orbitMap π x₀ (r • a) = r • orbitMap π x₀ a := map_smul _ _ _
      rw [this, map_smul, map_smul, ha, smul_comm]
  obtain ⟨w, rfl⟩ := orbitMap_surjective hπ.2 h0 x
  have := all w
  rwa [idem_of_mem hπ.1 hc hx] at this

end GlobalTheory.LFun.HeckeScalar

end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum

theorem doubleCoset_surj_of_le {G : Type*} [Group G] (H K J : Subgroup G) :
    Function.Surjective (fun p : DoubleCoset.Quotient (H : Set G) (K : Set G) × (K ⧸ J.subgroupOf K) =>
      DoubleCoset.mk H J (p.1.out * (p.2.out : G))) := by
  intro c
  obtain ⟨h, hh, k, hk, e⟩ := DoubleCoset.mk_out_eq_mul H K c.out
  refine ⟨(DoubleCoset.mk H K c.out, QuotientGroup.mk (⟨k⁻¹, K.inv_mem hk⟩ : K)), ?_⟩
  obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul (J.subgroupOf K) (⟨k⁻¹, K.inv_mem hk⟩ : K)
  have hjJ : ((j : K) : G) ∈ J := Subgroup.mem_subgroupOf.mp j.2
  simp only
  rw [hj, e]
  conv_rhs => rw [← DoubleCoset.out_eq' c]
  rw [eq_comm, DoubleCoset.eq]
  refine ⟨h, hh, _, hjJ, ?_⟩
  simp [mul_assoc]

theorem doubleCoset_card_le {G : Type*} [Group G] (H K J : Subgroup G)
    [Finite (DoubleCoset.Quotient (H : Set G) (K : Set G))] (hJ : J.relIndex K ≠ 0) :
    Finite (DoubleCoset.Quotient (H : Set G) (J : Set G)) ∧
      Nat.card (DoubleCoset.Quotient (H : Set G) (J : Set G)) ≤
        Nat.card (DoubleCoset.Quotient (H : Set G) (K : Set G)) * J.relIndex K := by
  have : Finite (K ⧸ J.subgroupOf K) := Nat.finite_of_card_ne_zero hJ
  refine ⟨Finite.of_surjective _ (doubleCoset_surj_of_le H K J), ?_⟩
  have := Nat.card_le_card_of_surjective _ (doubleCoset_surj_of_le H K J)
  rwa [Nat.card_prod] at this

theorem cls_finite_card_le : ∀ (D : D7) (N : ℕ), Finite (Cls D N (intG D N)) ∧ (Nat.card (Cls D N (intG D N)) : ℝ) ≤ (12 * (fF D : ℝ) ^ 2 * (N : ℝ) ^ 4 * D.host.rdE ^ 2) ^ (6 * fF D * N ^ 2) ∧ ∀ J : Subgroup (GA D N), J ≤ intG D N → J.relIndex (intG D N) ≠ 0 → Finite (Cls D N J) ∧ Nat.card (Cls D N J) ≤ Nat.card (Cls D N (intG D N)) * J.relIndex (intG D N) := by
  intro D N
  have hcm : IsCMField D.host.E := D.host.isCMField_hostE
  have hconj : ∀ x : D.host.E, IsCMField.complexConj D.host.E x = D.host.conj x := by
    intro x
    apply D.host.φ₀.injective
    have h1 := IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ x
    have h2 := D.host.conjE_apply D.host.φ₀ x
    exact h1.trans h2.symm
  have hfr : Module.finrank ℚ D.host.E = 2 * fF D := by
    rw [D.host.finrank_cmField, fF, Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
    ring
  obtain ⟨R, hR, hcov⟩ := GlobalTheory.exists_finset_selfDual_classes_rootDiscr D.host.E N
  obtain ⟨hrat, -, hex, -, -⟩ := GlobalTheory.NormSum.mem_ratG_intG D N
  obtain ⟨Lt, hSD, -, hLt, hmv, -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D N
  have key : ∀ g : GA D N, ∃ L₀ ∈ R, ∃ h ∈ ratG D N, Lt (h⁻¹ * g) = L₀ := by
    intro g
    obtain ⟨h1, h2, h3⟩ := (hSD g).2
    obtain ⟨L₀, hL₀, γ, hγ, hx⟩ := hcov (Lt g) h1 h2 (by
      intro y
      rw [h3 y]
      refine forall_congr' fun x => forall_congr' fun _ => ?_
      constructor
      · rintro ⟨z, hz⟩
        have hz' : (z : D.host.E) = ∑ i, IsCMField.complexConj D.host.E (x i) * y i := hz
        rw [← hz']
        exact z.isIntegral_coe
      · intro hz
        exact ⟨⟨_, hz⟩, rfl⟩)
    have hm : γ.map (IsCMField.complexConj D.host.E) = γ.map D.host.conj := by
      ext i j
      simp only [Matrix.map_apply, hconj]
    rw [hm] at hγ
    obtain ⟨h, hh⟩ := hex γ hγ
    refine ⟨L₀, hL₀, h, (hrat h).2 ⟨γ, hh⟩, ?_⟩
    ext x
    rw [hmv h (h⁻¹ * g) γ hh x, mul_inv_cancel_left, hx]
  choose L₀ hL₀ h hh hL using key
  let f : Cls D N (intG D N) → R := fun c => ⟨L₀ c.out, hL₀ _⟩
  have hf : Function.Injective f := by
    intro c c' e
    have e' : L₀ c.out = L₀ c'.out := congrArg Subtype.val e
    rw [← hL, ← hL, hLt] at e'
    rw [← DoubleCoset.out_eq' c, ← DoubleCoset.out_eq' c', DoubleCoset.eq]
    refine ⟨h c'.out * (h c.out)⁻¹, Subgroup.mul_mem _ (hh _) (Subgroup.inv_mem _ (hh _)), _, e', ?_⟩
    group
  have hfin : Finite (Cls D N (intG D N)) := Finite.of_injective f hf
  refine ⟨hfin, ?_, fun J _ hJ => doubleCoset_card_le _ _ J hJ⟩
  have hc : Nat.card (Cls D N (intG D N)) ≤ R.card := by
    have := Nat.card_le_card_of_injective f hf
    simpa using this
  refine le_trans (by exact_mod_cast hc) (hR.trans (le_of_eq ?_))
  have hrd : |(discr D.host.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ D.host.E : ℝ)) = D.host.rdE := rfl
  rw [hrd, hfr]
  have : 3 * (2 * fF D) * N ^ 2 = 6 * fF D * N ^ 2 := by ring
  rw [this]
  congr 1
  push_cast
  ring

end GlobalTheory.NormSum
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

theorem _root_.GlobalTheory.T.weilOperator_rationalTranslate_mem_thetaFunctions : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (z : Matrix (Fin N') (Fin N) D.host.E), ∀ F ∈ TT D (tor0 D cc δ) N N', Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F ∈ TT D (tor0 D cc δ) N N' := by
  first | exact @GlobalTheory.FinWeil.RatTransl.wd_mem_TT | exact GlobalTheory.FinWeil.RatTransl.wd_mem_TT | (intros; apply GlobalTheory.FinWeil.RatTransl.wd_mem_TT <;> assumption)
end
