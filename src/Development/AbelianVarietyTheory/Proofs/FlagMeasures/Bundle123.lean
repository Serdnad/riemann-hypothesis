module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace GlobalTheory.RowLev.GroupAlgPos

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

variable {Q : Type} [Group Q]

theorem coeff_mul_eq_sum [Fintype Q] (a b : MonoidAlgebra ℂ Q) (q : Q) :
    (a * b).coeff q = ∑ x, a.coeff x * b.coeff (x⁻¹ * q) := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (by simp)]

def adj [Finite Q] (a : MonoidAlgebra ℂ Q) : MonoidAlgebra ℂ Q :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun q => star (a.coeff q⁻¹))

theorem adj_coeff [Finite Q] (a : MonoidAlgebra ℂ Q) (q : Q) : (adj a).coeff q = star (a.coeff q⁻¹) := rfl

theorem adj_mul [Finite Q] (a b : MonoidAlgebra ℂ Q) : adj (a * b) = adj b * adj a := by
  haveI := Fintype.ofFinite Q
  ext q
  rw [adj_coeff, coeff_mul_eq_sum, coeff_mul_eq_sum, star_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft q) _ _ fun x => ?_
  simp [adj_coeff, mul_comm, mul_assoc]

theorem adj_adj [Finite Q] (a : MonoidAlgebra ℂ Q) : adj (adj a) = a := by
  ext q; simp [adj_coeff]

theorem adj_sub [Finite Q] (a b : MonoidAlgebra ℂ Q) : adj (a - b) = adj a - adj b := by
  ext q; simp [adj_coeff]

theorem isSA_iff [Finite Q] (a : MonoidAlgebra ℂ Q) : IsSA a ↔ adj a = a := by
  constructor
  · intro h
    ext q
    rw [adj_coeff, h q, star_star]
  · intro h q
    have := adj_coeff a q⁻¹
    rw [h, inv_inv] at this
    exact this

theorem coeff_mul_adj_one [Fintype Q] (a : MonoidAlgebra ℂ Q) :
    (a * adj a).coeff 1 = ∑ x, a.coeff x * star (a.coeff x) := by
  rw [coeff_mul_eq_sum]
  simp only [adj_coeff, mul_one, inv_inv]

theorem eq_zero_of_coeff_mul_adj [Finite Q] (a : MonoidAlgebra ℂ Q) (h : (a * adj a).coeff 1 = 0) : a = 0 := by
  haveI := Fintype.ofFinite Q
  rw [coeff_mul_adj_one] at h
  ext q
  have := (Finset.sum_eq_zero_iff_of_nonneg fun x _ => mul_star_self_nonneg (a.coeff x)).1 h q (Finset.mem_univ _)
  simpa using this

theorem isSA_central [Finite Q] (z : MonoidAlgebra ℂ Q) (hz : z * z = z) (hc : ∀ a, z * a = a * z) : IsSA z := by
  have hs : adj z * adj z = adj z := by rw [← adj_mul, hz]
  have h0 : z - z * adj z = 0 := by
    apply eq_zero_of_coeff_mul_adj
    rw [adj_sub, adj_mul, adj_adj]
    have e1 : z * adj z * adj z = z * adj z := by rw [mul_assoc, hs]
    have e2 : z * (z * adj z) = z * adj z := by rw [← mul_assoc, hz]
    have e3 : z * adj z * (z * adj z) = z * adj z := by
      rw [mul_assoc, ← mul_assoc (adj z), ← hc (adj z), mul_assoc z (adj z), hs, e2]
    rw [sub_mul, mul_sub, mul_sub, e1, e2, e3]; simp
  have h1 : z = z * adj z := sub_eq_zero.1 h0
  rw [isSA_iff]
  conv_lhs => rw [h1, adj_mul, adj_adj]
  exact h1.symm

end GlobalTheory.RowLev.GroupAlgPos
end
end

section

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev.SqfCrt

theorem mem_mul_smul_of_coprime {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M] (N : Submodule S M)
    {A B : Ideal S} (h : IsCoprime A B) {y : M} (hA : y ∈ A • N) (hB : y ∈ B • N) : y ∈ (A * B) • N := by
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 h
  have hsplit : y = a • y + b • y := by rw [← add_smul, hab, one_smul]
  rw [hsplit]
  refine Submodule.add_mem _ ?_ ?_
  · rw [Submodule.mul_smul]
    exact Submodule.smul_mem_smul ha hB
  · rw [mul_comm, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hb hA

theorem mem_prod_smul_of_coprime {S M ι : Type*} [CommRing S] [AddCommGroup M] [Module S M] (N : Submodule S M)
    (J : ι → Ideal S) (hJ : ∀ i j, i ≠ j → IsCoprime (J i) (J j)) {y : M} (hy : y ∈ N) (T : Finset ι)
    (h : ∀ i ∈ T, y ∈ J i • N) : y ∈ (∏ i ∈ T, J i) • N := by
  induction T using Finset.induction_on with
  | empty => simpa [Ideal.one_eq_top, Submodule.top_smul] using hy
  | @insert a T haT ih =>
    rw [Finset.prod_insert haT]
    refine mem_mul_smul_of_coprime N ?_ (h a (Finset.mem_insert_self a T))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact IsCoprime.prod_right fun i hi => hJ a i fun hai => haT (hai ▸ hi)

theorem exists_prod_le_of_isRadical {R : Type*} [CommRing R] [IsDedekindDomain R] {𝔞 : Ideal R} (h0 : 𝔞 ≠ ⊥)
    (hr : 𝔞.IsRadical) : ∃ T : Finset (HeightOneSpectrum R), (∀ u ∈ T, 𝔞 ≤ u.asIdeal) ∧
      ∏ u ∈ T, u.asIdeal ≤ 𝔞 := by
  have hfin := Ideal.finite_factors h0
  refine ⟨hfin.toFinset, fun u hu => Ideal.le_of_dvd ((Set.Finite.mem_toFinset hfin).1 hu), ?_⟩
  intro x hx
  apply hr
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro P ⟨hle, hP⟩
  have hP0 : P ≠ ⊥ := fun hb => h0 (le_bot_iff.1 (hb ▸ hle))
  let v : HeightOneSpectrum R := ⟨P, hP, hP0⟩
  have hv : v ∈ hfin.toFinset := (Set.Finite.mem_toFinset hfin).2 (Ideal.dvd_iff_le.2 hle)
  exact (Ideal.prod_le_inf.trans (Finset.inf_le hv)) hx

theorem extId_eq_image (I : AutInst) (𝔞 : Ideal (𝓞 I.E)) : extId I 𝔞 = 𝔞.map (Inhab.psi I.F I.E) := by
  unfold extId
  rw [Ideal.map]
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, hz⟩
    exact ⟨a, ha, Subtype.ext hz.symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

private theorem isCoprime_map_of_ne {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S]
    (f : R →+* S) {u v : HeightOneSpectrum R} (huv : u ≠ v) :
    IsCoprime (u.asIdeal.map f) (v.asIdeal.map f) := by
  have hmax : u.asIdeal ⊔ v.asIdeal = ⊤ :=
    u.isMaximal.coprime_of_ne v.isMaximal fun e => huv (HeightOneSpectrum.ext e)
  rw [Ideal.isCoprime_iff_sup_eq, ← Ideal.map_sup, hmax, Ideal.map_top]

private theorem prod_map_le_map_of_prod_le {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (T : Finset (HeightOneSpectrum R)) {𝔞 : Ideal R} (hle : ∏ u ∈ T, u.asIdeal ≤ 𝔞) :
    ∏ u ∈ T, u.asIdeal.map f ≤ 𝔞.map f := by
  have hprod : ∀ T' : Finset (HeightOneSpectrum R),
      ∏ u ∈ T', u.asIdeal.map f = (∏ u ∈ T', u.asIdeal).map f := by
    intro T'
    induction T' using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.prod_empty, Ideal.one_eq_top, Ideal.one_eq_top, Ideal.map_top]
    | @insert a T' haT ih => rw [Finset.prod_insert haT, Finset.prod_insert haT, Ideal.map_mul, ih]
  rw [hprod]
  exact Ideal.map_mono hle

private theorem mem_map_smul_of_forall_mem_map_smul {R S M : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S]
    [AddCommGroup M] [Module S M] (f : R →+* S) (N : Submodule S M) {𝔞 : Ideal R} (h0 : 𝔞 ≠ ⊥)
    (hr : 𝔞.IsRadical) {y : M} (hy : y ∈ N)
    (h : ∀ u : HeightOneSpectrum R, 𝔞 ≤ u.asIdeal → y ∈ u.asIdeal.map f • N) : y ∈ 𝔞.map f • N := by
  obtain ⟨T, hT, hle⟩ := exists_prod_le_of_isRadical h0 hr
  have hmem : y ∈ (∏ u ∈ T, u.asIdeal.map f) • N :=
    mem_prod_smul_of_coprime (ι := HeightOneSpectrum R) N (fun u => u.asIdeal.map f)
      (fun _ _ huv => isCoprime_map_of_ne f huv) hy T fun u hu => h u (hT u hu)
  exact Submodule.smul_mono_left (prod_map_le_map_of_prod_le f T hle) hmem

theorem mem_extId_smul_forall_iff : ∀ (I : AutInst) (m : ℕ), 1 ≤ m → (Ideal.span {(m : 𝓞 I.E)}).IsRadical →
    ∀ y ∈ I.Lf, (∀ u : HeightOneSpectrum (𝓞 I.E), (m : 𝓞 I.E) ∈ u.asIdeal → y ∈ extId I u.asIdeal • I.Lf) ↔
      ∃ z ∈ I.Lf, y = (m : (I.E ⊗[I.F] Af I.F)) • z := by
  intro I m hm hrad y hy
  constructor
  · intro h
    have h0 : Ideal.span {(m : 𝓞 I.E)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.2 (by omega)
    have key : y ∈ (Ideal.span {(m : 𝓞 I.E)}).map (Inhab.psi I.F I.E) • I.Lf :=
      mem_map_smul_of_forall_mem_map_smul (Inhab.psi I.F I.E) I.Lf h0 hrad hy fun u hu => by
        rw [← extId_eq_image I]
        exact h u (hu (Ideal.mem_span_singleton_self _))
    rw [Ideal.map_span, Set.image_singleton, map_natCast, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at key
    obtain ⟨z, hz, hzy⟩ := key
    refine ⟨z, hz, ?_⟩
    rw [← hzy, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  · rintro ⟨z, hz, rfl⟩ u hu
    have hm' : (m : IntAf I.F I.E) ∈ extId I u.asIdeal := by
      rw [extId_eq_image, ← map_natCast (Inhab.psi I.F I.E)]
      exact Ideal.mem_map_of_mem _ hu
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul (IntAf I.F I.E)]
    exact Submodule.smul_mem_smul hm' hz

end GlobalTheory.RowLev.SqfCrt
end

section

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev


open MeasureTheory NumberField IsDedekindDomain Matrix in
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical in
theorem _root_.GlobalTheory.RowLev.intAf_approx_inter_unit_conj : ∀ (I : _root_.Formalism.MainNotions.S.AutInst) (g : ℕ), 1 ≤ g →
    (∀ z ∈ _root_.Formalism.MainNotions.S.IntAf I.F I.E, ∃ a : 𝓞 I.E, ∃ z' ∈ _root_.Formalism.MainNotions.S.IntAf I.F I.E,
      z = _root_.Formalism.UG.inclE (F := I.F) (_root_.Formalism.MainNotions.S.Af I.F) (a : I.E) + (g : (I.E ⊗[I.F] _root_.Formalism.MainNotions.S.Af I.F)) * z') ∧
    (∀ a : I.E, _root_.Formalism.UG.inclE (F := I.F) (_root_.Formalism.MainNotions.S.Af I.F) a ∈ _root_.Formalism.MainNotions.S.IntAf I.F I.E ↔
      a ∈ (algebraMap (𝓞 I.E) I.E).range) ∧
    IsUnit (g : (I.E ⊗[I.F] _root_.Formalism.MainNotions.S.Af I.F)) ∧
    ∀ z ∈ _root_.Formalism.MainNotions.S.IntAf I.F I.E, _root_.Formalism.UG.sigR I.cm.sig (_root_.Formalism.MainNotions.S.Af I.F) z ∈ _root_.Formalism.MainNotions.S.IntAf I.F I.E := by
  intro I g hg
  have hg0 : g ≠ 0 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨b, t, hbt⟩ := _root_.GlobalTheory.RowLev.Inhab.exists_approx (F := I.F) (E := I.E) hg0 ⟨z, hz⟩
    refine ⟨b, t, t.2, ?_⟩
    have h := congrArg Subtype.val hbt
    simpa [_root_.GlobalTheory.RowLev.Inhab.psi] using h
  · intro a
    constructor
    · intro ha
      have hint : IsIntegral ℤ a := _root_.Formalism.UG.P.csGlob_int a ha
      exact ⟨⟨a, hint⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact _root_.Formalism.UG.CS.incl_int b
  · have hF : IsUnit (g : I.F) := isUnit_iff_ne_zero.mpr (by exact_mod_cast hg0)
    simpa using hF.map (algebraMap I.F (I.E ⊗[I.F] _root_.Formalism.MainNotions.S.Af I.F))
  · intro z hz
    exact _root_.Formalism.UG.P.csDual_sig_mem _ hz

end GlobalTheory.RowLev
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Dec

theorem countHyp_one_le_rd (I : AutInst) : 1 ≤ I.rd := by
  have hd : (1 : ℝ) ≤ |(discr I.E : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |discr I.E| := Int.one_le_abs (NumberField.discr_ne_zero I.E)
    exact_mod_cast h1
  show 1 ≤ |(discr I.E : ℝ)| ^ ((1 : ℝ) / (2 * (I.f : ℝ)))
  exact Real.one_le_rpow hd (by positivity)

theorem countHyp_card_places (I : AutInst) : Fintype.card (InfinitePlace I.F) = I.f := by
  have : IsTotallyReal I.F := I.cm.totReal
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero,
    add_zero]
  exact (IsTotallyReal.finrank I.F).symm

theorem countHyp_pAt_add_qAt (I : AutInst) (v : InfinitePlace I.F) : I.pAt v + I.qAt v = I.n := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin I.n)))
    (fun a => I.ε v a = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at h
  exact h

theorem countHyp_numerics : ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ → CountHyp B Cg n₀ d p q b → 0 ≤ Cg ∧ 1 ≤ B.I.rd ∧ 1 ≤ B.I.f ∧ Fintype.card (InfinitePlace B.I.F) = B.I.f ∧ p + q = B.I.n ∧ 2 * q + 2 ≤ B.I.n ∧ (∀ v, rkR (B.I.ε v) = q) ∧ min p q = q ∧ 0 < (∏ v, d v) ∧ 16 ≤ bigX B b ∧ 0 < tauStar B q b ∧ (1 ≤ q → tauStar B q b < 1 / 2 ∧ (B.I.n : ℝ) ^ 19 ≤ b ^ 2) ∧ ∃ h : ℝ, h = 8 * 10 ^ 14 * (Cg + 4) * (B.I.n : ℝ) ^ 19 * (B.I.f : ℝ) ^ 5 * Real.log (b * B.I.rd) ∧ GapGe B h ∧ HBig B 40 h ∧ HBig B 32 h ∧ 8 * (B.I.n : ℝ) * q < h ∧ 120 * (B.I.n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ h ∧ 40 * (B.I.n : ℝ) ^ 2 * Real.sqrt q ≤ h := by
  intro B Cg n₀ d p q b hn₀ hC
  unfold CountHyp at hC
  obtain ⟨hDS, hSig, hn, hq2, -, -, hb, -, hlam, hg1, hgC, -, -, -, hgap⟩ := hC
  have hrd : 1 ≤ B.I.rd := countHyp_one_le_rd B.I
  have hcard : Fintype.card (InfinitePlace B.I.F) = B.I.f := countHyp_card_places B.I
  have hf : 1 ≤ B.I.f := Module.finrank_pos
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace B.I.F) := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨hp₀, hq₀⟩ := hSig v₀
  have hpq : p + q = B.I.n := by rw [← hp₀, ← hq₀]; exact countHyp_pAt_add_qAt B.I v₀
  have h2q : 2 * q + 2 ≤ B.I.n := by
    rcases Nat.lt_or_ge q 3 with h | h
    · omega
    · nlinarith
  have hqp : q ≤ p := by omega
  have hmin : min p q = q := min_eq_right hqp
  have hrk : ∀ v, rkR (B.I.ε v) = q := by
    intro v
    obtain ⟨hp, hq⟩ := hSig v
    show min (B.I.pAt v) (B.I.qAt v) = q
    rw [hp, hq, hmin]
  have hd : 0 < ∏ v, d v := by
    refine Finset.prod_pos fun v _ => ?_
    obtain ⟨-, -, -, ⟨hdv, -⟩⟩ := hDS v
    exact hdv
  have hCg : 0 ≤ Cg := by
    by_contra hneg
    have h1 : b ^ Cg < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (lt_of_not_ge hneg)
    have h2 : (1 : ℝ) ≤ B.g := by exact_mod_cast hg1
    linarith
  have hnr : (8 : ℝ) ≤ B.I.n := by exact_mod_cast le_trans hn₀ hn
  have hfr : (1 : ℝ) ≤ B.I.f := by exact_mod_cast hf
  have hgr : (1 : ℝ) ≤ B.g := by exact_mod_cast hg1
  have hX : 16 ≤ bigX B b := by
    show 16 ≤ (B.I.n : ℝ) * B.I.f * B.I.rd * B.g * b
    have a1 : 8 ≤ (B.I.n : ℝ) * B.I.f := by nlinarith
    have a2 : 8 ≤ (B.I.n : ℝ) * B.I.f * B.I.rd := by nlinarith
    have a3 : 8 ≤ (B.I.n : ℝ) * B.I.f * B.I.rd * B.g := by nlinarith
    nlinarith
  have htpos : 0 < tauStar B q b := by
    show 0 < (bigX B b)⁻¹ ^ (11 * q)
    have : 0 < bigX B b := by linarith
    positivity

  have hL : Real.log 2 ≤ Real.log (b * B.I.rd) := Real.log_le_log (by norm_num) (by nlinarith)
  have hlog2 := Real.log_two_gt_d9
  have hF5 : (1 : ℝ) ≤ (B.I.f : ℝ) ^ 5 := one_le_pow₀ hfr
  have hP1 : 2 ≤ (Cg + 4) * Real.log (b * B.I.rd) := by nlinarith
  have hP : 2 ≤ (Cg + 4) * (B.I.f : ℝ) ^ 5 * Real.log (b * B.I.rd) := by
    have : (Cg + 4) * (B.I.f : ℝ) ^ 5 * Real.log (b * B.I.rd)
        = ((Cg + 4) * Real.log (b * B.I.rd)) * (B.I.f : ℝ) ^ 5 := by ring
    rw [this]
    nlinarith
  have hN : 0 ≤ (B.I.n : ℝ) ^ 19 := by positivity
  have hbig : 10 ^ 15 * (B.I.n : ℝ) ^ 19 ≤
      8 * 10 ^ 14 * (Cg + 4) * (B.I.n : ℝ) ^ 19 * (B.I.f : ℝ) ^ 5 * Real.log (b * B.I.rd) := by
    have : 8 * 10 ^ 14 * (Cg + 4) * (B.I.n : ℝ) ^ 19 * (B.I.f : ℝ) ^ 5 * Real.log (b * B.I.rd)
        = 8 * 10 ^ 14 * (B.I.n : ℝ) ^ 19 * ((Cg + 4) * (B.I.f : ℝ) ^ 5 * Real.log (b * B.I.rd)) := by
      ring
    rw [this]
    nlinarith
  have hn1 : (1 : ℝ) ≤ B.I.n := by linarith
  have hn2 : (B.I.n : ℝ) ^ 2 ≤ (B.I.n : ℝ) ^ 19 := pow_le_pow_right₀ hn1 (by norm_num)
  have hn3 : (B.I.n : ℝ) ^ 3 ≤ (B.I.n : ℝ) ^ 19 := pow_le_pow_right₀ hn1 (by norm_num)
  have hqn : (q : ℝ) ≤ B.I.n := by exact_mod_cast (show q ≤ B.I.n by omega)
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hsq : Real.sqrt q ≤ B.I.n := by
    calc Real.sqrt q ≤ Real.sqrt ((B.I.n : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = B.I.n := Real.sqrt_sq (by positivity)
  have hs40 : 40 * (B.I.n : ℝ) ^ 2 * Real.sqrt q ≤
      8 * 10 ^ 14 * (Cg + 4) * (B.I.n : ℝ) ^ 19 * (B.I.f : ℝ) ^ 5 * Real.log (b * B.I.rd) := by
    have e1 : 40 * (B.I.n : ℝ) ^ 2 * Real.sqrt q ≤ 40 * (B.I.n : ℝ) ^ 2 * B.I.n :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have e2 : 40 * (B.I.n : ℝ) ^ 2 * B.I.n = 40 * (B.I.n : ℝ) ^ 3 := by ring
    linarith
  refine ⟨hCg, hrd, hf, hcard, hpq, h2q, hrk, hmin, hd, hX, htpos, ?_, _, rfl, hgap, ?_, ?_, ?_, ?_, hs40⟩
  · intro hq1
    constructor
    · show (bigX B b)⁻¹ ^ (11 * q) < 1 / 2
      have hXp : 0 < bigX B b := by linarith
      have hi : (bigX B b)⁻¹ ≤ 16⁻¹ := inv_anti₀ (by norm_num) hX
      have hi0 : 0 ≤ (bigX B b)⁻¹ := inv_nonneg.mpr hXp.le
      have hpow : (bigX B b)⁻¹ ^ (11 * q) ≤ (bigX B b)⁻¹ :=
        pow_le_of_le_one hi0 (by linarith [show (16 : ℝ)⁻¹ ≤ 1 by norm_num]) (by omega)
      have : (16 : ℝ)⁻¹ < 1 / 2 := by norm_num
      linarith
    · have hpc : 0 < (Finset.univ.filter fun a => B.I.ε v₀ a = true).card := by
        show 0 < B.I.pAt v₀
        omega
      have hqc : 0 < (Finset.univ.filter fun a => B.I.ε v₀ a = false).card := by
        show 0 < B.I.qAt v₀
        omega
      obtain ⟨a, ha⟩ := Finset.card_pos.mp hpc
      obtain ⟨a', ha'⟩ := Finset.card_pos.mp hqc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ha'
      have hne : B.I.ε v₀ a ≠ B.I.ε v₀ a' := by rw [ha, ha']; decide
      have hg := hgap v₀ a a' hne
      obtain ⟨l1, l2⟩ := abs_le.mp (hlam v₀ a)
      obtain ⟨l3, l4⟩ := abs_le.mp (hlam v₀ a')
      have hdiff : |B.lam v₀ a - B.lam v₀ a'| ≤ 2 * b ^ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      have hb0 : 0 ≤ b ^ 2 := by positivity
      linarith
  · intro v
    rw [hrk v]
    linarith
  · intro v
    rw [hrk v]
    have : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
    nlinarith
  · have hpos : 0 < (B.I.n : ℝ) ^ 19 := by positivity
    have e1 : 8 * (B.I.n : ℝ) * q ≤ 8 * (B.I.n : ℝ) ^ 2 := by nlinarith
    linarith
  · have r1 : (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (B.I.n : ℝ) ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow hq0 hqn (by norm_num)
    have r2 : (B.I.n : ℝ) ^ ((3 : ℝ) / 2) ≤ (B.I.n : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
    rw [Real.rpow_two] at r2
    have e1 : 120 * (B.I.n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (B.I.n : ℝ) * (B.I.n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left (r1.trans r2) (by positivity)
    have e2 : 120 * (B.I.n : ℝ) * (B.I.n : ℝ) ^ 2 = 120 * (B.I.n : ℝ) ^ 3 := by ring
    linarith

end GlobalTheory.Dec
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem IsFdegG.dense_span_orbit {G : Type} [MeasurableSpace G] {μ : Measure G} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {σ : G → (H →L[ℂ] H)} {d : ℝ} (h : IsFdegG μ σ d)
    (w : H) (hw : w ≠ 0) : Dense (Submodule.span ℂ (Set.range fun g => σ g w) : Set H) := by
  obtain ⟨hd, hint⟩ := h
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro u hu
  rw [Submodule.mem_orthogonal] at hu

  have hzero : ∀ g, ⟪u, σ g w⟫_ℂ = 0 := fun g =>
    inner_eq_zero_symm.mp (hu (σ g w) (Submodule.subset_span ⟨g, rfl⟩))

  have key := (hint w u w u).2
  have hfun : (fun g => ⟪u, σ g w⟫_ℂ * star ⟪u, σ g w⟫_ℂ) = fun _ => (0 : ℂ) := by
    funext g
    simp [hzero g]
  rw [hfun, integral_zero] at key
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hw' : ⟪w, w⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hw
  have huu : ⟪u, u⟫_ℂ = 0 := by
    rcases div_eq_zero_iff.mp key.symm with h1 | h1
    · exact (mul_eq_zero.mp h1).resolve_left hw'
    · exact absurd h1 hd'
  exact inner_self_eq_zero.mp huu

theorem isIrr_and_dense_of_isFdegG : ∀ (G : Type) [MeasurableSpace G] (μ : Measure G) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G → (H →L[ℂ] H)) (d : ℝ), IsFdegG μ σ d → IsIrr σ ∧ ∀ w : H, w ≠ 0 → Dense (Submodule.span ℂ (Set.range fun g => σ g w) : Set H) := by
  intro G _ μ H _ _ _ σ d h
  refine ⟨?_, fun w hw => IsFdegG.dense_span_orbit h w hw⟩
  intro S hS hinv
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨w, hwS, hw⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot

    have hsub : Submodule.span ℂ (Set.range fun g => σ g w) ≤ S := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact hinv g w hwS
    have hcl : closure ((Submodule.span ℂ (Set.range fun g => σ g w) : Submodule ℂ H) : Set H) ⊆ (S : Set H) :=
      closure_minimal (fun y hy => hsub hy) hS
    rw [Submodule.eq_top_iff']
    intro x
    exact hcl (by rw [(IsFdegG.dense_span_orbit h w hw).closure_eq]; exact Set.mem_univ x)

end GlobalTheory.Dec
end
