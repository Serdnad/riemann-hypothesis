module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle344
public import Formalism.LocalToGlobal.Columns.Bundle015
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.XiAtPenultimateEqXiCpl1
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle348
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle326
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValDetSubOneLt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle346
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2.MemChart

theorem inv_smul_mem_of_be_eq_zero {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {d : Deco E n ST SG} (hd : d.Ok) (w : SG)
    (hq : ((Formalism.L2.Col.qOf w.1 : ℕ) : 𝓞 E) ∉ w.1.asIdeal ^ 2) {x : Sp E n} (hx : x ∈ d.at w.1) (h0 : d.be w x = 0) :
    ((Formalism.L2.Col.qOf w.1 : ℕ) : E)⁻¹ • x ∈ d.at w.1 := by
  obtain ⟨h1, h2⟩ := GlobalTheory.TopStep.liftFr_spec hd w
  set fr := d.liftFr w with hfr
  have e : fr (fr.symm x) = x := fr.apply_symm_apply x
  have hs : fr.symm x ∈ stdAt E n w.1 := (h1 _).1 (by rwa [e])
  have hr := h2 _ hs
  rw [e, h0] at hr
  have hi := GlobalTheory.TopStep.mem_stdAt.1 hs
  have hs' : ((Formalism.L2.Col.qOf w.1 : ℕ) : E)⁻¹ • fr.symm x ∈ stdAt E n w.1 := GlobalTheory.TopStep.mem_stdAt.2 fun i => by
    have := GlobalTheory.TopStep.intAt_div_of_redP hq (hi i) (congrFun hr i).symm
    rwa [div_eq_inv_mul] at this
  have := (h1 _).2 hs'
  rwa [map_smul, e] at this

theorem sub_mem_of_be_eq {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {d : Deco E n ST SG} (hd : d.Ok) (w : SG)
    (hq : ((Formalism.L2.Col.qOf w.1 : ℕ) : 𝓞 E) ∉ w.1.asIdeal ^ 2) {y y' z : Sp E n}
    (hy : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y ∈ d.at w.1) (hy' : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y' ∈ d.at w.1)
    (hz : z - y' ∈ d.at w.1)
    (e : d.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y) = d.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • z)) :
    y - y' ∈ d.at w.1 := by
  have hq0 : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
  have hqz : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • (z - y') ∈ d.at w.1 :=
    GlobalTheory.TopStep.smul_mem_locP (GlobalTheory.TopStep.intAt_nat _) hz
  have e1 : d.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • (z - y')) = 0 := by
    rw [GlobalTheory.TopStep.be_smul_int hd w (GlobalTheory.TopStep.intAt_nat _) hz, GlobalTheory.TopStep.reduction_absNorm_eq_zero, zero_smul]
  have e2 := hd.be_add w _ hqz _ hy'
  rw [← smul_add, sub_add_cancel, e1, zero_add, ← e] at e2
  have hx : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • (y - y') ∈ d.at w.1 := by
    rw [smul_sub]
    exact sub_mem hy hy'
  have e3 := hd.be_add w _ hx _ hy'
  rw [← smul_add, sub_add_cancel, e2, right_eq_add] at e3
  have := inv_smul_mem_of_be_eq_zero hd w hq hx e3
  rwa [smul_smul, inv_mul_cancel₀ hq0, one_smul] at this

theorem mem_coset {M : Type} [AddCommGroup M] {A : Type} [Ring A] [Module A M] {L : Submodule A M} {y z : M} :
    z ∈ {z | z - y ∈ L} ↔ z - y ∈ L := Iff.rfl

theorem coset_eq {M : Type} [AddCommGroup M] {A : Type} [Ring A] [Module A M] (L : Submodule A M) {y y' : M} (h : y - y' ∈ L) :
    {z | z - y ∈ L} = {z | z - y' ∈ L} := by
  refine Set.ext fun z => ?_
  rw [mem_coset, mem_coset]
  refine ⟨fun h' => ?_, fun h' => ?_⟩
  · have := add_mem h' h
    rwa [sub_add_sub_cancel] at this
  · have := sub_mem h' h
    rwa [sub_sub_sub_cancel_right] at this

theorem eq_of_deco_bar : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, QE sel (mu : Chr X.F X.E X.K) = ∅ → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) → ∀ q q' : PtAt R sel mu cst u j, q.1.1.deco = q'.1.1.deco → MemChart.bar q = MemChart.bar q' → q = q' := by
  intro X Pr R sel S mu cst u j hQ hq q q' hd hb
  have hP : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs := fun P => by
    have := P.2
    simpa [rowSG, uSG, hQ] using this
  have hfr : q.1.1 = q'.1.1 := by
    apply Subtype.ext
    have hE : ∀ a, a ∈ QE sel (mu : Chr X.F X.E X.K) → False := fun a ha => by
      rw [hQ] at ha
      simp at ha
    exact Prod.ext hd (funext fun P => (hE _ P.2).elim)
  suffices h2 : q.1.2 = q'.1.2 from Subtype.ext (Prod.ext hfr h2)
  by_cases hj : j + 1 = R.m
  · obtain ⟨y, hy, eY⟩ := q.mem_ybSet hj
    obtain ⟨y', hy', eY'⟩ := q'.mem_ybSet hj
    have eN : q'.1.1.deco.1.N = q.1.1.deco.1.N := by rw [hd]
    rw [eN] at hy' eY'
    have key : ∀ e : rowSG Pr sel mu → ℤ, (∀ P, e P = 0) → y - y' ∈ locLat (rowSG Pr sel mu) q.1.1.deco.1.N e := by
      intro e he
      refine (mem_locLat _ _ _ _).2 fun P => ?_
      rw [he P, zpow_zero, inv_one, one_smul]
      have hm : q.1.1.deco.1.be ⟨P.1, hP P⟩ (((Formalism.L2.Col.qOf P.1 : ℕ) : X.E) • y) ∈ bar q ⟨P.1, hP P⟩ :=
        ⟨y, by rw [eY, mem_coset, sub_self]; exact zero_mem _, rfl⟩
      rw [congrFun hb ⟨P.1, hP P⟩] at hm
      obtain ⟨z, hz, ez⟩ := hm
      rw [← hd] at ez
      rw [eY'] at hz
      have hz' := (mem_locLat _ _ _ _).1 (mem_coset.1 hz) P
      rw [if_pos (hP P), zpow_zero, inv_one, one_smul] at hz'
      have h1 := (mem_locLat _ _ _ _).1 hy P
      have h2 := (mem_locLat _ _ _ _).1 hy' P
      rw [if_pos (hP P), _root_.zpow_neg_one, inv_inv] at h1 h2
      exact sub_mem_of_be_eq q.1.1.deco.2 ⟨P.1, hP P⟩ (hq _ (hP P)) h1 h2 hz' ez
    rw [eY, eY']
    exact coset_eq _ (key _ fun P => if_pos (hP P))
  · have h1 := q.2
    have h1' := q'.2
    rw [ysAt_ys_of_ne sel mu cst hj] at h1 h1'
    exact h1.trans h1'.symm

end GlobalTheory.Mem.Col2.MemChart
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2.MemChart.CosetLift

section Local

variable {E : Type} [Field E] [NumberField E]

theorem exists_pow_intAt_div (P : HeightOneSpectrum (𝓞 E)) {m : ℕ} (hm : m ≠ 0) :
    ∃ K : ℕ, ∀ e ∈ P.asIdeal ^ K, Formalism.L2.Col.IntAt P (algebraMap (𝓞 E) E e / (m : E)) := by
  have h0 : P.intValuation (m : 𝓞 E) ≠ 0 := P.intValuation_ne_zero _ (Nat.cast_ne_zero.2 hm)
  refine ⟨(-WithZero.log (P.intValuation (m : 𝓞 E))).toNat, fun e he => ?_⟩
  have hv : P.valuation E (algebraMap (𝓞 E) E e / (m : E)) ≤ 1 := by
    rw [← map_natCast (algebraMap (𝓞 E) E) m, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap]
    have h1 := (P.intValuation_le_pow_iff_mem e _).2 he
    have h2 : WithZero.exp (-((-WithZero.log (P.intValuation (m : 𝓞 E))).toNat : ℤ)) ≤ P.intValuation (m : 𝓞 E) := by
      conv_rhs => rw [← WithZero.exp_log h0]
      rw [WithZero.exp_le_exp]
      omega
    exact (div_le_one₀ (zero_lt_iff.2 h0)).2 (h1.trans h2)
  obtain ⟨r, s, hrs⟩ := P.exists_primeCompl_mul_eq_of_integer _ hv
  exact ⟨r, s, s.2, by rw [mul_comm]; exact hrs⟩

theorem exists_one_intAt_div (T : Finset (HeightOneSpectrum (𝓞 E))) (w : HeightOneSpectrum (𝓞 E)) {m : ℕ} (hm : m ≠ 0) :
    ∃ e : 𝓞 E, Ideal.Quotient.mk w.asIdeal e = 1 ∧
      ∀ w' ∈ T, w' ≠ w → Formalism.L2.Col.IntAt w' (algebraMap (𝓞 E) E e / (m : E)) := by
  classical
  choose K hK using fun w' : HeightOneSpectrum (𝓞 E) => exists_pow_intAt_div w' hm
  have ht : ∀ w' : HeightOneSpectrum (𝓞 E), ∃ t : 𝓞 E, t ∉ w.asIdeal ∧ (w' ≠ w → t ∈ w'.asIdeal) := by
    intro w'
    by_cases hne : w' = w
    · exact ⟨1, Formalism.L2.Col.one_notMem w, fun h => absurd hne h⟩
    · by_contra hc
      refine hne (HeightOneSpectrum.ext (w'.isMaximal.eq_of_le w.isPrime.ne_top fun t h => ?_))
      by_contra h'
      exact hc ⟨t, h', fun _ => h⟩
  choose t ht1 ht2 using ht
  have := w.isMaximal
  have := w.isPrime
  have he0 : (∏ w' ∈ T, t w' ^ K w') ∉ w.asIdeal :=
    w.asIdeal.primeCompl.prod_mem fun w' _ => w.asIdeal.primeCompl.pow_mem (ht1 w') _
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv (Formalism.L2.Col.mk_ne_zero he0)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨(∏ w' ∈ T, t w' ^ K w') * b, by rw [map_mul, hb], fun w' hw' hne => hK w' _ (Ideal.mul_mem_right _ _ ?_)⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun w' => t w' ^ K w') hw'
  rw [hc]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (ht2 w' hne) _)

variable [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem exists_vec (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (v : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal) :
    ∃ y : Sp E n, ∀ w : SG, ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y ∈ d.1.at w.1 ∧
      d.1.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y) = v w := by
  classical
  choose x hxN hxv using fun w : SG => d.2.be_surj w (v w)
  choose e he1 he2 using fun w : SG => exists_one_intAt_div SG w.1 (m := Formalism.L2.Col.qOf w.1)
    (Nat.cast_ne_zero.1 (TopStep.qOf_ne_zero (P := w.1)))
  refine ⟨∑ w : SG, (algebraMap (𝓞 E) E (e w) / ((Formalism.L2.Col.qOf w.1 : ℕ) : E)) • x w, fun w0 => ?_⟩
  have hc : ((Formalism.L2.Col.qOf w0.1 : ℕ) : E) * (algebraMap (𝓞 E) E (e w0) / ((Formalism.L2.Col.qOf w0.1 : ℕ) : E)) =
      algebraMap (𝓞 E) E (e w0) := mul_div_cancel₀ _ TopStep.qOf_ne_zero
  have hi : ∀ w : SG, Formalism.L2.Col.IntAt w0.1
      (((Formalism.L2.Col.qOf w0.1 : ℕ) : E) * (algebraMap (𝓞 E) E (e w) / ((Formalism.L2.Col.qOf w.1 : ℕ) : E))) := fun w => by
    by_cases h : w = w0
    · rw [h, hc]
      exact Formalism.L2.Col.IntAt.coe _ _
    · exact (TopStep.intAt_nat _).mul (he2 w w0.1 w0.2 fun h' => h (Subtype.ext h'.symm))
  have hx : ∀ w : SG, x w ∈ d.1.at w0.1 := fun w => Formalism.L2.Col.le_locP _ _ (hxN w)
  simp only [Finset.smul_sum, smul_smul]
  refine ⟨Submodule.sum_mem _ fun w _ => TopStep.smul_mem_locP (hi w) (hx w), ?_⟩
  rw [TopStep.be_sum d.2 w0 _ fun w _ => TopStep.smul_mem_locP (hi w) (hx w), Finset.sum_eq_single w0]
  · rw [TopStep.be_smul_int d.2 w0 (hi w0) (hx w0), hc, Formalism.L2.Col.reduction_coe, he1, one_smul, hxv]
  · intro w _ h
    rw [TopStep.be_smul_int d.2 w0 (hi w) (hx w), Formalism.L2.Col.reduction_mul (TopStep.intAt_nat _)
      (he2 w w0.1 w0.2 fun h' => h (Subtype.ext h'.symm)), TopStep.reduction_absNorm_eq_zero, zero_mul, zero_smul]
  · exact fun h => absurd (Finset.mem_univ _) h

theorem coset_be (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (SB : Finset (HeightOneSpectrum (𝓞 E))) (w : SG) (hw : w.1 ∈ SB) (e0 : SB → ℤ)
    (h0 : e0 ⟨w.1, hw⟩ = 0) {y : Sp E n} (hy : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y ∈ d.1.at w.1) :
    {v | ∃ z ∈ {z | z - y ∈ Formalism.L2.Col.locLat SB d.1.N e0}, v = d.1.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • z)} =
      {d.1.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y)} := by
  ext v
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : z - y ∈ d.1.at w.1 := by
      have := (Formalism.L2.Col.mem_locLat _ _ _ _).1 hz ⟨w.1, hw⟩
      rwa [h0, zpow_zero, inv_one, one_smul] at this
    have e : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • z =
        ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y + ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • (z - y) := by
      rw [← smul_add, add_sub_cancel]
    rw [Set.mem_singleton_iff, e, d.2.be_add w _ hy _ (TopStep.smul_mem_locP (TopStep.intAt_nat _) hz'),
      TopStep.be_smul_int d.2 w (TopStep.intAt_nat _) hz', TopStep.reduction_absNorm_eq_zero, zero_smul, add_zero]
  · intro hv
    exact ⟨y, by rw [Set.mem_setOf_eq, sub_self]; exact zero_mem _, hv⟩

end Local

theorem exists_ptAt_bar_eq {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}
    (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (_hq : ∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2)
    (q : PtAt R sel mu cst u j) (d : DecoSet (E := X.E) (n := R.N j) (ST := Pr.vT u) (SG := Pr.vGs)) :
    ∃ q' : PtAt R sel mu cst u j, q'.1.1.deco = d ∧ MemChart.bar q' = MemChart.bar q := by
  classical
  by_cases h : j + 1 = R.m
  · obtain ⟨y, hy, hY⟩ := q.mem_ybSet h
    have hG : ∀ w : Pr.vGs, w.1 ∈ rowSG Pr sel mu := fun w => Finset.mem_union_left _ w.2
    have hG' : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs := fun P =>
      (Finset.mem_union.mp P.2).resolve_right fun h' => chfok_false hQ ⟨P.1, h'⟩
    obtain ⟨y', hy'⟩ := exists_vec d fun w => q.1.1.deco.1.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : X.E) • y)
    refine ⟨⟨(chfokLift hQ d, {z | z - y' ∈ Formalism.L2.Col.locLat (rowSG Pr sel mu) d.1.N
      (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))}), ?_⟩, rfl, ?_⟩
    · rw [ysAt_ys_of_eq sel mu cst h]
      refine ⟨y', (Formalism.L2.Col.mem_locLat _ _ _ _).2 fun P => ?_, by congr!⟩
      rw [if_pos (hG' P), _root_.zpow_neg_one, inv_inv]
      exact (hy' ⟨P.1, hG' P⟩).1
    · funext w
      have h1 := (Formalism.L2.Col.mem_locLat _ _ _ _).1 hy ⟨w.1, hG w⟩
      rw [if_pos w.2, _root_.zpow_neg_one, inv_inv] at h1
      refine (coset_be d _ w (hG w) _ (if_pos w.2) (hy' w).1).trans ?_
      rw [(hy' w).2, MemChart.bar, hY]
      exact (coset_be q.1.1.deco _ w (hG w) _ (if_pos w.2) h1).symm
  · have hY : q.1.2 = ∅ := by
      have := q.2
      rwa [ysAt_ys_of_ne sel mu cst h] at this
    refine ⟨⟨(chfokLift hQ d, ∅), by rw [ysAt_ys_of_ne sel mu cst h]; rfl⟩, rfl, ?_⟩
    funext w
    simp [MemChart.bar, hY]

end GlobalTheory.Mem.Col2.MemChart.CosetLift
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymChar.Resid

theorem hA_bwd_symVec : ∀ (D : D7) (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (k : Fin 2), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → GlobalTheory.Mem.SymFrame.EwAt X w → 1 - X.ew ∈ GlobalTheory.Mem.SymChar.wInt X w → ∀ (i : Fin D.R.k) (j : Fin D.R.r), hA X.B.I (X.bwd i) (GlobalTheory.Mem.SymFrame.symVec X w j) - (if j = GlobalTheory.Mem.SymChar.Resid.posB D i then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X w := by
  intro D X w k hg hw hew i j
  have hZ : ∀ {c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F}, ZMod' X.B.I X.B.g c → c ∈ wInt X w :=
    fun hc => wInt_of_zmod X k hg hc
  have he : GlobalTheory.Mem.SymFrame.epsW X w = X.bw := by
    unfold GlobalTheory.Mem.SymFrame.epsW; rw [if_pos hw]
  have hr := rank_eq D
  have hp : (j = posB D i) ↔ j.1 = D.R.rS + i.1 := by rw [Fin.ext_iff]; rfl
  have hi := i.2
  unfold GlobalTheory.Mem.SymFrame.symVec GlobalTheory.SeeConjRead.flagV
  rw [he]
  by_cases h1 : j.1 < D.R.rS
  · rw [dite_eq_left h1, if_neg (by rw [hp]; omega), sub_zero]
    apply hZ
    rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_symm]
    exact Formalism.L2.SG.Pf.unitaryCongruence.Z_sig X.B.I X.B.g ((X.weightVectorsIntegral i).2.2 _).2.2.1
  rw [dite_eq_right h1]
  by_cases h2 : j.1 < D.R.rS + D.R.k
  · rw [dite_eq_left h2]
    have hd := X.bw_dual i ⟨j.1 - D.R.rS, by omega⟩
    by_cases hl : j.1 = D.R.rS + i.1
    · rw [if_pos (hp.2 hl)]
      rw [if_pos (Fin.ext (by simp only; omega))] at hd
      have := sub_mem (hZ hd) hew
      convert this using 1
      ring
    · rw [if_neg (fun h => hl (hp.1 h))]
      rw [if_neg (fun h => hl (by have := congrArg Fin.val h; simp only at this; omega))] at hd
      simpa using hZ hd
  rw [dite_eq_right h2]
  by_cases h4 : j.1 = D.R.rS + D.R.k
  · rw [dite_eq_left h4, if_neg (by rw [hp]; omega), sub_zero]
    apply hZ
    rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_symm]
    exact Formalism.L2.SG.Pf.unitaryCongruence.Z_sig X.B.I X.B.g (X.weightVectorsIntegral i).2.1
  rw [dite_eq_right h4]
  by_cases h3 : j.1 < 2 * D.R.rS + D.R.k + 1
  · rw [dite_eq_left h3, if_neg (by rw [hp]; omega), sub_zero]
    apply hZ
    rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_symm]
    exact Formalism.L2.SG.Pf.unitaryCongruence.Z_sig X.B.I X.B.g ((X.weightVectorsIntegral i).2.2 _).2.2.2
  · rw [dite_eq_right h3, if_neg (by rw [hp]; omega), sub_zero, hA_zero_right']
    exact zero_mem _

end GlobalTheory.Mem.SymChar.Resid
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.FullDt

theorem adAt_eq_one_of_prV {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) {z : AfE F E}
    (hz : Formalism.UG.prV (E := E) (P.under (𝓞 F)) z = 1) : adAt F P z = 1 := by
  set v := P.under (𝓞 F)
  have h1 : Formalism.UG.P.afsplitEps E v * z = Formalism.UG.P.afsplitEps E v := by
    rw [← Formalism.UG.P.afsplit_decomp, hz]
    rfl
  have h2 : Formalism.UG.P.afsplitEps E v = (1 : E) ⊗ₜ[F] Formalism.UG.P.afsplitI v (1 : v.adicCompletion F) := by
    rw [Formalism.UG.P.afsplitEps, Algebra.TensorProduct.one_def, Formalism.UG.P.afsplitIE_tmul]
  have h3 : adAt F P (Formalism.UG.P.afsplitEps E v) = 1 := by
    rw [h2, adAt_apply, GlobalTheory.Mem.ReadTwist.afIso_one_tmul (k := 1)]
    · simp
    · rw [Formalism.UG.P.afsplitI_self]; simp
  have h4 := congrArg (adAt F P) h1
  rwa [map_mul, h3, one_mul] at h4

theorem detPt_eq_u1Dt_of_level : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (n : ℕ) (ST SG Q SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (p : DecoF H.E n ST SG Q) (y k : GL (Fin n) (AfE H.F H.E)) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)), LevOk H SG SQ → IsPtOf (host_cmData R H) (y * k) (extTo SQ p) → k ∈ Formalism.L2.Herm.UstdAf (host_cmData R H) n → Formalism.L2.Herm.Carries k (stdLat H.E n) (stdLat H.E n) → (∀ P ∈ uSG SG SQ, Formalism.UG.bc (Formalism.UG.prV (E := H.E) (P.under (𝓞 H.F))) k = 1) → Matrix.GeneralLinearGroup.det x.1 = Matrix.GeneralLinearGroup.det y → detPt H SQ p = u1Dt H SQ x := by
  intro R H n ST SG Q SQ p y k x hl hp hk hc hbc hx
  obtain ⟨a, ha⟩ := exists_lift H x
  obtain ⟨b, hb⟩ := DetLift.exists_isDetLift R H n k hk
  have hab : IsDetLift (host_cmData R H) (y * k) (a * b) := by
    unfold IsDetLift at ha hb ⊢
    rw [map_mul, map_mul, ha, hb, hx, map_mul]
  have hK : b ∈ KDq H SQ := by
    refine mem_KDq_of_conj hl b (fun w => ?_) fun P hP => ?_
    · rw [DetSpec.val_compAt_eq hb ⟨stdLat_lattice, stdLat_unimodular⟩ hc (fr := fun _ => LinearEquiv.refl _ _)
        (fun _ _ => Iff.rfl) w]
      simp
    · have hdet : adAt H.F P (k : Matrix (Fin n) (Fin n) (AfE H.F H.E)).det = 1 := by
        refine adAt_eq_one_of_prV P ?_
        have h := congrArg (fun g => Matrix.det (Units.val g)) (hbc P hP)
        simp only [Formalism.UG.bc, Units.coe_map, Units.val_one, Matrix.det_one] at h
        rw [RingHom.map_det]
        exact h
      have hs0 : adAt H.F P (Formalism.UG.sigR (host_cmData R H).sig _ (finAf H.F H.E b : AfE H.F H.E)) ≠ 0 :=
        (((Units.isUnit (finAf H.F H.E b)).map (Formalism.UG.sigR (host_cmData R H).sig _)).map (adAt H.F P)).ne_zero
      rw [DetSpec.compAt_eq hb P, hdet, one_mul, div_self hs0, sub_self, map_zero]
      exact zero_lt_one
  rw [normOneFiniteAdeleDetClass_of_isDetLift H SQ x a ha, ← DetSpec.mk_eq_detPt R H n ST SG Q SQ p (y * k) (a * b) hl hp hab,
    QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff b).2 hK, mul_one]

end GlobalTheory.Mem.Col2.FullDt
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.FullDt

theorem e1Q_eq_u1Dt_of_det_eq : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (z : unitary H.E) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)), Matrix.GeneralLinearGroup.det x.1 = Formalism.L2.Herm.unitaryOneRationalAdele H.F z → e1Q H SQ z = u1Dt H SQ x := by
  intro R H SQ z x hx
  obtain ⟨k, hk⟩ := exists_eq_div_conj H z
  rw [← isUnitaryPointsMap_unitaryRationalPointsFiner H SQ k z hk]
  symm
  apply normOneFiniteAdeleDetClass_of_isDetLift
  unfold IsDetLift
  rw [hx]
  have hf : finAf H.F H.E (Neutral.B1.diagUnits H.E k) = Units.map (Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F)).toMonoidHom k := by
    apply Units.ext
    apply (afIso H.F H.E).injective
    rw [afIso_finAf]
    show _ = afIso H.F H.E ((k : H.E) ⊗ₜ[H.F] 1)
    rw [afIso_tmul_one]
    rfl
  rw [hf]
  have key : Formalism.L2.Herm.unitaryOneRationalAdele H.F z * conjId (host_cmData R H).sig
      (Units.map (Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F)).toMonoidHom k) =
      Units.map (Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F)).toMonoidHom k := by
    apply Units.ext
    show Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F) (z : H.E) *
      Formalism.UG.sigR (host_cmData R H).sig _ (Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F) (k : H.E)) =
      Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F) (k : H.E)
    rw [sigR_inclE, ← map_mul, bridge_star_holds R H, hk]
  rw [h90, MonoidHom.div_apply, MonoidHom.id_apply, div_eq_iff_eq_mul]
  exact key.symm

end GlobalTheory.Mem.Col2.FullDt
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.HeckeLocN




theorem psiInt_of_embW : ∀ (D : D7) (C : NChoice D) (X : CoefIn D.what₂) (ψ0 : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)), (∀ w g, C.embW w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL) = algebraMap (C.Oe w) (FractionRing (C.Oe w)) (algebraMap (D.ntw.Ok (C.twI w) (C.k' w)) (C.Oe w) ((C.psi' w (D.ntw.art (C.twI w) (C.Q w) g) : (D.ntw.Ok (C.twI w) (C.k' w))ˣ) : D.ntw.Ok (C.twI w) (C.k' w)))) → PsiInt X ψ0 := by
  intro D C X ψ0 h j w g
  have hint : ∀ g, ∃ y : OcC X j w, algebraMap (OcC X j w) (FractionRing (OcC X j w)) y =
      ecC X j w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL) := by
    intro g
    have h0 : 0 ≤ D.what₂.places.val w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL) :=
      (C.embW_w w _).2 ⟨_, (h w g).symm⟩
    exact (ecC_w X j w _).1 h0
  obtain ⟨a, ha⟩ := hint g
  obtain ⟨b, hb⟩ := hint g⁻¹
  have hab : a * b = 1 := by
    apply IsFractionRing.injective (OcC X j w) (FractionRing (OcC X j w))
    rw [map_mul, ha, hb, ← map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, map_one, map_one]
  exact ⟨Units.mkOfMulEqOne a b hab, ha⟩

end GlobalTheory.HeckeLocN
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Th

theorem petInt_of_cuspRapidDecay (hP : GlobalTheory.Published.CuspRapidDecay) (D : D7) : PetInt D :=
  fun _ hθ _ μ 𝓕 hq _ _ hψ hφ =>
    GlobalTheory.CuspDecay.integrableOn_star_mul hP GlobalTheory.Mem.VolFin.finVol hθ μ 𝓕 hq.1 hq.2 hψ hφ.1 hφ.2

end GlobalTheory.Mem.Th
end
