module

public import Formalism.PeriodIntegrals.Bundle032
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.IsLoUniConjTranspose
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.CoefXOfMemXS
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
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
import Formalism.PeriodIntegrals.Bundle030

@[expose] public section

section

noncomputable section

open scoped Classical

namespace PI.NRCW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.PairValDefs Matrix IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem normRepMove_of_steps (D : D7) (u u' : D.what₂.Word) (hE : TermEqIff D u u')
    (h1 : StepExp D) (h2 : StepGram D) (h3 : StepGlob D) (h4 : StepLoc D) (h5 : StepTr D) :
    PI.NormRepChange.NormRepMove D u u' := by
  intro F0 Λ hΛ t _hrel F₁ F₂ hR1 hA1 hR2 hA2 w _hw
  obtain ⟨p1, e1⟩ := hR1
  obtain ⟨p2, e2⟩ := hR2
  have hDC : DCRel Λ (lf D F0) F₁ F₂ :=
    ((hE F0 Λ hΛ) ⟨F₁, p1⟩ ⟨F₂, p2⟩).mp (e1.trans e2.symm)
  obtain ⟨n, hn, m, hm, hfr, -⟩ := hDC
  obtain ⟨hNu, hNe⟩ := h1 Λ (lf D F0) n hn
  obtain ⟨hMu, hMe⟩ := h1 Λ F₁ m hm
  have hG := h2 (lf D F0) F₁ F₂ n m (fmat D (lf D F0) n) (fmat D F₁ m) hn.1.1 hNe hMe hfr
  obtain ⟨A, B, hA, hB, hZ, hs⟩ := core_Z _ _ _ _ hNu hMu hG
  refine ⟨A, B, hA, hB, hZ, ?_⟩
  rw [hs]
  obtain ⟨_, ⟨_, _, hLift0, hConv0⟩, hXS0⟩ := hΛ
  obtain ⟨hLift1, _, hConv1, hXS1⟩ := p1
  have hglob : ∀ δ ∈ ddS D, ∃ o : 𝓞 D.host.E,
      (o : D.host.E) = (sgUp (fmat D (lf D F0) n) + sgUp (fmat D F₁ m)) * δ := by
    intro δ hδ
    obtain ⟨o1, ho1⟩ := h3 Λ (lf D F0) n hn hXS0 hLift0.1 δ hδ
    obtain ⟨o2, ho2⟩ := h3 Λ F₁ m hm hXS1 hLift1.1 δ hδ
    exact ⟨o1 + o2, by rw [add_mul, ← ho1, ← ho2]; norm_cast⟩
  have hloc := h4 Λ (lf D F0) F₁ F₂ n m hn hm hfr hConv0 hConv1 hA1 hA2 hLift0.1 hLift1.1
  obtain ⟨k, hk⟩ := h5 _ hglob hloc
  exact psiInf_of_trace (gS D) _ _ k hk

end PI.NRCW
end
end

section

noncomputable section

open scoped Classical

namespace PI.NRCW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat PI.PairValDefs IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gS_ne_zero (D : D7) : gS D ≠ 0 := by
  show D.host.g 0 * D.host.g 1 ≠ 0
  exact mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero

theorem coe_algebraMap_OF (D : D7) (δ : 𝓞 D.host.F) :
    ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) δ : 𝓞 D.host.E) : D.host.E) =
      algebraMap D.host.F D.host.E (δ : D.host.F) := rfl

theorem trace_int_of_mul_dd (D : D7) (x : D.host.E)
    (hx : ∀ δ ∈ ddS D, ∃ o : 𝓞 D.host.E, (o : D.host.E) = x * δ) :
    ∃ k : ℤ, Algebra.trace ℚ D.host.E x = k := by
  have ha : ∀ δ ∈ differentIdeal ℤ (𝓞 D.host.F),
      ∃ a : 𝓞 D.host.F, (a : D.host.F) = (δ : D.host.F) * Algebra.trace D.host.F D.host.E x := by
    intro δ hδ
    have hmem : algebraMap D.host.F D.host.E (δ : D.host.F) ∈ ddS D := by
      unfold ddS
      rw [FractionalIdeal.mem_coeIdeal]
      exact ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) δ, Ideal.mem_map_of_mem _ hδ, coe_algebraMap_OF D δ⟩
    obtain ⟨o, ho⟩ := hx _ hmem
    have htr : Algebra.trace D.host.F D.host.E (o : D.host.E) = (δ : D.host.F) * Algebra.trace D.host.F D.host.E x := by
      rw [ho, mul_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
    have hint : IsIntegral ℤ (Algebra.trace D.host.F D.host.E (o : D.host.E)) :=
      Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe o)
    rw [htr] at hint
    exact ⟨⟨_, hint⟩, rfl⟩
  have hdual : Algebra.trace D.host.F D.host.E x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) := by
    rw [← inv_inv (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F)), ← coeIdeal_differentIdeal ℤ ℚ D.host.F,
      FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.mpr differentIdeal_ne_bot)]
    intro y hy
    obtain ⟨y', hy', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
    obtain ⟨a, ha'⟩ := ha y' hy'
    rw [FractionalIdeal.mem_one_iff]
    exact ⟨a, by rw [mul_comm]; exact ha'⟩
  rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) ≠ 0)] at hdual
  obtain ⟨k, hk⟩ := hdual 1 (FractionalIdeal.one_mem_one _)
  refine ⟨k, ?_⟩
  have h1 : Algebra.traceForm ℚ D.host.F (Algebra.trace D.host.F D.host.E x) 1 = Algebra.trace ℚ D.host.F (Algebra.trace D.host.F D.host.E x) := by
    rw [Algebra.traceForm_apply, mul_one]
  rw [← Algebra.trace_trace (S := D.host.F), ← h1, ← hk]
  simp

theorem stepTr (D : D7) : StepTr D := by
  intro y hy hP
  have hg0 : (gS D : D.host.E) ≠ 0 := by exact_mod_cast gS_ne_zero D
  have hint : ∀ δ ∈ ddS D, ∃ o : 𝓞 D.host.E, (o : D.host.E) = y / (gS D : D.host.E) * δ := by
    intro δ hδ
    obtain ⟨o, ho⟩ := hy δ hδ
    have hδint : ∃ d' : 𝓞 D.host.E, (d' : D.host.E) = δ := by
      unfold ddS at hδ
      obtain ⟨d', -, hd'⟩ := (FractionalIdeal.mem_coeIdeal _).mp hδ
      exact ⟨d', hd'⟩
    obtain ⟨d', rfl⟩ := hδint
    have hval : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
        P.valuation D.host.E (y / (gS D : D.host.E) * d') ≤ 1 := by
      intro P
      by_cases hPg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
      · rw [map_mul]
        exact mul_le_one' (hP P hPg) (P.valuation_le_one d')
      · have h1 : P.valuation D.host.E ((gS D : ℕ) : D.host.E) = 1 := by
          have h2 := (P.valuation_eq_one_iff_notMem (K := D.host.E)).mpr hPg
          simpa using h2
        have e : y / (gS D : D.host.E) * d' = (y * d') / (gS D : D.host.E) := by ring
        rw [e, map_div₀, h1, div_one, ← ho]
        exact P.valuation_le_one o
    obtain ⟨o', ho'⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (h := hval)
    exact ⟨o', ho'⟩
  obtain ⟨k, hk⟩ := trace_int_of_mul_dd D (y / (gS D : D.host.E)) hint
  refine ⟨k, ?_⟩
  have e : y = ((gS D : ℚ)) • (y / (gS D : D.host.E)) := by
    rw [Algebra.smul_def, map_natCast]
    field_simp
  rw [e, LinearMap.map_smul, hk, smul_eq_mul]

end PI.NRCW
end
end

section

noncomputable section

open scoped Classical

namespace PI.NRCW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.PairValDefs Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stepGram (D : D7) : StepGram D := by
  intro T T' G G₁ G₂ n m N M hn hN hM hG
  unfold ZhatL Zhat brS frame at *
  have hiso : ∀ x y, (VS D).hT (n x) (n y) = (VS D).hT x y := hn
  funext a b

  have hL : ∑ c, star (N c a) * (VS D).hT (G.fl.fvec c) (G₂.fl.fvec b) =
      (VS D).hT (n (G.fl.fvec a)) (G₂.fl.fvec b) := by
    rw [hN a]

    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
    smul_eq_mul, starRingEnd_apply]
  have hR : ∑ c, (VS D).hT (G.fl.fvec a) (G₁.fl.fvec c) * M c b =
      (VS D).hT (G.fl.fvec a) (m (G₁.fl.fvec b)) := by
    rw [hM b]

    simp only [map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  change ∑ c, star (N c a) * (VS D).hT (G.fl.fvec c) (G₂.fl.fvec b) =
    ∑ c, (VS D).hT (G.fl.fvec a) (G₁.fl.fvec c) * M c b
  rw [hL, hR, hG b, hiso]

end PI.NRCW
end
end

section

noncomputable section

open scoped Classical

namespace PI.NRCW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat PI.PairValDefs IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section IntP

variable {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E))

def IntP (x : D.host.E) : Prop :=
  ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 D.host.E, (s : D.host.E) * x = o

theorem one_not_mem_P : (1 : 𝓞 D.host.E) ∉ P.asIdeal :=
  fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)

theorem mul_not_mem_P {s t : 𝓞 D.host.E} (hs : s ∉ P.asIdeal) (ht : t ∉ P.asIdeal) : s * t ∉ P.asIdeal :=
  fun h => (P.isPrime.mem_or_mem h).elim hs ht

theorem intP_O (o : 𝓞 D.host.E) : IntP P (o : D.host.E) := ⟨1, one_not_mem_P P, o, by simp⟩

theorem intP_add {x y : D.host.E} (hx : IntP P x) (hy : IntP P y) : IntP P (x + y) := by
  obtain ⟨s1, hs1, o1, h1⟩ := hx
  obtain ⟨s2, hs2, o2, h2⟩ := hy
  refine ⟨s1 * s2, mul_not_mem_P P hs1 hs2, o1 * s2 + o2 * s1, ?_⟩
  push_cast
  linear_combination (s2 : D.host.E) * h1 + (s1 : D.host.E) * h2

theorem intP_sum {ι : Type*} (s : Finset ι) (f : ι → D.host.E) (h : ∀ i ∈ s, IntP P (f i)) :
    IntP P (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using intP_O P 0
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact intP_add P (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem valuation_le_one_of_isIntegralAt {x : D.host.E} (hx : IntP P x) : P.valuation D.host.E x ≤ 1 := by
  obtain ⟨s, hs, o, h⟩ := hx
  have e1 : algebraMap (𝓞 D.host.E) D.host.E s = (s : D.host.E) := rfl
  have e2 : algebraMap (𝓞 D.host.E) D.host.E o = (o : D.host.E) := rfl
  have := congrArg (P.valuation D.host.E) h
  rw [map_mul, ← e1, ← e2, P.valuation_of_algebraMap, P.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_one_iff.mpr hs, one_mul] at this
  rw [this]
  exact P.intValuation_le_one o

end IntP

section Loc

variable {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E))

def LP (L : Submodule (𝓞 D.host.E) (VS D).V) : Submodule (𝓞 D.host.E) (VS D).V :=
  haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal L

theorem mem_LP {L : Submodule (𝓞 D.host.E) (VS D).V} {x : (VS D).V} :
    x ∈ LP P L ↔ ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ s • x ∈ L := by
  unfold LP Formalism.HermitianLatticesTheory.localization₂ Formalism.HermitianLatticesTheory.locS
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]
  rfl

theorem smul_eq_E (o : 𝓞 D.host.E) (v : (VS D).V) : o • v = (o : D.host.E) • v :=
  (algebraMap_smul D.host.E o v).symm

theorem mem_localization_of_mem₃ {L : Submodule (𝓞 D.host.E) (VS D).V} {x : (VS D).V} (hx : x ∈ L) : x ∈ LP P L :=
  (mem_LP P).mpr ⟨1, one_not_mem_P P, by rw [one_smul]; exact hx⟩

theorem localization_mono₃ {L L' : Submodule (𝓞 D.host.E) (VS D).V} (hle : L ≤ L') {x : (VS D).V} (hx : x ∈ LP P L) :
    x ∈ LP P L' := by
  obtain ⟨s, hs, h⟩ := (mem_LP P).mp hx
  exact (mem_LP P).mpr ⟨s, hs, hle h⟩

theorem sub_mem_localization {L : Submodule (𝓞 D.host.E) (VS D).V} {x y : (VS D).V} (hx : x ∈ LP P L) (hy : y ∈ LP P L) :
    x - y ∈ LP P L := sub_mem hx hy

theorem smul_mem_localization {L : Submodule (𝓞 D.host.E) (VS D).V} {c : D.host.E} (hc : IntP P c) {x : (VS D).V}
    (hx : x ∈ LP P L) : c • x ∈ LP P L := by
  obtain ⟨s, hs, o, ho⟩ := hc
  obtain ⟨t, ht, h⟩ := (mem_LP P).mp hx
  refine (mem_LP P).mpr ⟨s * t, mul_not_mem_P P hs ht, ?_⟩
  have : (s * t) • (c • x) = o • (t • x) := by
    rw [smul_eq_E, smul_eq_E o, smul_eq_E t, smul_smul, smul_smul, ← ho]
    push_cast
    ring_nf
  rw [this]
  exact L.smul_mem o h

theorem LP_sum {L : Submodule (𝓞 D.host.E) (VS D).V} {ι : Type*} (s : Finset ι) (f : ι → (VS D).V)
    (h : ∀ i ∈ s, f i ∈ LP P L) : ∑ i ∈ s, f i ∈ LP P L := Submodule.sum_mem _ h

theorem LP_map {L L' : Submodule (𝓞 D.host.E) (VS D).V} (f : (VS D).V →ₗ[D.host.E] (VS D).V)
    (hf : ∀ v ∈ L, f v ∈ L') {x : (VS D).V} (hx : x ∈ LP P L) : f x ∈ LP P L' := by
  obtain ⟨s, hs, h⟩ := (mem_LP P).mp hx
  refine (mem_LP P).mpr ⟨s, hs, ?_⟩
  rw [smul_eq_E, ← f.map_smul, ← smul_eq_E]
  exact hf _ h

theorem mem_gLam {Λ : Submodule (𝓞 D.host.E) (VS D).V} {g : ℕ} {x : (VS D).V} :
    x ∈ Ideal.span {((g : ℕ) : 𝓞 D.host.E)} • Λ ↔ ∃ l ∈ Λ, ((g : ℕ) : D.host.E) • l = x := by
  have hc : (((g : ℕ) : 𝓞 D.host.E) : D.host.E) = ((g : ℕ) : D.host.E) :=
    map_natCast (algebraMap (𝓞 D.host.E) D.host.E) g
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨l, hl, rfl⟩; exact ⟨l, hl, by rw [smul_eq_E, hc]⟩
  · rintro ⟨l, hl, rfl⟩; exact ⟨l, hl, by rw [smul_eq_E, hc]⟩

theorem nlam_gLam {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {G : LFlag (D.sp.Y 0) D.R.rS T}
    {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NLam Λ G) (g : ℕ) :
    ∀ v ∈ Ideal.span {((g : ℕ) : 𝓞 D.host.E)} • Λ, (n : (VS D).V →ₗ[D.host.E] (VS D).V) v ∈
      Ideal.span {((g : ℕ) : 𝓞 D.host.E)} • Λ := by
  intro v hv
  obtain ⟨l, hl, rfl⟩ := mem_gLam.mp hv
  exact mem_gLam.mpr ⟨n l, nlam_mem hn hl, by simp⟩

end Loc

section Coef

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem coefX_of_mem_spanO (F : FlagG S r T) {u : S.V} (hu : u ∈ Submodule.span (𝓞 E) (Set.range F.e)) :
    u ∈ F.X ∧ ∀ a, F.coefX u a ∈ (algebraMap (𝓞 E) E).range := by
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a', rfl⟩ := hy
    refine ⟨e_mem_X F a', fun a => ?_⟩
    rw [coefX_e]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  | zero => exact ⟨zero_mem _, fun a => by rw [coefX_zero]; exact Subring.zero_mem _⟩
  | add v w _ _ hv hw =>
    exact ⟨add_mem hv.1 hw.1, fun a => by rw [coefX_add _ hv.1 hw.1]; exact Subring.add_mem _ (hv.2 a) (hw.2 a)⟩
  | smul o v _ hv =>
    have e : o • v = (algebraMap (𝓞 E) E o) • v := (algebraMap_smul E o v).symm
    refine ⟨by rw [e]; exact Submodule.smul_mem _ _ hv.1, fun a => ?_⟩
    rw [e, coefX_smul _ hv.1]
    exact Subring.mul_mem _ ⟨o, rfl⟩ (hv.2 a)

end Coef

section FixedConv

variable {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E))

theorem fixedConv_at {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {G : LFlag (D.sp.Y 0) D.R.rS T}
    (hC : IsFixedConv Λ (gS D) G) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    LP P (XLam Λ G) = LP P (Submodule.span (𝓞 D.host.E) (Set.range G.fl.e)) := by
  obtain ⟨c, _, hc1, hloc⟩ := hC.1 P
  have hc : (fun a => c a • G.fl.e a) = G.fl.e := funext fun a => by rw [hc1 hP a, one_smul]
  rw [hc] at hloc
  exact hloc

theorem e_mem_LP {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {G : LFlag (D.sp.Y 0) D.R.rS T}
    (hC : IsFixedConv Λ (gS D) G) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) (a : Fin D.R.rS) :
    G.fl.e a ∈ LP P Λ := by
  have h : G.fl.e a ∈ LP P (Submodule.span (𝓞 D.host.E) (Set.range G.fl.e)) :=
    mem_localization_of_mem₃ P (Submodule.subset_span ⟨a, rfl⟩)
  rw [← fixedConv_at P hC hP] at h
  exact localization_mono₃ P (fun v hv => by rw [XLam, Submodule.mem_inf] at hv; exact hv.1) h

theorem coef_intP {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {G : LFlag (D.sp.Y 0) D.R.rS T}
    (hC : IsFixedConv Λ (gS D) G) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) {w : (VS D).V}
    (hw : w ∈ LP P Λ) (hwX : w ∈ G.fl.X) (a : Fin D.R.rS) : IntP P (G.fl.coefX w a) := by
  obtain ⟨s, hs, hsw⟩ := (mem_LP P).mp hw
  have hsX : s • w ∈ G.fl.X := by rw [smul_eq_E]; exact Submodule.smul_mem _ _ hwX
  have h1 : s • w ∈ LP P (XLam Λ G) := mem_localization_of_mem₃ P (by rw [XLam, Submodule.mem_inf]; exact ⟨hsw, hsX⟩)
  rw [fixedConv_at P hC hP] at h1
  obtain ⟨t, ht, h2⟩ := (mem_LP P).mp h1
  obtain ⟨-, h3⟩ := coefX_of_mem_spanO G.fl h2
  obtain ⟨o, ho⟩ := h3 a
  refine ⟨t * s, mul_not_mem_P P ht hs, o, ?_⟩
  rw [smul_eq_E, smul_eq_E, coefX_smul _ (Submodule.smul_mem _ _ hwX), coefX_smul _ hwX] at ho
  have e2 : algebraMap (𝓞 D.host.E) D.host.E o = (o : D.host.E) := rfl
  rw [← e2, ho]
  push_cast
  ring

theorem coef_intP_g {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {G : LFlag (D.sp.Y 0) D.R.rS T}
    (hC : IsFixedConv Λ (gS D) G) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal)
    (hg : ((gS D : ℕ) : D.host.E) ≠ 0) {Y : (VS D).V}
    (hY : Y ∈ LP P (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ)) (hYX : Y ∈ G.fl.X) (a : Fin D.R.rS) :
    IntP P (G.fl.coefX Y a / (gS D : D.host.E)) := by
  obtain ⟨s, hs, hsY⟩ := (mem_LP P).mp hY
  obtain ⟨l, hl, hlY⟩ := mem_gLam.mp hsY
  have hl' : l = ((s : D.host.E) / (gS D : D.host.E)) • Y := by
    rw [smul_eq_E] at hlY
    rw [div_eq_mul_inv, mul_comm, ← smul_smul, ← hlY, smul_smul, inv_mul_cancel₀ hg, one_smul]
  have hlX : l ∈ G.fl.X := by rw [hl']; exact Submodule.smul_mem _ _ hYX
  obtain ⟨t, ht, o, ho⟩ := coef_intP P hC hP (mem_localization_of_mem₃ P hl) hlX a
  refine ⟨t * s, mul_not_mem_P P ht hs, o, ?_⟩
  rw [hl', coefX_smul _ hYX] at ho
  rw [← ho]
  push_cast
  ring

end FixedConv

end PI.NRCW
end
end
