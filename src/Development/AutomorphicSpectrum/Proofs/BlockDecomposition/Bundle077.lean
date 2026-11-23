module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.VecClose
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle046
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle047
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory Topology
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KerVec

theorem ker_mul_right {G : Type} [Group G] (Γ : Subgroup G) (φ : G → ℂ) (z y w : G) :
    ker Γ (fun g => φ (g * w)) z y = ker Γ φ z (y * w) := by
  simp only [ker, mul_assoc]

theorem tst_mul_right {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {φ : G → ℂ} (h : Tst φ) (w : G) : Tst (fun g => φ (g * w)) :=
  ⟨h.1.comp (continuous_mul_const w), h.2.comp_homeomorph (Homeomorph.mulRight w)⟩

theorem continuousAt_of_sq_bound {G E : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SeminormedAddCommGroup E] (f : G → E) (y₀ : G) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ w in 𝓝 (1 : G),
      ‖f (y₀ * w) - f y₀‖ₑ ^ 2 ≤ c * ENNReal.ofReal ε ^ 2) : ContinuousAt f y₀ := by
  rw [ContinuousAt, ← map_mul_left_nhds_one y₀, Filter.tendsto_map'_iff, Metric.tendsto_nhds]
  intro ε hε
  have hc0 : 0 ≤ c.toReal := ENNReal.toReal_nonneg
  have hε' : 0 < ε / (c.toReal + 1) := by positivity
  filter_upwards [h _ hε'] with w hw
  have hb : ‖f (y₀ * w) - f y₀‖ ^ 2 ≤ c.toReal * (ε / (c.toReal + 1)) ^ 2 := by
    have hr : ENNReal.ofReal (‖f (y₀ * w) - f y₀‖ ^ 2) ≤
        ENNReal.ofReal (c.toReal * (ε / (c.toReal + 1)) ^ 2) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_mul hc0,
        ENNReal.ofReal_pow hε'.le, ENNReal.ofReal_toReal hc, ofReal_norm]
      exact hw
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hr
  have hlt : c.toReal * (ε / (c.toReal + 1)) ^ 2 < ε ^ 2 := by
    have hd : 0 < (c.toReal + 1) ^ 2 := by positivity
    rw [div_pow, ← mul_div_assoc, div_lt_iff₀ hd]
    have : 0 < ε ^ 2 := by positivity
    nlinarith [mul_nonneg hc0 hc0, mul_nonneg hc0 this.le, mul_nonneg (mul_nonneg hc0 hc0) this.le]
  show dist (f ((fun x => y₀ * x) w)) (f y₀) < ε
  rw [dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le (hb.trans_lt hlt)

theorem vecEx : CntBasic → KernelL2RowsColumns → TwoUnif → VecClose → VecEx := by
  intro hC hL hT hV X ι _ Φ hΦ
  let k : X.G → ι → X.Hs ι := fun y j =>
    WithLp.toLp 2 fun l => ((hL X (Φ l j) (hΦ l j)).1 y).toLp _
  have hk : ∀ y j, X.IsVec Φ y j (k y j) := fun y j l =>
    ((hL X (Φ l j) (hΦ l j)).1 y).coeFn_toLp
  refine ⟨k, fun j => continuous_iff_continuousAt.2 fun y₀ => ?_, hk⟩
  obtain ⟨N, hNc, hN1⟩ := exists_compact_mem_nhds (1 : X.G)
  have h1N : (1 : X.G) ∈ N := mem_of_mem_nhds hN1
  have hS : IsCompact (⋃ l, tsupport (Φ l j)) := isCompact_iUnion fun l => (hΦ l j).2
  obtain ⟨Ω, hΩdef⟩ : ∃ Ω : Set X.G, Ω = (⋃ l, tsupport (Φ l j)) * N⁻¹ := ⟨_, rfl⟩
  have hΩ : IsCompact Ω := hΩdef ▸ hS.mul hNc.inv
  have hsub : ∀ (l : ι) (w : X.G), w ∈ N → Function.support (fun g => Φ l j (g * w)) ⊆ Ω := by
    intro l w hw g hg
    rw [hΩdef]
    have h1 : g * w ∈ ⋃ l, tsupport (Φ l j) :=
      Set.mem_iUnion.2 ⟨l, subset_tsupport _ hg⟩
    have h2 : w⁻¹ ∈ N⁻¹ := Set.inv_mem_inv.2 hw
    simpa using Set.mul_mem_mul h1 h2
  have hc : (Fintype.card ι : ℝ≥0∞) * (X.μ Ω⁻¹ * cnt X.Γ (Ω⁻¹ * Ω) y₀) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top hΩ.inv.measure_lt_top.ne
      ((hC X).1 _ (hΩ.inv.mul hΩ) y₀))
  refine continuousAt_of_sq_bound (fun y => k y j) y₀ _ hc fun ε hε => ?_
  choose W hW hW' using fun l => hT X (Φ l j) ε (hΦ l j) hε
  filter_upwards [hN1, Filter.eventually_all.2 hW] with w hwN hwW
  have hv : X.IsVec (fun l i g => Φ l i (g * w)) y₀ j (k (y₀ * w) j) := fun l =>
    (hk (y₀ * w) j l).trans (Filter.Eventually.of_forall fun z => (ker_mul_right X.Γ (Φ l j) z y₀ w).symm)
  have key := hV X ι (fun l i g => Φ l i (g * w)) Φ Ω ε y₀ j _ _ hΩ
    (fun l => ⟨tst_mul_right (hΦ l j) w, hΦ l j, hsub l w hwN,
      by simpa using hsub l 1 h1N, fun z => by
        simpa using hW' l 1 (mem_of_mem_nhds (hW l)) w (hwW l) z⟩) hv (hk y₀ j)
  refine key.trans (le_of_eq ?_)
  ring

end GlobalTheory.CompanionTheory.KerVec

end
end

section

noncomputable section

open PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisPar

variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R]

theorem continuous_circle_coe : Continuous (fun z : Circle => (z : ℂ)) := by
  first | fun_prop | exact continuous_subtype_val | exact continuous_induced_dom

theorem stab_univ_eq_top {κ : Type} [Fintype κ] [DecidableEq κ] : stab R (Set.univ : Set κ) = ⊤ := by
  refine eq_top_iff.2 fun g _ r hr => ?_
  exact absurd (Set.mem_univ r) hr

theorem isCh_of_top {G : Type} [Group G] [TopologicalSpace G] {Γ P : Subgroup G} {c : G → ℂ} (h : IsCh Γ ⊤ c) : IsCh Γ P c := by
  exact ⟨fun p _ q _ => h.mul p (Subgroup.mem_top p) q (Subgroup.mem_top q),
    fun p _ => h.norm p (Subgroup.mem_top p),
    fun γ hγ _ => h.rat γ hγ (Subgroup.mem_top γ),
    h.cont.mono fun x _ => Subgroup.mem_top x⟩

theorem isCh_cGL (hB : BdetLaw) (A : Ad E R) (hA : A.GoodL) (κ : Type) [Fintype κ] [DecidableEq κ] :
    IsCh (A.ratGL κ) ⊤ (A.cGL κ) := by
  obtain ⟨-, hm, hcont, hr, -, hd⟩ := hB E R A hA κ Set.univ
  have htop : ∀ g : GL κ R, g ∈ stab R (Set.univ : Set κ) := fun g => by
    rw [stab_univ_eq_top]; trivial
  have hc : ∀ g : GL κ R, A.cGL κ g = A.χ (bdet Set.univ g) := fun g => by
    rw [hd]; rfl
  refine ⟨fun p _ q _ => ?_, fun p _ => ?_, fun γ hγ _ => ?_, ?_⟩
  · rw [hc, hc, hc, hm p (htop p) q (htop q), map_mul, Circle.coe_mul]
  · rw [hc]; exact Circle.norm_coe _
  · obtain ⟨x, hx⟩ := hr γ (htop γ) hγ
    rw [hc, hx, hA.χi, Circle.coe_one]
  · have hcon : Continuous (bdet (R := R) (Set.univ : Set κ)) := by
      rw [← continuousOn_univ]
      refine hcont.mono fun g _ => htop g
    have : A.cGL κ = fun g => ((A.χ (bdet Set.univ g) : Circle) : ℂ) := funext hc
    rw [this]
    exact (continuous_circle_coe.comp (hA.χcont.comp hcon)).continuousOn

theorem ext_gl (hB : BdetLaw) (hE : ExtLaw) (hT : GrpTop) (A : Ad E R) (hA : A.Good) (κ : Type) [Fintype κ] [DecidableEq κ]
    (t : Set κ) : IsHt (A.ratGL κ) (A.kGL κ) (stab R t) (A.htGL t) ∧
      ∀ p ∈ stab R t, ∀ k ∈ A.kGL κ, A.htGL t (p * k) = A.lg (bdet t p) := by
  obtain ⟨hc, hm, hcont, hr, hk, -⟩ := hB E R A hA.toGoodL κ t
  haveI : T2Space (GL κ R) := (hT E R A hA κ 1).1
  refine hE (GL κ R) (A.ratGL κ) (A.kGL κ) (stab R t) (fun p => A.lg (bdet t p)) (hA.kcpt κ) hc (hA.iwa κ t) ?_ ?_ hk ?_
  · intro p hp q hq
    simp only [hm p hp q hq, hA.lgmul]
  · exact hA.lgcont.comp_continuousOn hcont
  · intro p hp hg
    obtain ⟨x, hx⟩ := hr p hp hg
    simp only [hx, hA.lgi x]

theorem closed_uQ (hB : BdetLaw) (A : Ad E R) (hA : A.GoodL) (ε : ℤˣ) {κ : Type} [Fintype κ] [DecidableEq κ] (t : Set κ) :
    IsClosed (A.uQ ε t : Set (A.U ε κ)) :=
  (hB E R A hA (κ ⊕ κ) (Sum.inl '' t)).1.preimage continuous_subtype_val

theorem ext_u (hB : BdetLaw) (hE : ExtLaw) (hT : GrpTop) (A : Ad E R) (hA : A.Good) (ε : ℤˣ) {κ : Type} [Fintype κ]
    [DecidableEq κ] (t : Set κ) (hI : Iwa (A.uQ ε t) (A.uK ε κ)) :
    IsHt (A.uΓ ε κ) (A.uK ε κ) (A.uQ ε t) (A.uH ε t) ∧
      ∀ p ∈ A.uQ ε t, ∀ k ∈ A.uK ε κ, A.uH ε t (p * k) = A.lg (bdet (Sum.inl '' t) p.1) := by
  obtain ⟨-, hm, hcont, hr, hk, -⟩ := hB E R A hA.toGoodL (κ ⊕ κ) (Sum.inl '' t)
  obtain ⟨-, -, -, h2, -, -, hK⟩ := hT E R A hA κ ε
  haveI := h2
  refine hE (A.U ε κ) (A.uΓ ε κ) (A.uK ε κ) (A.uQ ε t) (fun p => A.lg (bdet (Sum.inl '' t) p.1)) hK
    (closed_uQ hB A hA.toGoodL ε t) hI ?_ ?_ ?_ ?_
  · intro p hp q hq
    simp only [Subgroup.coe_mul, hm p.1 hp q.1 hq, hA.lgmul]
  · exact hA.lgcont.comp_continuousOn (hcont.comp continuous_subtype_val.continuousOn fun x hx => hx)
  · exact fun p hp hpk => hk p.1 hp hpk
  · intro p hp hg
    obtain ⟨x, hx⟩ := hr p.1 hp hg
    simp only [hx, hA.lgi x]

theorem isCh_uC (hB : BdetLaw) (A : Ad E R) (hA : A.GoodL) (ε : ℤˣ) {κ : Type} [Fintype κ] [DecidableEq κ] :
    IsCh (A.uΓ ε κ) (A.uQ ε (Set.univ : Set κ)) (A.uC ε κ) := by
  obtain ⟨-, hm, hcont, hr, -, -⟩ := hB E R A hA (κ ⊕ κ) (Sum.inl '' (Set.univ : Set κ))
  refine ⟨fun p hp q hq => ?_, fun p _ => Circle.norm_coe _, fun γ hγ hp => ?_, ?_⟩
  · simp only [Ad.uC, Subgroup.coe_mul, hm p.1 hp q.1 hq, map_mul, Circle.coe_mul]
  · obtain ⟨x, hx⟩ := hr γ.1 hp hγ
    simp only [Ad.uC, hx, hA.χi, Circle.coe_one]
  · exact continuous_circle_coe.comp_continuousOn
      (hA.χcont.comp_continuousOn (hcont.comp continuous_subtype_val.continuousOn fun x hx => hx))

theorem parLaw : BdetLaw → ExtLaw → GrpTop → ParLaw := by
  intro hB hE hT E R _ _ _ _ _ _ _ A hA ι _ _ ε s
  obtain ⟨hc, -⟩ := hB E R A hA.toGoodL ι s
  have hch := isCh_cGL hB A hA.toGoodL ι
  refine ⟨⟨⟨hc, hA.iwa ι s, ?_⟩, ⟨hc, hA.iwa ι s, isCh_of_top hch⟩, hch, (ext_gl hB hE hT A hA ι s).1, stab_univ_eq_top⟩, ?_⟩
  · refine ⟨fun _ _ _ _ => by simp, fun _ _ => by simp, fun _ _ _ => rfl, continuousOn_const⟩
  intro hI
  have hI' : Iwa (A.uQ ε s) (A.uK ε ι) := fun g => by
    obtain ⟨p, hp, k, hk, e⟩ := hI g
    exact ⟨p, hp.1, k, hk, e⟩
  have hu := ext_u hB hE hT A hA ε s hI'
  have hC := isCh_uC hB A hA.toGoodL (ε := ε) (κ := ι)
  refine ⟨⟨(closed_uQ hB A hA.toGoodL ε s).inter (closed_uQ hB A hA.toGoodL ε Set.univ), hI, ?_⟩, hu.1, fun g => ?_⟩
  · exact ⟨fun p hp q hq => hC.mul p hp.2 q hq.2, fun p hp => hC.norm p hp.2, fun γ hγ hp => hC.rat γ hγ hp.2,
      hC.cont.mono fun _ h => h.2⟩
  · obtain ⟨p, hp, k, hk, rfl⟩ := hI' g
    rw [hu.2 p hp k hk]
    exact ((ext_gl hB hE hT A hA (ι ⊕ ι) (Sum.inl '' s)).2 p.1 hp k.1 hk).symm

end GlobalTheory.CompanionTheory.RgEisPar
end
end

section

noncomputable section

open PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisExt

variable {G : Type} [Group G]

theorem ext_mul {K P : Subgroup G} {f : G → ℝ} (hadd : ∀ p ∈ P, ∀ q ∈ P, f (p * q) = f p + f q)
    (hfK : ∀ p ∈ P, p ∈ K → f p = 0) {p k : G} (hp : p ∈ P) (hk : k ∈ K) :
    PositivityTheory.RgEis.ext K P f (p * k) = f p := by
  have hex : ∃ c : K, p * k * (c : G)⁻¹ ∈ P := ⟨⟨k, hk⟩, by simpa using hp⟩
  rw [PositivityTheory.RgEis.ext, dite_eq_left hex]
  have hcP : p * k * (hex.choose : G)⁻¹ ∈ P := hex.choose_spec
  have hq : p⁻¹ * (p * k * (hex.choose : G)⁻¹) ∈ P := P.mul_mem (P.inv_mem hp) hcP
  have hqK : p⁻¹ * (p * k * (hex.choose : G)⁻¹) ∈ K := by
    have he : p⁻¹ * (p * k * (hex.choose : G)⁻¹) = k * (hex.choose : G)⁻¹ := by group
    rw [he]
    exact K.mul_mem hk (K.inv_mem hex.choose.2)
  have h0 := hfK _ hq hqK
  have hsplit := hadd p hp _ hq
  rw [mul_inv_cancel_left] at hsplit
  rw [hsplit, h0, add_zero]

theorem extLaw : ExtLaw := by
  intro G _ _ _ _ Γ K P f hK hP hIwa hadd hfc hfK hfΓ
  have hval : ∀ p ∈ P, ∀ k ∈ K, PositivityTheory.RgEis.ext K P f (p * k) = f p :=
    fun p hp k hk => ext_mul hadd hfK hp hk
  have hone : ∀ p ∈ P, PositivityTheory.RgEis.ext K P f p = f p := by
    intro p hp
    simpa using hval p hp 1 K.one_mem
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hval⟩
  · intro p hp g
    obtain ⟨q, hq, k, hk, rfl⟩ := hIwa g
    rw [← mul_assoc, hval _ (P.mul_mem hp hq) k hk, hval q hq k hk, hone p hp, hadd p hp q hq]
  · intro g k hk
    obtain ⟨q, hq, k', hk', rfl⟩ := hIwa g
    rw [mul_assoc, hval q hq _ (K.mul_mem hk' hk), hval q hq k' hk']
  · intro γ hγ hγP
    rw [hone γ hγP]
    exact hfΓ γ hγP hγ
  · open Pointwise in
    · rw [continuous_iff_isClosed]
      intro C hC
      have hset : PositivityTheory.RgEis.ext K P f ⁻¹' C = ((P : Set G) ∩ f ⁻¹' C) * (K : Set G) := by
        ext g
        constructor
        · intro hg
          obtain ⟨q, hq, k, hk, rfl⟩ := hIwa g
          have hC' : PositivityTheory.RgEis.ext K P f (q * k) ∈ C := hg
          rw [hval q hq k hk] at hC'
          exact Set.mem_mul.mpr ⟨q, ⟨hq, hC'⟩, k, hk, rfl⟩
        · intro hg
          obtain ⟨q, ⟨hq, hqC⟩, k, hk, rfl⟩ := Set.mem_mul.mp hg
          show PositivityTheory.RgEis.ext K P f (q * k) ∈ C
          rw [hval q hq k hk]
          exact hqC
      rw [hset]
      exact (hfc.preimage_isClosed_of_isClosed hP hC).mul_right_of_isCompact hK

end GlobalTheory.CompanionTheory.RgEisExt
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.RgEis.UnitaryConv

open PositivityTheory.RgEis

variable {G : Type} [Group G]

theorem cos_mk_eq_iff {P Γ : Subgroup G} (a b : Γ) :
    (Quotient.mk (QuotientGroup.rightRel (P.subgroupOf Γ)) a : Cos P Γ) = Quotient.mk _ b ↔
      (b : G) * (a : G)⁻¹ ∈ P := by
  constructor
  · intro h
    have h1 : b * a⁻¹ ∈ P.subgroupOf Γ := QuotientGroup.rightRel_apply.mp (Quotient.exact h)
    simpa using Subgroup.mem_subgroupOf.mp h1
  · intro h
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    apply Subgroup.mem_subgroupOf.mpr
    simpa using h

theorem cos_eq_of_rep {P Γ : Subgroup G} {q q' : Cos P Γ} (h : rep q' * (rep q)⁻¹ ∈ P) : q = q' := by
  have h' := (cos_mk_eq_iff (P := P) (Γ := Γ) (Quotient.out q) (Quotient.out q')).mpr h
  rw [Quotient.out_eq, Quotient.out_eq] at h'
  exact h'

theorem rep_mk {P Γ : Subgroup G} (a : Γ) :
    ∃ p ∈ Γ, p ∈ P ∧ rep (Quotient.mk (QuotientGroup.rightRel (P.subgroupOf Γ)) a : Cos P Γ) = p * a := by
  refine ⟨rep (Quotient.mk _ a : Cos P Γ) * (a : G)⁻¹, ?_, ?_, ?_⟩
  · exact Γ.mul_mem (Quotient.out (Quotient.mk _ a : Cos P Γ)).2 (Γ.inv_mem a.2)
  · exact (cos_mk_eq_iff (P := P) (Γ := Γ) a (Quotient.out (Quotient.mk _ a : Cos P Γ))).mp
      (Quotient.out_eq _).symm
  · exact (inv_mul_cancel_right _ _).symm

theorem conv_comap {G' : Type} [Group G'] (φ : G' →* G) {Γ P : Subgroup G} {Γ' P' : Subgroup G'} {l : G → ℝ}
    (hΓ : ∀ γ ∈ Γ', φ γ ∈ Γ) (hP : ∀ γ ∈ Γ', φ γ ∈ P → γ ∈ P')
    (hl : ∀ γ ∈ Γ, γ ∈ P → ∀ g, l (γ * g) = l g) (hc : Conv Γ P l) :
    Conv Γ' P' fun g => l (φ g) := by
  intro g'
  have hinj : Function.Injective (fun q' : Cos P' Γ' =>
      (Quotient.mk _ ⟨φ (rep q'), hΓ (rep q') (Quotient.out q').2⟩ : Cos P Γ)) := by
    intro q₁ q₂ h
    have h' := (cos_mk_eq_iff (P := P) (Γ := Γ) _ _).mp h
    apply cos_eq_of_rep
    have hmem : rep q₂ * (rep q₁)⁻¹ ∈ Γ' :=
      Γ'.mul_mem (Quotient.out q₂).2 (Γ'.inv_mem (Quotient.out q₁).2)
    refine hP _ hmem ?_
    rw [map_mul, map_inv]
    exact h'
  refine ((hc (φ g')).comp_injective hinj).congr fun q' => ?_
  obtain ⟨p, hpΓ, hpP, hp⟩ := rep_mk (P := P) (Γ := Γ) ⟨φ (rep q'), hΓ (rep q') (Quotient.out q').2⟩
  show Real.exp (l (rep (Quotient.mk _ ⟨φ (rep q'), hΓ (rep q') (Quotient.out q').2⟩ : Cos P Γ) * φ g')) =
    Real.exp (l (φ (rep q' * g')))
  rw [hp, map_mul, mul_assoc, hl p hpΓ hpP]

theorem conv_inf {Γ P₁ P₂ : Subgroup G} {l₁ l₂ : G → ℝ}
    (h₁ : ∀ γ ∈ Γ, γ ∈ P₁ → ∀ g, l₁ (γ * g) = l₁ g) (h₂ : ∀ γ ∈ Γ, γ ∈ P₂ → ∀ g, l₂ (γ * g) = l₂ g)
    (c₁ : Conv Γ P₁ l₁) (c₂ : Conv Γ P₂ l₂) : Conv Γ (P₁ ⊓ P₂) fun g => l₁ g + l₂ g := by
  intro g
  have hinj : Function.Injective (fun q : Cos (P₁ ⊓ P₂) Γ =>
      ((Quotient.mk _ (Quotient.out q) : Cos P₁ Γ), (Quotient.mk _ (Quotient.out q) : Cos P₂ Γ))) := by
    intro q q' h
    have e1 := (cos_mk_eq_iff (P := P₁) (Γ := Γ) _ _).mp (congrArg Prod.fst h)
    have e2 := (cos_mk_eq_iff (P := P₂) (Γ := Γ) _ _).mp (congrArg Prod.snd h)
    exact cos_eq_of_rep (Subgroup.mem_inf.mpr ⟨e1, e2⟩)
  have hprod : Summable fun x : Cos P₁ Γ × Cos P₂ Γ =>
      Real.exp (l₁ (rep x.1 * g)) * Real.exp (l₂ (rep x.2 * g)) := by
    exact Summable.mul_of_nonneg (c₁ g) (c₂ g) (fun _ => (Real.exp_pos _).le)
      (fun _ => (Real.exp_pos _).le)
  refine (hprod.comp_injective hinj).congr fun q => ?_
  obtain ⟨p₁, hp₁Γ, hp₁P, hp₁⟩ := rep_mk (P := P₁) (Γ := Γ) (Quotient.out q)
  obtain ⟨p₂, hp₂Γ, hp₂P, hp₂⟩ := rep_mk (P := P₂) (Γ := Γ) (Quotient.out q)
  show Real.exp (l₁ (rep (Quotient.mk _ (Quotient.out q) : Cos P₁ Γ) * g)) *
      Real.exp (l₂ (rep (Quotient.mk _ (Quotient.out q) : Cos P₂ Γ) * g)) =
    Real.exp (l₁ (rep q * g) + l₂ (rep q * g))
  rw [hp₁, hp₂, mul_assoc, mul_assoc, h₁ p₁ hp₁Γ hp₁P, h₂ p₂ hp₂Γ hp₂P, Real.exp_add]
  rfl

theorem convU_of_parLaw : ParLaw → ConvU := by
  intro hPar E R _ _ _ _ _ _ _ A hA hGr ι _ _ ε s hIwa
  have inv : ∀ {H : Type} [Group H] [TopologicalSpace H] {Γ K P : Subgroup H} {η : H → ℝ} (c : ℝ),
      IsHt Γ K P η → ∀ γ ∈ Γ, γ ∈ P → ∀ g, c * η (γ * g) = c * η g := by
    intro H _ _ Γ K P η c h γ hγ hγP g
    rw [h.left γ hγP g, h.rat γ hγ hγP, zero_add]
  have hconv : ∀ (t : Set ι) (x : ℝ), (∀ g : A.U ε ι, A.uH ε t g = A.htGL (Sum.inl '' t) g.1) →
      IsHt (A.ratGL (ι ⊕ ι)) (A.kGL (ι ⊕ ι)) (stab R (Sum.inl '' t)) (A.htGL (Sum.inl '' t)) →
      Conv (A.ratGL (ι ⊕ ι)) (stab R (Sum.inl '' t)) (fun g => x * A.htGL (Sum.inl '' t) g) →
      Conv (A.uΓ ε ι) (A.uQ ε t) fun g => x * A.uH ε t g := by
    intro t x heq hHt hc
    have h := conv_comap (A.uSub ε ι).subtype (Γ := A.ratGL (ι ⊕ ι)) (P := stab R (Sum.inl '' t))
      (Γ' := A.uΓ ε ι) (P' := A.uQ ε t) (l := fun g => x * A.htGL (Sum.inl '' t) g)
      (fun γ hγ => Subgroup.mem_subgroupOf.mp hγ) (fun γ _ hγ => Subgroup.mem_subgroupOf.mpr hγ)
      (inv x hHt) hc
    have hfun : (fun g : A.U ε ι => x * A.uH ε t g) =
        fun g => x * A.htGL (Sum.inl '' t) ((A.uSub ε ι).subtype g) := by
      funext g
      exact congrArg (fun r => x * r) (heq g)
    rw [hfun]
    exact h
  have hIwaU : Iwa (A.uQ ε (Set.univ : Set ι) ⊓ A.uQ ε Set.univ) (A.uK ε ι) := by
    intro g
    obtain ⟨p, hp, k, hk, hg⟩ := hIwa g
    exact ⟨p, Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hp).2, (Subgroup.mem_inf.mp hp).2⟩, k, hk, hg⟩
  obtain ⟨Rs, hRs⟩ := hGr (ι ⊕ ι) (Sum.inl '' s)
  obtain ⟨Ru, hRu⟩ := hGr (ι ⊕ ι) (Sum.inl '' (Set.univ : Set ι))
  have hs := (hPar E R A hA ι ε s).2 hIwa
  have hu := (hPar E R A hA ι ε Set.univ).2 hIwaU
  have hGs := (hPar E R A hA (ι ⊕ ι) ε (Sum.inl '' s)).1.2.2.2.1
  have hGu := (hPar E R A hA (ι ⊕ ι) ε (Sum.inl '' (Set.univ : Set ι))).1.2.2.2.1
  refine ⟨max Rs Ru, fun y hy => ?_, fun x y hx hy => ?_⟩
  · exact hconv Set.univ y hu.2.2 hGu (hRu y (lt_of_le_of_lt (le_max_right _ _) hy))
  · exact conv_inf (l₁ := fun g => x * A.uH ε s g) (l₂ := fun g => y * A.uH ε Set.univ g)
      (inv x hs.2.1) (inv y hu.2.1)
      (hconv s x hs.2.2 hGs (hRs x (lt_of_le_of_lt (le_max_left _ _) hx)))
      (hconv Set.univ y hu.2.2 hGu (hRu y (lt_of_le_of_lt (le_max_right _ _) hy)))

end GlobalTheory.CompanionTheory.RgEis.UnitaryConv
end
end

section

open Filter Topology

theorem _root_.GlobalTheory.T.coarse_lipschitz_exponential_estimate : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (Γ Δ P P' : Subgroup G) (ξ l₁ l₂ : G → ℝ) (H : ℂ → G → X)
    (a b e₁ e₂ M : ℝ),
    (∀ C : Set G, IsCompact C → ∃ A : ℝ, ∀ g, ∀ u ∈ C, |ξ (g * u) - ξ g| ≤ A) →
    (∀ C : Set G, IsCompact C → ∃ A : ℝ, ∀ g, ∀ u ∈ C, |l₁ (g * u) - l₁ g| ≤ A) →
    (∀ C : Set G, IsCompact C → ∃ A : ℝ, ∀ g, ∀ u ∈ C, |l₂ (g * u) - l₂ g| ≤ A) →
    PositivityTheory.RgEis.Conv Δ P l₁ → PositivityTheory.RgEis.Conv Δ P' l₂ →
    (∀ z : ℂ, b ≤ z.re → z.re ≤ a → ∀ g, ‖H z g‖ ≤ M * (PositivityTheory.RgEis.pos Δ P l₁ g + PositivityTheory.RgEis.pos Δ P' l₂ g)) →
    (∀ g, Summable fun r : PositivityTheory.RgEis.Cos Δ Γ => Real.exp (e₁ * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos Δ P l₁ (PositivityTheory.RgEis.rep r * g)) →
    (∀ g, Summable fun r : PositivityTheory.RgEis.Cos Δ Γ => Real.exp (e₂ * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos Δ P l₁ (PositivityTheory.RgEis.rep r * g)) →
    (∀ g, Summable fun r : PositivityTheory.RgEis.Cos Δ Γ => Real.exp (e₁ * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos Δ P' l₂ (PositivityTheory.RgEis.rep r * g)) →
    (∀ g, Summable fun r : PositivityTheory.RgEis.Cos Δ Γ => Real.exp (e₂ * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos Δ P' l₂ (PositivityTheory.RgEis.rep r * g)) →
    ∀ g : G, ∃ U ∈ 𝓝 g, ∃ u : PositivityTheory.RgEis.Cos Δ Γ → ℝ, Summable u ∧
      ∀ l : ℂ × ℂ, b ≤ l.1.re → l.1.re ≤ a → e₁ ≤ l.2.re → l.2.re ≤ e₂ → ∀ g' ∈ U, ∀ r,
        ‖Complex.exp (l.2 * ξ (PositivityTheory.RgEis.rep r * g')) • H l.1 (PositivityTheory.RgEis.rep r * g')‖ ≤ u r := by
  first | exact @GlobalTheory.CompanionTheory.EisCross.dom | exact GlobalTheory.CompanionTheory.EisCross.dom | (intros; apply GlobalTheory.CompanionTheory.EisCross.dom <;> assumption)
end

section

open Filter Topology

theorem _root_.GlobalTheory.T.coset_series_summable_shifted : PositivityTheory.RgEis.PiLocalization₂ → ∀ (G : Type) [Group G] (Γ Q P : Subgroup G) (ξ lam : G → ℝ) (t : ℝ),
    P ≤ Q → (∀ γ ∈ Γ, γ ∈ Q → ∀ x, ξ (γ * x) = ξ x) → (∀ γ ∈ Γ, γ ∈ P → ∀ x, lam (γ * x) = lam x) →
    PositivityTheory.RgEis.Conv Γ P (fun x => lam x + t * ξ x) → ∀ g : G,
    Summable fun r : PositivityTheory.RgEis.Cos (Γ ⊓ Q) Γ => Real.exp (t * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos (Γ ⊓ Q) P lam (PositivityTheory.RgEis.rep r * g) := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.cross_stage_pos | exact GlobalTheory.CompanionTheory.RgEis.cross_stage_pos | (intros; apply GlobalTheory.CompanionTheory.RgEis.cross_stage_pos <;> assumption)
end

section

open Filter Topology

theorem _root_.GlobalTheory.T.holomorphic_series_uniform_tube : ∀ (ι X T : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] [TopologicalSpace T]
    (t : ι → ℂ × ℂ → T → X) (Ω : Set (ℝ × ℝ)),
    (∀ r g (p v : ℂ × ℂ), Differentiable ℂ fun τ : ℂ => t r (p + τ • v) g) →
    (∀ r, Continuous fun y : (ℂ × ℂ) × T => t r y.1 y.2) →
    (∀ x ∈ Ω, ∀ g, ∃ V ∈ 𝓝 x, ∃ U ∈ 𝓝 g, ∃ u : ι → ℝ, Summable u ∧
      ∀ l ∈ PositivityTheory.RgEis.tube V, ∀ g' ∈ U, ∀ r, ‖t r l g'‖ ≤ u r) →
    PositivityTheory.RgEis.TubeGood (fun l g => ∑' r, t r l g) Ω ∧
      ∀ l ∈ PositivityTheory.RgEis.tube Ω, ∀ g, Summable fun r => ‖t r l g‖ := by
  first | exact @GlobalTheory.CompanionTheory.RgEisCross.tubeGood_tsum | exact GlobalTheory.CompanionTheory.RgEisCross.tubeGood_tsum | (intros; apply GlobalTheory.CompanionTheory.RgEisCross.tubeGood_tsum <;> assumption)
end

section


theorem _root_.GlobalTheory.T.identity_tube_holds : PositivityTheory.RgEis.IdTube := by
  first | exact @GlobalTheory.CompanionTheory.Eis.idTube | exact GlobalTheory.CompanionTheory.Eis.idTube | (intros; apply GlobalTheory.CompanionTheory.Eis.idTube <;> assumption)
end
