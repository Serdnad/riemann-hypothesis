module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle098
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle002
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle099
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
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.Bundle008
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Host Formalism.L2.Col Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.NormOneHilbert90Units

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_ne_zero_mul_conj_eq_of_unitary (D : D7) (z : unitary D.host.E) :
    ∃ w : D.host.E, w ≠ 0 ∧ (z : D.host.E) * D.host.conj w = w := by
  have hz : (z : D.host.E) * star (z : D.host.E) = 1 := z.2.2
  have key : ∀ a : D.host.E, (z : D.host.E) * star (a + (z : D.host.E) * star a) = a + (z : D.host.E) * star a := by
    intro a
    rw [star_add, star_mul, star_star]
    linear_combination a * hz
  obtain ⟨x, hx⟩ : ∃ x : D.host.E, star x ≠ x := by
    by_contra h
    push_neg at h
    apply NumberField.IsCMField.complexConj_ne_one D.host.E
    refine AlgEquiv.ext fun x => ?_
    rw [← Formalism.BasicNotions.Examples₂.cmStar_apply]
    exact h x
  by_cases h1 : (1 : D.host.E) + (z : D.host.E) * star (1 : D.host.E) = 0
  · refine ⟨x + (z : D.host.E) * star x, ?_, ?_⟩
    · intro h2
      have hz1 : (z : D.host.E) = -1 := by rw [star_one] at h1; linear_combination h1
      rw [hz1] at h2
      exact hx (by linear_combination -h2)
    · rw [← Formalism.BasicNotions.Examples₂.star_eq_conj]; exact key x
  · exact ⟨_, h1, by rw [← Formalism.BasicNotions.Examples₂.star_eq_conj]; exact key 1⟩

section Comparison₂

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

end Comparison₂

end GlobalTheory.NormOneHilbert90Units
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

namespace GlobalTheory.Proof.datum_support_div_lattice_interior

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem intAt_sum {P : HeightOneSpectrum (𝓞 E)} {ι : Type} (s : Finset ι) (f : ι → E)
    (h : ∀ i ∈ s, IntAt P (f i)) : IntAt P (∑ i ∈ s, f i) := by
  refine Finset.sum_induction f (IntAt P) (fun _ _ ha hb => ha.add hb) ?_ h
  simpa using IntAt.coe P 0

theorem smul_mem_of_frames {a b : ℕ} (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) (Sp E a))
    (M' : Submodule (𝓞 E) (Sp E b)) (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b)
    (hf : ∀ x, f x ∈ M ↔ x ∈ stdAt E a P) (hf' : ∀ x, f' x ∈ M' ↔ x ∈ stdAt E b P)
    (x : HomE E a b) (c : E) (h : ∀ s l, IntAt P (c * inFr f f' x (Pi.single s 1) l)) :
    ∀ y ∈ M, c • x y ∈ M' := by
  classical
  intro y hy
  obtain ⟨z, rfl⟩ := f.surjective y
  have hz : ∀ i, IntAt P (z i) := (mem_localization_standardLattice P z).1 ((hf z).1 hy)
  have e : c • x (f z) = f' (c • inFr f f' x z) := by simp [inFr]
  rw [e, hf']
  refine (mem_localization_standardLattice P _).2 fun l => ?_
  have hz' : z = ∑ s, z s • (Pi.single s (1 : E) : Sp E a) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have e2 : (c • inFr f f' x z) l = ∑ s, z s * (c * inFr f f' x (Pi.single s 1) l) := by
    conv_lhs => rw [hz']

    simp only [map_sum, map_smul, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e2]
  exact intAt_sum _ _ fun s _ => (hz s).mul (h s l)

end General

end GlobalTheory.Proof.datum_support_div_lattice_interior
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

namespace GlobalTheory

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}


open NumberField IsDedekindDomain in
variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} in
theorem _root_.GlobalTheory.phiT_add_smul_homAt (K : Type) [Field K]
    {ST SG SG' S : Finset (HeightOneSpectrum (𝓞 E))}
    (d : _root_.Formalism.L2.Col.Deco E a ST SG) (d' : _root_.Formalism.L2.Col.Deco E b ST SG') (hd' : d'.Ok) (hS : ST ⊆ S) (c : 𝓞 E)
    (hc : ∀ P : ST, c ∈ P.1.asIdeal) (x y₀ : _root_.Formalism.L2.Col.HomE E a b) (hy : y₀ ∈ _root_.Formalism.L2.Col.homAt S d.N d'.N) :
    _root_.Formalism.L2.Col.phiT K d d' (x + c • y₀) = _root_.Formalism.L2.Col.phiT K d d' x := by
  unfold _root_.Formalism.L2.Col.phiT
  have key : ∀ P : ST, ∀ y ∈ d.at P,
      ((x + c • y₀) y ∈ d'.at P ∧ d'.f P ((x + c • y₀) y) = d.f P y) ↔
        (x y ∈ d'.at P ∧ d'.f P (x y) = d.f P y) := by
    intro P y hyP
    have hy0 : y₀ y ∈ d'.at P := hy P.1 (hS P.2) y hyP
    have hcy : c • y₀ y ∈ d'.at P := Submodule.smul_mem _ c hy0
    have hf0 : d'.f P (c • y₀ y) = 0 := by
      rw [hd'.f_smul P c _ hy0, Ideal.Quotient.eq_zero_iff_mem.2 (hc P), zero_mul]
    have happ : (x + c • y₀) y = x y + c • y₀ y := rfl
    rw [happ, Submodule.add_mem_iff_left _ hcy]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [← h2, hd'.f_add P _ h1 _ hcy, hf0, add_zero]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [hd'.f_add P _ h1 _ hcy, hf0, add_zero, h2]⟩
  have hiff : (∀ P : ST, ∀ y ∈ d.at P,
      (x + c • y₀) y ∈ d'.at P ∧ d'.f P ((x + c • y₀) y) = d.f P y) ↔
      (∀ P : ST, ∀ y ∈ d.at P, x y ∈ d'.at P ∧ d'.f P (x y) = d.f P y) :=
    forall_congr' fun P => forall₂_congr fun y hyP => key P y hyP
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hiff.1 h1) h2
  · exact absurd (hiff.2 h2) h1
  · rfl

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} in
omit [NumberField E] [StarRing E] in
theorem _root_.GlobalTheory.inFr_add (f : _root_.Formalism.L2.Col.Sp E a ≃ₗ[E] _root_.Formalism.L2.Col.Sp E a) (f' : _root_.Formalism.L2.Col.Sp E b ≃ₗ[E] _root_.Formalism.L2.Col.Sp E b)
    (x y : _root_.Formalism.L2.Col.HomE E a b) :
    _root_.Formalism.L2.Col.inFr f f' (x + y) = _root_.Formalism.L2.Col.inFr f f' x + _root_.Formalism.L2.Col.inFr f f' y := by
  unfold _root_.Formalism.L2.Col.inFr
  rw [LinearMap.add_comp, LinearMap.comp_add]


open NumberField IsDedekindDomain in
variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} in
theorem _root_.GlobalTheory.intAt_inFr_smul_homAt {S : Finset (HeightOneSpectrum (𝓞 E))}
    {N : Submodule (𝓞 E) (_root_.Formalism.L2.Col.Sp E a)}
    {N' : Submodule (𝓞 E) (_root_.Formalism.L2.Col.Sp E b)} {P : HeightOneSpectrum (𝓞 E)} (hP : P ∈ S)
    (f : _root_.Formalism.L2.Col.Sp E a ≃ₗ[E] _root_.Formalism.L2.Col.Sp E a) (f' : _root_.Formalism.L2.Col.Sp E b ≃ₗ[E] _root_.Formalism.L2.Col.Sp E b)
    (hf : ∀ x, f x ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N ↔ x ∈ _root_.Formalism.L2.Col.stdAt E a P)
    (hf' : ∀ x, f' x ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N' ↔ x ∈ _root_.Formalism.L2.Col.stdAt E b P)
    (c r : 𝓞 E) (e : E) (he : e ≠ 0) (hc : algebraMap (𝓞 E) E c = e * algebraMap (𝓞 E) E r)
    (y₀ : _root_.Formalism.L2.Col.HomE E a b) (hy : y₀ ∈ _root_.Formalism.L2.Col.homAt S N N') (s : Fin a) (l : Fin b) :
    _root_.Formalism.L2.Col.IntAt P (e⁻¹ * _root_.Formalism.L2.Col.inFr f f' (c • y₀) (Pi.single s 1) l) := by
  have hv : (Pi.single s 1 : _root_.Formalism.L2.Col.Sp E a) ∈ _root_.Formalism.L2.Col.stdAt E a P := by
    refine ⟨1, P.asIdeal.primeCompl.one_mem, ?_⟩
    rw [one_smul]
    refine Submodule.mem_pi.2 fun i _ => ?_
    by_cases h : i = s
    · subst h
      rw [Pi.single_eq_same]
      exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · rw [Pi.single_eq_of_ne h]
      exact Submodule.zero_mem _
  have hz : y₀ (f (Pi.single s 1)) ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N' := hy P hP _ ((hf _).2 hv)
  have hw : f'.symm (y₀ (f (Pi.single s 1))) ∈ _root_.Formalism.L2.Col.stdAt E b P :=
    (hf' _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hz)
  obtain ⟨t, ht, htw⟩ := hw
  have hl : (t • f'.symm (y₀ (f (Pi.single s 1)))) l ∈ (1 : Submodule (𝓞 E) E) :=
    Submodule.mem_pi.1 htw l (Set.mem_univ l)
  obtain ⟨r', hr'⟩ := Submodule.mem_one.1 hl
  have hval : _root_.Formalism.L2.Col.inFr f f' (c • y₀) (Pi.single s 1) l =
      algebraMap (𝓞 E) E c * f'.symm (y₀ (f (Pi.single s 1))) l := by
    show (f'.symm (c • y₀ (f (Pi.single s 1)))) l = _
    rw [← algebraMap_smul E c (y₀ (f (Pi.single s 1))), map_smul, Pi.smul_apply, smul_eq_mul]
  unfold _root_.Formalism.L2.Col.IntAt
  refine ⟨r * r', t, ht, ?_⟩
  rw [hval, hc, map_mul, hr', Pi.smul_apply, Algebra.smul_def]
  calc _ = (e⁻¹ * e) * (algebraMap (𝓞 E) E t * (algebraMap (𝓞 E) E r *
        f'.symm (y₀ (f (Pi.single s 1))) l)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ he, one_mul]; ring

end General

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.LamQBCong

open GlobalTheory.TopStep

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

theorem entry_cong (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} (g : HomE E N N)
    (hg : ∀ x ∈ stdAt E N P, (qOf P : E)⁻¹ • (g x - x) ∈ stdAt E N P) (s t : Fin N) :
    IntAt P (g (Pi.single t 1) s) ∧ redP P (g (Pi.single t 1) s) = if s = t then 1 else 0 := by
  classical
  have hq0 : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero
  have hx := mem_stdAt.1 (hg _ (single_mem_stdAt (P := P) t)) s
  set δ : E := (Pi.single t (1 : E) : Sp E N) s with hδ
  have hδI : IntAt P δ := mem_stdAt.1 (single_mem_stdAt (P := P) t) s
  have hdiv : IntAt P ((g (Pi.single t 1) s - δ) / (qOf P : E)) := by
    have e : (((qOf P : E)⁻¹ • (g (Pi.single t 1) - Pi.single t 1) : Sp E N)) s = (g (Pi.single t 1) s - δ) / (qOf P : E) := by
      rw [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rw [← e]
    exact hx
  have hI : IntAt P (g (Pi.single t 1) s - δ) := by
    have e : g (Pi.single t 1) s - δ = (qOf P : E) * ((g (Pi.single t 1) s - δ) / (qOf P : E)) := by
      field_simp
    rw [e]
    exact (intAt_nat _).mul hdiv
  have hI' : IntAt P (g (Pi.single t 1) s) := by
    have := intAt_sub hI (intAt_neg hδI)
    rwa [sub_neg_eq_add, sub_add_cancel] at this
  refine ⟨hI', ?_⟩
  have h0 := redP_eq_zero_of_div hdiv
  rw [reduction_sub hI' hδI, sub_eq_zero] at h0
  rw [h0, hδ, Pi.single_apply]
  split_ifs
  · exact reduction_one₂
  · exact reduction_zero

theorem lamQB_eq_one_of_cong : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E))
    (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj n N : ℕ) (g : HomE E N N), n ≤ N →
    (∀ x ∈ stdAt E N P, (qOf P : E)⁻¹ • (g x - x) ∈ stdAt E N P) → LocE.lamQB ξ kj n g = 1 := by
  intro E K _ _ _ _ P ξ kj n N g hn hg
  classical
  unfold LocE.lamQB
  set D : Matrix (Fin (n - kj)) (Fin (n - kj)) E := Matrix.of fun s t : Fin (n - kj) =>
    Loc.atN (g (Loc.eN E N (kj + t.1))) (kj + s.1) with hD
  have hent : ∀ s t : Fin (n - kj), IntAt P (D s t) ∧ redP P (D s t) = (1 : Matrix _ _ (𝓞 E ⧸ P.asIdeal)) s t := by
    intro s t
    have hs : kj + s.1 < N := by have := s.2; omega
    have ht : kj + t.1 < N := by have := t.2; omega
    have e1 : Loc.eN E N (kj + t.1) = Pi.single ⟨kj + t.1, ht⟩ 1 := by
      funext l
      unfold Loc.eN
      rw [Pi.single_apply]
      congr 1
      apply propext
      constructor
      · intro h; exact Fin.ext h
      · intro h; rw [h]
    have e2 : D s t = g (Pi.single ⟨kj + t.1, ht⟩ 1) ⟨kj + s.1, hs⟩ := by
      rw [hD, Matrix.of_apply, e1]
      unfold Loc.atN
      rw [dite_eq_left hs]
    obtain ⟨h1, h2⟩ := entry_cong P g hg ⟨kj + s.1, hs⟩ ⟨kj + t.1, ht⟩
    rw [e2]
    refine ⟨h1, ?_⟩
    rw [h2, Matrix.one_apply]
    by_cases hst : s = t
    · rw [if_pos (Fin.ext (by simp [hst])), if_pos hst]
    · rw [if_neg (fun h => hst (Fin.ext (by have := congrArg Fin.val h; simp at this; omega))), if_neg hst]
  have hdet : redP P D.det = 1 := by
    rw [(det_int fun s t => (hent s t).1).2]
    have : D.map (redP P) = 1 := Matrix.ext fun s t => (hent s t).2
    rw [this, Matrix.det_one]
  unfold LocE.unitV
  have hu : IsUnit (redP P D.det) := by rw [hdet]; exact isUnit_one
  rw [dite_eq_left hu]
  have : hu.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, hdet]; rfl)
  rw [this, map_one, Units.val_one, inv_one]

end GlobalTheory.LamQBCong
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.ParahoricOfCong

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))

theorem mem_stdAt_iff_sclLat_zero (q N : ℕ) (x : Sp E N) :
    x ∈ stdAt E N P ↔ x ∈ LocE.sclLat P q N (fun _ => 0) := by
  rw [GlobalTheory.CongLevel.mem_sclLat, GlobalTheory.TopStep.mem_stdAt]
  simp

theorem map_mem_of_cong {N : ℕ} (q : E) (M : Submodule (𝓞 E) (Sp E N)) (hM : M ≤ stdAt E N P)
    (hqM : ∀ y : Sp E N, q⁻¹ • y ∈ stdAt E N P → y ∈ M)
    (h : Sp E N ≃ₗ[E] Sp E N) (hh : ∀ x ∈ stdAt E N P, q⁻¹ • (h x - x) ∈ stdAt E N P) :
    ∀ x ∈ M, h x ∈ M := by
  intro x hx
  have e : h x = x + (h x - x) := by abel
  rw [e]
  exact M.add_mem hx (hqM _ (hh x (hM hx)))

theorem mem_stabL_of_cong {N : ℕ} (q : E) (M : Submodule (𝓞 E) (Sp E N)) (hM : M ≤ stdAt E N P)
    (hqM : ∀ y : Sp E N, q⁻¹ • y ∈ stdAt E N P → y ∈ M)
    (g : Sp E N ≃ₗ[E] Sp E N) (h1 : ∀ x ∈ stdAt E N P, q⁻¹ • (g x - x) ∈ stdAt E N P)
    (h2 : ∀ x ∈ stdAt E N P, q⁻¹ • (g⁻¹ x - x) ∈ stdAt E N P) :
    g ∈ stabL E N M := by
  intro x
  constructor
  · intro hx
    have := map_mem_of_cong P q M hM hqM g⁻¹ h2 (g x) hx
    have e : g⁻¹ (g x) = x := LinearEquiv.symm_apply_apply g x
    rwa [e] at this
  · exact map_mem_of_cong P q M hM hqM g h1 x

end GlobalTheory.ParahoricOfCong


open GlobalTheory.ParahoricOfCong in
theorem GlobalTheory.ParahoricOfCong.mem_JQ_of_cong : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (kj n c : ℕ) (g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)), (∀ x ∈ stdAt E (n + c) P, (qOf P : E)⁻¹ • (g x - x) ∈ stdAt E (n + c) P) → (∀ x ∈ stdAt E (n + c) P, (qOf P : E)⁻¹ • (g⁻¹ x - x) ∈ stdAt E (n + c) P) → g ∈ LocE.JQ P (qOf P) kj n c := by
  intro E _ _ _ P kj n c g h1 h2
  have hq : ((qOf P : ℕ) : E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero (P := P)
  refine ⟨?_, ?_⟩
  · refine mem_stabL_of_cong P _ _ le_rfl (fun y hy => ?_) g h1 h2
    have e : y = (qOf P : E) • ((qOf P : E)⁻¹ • y) := by rw [smul_smul, mul_inv_cancel₀ hq, one_smul]
    rw [e, Nat.cast_smul_eq_nsmul E]
    exact nsmul_mem hy _
  · refine mem_stabL_of_cong P _ _ ?_ ?_ g h1 h2
    · intro x hx
      rw [mem_stdAt_iff_sclLat_zero P (qOf P)]
      have := GlobalTheory.CongLevel.sclLat_le P (qOf P) hq (n + c) (fun _ => 0) (fun l => kj ≤ l ∧ l < n)
      exact this (by simpa [LocE.parL] using hx)
    · intro y hy
      rw [mem_stdAt_iff_sclLat_zero P (qOf P)] at hy
      have := GlobalTheory.CongLevel.smul_mem_sclLat P (qOf P) hq (n + c) (fun _ => 0) (fun l => kj ≤ l ∧ l < n) y hy
      simpa [LocE.parL] using this
end
end

section

open MvPolynomial Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.BranchFormula

open Formalism.L2.Col.Br

theorem brEquiv_all : ∀ (K : Type) [Field K] [CharZero K] {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n), Br.BrEquiv K hN lam sg := by
  intro K _ _ ι _ N n hN lam sg hS g g' h G
  have hB : ∀ τ, IsBlock hN (g' τ : Matrix (Fin N) (Fin N) K) (g τ : Matrix (Fin n) (Fin n) K) 1 := h
  apply Subtype.ext
  have hd : detTwK lam g' = detTwK sg g := by
    rw [detTwK, detTwK]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [detPow, detPow, hS τ, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val,
      Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, (hB τ).det, mul_one]
  simp only [brStd, brStdP, LinearMap.comp_apply, Submodule.subtype_apply, rhoK_coe, LinearMap.smul_apply, actP, trAct,
    AlgHom.toLinearMap_apply, map_smul, Submodule.coe_smul]
  rw [coefLast_blockAct K ι hN _ _ _ (fun _ => 1) fun τ => (hB τ).transpose, map_smul, Submodule.coe_smul, projVV_blockAct]
  simp only [smul_smul, one_pow, Finset.prod_const_one, mul_one]
  rw [hd]
  congr 1
  ring

end GlobalTheory.BranchFormula
end
end

section

noncomputable section

namespace GlobalTheory.PadicUnfold.Period

def extZero {k : Type} [CommRing k] {n' n : ℕ} (c' c : ℕ) (y : (Fin n' → k) →ₗ[k] (Fin n → k)) :
    (Fin (n' + c') → k) →ₗ[k] (Fin (n + c) → k) :=
  Matrix.toLin' (Matrix.of fun (l : Fin (n + c)) (s : Fin (n' + c')) =>
    if hs : s.1 < n' then
      (if hl : l.1 < n then y (Pi.single ⟨s.1, hs⟩ 1) ⟨l.1, hl⟩ else 0) else 0)

theorem extZero_single {k : Type} [CommRing k] {n' n : ℕ} (c' c : ℕ)
    (y : (Fin n' → k) →ₗ[k] (Fin n → k)) (s : Fin (n' + c')) (l : Fin (n + c)) :
    extZero c' c y (Pi.single s 1) l = if hs : s.1 < n' then
      (if hl : l.1 < n then y (Pi.single ⟨s.1, hs⟩ 1) ⟨l.1, hl⟩ else 0) else 0 := by
  simp [extZero, Matrix.toLin'_apply]

theorem periodXX1_add_smul {k : Type} [CommRing k] {n' c' n c : ℕ} (a : k)
    (x y : (Fin n' → k) →ₗ[k] (Fin n → k)) (t : Formalism.L2.Col.Loc.FC n' c' n c → k) :
    Formalism.L2.Col.Loc.xx1 (x + a • y) t =
      Formalism.L2.Col.Loc.xx1 x t + a • extZero c' c y := by
  refine hom_ext fun s l => ?_
  rw [LinearMap.add_apply, Pi.add_apply, LinearMap.smul_apply, Pi.smul_apply, linearMap_unfolding_apply_single, linearMap_unfolding_apply_single,
    extZero_single]
  by_cases hf : Formalism.L2.Col.Loc.IsFree n' n c l.1 s.1
  · have hs : ¬ s.1 < n' := not_lt.2 hf.1
    simp [hf, hs]
  · by_cases hs : s.1 < n'
    · by_cases hl : l.1 < n <;> simp [hf, hs, hl]
    · simp [hf, hs]

theorem chArg_smul_extZero {k : Type} [CommRing k] {n' n c : ℕ} (a : k)
    (y : (Fin n' → k) →ₗ[k] (Fin n → k)) :
    Formalism.L2.Col.Loc.chArg (a • extZero (c + 1) c y) = 0 := by
  rw [chArg_eq]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, extZero_single, dite_eq_right (by simp; omega), smul_zero]

variable {g : ℕ} [Fact g.Prime]

end GlobalTheory.PadicUnfold.Period
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

theorem _root_.GlobalTheory.T.low_term_le_second_real_place_bounds : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (ce : ErrC) (Xe : ErrX D) (dG : ℕ → ℕ), L.FDef → dG 0 = 0 → (∀ j, dG j ≤ padicValNat (D.what₂.places.resChar w) (D.mem u).C.DGam) → WeilJacquetShalikaLaw.lowS L Xe K ce 1 u w ≤ (∑ j ∈ Finset.Icc 1 D.R.m, ∑ t ∈ reps X (D.what₂.places.resChar w), if ((D.what₂.places.resChar w) : ℝ) ≤ L.sc.X'' D.R.n then FOrb D j (D.what₂.places.resChar w) (true, t) - OrbitPlaces.errF L K ce j (D.what₂.places.resChar w) (true, t) else 0) - ∑ j ∈ Finset.range D.R.m, (dG j : ℝ) := by
  first | exact @GlobalTheory.TwU.LowTerm.lowS_le | exact GlobalTheory.TwU.LowTerm.lowS_le | (intros; apply GlobalTheory.TwU.LowTerm.lowS_le <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.localization_eq_of_heckeAgreement_twistLaws : ∀ (D : D7) (M : Formalism.L2.MtFam D), Formalism.L2.HeckeTied D M → GlobalTheory.RowTie.CharLaws D.nd D.naut → (∀ (i i' : D.nd.Loc) (σ : D.what₂.FT) (v : PlE D.host), IsSplitPl D.host v → D.naut.locW i σ v = D.naut.locW i' σ v) → (∀ i i' : D.nd.Loc, D.nd.j i = D.nd.j i' → D.nd.w i = D.nd.w i' → D.naut.muC i = D.naut.muC i') → KillingConditions.LocalisationUniqueness D := by
  first | exact @GlobalTheory.LocSepTie.main | exact GlobalTheory.LocSepTie.main | (intros; apply GlobalTheory.LocSepTie.main <;> assumption)
end
