module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle180
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle097
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSelfDualLatticeIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle108
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle100
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle073
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle075
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle120
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle017
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle296
import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle182
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

namespace GlobalTheory.Mem.Col2.IdxExZeroQ

section Loc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem parL_self (q kj n c : ℕ) (h : n ≤ kj) : LocE.parL P q kj n c = stdAt E (n + c) P := by
  ext x
  unfold LocE.parL
  rw [GlobalTheory.CongLevel.mem_sclLat, GlobalTheory.GO.ChRoot.mem_stdAt']
  refine forall_congr' fun l => ?_
  rw [if_neg (by omega)]
  simp

theorem lamY_zero (q n c : ℕ) : LocE.lamY P q n c 0 = stdAt E (n + c) P :=
  Submodule.ext fun _ => GlobalTheory.GO.ChRoot.mem_lamY_zero


omit [StarRing E] in
theorem lamQB_empty {K : Type} [Field K] (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj n : ℕ) (hn : n ≤ kj) {N : ℕ}
    (h : HomE E N N) : LocE.lamQB ξ kj n h = 1 := by
  unfold LocE.lamQB
  haveI : IsEmpty (Fin (n - kj)) := ⟨fun i => by have := i.2; omega⟩
  have h1 : redP P (1 : E) = 1 := by simpa using reduction_coe P 1
  rw [Matrix.det_isEmpty]
  unfold LocE.unitV
  rw [dite_eq_left (by rw [h1]; exact isUnit_one)]
  have : ∀ hu : IsUnit (redP P (1 : E)), hu.unit = 1 := fun hu => Units.ext (by simp [h1])
  rw [this, map_one]
  simp

end Loc

theorem zero_level : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs → cst.Ok → GrpQ (R := R) sel mu cst 0 P 1 ⟨⊤, 1⟩ ∧ ChrQ Ch sel mu cst 0 P 1 ⟨⊤, 1⟩ := by
  intro X Pr R Ch sel S mu cst P hP hc
  have hN : R.N 0 ≤ R.k + 0 := by rw [Ranks.N_zero]; omega
  have hJ : Jat (Pr := Pr) (R := R) cst.sharp 0 P.1 = stabL X.E _ (stdAt X.E (R.N 0 + cOf R 0) P.1) := by
    unfold Jat
    rw [if_neg hP]
    unfold LocE.JQ
    rw [parL_self _ _ _ _ hN, inf_idem]
  have e : ∀ r : AutY X R 0, (MulAut.conj (1 : AutY X R 0)⁻¹).toMonoidHom r = r := by
    intro r
    simp
  constructor
  · unfold GrpQ
    symm
    rw [eq_top_iff]
    intro g _
    rw [Subgroup.mem_subgroupOf]
    refine ⟨GlobalTheory.CongLevel.extE _ g.1, ⟨GlobalTheory.CongLevel.extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup _ g.1, ?_⟩, GlobalTheory.CongLevel.extE_inX _ g.1⟩
    show (MulAut.conj (1 : AutY X R 0)⁻¹).toMonoidHom (GlobalTheory.CongLevel.extE (cOf R 0) g.1) ∈ Jat (Pr := Pr) cst.sharp 0 P.1
    rw [e, hJ, ← lamY_zero (qOf P.1)]
    exact GlobalTheory.CongLevel.extE_stab _ _ _ _ _ g.2
  · intro g r hr _
    have h2 : (MulAut.conj (1 : AutY X R 0)⁻¹).toMonoidHom r ∈ Jat (Pr := Pr) cst.sharp 0 P.1 := hr.2
    rw [e, hJ] at h2
    have hint : IntAt P.1 (1 * Loc.n1Arg r) :=
      GlobalTheory.GO.ChRoot.intAt_n1Arg 1 r fun x hx => by rw [one_smul]; exact (h2 x).2 hx
    rw [one_mul] at hint
    unfold chiInv lamRow
    rw [if_neg hP, hc.psi_int P _ hint, lamQB_empty _ _ _ hN]
    simp

end GlobalTheory.Mem.Col2.IdxExZeroQ
end

section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LevelHecke.AboveSum

variable {R V k : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k]

theorem mem_of_one {res : R →+* k} {q : Pr R V k} (h : q.Ok res) {e : V} (he : q.f e = 1) : e ∈ q.L := by
  by_contra hn
  rw [h.off e hn] at he
  exact zero_ne_one he

theorem smul_mem_ker {res : R →+* k} {q : Pr R V k} {Λ : Submodule R V} (h : q.Ok res) (hk : q.IsKer Λ) {t : R}
    (ht : res t = 0) {e : V} (he : q.f e = 1) : t • e ∈ Λ :=
  (hk _).2 ⟨q.L.smul_mem _ (mem_of_one h he), by rw [h.smul _ _ (mem_of_one h he), ht, zero_mul]⟩

theorem sub_mem_ker {res : R →+* k} {q : Pr R V k} {Λ : Submodule R V} (h : q.Ok res) (hk : q.IsKer Λ)
    {e : V} (he : q.f e = 1) {y : V} (hy : y ∈ q.L) {a : R} (ha : res a = q.f y) : y + (-a) • e ∈ Λ := by
  have he' := mem_of_one h he
  refine (hk _).2 ⟨q.L.add_mem hy (q.L.smul_mem _ he'), ?_⟩
  rw [h.add _ hy _ (q.L.smul_mem _ he'), h.smul _ _ he', he, map_neg, ha]
  ring

theorem le_of_ker {res : R →+* k} (hres : Function.Surjective res) {q q' : Pr R V k} {Λ : Submodule R V}
    (h : q.Ok res) (hk : q.IsKer Λ) (h' : q'.Ok res) (hk' : q'.IsKer Λ) {e e' : V} (he : q.f e = 1)
    (he' : q'.f e' = 1) (hd : e - e' ∈ Λ) {y : V} (hy : y ∈ q.L) : y ∈ q'.L ∧ q'.f y = q.f y := by
  obtain ⟨a, ha⟩ := hres (q.f y)
  have h1 := sub_mem_ker h hk he hy ha
  have h2 := (hk' _).1 (Λ.add_mem h1 (Λ.smul_mem a hd))
  have h3 := mem_of_one h' he'
  have e0 : y = (y + (-a) • e + a • (e - e')) + a • e' := by
    rw [smul_sub, neg_smul]; abel
  have h4 := q'.L.smul_mem a h3
  constructor
  · rw [e0]; exact q'.L.add_mem h2.1 h4
  · have h5 := h'.add _ h2.1 _ h4
    rw [← e0, h2.2, h'.smul _ _ h3, he', ha] at h5
    rw [h5]; ring

theorem eq_of_ker {res : R →+* k} (hres : Function.Surjective res) {q q' : Pr R V k} {Λ : Submodule R V}
    (h : q.Ok res) (hk : q.IsKer Λ) (h' : q'.Ok res) (hk' : q'.IsKer Λ) {e e' : V} (he : q.f e = 1)
    (he' : q'.f e' = 1) (hd : e - e' ∈ Λ) : q = q' := by
  have hd' : e' - e ∈ Λ := by rw [← neg_sub]; exact Λ.neg_mem hd
  ext y
  · exact ⟨fun hy => (le_of_ker hres h hk h' hk' he he' hd hy).1,
      fun hy => (le_of_ker hres h' hk' h hk he' he hd' hy).1⟩
  · by_cases hy : y ∈ q.L
    · exact (le_of_ker hres h hk h' hk' he he' hd hy).2.symm
    · rw [h.off y hy, h'.off y (fun hy' => hy (le_of_ker hres h' hk' h hk he' he hd' hy').1)]

theorem finsum_above : ∀ (R V k W M : Type) [CommRing R] [AddCommGroup V] [Module R V] [Field k] [AddCommGroup W] [Module k W] [AddCommMonoid M] (res : R →+* k) (t : R) (p : Pr R V k) (π : V → W) (φ : Module.Dual k W) (q : W → Pr R V k) (Φ : Pr R V k → M), Function.Surjective res → res t = 0 → (∀ x : V, t • x = 0 → x = 0) → (∀ s x, res s ≠ 0 → s • x ∈ p.L → x ∈ p.L) → Red res t p.L π → (∀ x ∈ p.L, p.f x = φ (π x)) → (∀ w, φ w = 1 → (q w).Ok res ∧ (q w).IsKer p.L ∧ ∃ e, (q w).f e = 1 ∧ π (t • e) = w) → ∑ᶠ q' ∈ {q' | Pr.Inc res t p q'}, Φ q' = ∑ᶠ w ∈ {w | φ w = 1}, Φ (q w) := by
  intro R V k W M _ _ _ _ _ _ _ res t p π φ q Φ hres ht htf hsat hred hf hq
  symm
  refine finsum_mem_eq_of_bijOn q ⟨?_, ?_, ?_⟩ (fun _ _ => rfl)
  · intro w hw
    obtain ⟨h1, h2, e, h3, h4⟩ := hq w hw
    refine ⟨h1, h2, e, h3, ?_⟩
    rw [hf _ (smul_mem_ker h1 h2 ht h3), h4]
    exact hw
  · intro w hw w' hw' hww
    obtain ⟨h1, h2, e, h3, h4⟩ := hq w hw
    obtain ⟨-, -, e', h3', h4'⟩ := hq w' hw'
    rw [← hww] at h3'
    have hd : e + (-1 : R) • e' ∈ p.L :=
      sub_mem_ker h1 h2 h3' (mem_of_one h1 h3) (by rw [map_one, h3])
    have e0 : t • e = t • e' + t • (e + (-1 : R) • e') := by
      rw [neg_smul, one_smul, smul_add, smul_neg]; abel
    rw [← h4, ← h4', e0, hred.add _ (smul_mem_ker h1 h2 ht h3') _ (p.L.smul_mem _ hd), hred.smul _ _ hd, ht,
      zero_smul, add_zero]
  · rintro q' ⟨h1', h2', e', h3', h4'⟩
    have hm' := smul_mem_ker h1' h2' ht h3'
    have hw : φ (π (t • e')) = 1 := by rw [← hf _ hm', h4']
    refine ⟨π (t • e'), hw, ?_⟩
    obtain ⟨h1, h2, e, h3, h4⟩ := hq _ hw
    have hm := smul_mem_ker h1 h2 ht h3
    have h0 : π (t • e + (-1 : R) • t • e') = 0 := by
      rw [hred.add _ hm _ (p.L.smul_mem _ hm'), hred.smul _ _ hm', h4, map_neg, map_one, neg_smul, one_smul,
        add_neg_cancel]
    obtain ⟨y, hy, s, hs, hsy⟩ := (hred.ker _ (p.L.add_mem hm (p.L.smul_mem _ hm'))).1 h0
    have h5 : s • (e - e') - y = 0 := by
      apply htf
      rw [smul_sub, ← hsy, smul_comm t s, neg_smul, one_smul, smul_sub t, sub_eq_add_neg (t • e), sub_self]
    refine eq_of_ker hres h1 h2 h1' h2' h3 h3' (hsat s _ hs ?_)
    rw [sub_eq_zero.1 h5]; exact hy

end GlobalTheory.LevelHecke.AboveSum
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem isAddHaarMeasure_tupMeas_of_lc {S : Type} [AddCommGroup S] [TopologicalSpace S]
    [IsTopologicalAddGroup S] [LocallyCompactSpace S] [SecondCountableTopology S]
    [MeasurableSpace S] [BorelSpace S] (lam : Measure S) (h : lam.IsAddHaarMeasure) (n M : ℕ) :
    (tupMeas lam n M).IsAddHaarMeasure := by
  unfold tupMeas
  haveI : (Measure.pi fun _ : Fin M => lam).IsAddHaarMeasure := inferInstance
  infer_instance

theorem setOf_isUnit_ainf (F : Type) [Field F] [NumberField F] :
    {c : Ainf F | IsUnit c} = {c : Ainf F | ∀ w, c w ≠ 0} := by
  ext c
  simp only [Set.mem_setOf_eq]
  refine (Pi.isUnit_iff (x := c)).trans (forall_congr' fun w => isUnit_iff_ne_zero)

theorem existsUnique_isStdX : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (β : F), 3 ≤ M → IsHermND σ J → β ≠ 0 → ∃! ν, IsStdX s σ J β ν := by
  intro F E _ _ _ _ _ σ hσ d b s M J β hM hJ hβ
  have hM1 : 1 ≤ M := by omega
  obtain ⟨nI, nV⟩ := GlobalTheory.GaugeEx.nice_ainf_fv F
  have uI : IsUnit (algebraMap F (Ainf F) β) := (isUnit_iff_ne_zero.2 hβ).map _
  have uV : ∀ v, IsUnit (algebraMap F (Fv F v) β) := fun v => (isUnit_iff_ne_zero.2 hβ).map _
  have bI := fun m => GlobalTheory.GaugeEx.FibBasic.fibAt_basic F E σ (Ainf F) nI M J (tupMeas s.lamI 1 M) s.nuI _ m s.haar_nuI uI
  have bV := fun v m => GlobalTheory.GaugeEx.FibBasic.fibAt_basic F E σ (Fv F v) (nV v) M J (tupMeas (s.lamV v) 1 M) (s.nuV v) _ m
    (s.haar_nuV v) (uV v)
  obtain ⟨mi, hmi⟩ : ∃ mi, FibAt (Ainf F) σ J (tupMeas s.lamI 1 M) s.nuI (algebraMap F _ β) mi := by
    obtain ⟨fib, hfib⟩ := GlobalTheory.T.exists_fibreFamily_hermitianLength_infiniteAdeles F E σ hσ M J (tupMeas s.lamI 1 M) s.nuI hM1 hJ
      (isAddHaarMeasure_tupMeas_of_lc _ s.haar_lamI 1 M) s.haar_nuI
    exact ⟨_, fib, by rw [setOf_isUnit_ainf]; exact hfib, rfl⟩
  have hex : ∀ v, ∃ m, FibAt (Fv F v) σ J (tupMeas (s.lamV v) 1 M) (s.nuV v) (algebraMap F _ β) m := by
    intro v
    obtain ⟨-, fib, hfib⟩ := GlobalTheory.LocalDensityCompare.null_and_exists v σ J hσ hM1 hJ
      (tupMeas (s.lamV v) 1 M) (isAddHaarMeasure_tupMeas_of_lc _ (s.haar_lamV v) 1 M) (s.nuV v)
      (s.haar_nuV v)
    refine ⟨_, fib, ?_, rfl⟩
    simp only [isUnit_iff_ne_zero]
    exact hfib
  choose mv hmv using hex
  have hconv : Conv b mi mv := by
    refine ⟨(bI mi hmi).2.1, fun v => (bV v _ (hmv v)).2.1, ?_⟩
    have hs := ((GlobalTheory.countable_ideal_and_summable_absNorm_rpow F).2 2 (by norm_num)).2
    refine Summable.of_norm_bounded_eventually hs ?_
    filter_upwards [GlobalTheory.T.eventually_localDensity_standardLattice_bound F E σ hσ d b s M J β hM1 hJ hβ] with v hv
    have h := hv _ (hmv v)
    have hq : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
      have : Ideal.absNorm v.asIdeal ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
      exact_mod_cast Nat.one_le_iff_ne_zero.2 this
    set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ)
    set a : ℝ := |(mv v (latV b v)).toReal - 1|
    have ha : 0 ≤ a := abs_nonneg _
    have hq0 : 0 < q := by linarith
    have h3 : a * q ^ 3 ≤ q := (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq hM) ha).trans h
    have h2 : a * q ^ 2 ≤ 1 := by
      refine le_of_mul_le_mul_right ?_ hq0
      calc a * q ^ 2 * q = a * q ^ 3 := by ring
        _ ≤ 1 * q := by rw [one_mul]; exact h3
    rw [Real.norm_of_nonneg ha, Real.rpow_neg hq0.le, Real.rpow_two, ← one_div,
      le_div_iff₀ (by positivity)]
    exact h2
  obtain ⟨ν, hν⟩ := GlobalTheory.T.exists_isRestrictedProductTupleMeasure F E d b 1 M mi mv hconv
  refine ⟨ν, ⟨mi, mv, hmi, hmv, hν⟩, ?_⟩
  rintro ν' ⟨mi', mv', hmi', hmv', hν'⟩
  obtain rfl : mi' = mi := (bI mi hmi).2.2 _ hmi'
  obtain rfl : mv' = mv := funext fun v => (bV v _ (hmv v)).2.2 _ (hmv' v)
  exact (GlobalTheory.T.restrictedProductMeasure_basic_properties F E d b 1 M ν _ _ hν).2.2.1 _ hν'

end GlobalTheory.GaugeEx
end

section

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Branching

noncomputable section

namespace GlobalTheory.CoefIrred

theorem eq_bot_or_top_of_tensor {K ι : Type} [Field K] [Fintype ι] {V κ G : ι → Type}
    [∀ τ, AddCommGroup (V τ)] [∀ τ, Module K (V τ)] [Fintype (∀ τ, κ τ)] {W : Type} [AddCommGroup W] [Module K W]
    (b : ∀ τ, Module.Basis (κ τ) K (V τ)) (t : (∀ τ, V τ) →ₘₗ[K] W)
    (B : Module.Basis (∀ τ, κ τ) K W)
    (hB : ∀ i, B i = t fun τ => b τ (i τ)) (ρ : ∀ τ, G τ → Module.End K (V τ))
    (hρ : ∀ τ, Submodule.span K (Set.range (ρ τ)) = ⊤) (U : Submodule K W)
    (hU : ∀ g : ∀ τ, G τ, ∃ L : Module.End K W,
      (∀ f, L (t f) = t fun τ => ρ τ (g τ) (f τ)) ∧ ∀ x ∈ U, L x ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  classical
  rw [or_iff_not_imp_left]
  intro hne
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨i₀, hi₀⟩ : ∃ i, B.repr x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (B.repr.map_eq_zero_iff.1 (Finsupp.ext h))
  let Φ : (∀ τ, Module.End K (V τ)) →ₘₗ[K] W :=
    ∑ i, B.repr x i • t.compLinearMap fun τ => LinearMap.applyₗ (b τ (i τ))
  have hΦ : ∀ T, Φ T = ∑ i, B.repr x i • t fun τ => T τ (b τ (i τ)) := by
    intro T
    simp [Φ]
  have h0 : U.mkQ.compMultilinearMap Φ = 0 := by
    refine MultilinearMap.ext_of_span_eq_top hρ fun g => ?_
    obtain ⟨L, hL, hLU⟩ := hU g
    have : Φ (fun τ => ρ τ (g τ)) = L x := by
      rw [hΦ]
      conv_rhs => rw [← B.sum_repr x]

      simp only [map_sum, map_smul, hB, hL]
    simpa [this] using hLU x hx
  have hmem : ∀ T, Φ T ∈ U := fun T => by
    simpa using congrArg (fun m => m T) h0
  have hj : ∀ j, B j ∈ U := by
    intro j
    have h1 := hmem fun τ => ((b τ).coord (i₀ τ)).smulRight (b τ (j τ))
    rw [hΦ, Finset.sum_eq_single i₀] at h1
    · simp only [LinearMap.smulRight_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_eq_same, one_smul, ← hB] at h1
      exact (U.smul_mem_iff hi₀).1 h1
    · intro i _ hi
      obtain ⟨τ, hτ⟩ := Function.ne_iff.1 hi
      rw [t.map_coord_zero τ, smul_zero]
      simp [Finsupp.single_eq_of_ne hτ.symm]
    · simp
  rw [eq_top_iff, ← B.span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact hj j

variable {K ι : Type} [Field K] [Fintype ι] {n : ℕ}

def tenMul (lam : ι → DomWeight n) : (∀ τ, nablaSq K n (lam τ)) →ₘₗ[K] VV K lam :=
  haveI := Classical.decEq ι
  ((MultilinearMap.mkPiAlgebra K ι (Pol K ι n)).compLinearMap fun τ =>
    (Formalism.GradedWeylDivisibility.blockEmb K τ).toLinearMap ∘ₗ (nablaSq K n (lam τ)).subtype).codRestrict (VV K lam)
    fun f => Submodule.subset_span ⟨fun τ => f τ, fun τ => (f τ).2, by simp⟩

theorem tenMul_coe (lam : ι → DomWeight n) (f : ∀ τ, nablaSq K n (lam τ)) :
    (tenMul lam f : Pol K ι n) = ten fun τ => (f τ : MvPolynomial (Fin n × Fin n) K) := by
  classical
  exact (MultilinearMap.mkPiAlgebra_apply (R := K) _).trans rfl

def ssBasis (K : Type) [Field K] (mu : DomWeight n) :
    Module.Basis (Formalism.GradedWeylDivisibility.ssIdx n n mu.natW) K (nablaSq K n mu) :=
  (Module.Basis.span (Formalism.GradedWeylDivisibility.sSBasis K n n mu.natW).choose_spec.1.1).map
    (LinearEquiv.ofEq _ _ (Formalism.GradedWeylDivisibility.sSBasis K n n mu.natW).choose_spec.1.2.1)

theorem ssBasis_coe (mu : DomWeight n) (i : Formalism.GradedWeylDivisibility.ssIdx n n mu.natW) :
    (ssBasis K mu i : MvPolynomial (Fin n × Fin n) K) = ssB K mu.natW i := by
  simp only [ssBasis, ssB, Module.Basis.map_apply, Module.Basis.span_apply]
  rfl

theorem vv_irreducible_unitary :
    ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → Formalism.BasicNotions.DomWeight n) (U : Submodule ℂ (Formalism.L2.DIV.VV ℂ lam)), (∀ g : ι → GL (Fin n) ℂ, (∀ τ, (g τ : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ x ∈ U, Formalism.L2.DIV.rhoK lam g x ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro ι _ n lam U hU
  refine eq_bot_or_top_of_tensor (G := fun _ => Matrix.unitaryGroup (Fin n) ℂ)
    (fun τ => ssBasis ℂ (lam τ)) (tenMul lam) (bVV ℂ lam) (fun i => ?_)
    (fun τ => smallRep (unitaryIncl n) (lam τ))
    (fun τ => GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible _ _ _ (isIrreducible_smallRep_unitary n (lam τ)))
    U fun g => ⟨rhoK lam fun τ => unitaryIncl n (g τ), fun f => ?_, hU _ fun τ => (g τ).2⟩
  · apply Subtype.ext
    rw [bVV_coe, tenMul_coe, bVVfun]
    simp only [ssBasis_coe]
  · apply Subtype.ext
    rw [tenMul_coe]
    change actP lam _ (tenMul lam f : Pol ℂ ι n) = _
    rw [tenMul_coe, actTen]
    rfl

end GlobalTheory.CoefIrred
end
end

section

noncomputable section

namespace GlobalTheory.Mem.SJ.HaarMove

open MeasureTheory
open scoped Pointwise

theorem exists_haar_fund {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [MeasurableSpace G'] [BorelSpace G']
    (μ' : Measure G') [μ'.IsHaarMeasure] (ι : G ≃ₜ* G') (Γ : Subgroup G) (Γ' : Set G')
    (hΓ : ∀ g, g ∈ Γ ↔ ι g ∈ Γ') (F' : Set G') (hm : MeasurableSet F') (hc : ∀ y, ∃ γ ∈ Γ', γ * y ∈ F')
    (hd : ∀ γ ∈ Γ', γ ≠ 1 → μ' ((fun y => γ * y) '' F' ∩ F') = 0) (t : G) :
    ∃ (μ : Measure G) (F : Set G), μ.IsHaarMeasure ∧ IsFundamentalDomain Γ F μ ∧
      ∀ f : G → ℂ, ∫ g in F, f g ∂μ = ∫ x in F', f (ι.symm x * t) ∂μ' := by
  let e : G' ≃ᵐ G := (ι.symm.toHomeomorph.trans (Homeomorph.mulRight t)).toMeasurableEquiv
  have he : ∀ x, e x = ι.symm x * t := fun _ => rfl
  have hes : ∀ g, e.symm g = ι (g * t⁻¹) := fun g => by
    rw [MeasurableEquiv.symm_apply_eq, he]; simp
  have hH : (μ'.map e).IsHaarMeasure := by
    have h1 : (μ'.map ι.symm).IsHaarMeasure := ι.symm.isHaarMeasure_map μ'
    have h2 : μ'.map e = (μ'.map ι.symm).map (· * t) := by
      exact (Measure.map_map (measurable_mul_const t) (map_continuous ι.symm).measurable).symm
    rw [h2]; infer_instance
  refine ⟨μ'.map e, e.symm ⁻¹' F', hH, ?_, fun f => ?_⟩
  · refine IsFundamentalDomain.mk'' (e.symm.measurable hm).nullMeasurableSet (ae_of_all _ fun g => ?_)
      (fun γ hγ => ?_) (fun γ => (measurePreserving_mul_left (μ'.map e) (γ : G)).quasiMeasurePreserving)
    · obtain ⟨γ, hγ, h⟩ := hc (e.symm g)
      refine ⟨⟨ι.symm γ, (hΓ _).2 (by simpa using hγ)⟩, ?_⟩
      show e.symm (ι.symm γ * g) ∈ F'
      rw [hes] at h ⊢
      simpa [mul_assoc] using h
    · have h0 := hd (ι γ) ((hΓ _).1 γ.2) (fun h => hγ (Subtype.ext (ι.injective (by simpa using h))))
      rw [AEDisjoint, MeasurableEquiv.map_apply]
      refine measure_mono_null ?_ h0
      rintro x ⟨⟨g, hg, hx⟩, h2⟩
      refine ⟨⟨e.symm g, hg, ?_⟩, by simpa using h2⟩
      have hx' : (γ : G) * g = ι.symm x * t := hx
      show ι γ * e.symm g = x
      rw [hes, ← map_mul, ← mul_assoc, hx']; simp
  · rw [setIntegral_map_equiv]
    simp only [he]
    congr 2
    ext x; simp

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult
open scoped InnerProductSpace TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem schur_of_bridge {D : D7} {V : HSp D} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} (M : DSModel V S)
    (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (J : Set (GA D V))
    (χ : GA D V → ℂ) (hS : ∀ μ 𝓕, SchurMult θ M J χ μ 𝓕) (hθ : IsInfFam θ)
    (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA)
    (hf : I.IsFundDom (I.muA μf) fund) (ι : GA D V ≃ₜ* I.GA) (hι : ∀ g, g ∈ GQ V ↔ ι g ∈ I.GFset) (t : GA D V)
    (T : MMap M) (hT : T ∈ Mult θ M J χ) (T' : MMap M) (hT' : T' ∈ Mult θ M J χ) :
    ∃ c : ℂ, ∀ v v' : M.Vec, ∫ x, star (T v (ι.symm x * t)) * T' v' (ι.symm x * t) ∂((I.muA μf).restrict fund) =
      c * ∏ τ, ⟪(v τ : M.H τ), (v' τ : M.H τ)⟫_ℂ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : (I.muA μf).IsHaarMeasure := by
    unfold AutInst.muA Formalism.REAL.muG; infer_instance
  obtain ⟨μ, F, hμ, hF, hint⟩ := exists_haar_fund (I.muA μf) ι (GQ V) I.GFset hι fund hf.1 hf.2.1 hf.2.2 t
  obtain ⟨c, hc⟩ := hS μ F hθ hμ hF T hT T' hT'
  exact ⟨c, fun v v' => (hint fun g => star (T v g) * T' v' g).symm.trans (hc v v').2⟩

end GlobalTheory.Mem.SJ.HaarMove

end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.existsUnique_section_compatible_square_thickening : SecBaseChangeSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] (P : PolAV (Spec (CommRingCat.of R))) (n : ℕ), 1 ≤ n → ∀ s : ∀ e : ℕ, LB.Sec (LB.LinComb (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) (K := Fin 1) (fun _ => (fstG I e P.A).left) (fun _ => (n : ℤ))), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)).ι), Good (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) z J → sval (s (e + 1)) (r ≫ thickMap R I e P.A) z J = sval (s e) r z J) → ∃! σ : H0 (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) n, ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)).ι), Good (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) z J → sval σ (r ≫ (fstG I e P.A).left) z J = sval (s e) r z J := by
  first | exact @GlobalTheory.SectionLimitSq.existsUnique_sec_of_compatible_sq | exact GlobalTheory.SectionLimitSq.existsUnique_sec_of_compatible_sq | (intros; apply GlobalTheory.SectionLimitSq.existsUnique_sec_of_compatible_sq <;> assumption)
end
