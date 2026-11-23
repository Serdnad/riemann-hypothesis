module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle118
import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle122
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle014
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle003
public import Formalism.LocalRingCardinality.Bundle002
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle053
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle102
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle121
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle108
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle123
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ColPeriod

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recWts)

theorem nuRow_succ_eq_wt (D : D7) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m) (τ : D.what₂.Tau) (n : ℕ) (hn : n < D.R.N j) :
    DV.nuRow D u (j + 1) τ n =
      ((Examples₂.wtN (D.hcW u τ) n + wG D.R ((D.hcW u τ).e ⟨j, hj⟩) (j + 1) : ℚ) : ℝ) := by
  have hw : DV.wSz D (j + 1) τ = (((D.hcW u τ).e ⟨j, hj⟩ : ℚ) : ℝ) := by
    unfold DV.wSz
    rw [dite_eq_left ⟨by omega, by omega⟩, D.hcW_e]
    rfl
  unfold DV.nuRow
  rw [hw]
  unfold DV.srcPar Examples₂.wtN Examples₂.blkN
  by_cases hk : n < D.R.k
  · rw [dite_eq_left hk, dite_eq_left hk]
    unfold hcToWeightQ rhoVec wG Ranks.N
    push_cast
    ring
  · have hb : (n - D.R.k) / (D.R.t + 1) < D.R.m := by
      have hN : n < D.R.k + j * (D.R.t + 1) := hn
      have h2 : n - D.R.k < j * (D.R.t + 1) := Nat.sub_lt_left_of_lt_add (by omega) hN
      have h3 : (n - D.R.k) / (D.R.t + 1) < j := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact h2)
      omega
    rw [dite_eq_right hk, dite_eq_right hk, dite_eq_left hb, dite_eq_left hb]
    have hnat : n = D.R.k + (n - D.R.k) / (D.R.t + 1) * (D.R.t + 1) + (n - D.R.k) % (D.R.t + 1) := by
      have := Nat.div_add_mod (n - D.R.k) (D.R.t + 1)
      rw [mul_comm] at this
      omega
    have key : (n : ℝ) = (D.R.k : ℝ) + (((n - D.R.k) / (D.R.t + 1) : ℕ) : ℝ) * ((D.R.t : ℝ) + 1)
        + (((n - D.R.k) % (D.R.t + 1) : ℕ) : ℝ) := by
      conv_lhs => rw [hnat]
      push_cast
      ring
    unfold wG Ranks.N
    push_cast
    linear_combination key

theorem partitionSize : PartitionSize := by
  intro D EX u j hj τ
  unfold nuAbs
  show ∑ i ∈ Finset.range (D.R.N j), DV.nuRow D u (j + 1) τ i = _
  rw [Finset.sum_range, Int.cast_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [nuRow_succ_eq_wt D u j hj τ a a.2]
  have h1 := Wts.nuW_eq (recWts EX) u hj τ a
  have h2 := lamOf_wtN ((recWts EX).hc u τ) hj.le a
  have h3 : (((recWts EX).nuW u (j + 1) τ).w a : ℝ) = ((((recWts EX).nuW u (j + 1) τ).w a : ℚ) : ℝ) := by
    simp
  rw [h3, h1]
  unfold Wts.lamN
  rw [h2]
  rfl

end GlobalTheory.ColPeriod
end
end

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix

namespace GlobalTheory.PlaceComp.StabLoc

section Ring

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (O : Subring R)

theorem mem_range_iff (m : GL n R) :
    m ∈ (Formalism.UG.bc (n := n) O.subtype).range ↔
      ∀ y : n → R, (∀ i, y i ∈ O) ↔ ∀ i, m.1.mulVec y i ∈ O := by
  have key : ∀ (A : Matrix n n R), (∀ i j, A i j ∈ O) → ∀ y : n → R, (∀ i, y i ∈ O) →
      ∀ i, A.mulVec y i ∈ O := fun A hA y hy i =>
    O.sum_mem fun j _ => O.mul_mem (hA i j) (hy j)
  have hs : ∀ j i : n, (Pi.single j (1 : R) : n → R) i ∈ O := by
    intro j i
    by_cases h : i = j
    · subst h; simp [O.one_mem]
    · simp [h, O.zero_mem]
  constructor
  · rintro ⟨k, rfl⟩ y
    refine ⟨key _ (fun i j => (k.1 i j).2) y, fun h => ?_⟩
    have := key (Formalism.UG.bc (n := n) O.subtype k⁻¹).1 (fun i j => ((k⁻¹).1 i j).2) _ h
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.one_mulVec] at this
  · intro h
    have h1 : ∀ i j, m.1 i j ∈ O := fun i j => by
      simpa using (h (Pi.single j 1)).1 (hs j) i
    have h2 : ∀ i j, (m⁻¹).1 i j ∈ O := fun i j => by
      have := (h ((m⁻¹).1.mulVec (Pi.single j 1))).2 (by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
        exact hs j) i
      rwa [Matrix.mulVec_single_one] at this
    let A : Matrix n n O := Matrix.of fun i j => ⟨m.1 i j, h1 i j⟩
    let B : Matrix n n O := Matrix.of fun i j => ⟨(m⁻¹).1 i j, h2 i j⟩
    have hA : O.subtype.mapMatrix A = m.1 := rfl
    have hB : O.subtype.mapMatrix B = (m⁻¹).1 := rfl
    have hinj : Function.Injective (O.subtype.mapMatrix : Matrix n n O →+* Matrix n n R) :=
      fun X Y hXY => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun hXY i) j)
    refine ⟨⟨A, B, hinj ?_, hinj ?_⟩, Units.ext rfl⟩
    · rw [map_mul, hA, hB, map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    · rw [map_mul, hA, hB, map_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]

end Ring

theorem stab_iff (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : CMData F E) (V : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (h : GL (Fin V.rank) (Fv F v ⊗[F] E))
    (hh : IsFrameAt V v h) (g : HA (AF F) hc.sig V.gram) (hg : ∀ w, w ≠ v → locMat hc V w g = 1) :
    Stab hc V g ↔
      h⁻¹ * locMat hc V v g * h ∈ (Formalism.UG.bc (n := Fin V.rank) (ordAt E v).subtype).range := by
  have hev : ∀ w (y : Fin V.rank → Af F ⊗[F] E),
      (fun i => evF E w ((finMat hc.sig V.gram g).mulVec y i)) =
        (locMat hc V w g).1.mulVec fun i => evF E w (y i) := fun w y => by
    funext i
    rw [locMat_val]
    exact RingHom.map_mulVec (evF E w) _ y i
  have hloc : Stab hc V g ↔ ∀ x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v ↔
      (locMat hc V v g).1.mulVec x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v := by
    constructor
    · intro hs x
      have hx : ∀ w, w ≠ v → (fun i => evF E w (sgT E v (x i))) = 0 := fun w hw =>
        funext fun i => evF_sgT_ne hw _
      have hxv : (fun i => evF E v (sgT E v (x i))) = x := funext fun i => evF_sgT_self v _
      have := hs fun i => sgT E v (x i)
      rw [mem_lamHat_iff, mem_lamHat_iff] at this
      simp only [hev] at this
      constructor
      · intro h0
        have h1 := this.1 (fun w => by
          by_cases hw : w = v
          · subst hw; rw [hxv]; exact h0
          · rw [hx w hw]; exact zero_mem _) v
        rwa [hxv] at h1
      · intro h0
        have h1 := this.2 (fun w => by
          by_cases hw : w = v
          · subst hw; rw [hxv]; exact h0
          · rw [hx w hw, Matrix.mulVec_zero]; exact zero_mem _) v
        rwa [hxv] at h1
    · intro hs y
      rw [mem_lamHat_iff, mem_lamHat_iff]
      refine forall_congr' fun w => ?_
      rw [hev]
      by_cases hw : w = v
      · subst hw; exact hs _
      · rw [hg w hw, Units.val_one, Matrix.one_mulVec]
  rw [hloc, mem_range_iff]
  constructor
  · intro hs y
    have := hs (h.1.mulVec y)
    rw [hh, hh, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
    rwa [Units.val_mul, Units.val_mul]
  · intro hs x
    have := hs ((h⁻¹).1.mulVec x)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_right, Units.val_mul,
      ← Matrix.mulVec_mulVec] at this
    rw [hh, hh]
    exact this

end GlobalTheory.PlaceComp.StabLoc
end

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix

namespace GlobalTheory.PlaceComp.IntLocal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_int_generators (E : Type) [Field E] [NumberField E] :
    ∃ (k : ℕ) (x : Fin k → 𝓞 E), ∀ w : 𝓞 E, ∃ n : Fin k → ℤ, w = ∑ j, n j • x j := by
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  refine ⟨k, s, fun w => ?_⟩
  have : w ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨n, hn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 this
  exact ⟨n, hn.symm⟩


omit [NumberField E] in
theorem mem_addClosure_of_mem_ordAt (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E)
    (hy : y ∈ ordAt E v) :
    y ∈ AddSubgroup.closure
      {y : Fv F v ⊗[F] E | ∃ a ∈ v.adicCompletionIntegers F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} := by
  have h := Subring.mem_closure_iff.1 hy
  refine AddSubgroup.closure_mono ?_ h
  intro z hz
  induction hz using Submonoid.closure_induction with
  | mem z hz => exact hz
  | one => exact ⟨1, one_mem _, 1, rfl⟩
  | mul z w _ _ hz hw =>
    obtain ⟨a, ha, x, rfl⟩ := hz
    obtain ⟨b, hb, x', rfl⟩ := hw
    exact ⟨a * b, mul_mem ha hb, x * x', by
      rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl⟩


omit [NumberField E] in
theorem exists_coeff {k : ℕ} (x : Fin k → 𝓞 E)
    (hx : ∀ w : 𝓞 E, ∃ n : Fin k → ℤ, w = ∑ j, n j • x j) (v : HeightOneSpectrum (𝓞 F))
    (y : Fv F v ⊗[F] E) (hy : y ∈ ordAt E v) :
    ∃ a : Fin k → Fv F v, (∀ j, a j ∈ v.adicCompletionIntegers F) ∧
      y = ∑ j, a j ⊗ₜ[F] (x j : E) := by
  have hy' := mem_addClosure_of_mem_ordAt v y hy
  clear hy
  induction hy' using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, w, rfl⟩ := hy
    obtain ⟨n, rfl⟩ := hx w
    refine ⟨fun j => n j • a, fun j => zsmul_mem ha _, ?_⟩
    show a ⊗ₜ[F] (algebraMap (𝓞 E) E (∑ j, n j • x j)) =
      ∑ j, (n j • a) ⊗ₜ[F] (algebraMap (𝓞 E) E (x j))

    simp only [map_sum, map_zsmul, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.smul_tmul]
  | zero => exact ⟨0, fun _ => zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, ea⟩ := hy
    obtain ⟨b, hb, eb⟩ := hz
    exact ⟨a + b, fun j => add_mem (ha j) (hb j), by
      simp only [Pi.add_apply, ea, eb, TensorProduct.add_tmul, Finset.sum_add_distrib]⟩
  | neg y _ hy =>
    obtain ⟨a, ha, ea⟩ := hy
    exact ⟨-a, fun j => neg_mem (ha j), by
      simp only [Pi.neg_apply, ea, TensorProduct.neg_tmul, Finset.sum_neg_distrib]⟩

theorem mem_intA_iff :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (z : Af F ⊗[F] E),
      z ∈ intA F E ↔ ∀ v : HeightOneSpectrum (𝓞 F), evF E v z ∈ ordAt E v := by
  intro F E _ _ _ _ _ z
  constructor
  · intro hz v
    induction hz using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hy
      exact Subring.subset_closure ⟨_, ha v, x, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg]; exact neg_mem hy
  · intro h
    obtain ⟨k, x, hx⟩ := exists_int_generators E
    choose a ha ea using fun v => exists_coeff x hx v _ (h v)
    let A : Fin k → Af F := fun j =>
      ⟨fun v => a v j, Filter.Eventually.of_forall fun v => ha v j⟩
    have e : z = ∑ j, A j ⊗ₜ[F] (x j : E) := by
      apply evF_ext
      intro v

      rw [ea v, map_sum]
      exact Finset.sum_congr rfl fun j _ => rfl
    rw [e]
    exact sum_mem fun j _ => AddSubgroup.subset_closure ⟨A j, fun v => ha v j, x j, rfl⟩

end GlobalTheory.PlaceComp.IntLocal
end

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.InertCompare Classical

namespace GlobalTheory.InertCompare

open Formalism.FrobeniusOrbits GlobalTheory.Proof.IdempotentLatticeSequence

theorem ne_of_inert (D : D7) (l : ℕ) (h : IsResidueClassZero D l ∨ IsSg D l) : l ∉ D.host.small ∧ l ≠ D.host.q ∧ l ≠ D.host.d := by
  rcases h with h | h
  · have k := (primeClass_eq_inert_iff D.host.toHostRaw).1 h
    exact ⟨k.1, k.2.1, k.2.2.1⟩
  · have k := (primeClass_eq_signal_iff D.host.toHostRaw).1 h
    exact ⟨k.1, k.2.1, k.2.2.1⟩

theorem primeOf_liesOver {l : ℕ} [Fact l.Prime] {E : Type} [Field E] (ρ : E →+* ℂ_[l]) :
    (primeOf ρ).LiesOver (Ideal.span {(l : ℤ)}) := by
  have := primeOf_isPrime ρ
  refine ⟨(span_prime_isMaximal l Fact.out).eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
  exact natCast_mem_primeOf ρ

theorem galE_frob_snd (D : D7) (l : ℕ) [Fact l.Prime] (h2 : l ∉ D.host.small) (hq : l ≠ D.host.q) (hd : l ≠ D.host.d)
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})]
    (σ : D.host.E ≃ₐ[ℚ] D.host.E) (hσ : IsArithFrobAt ℤ σ P) :
    (D.host.galE σ).2 = D.R.iota (G.hP D l) := by
  have hc : l.Coprime D.host.condN :=
    (Nat.Prime.coprime_iff_not_dvd Fact.out).2 (UpperTheory.Small.not_dvd_condN D.host Fact.out h2 hq hd)
  have hne : ∃ g, g ∈ Formalism.MainNotions.G.frobSet D l := ⟨_, P, inferInstance, inferInstance, σ, hσ, rfl⟩
  obtain ⟨P₀, hP₀, hL₀, σ₀, hσ₀, hg₀⟩ := Classical.epsilon_spec hne
  have e1 := (D.host.toHostAx.frob_iff l hc P σ).1 hσ
  have e2 := (@Formalism.HC.HostAx.frob_iff _ D.host.toHostAx l _ hc P₀ hP₀ hL₀ σ₀).1 hσ₀
  unfold Formalism.MainNotions.G.hP
  rw [Formalism.HC.Frame.iota_iotaInv, ← hg₀]
  exact congrArg Prod.snd (e1.trans e2.symm)

theorem plGG_posPl_one (D : D7) (l : ℕ) [Fact l.Prime] (h : IsResidueClassZero D l ∨ IsSg D l)
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})]
    (σ : D.host.E ≃ₐ[ℚ] D.host.E) (hσ : IsArithFrobAt ℤ σ P) (z : Bool × HH D) :
    plGG D (posPl D l z 1) = plGG D z * D.host.galE σ * D.R.cc := by
  obtain ⟨h2, hq, hd⟩ := ne_of_inert D l h
  have hC := factClassFrob D.R D.host l (UpperTheory.Small.not_dvd_condN D.host Fact.out h2 hq hd) P σ hσ
  have hH := galE_frob_snd D l h2 hq hd P σ hσ
  have hpl : ∀ z : Bool × HH D, plGG D z = ((if z.1 then -1 else 1, 1), D.R.iota z.2) := by
    rintro ⟨b, t⟩
    cases b <;> rfl
  rw [hpl, hpl]
  refine Prod.ext ?_ ?_
  · rcases h with h | h
    · have h1 := hC.2.2.1 h
      have hs : ¬ IsSg D l := fun hs => by
        have := h.symm.trans hs
        cases this
      simp only [Prod.fst_mul, h1, Formalism.HC.Frame.cc, c0, posPl, partner, hs]
      cases z.1 <;> simp
    · have h1 := hC.2.1.1 h
      have hp : (partner D l z.2 1).1 = true := decide_eq_true ⟨h, odd_one⟩
      simp only [Prod.fst_mul, h1, Formalism.HC.Frame.cc, c0, posPl, hp]
      cases z.1 <;> simp
  · simp only [Prod.snd_mul, Formalism.HC.Frame.cc, mul_one, hH, posPl, partner, one_smul]
    rw [Formalism.HC.Frame.iota_add]

theorem exists_frob_step (D : D7) (l : ℕ) [Fact l.Prime] (h : IsResidueClassZero D l ∨ IsSg D l)
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})] :
    ∃ φ : D.host.E ≃ₐ[ℚ] D.host.E, IsArithFrobAt ℤ φ P ∧ ∀ z : Bool × HH D,
      plGG D (posPl D l z 1) = plGG D z * D.host.galE φ * D.R.cc := by
  obtain ⟨h2, hq, hd⟩ := ne_of_inert D l h
  obtain ⟨φ, hφ⟩ := (D.host.der.frob l (UpperTheory.Small.not_dvd_condN D.host Fact.out h2 hq hd) P).1
  exact ⟨φ, hφ, plGG_posPl_one D l h P φ hφ⟩

theorem embT_tauPl (D : D7) (z : Bool × HH D) : embT D (tauPl D z) = D.host.emb (plGG D z) := by
  unfold embT tauPl
  rw [Equiv.apply_symm_apply]

theorem emb_mul_galE {R : Ranks} (H : Formalism.BasicNotions.Host R) (g : R.GG) (σ : H.E ≃ₐ[ℚ] H.E) (x : H.E) :
    H.emb (g * H.galE σ) x = H.emb g (σ x) := by
  have he : H.sigmaOf (g * H.galE σ) = H.sigmaOf g * σ := by
    unfold Host.sigmaOf
    rw [map_mul, MulEquiv.symm_apply_apply]
  change H.φ₀ (H.sigmaOf (g * H.galE σ) x) = H.φ₀ ((H.sigmaOf g * σ) x)
  rw [he]

theorem rhoH_posPl_one (D : D7) (l : ℕ) [Fact l.Prime] (lam : Qbar →+* ℂ_[l]) (h : IsResidueClassZero D l ∨ IsSg D l)
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})]
    (σ : D.host.E ≃ₐ[ℚ] D.host.E) (hσ : IsArithFrobAt ℤ σ P) (z : Bool × HH D) (x : D.host.E) :
    rhoH D lam (tauPl D (posPl D l z 1)) x = rhoH D lam (tauPl D z) (σ (D.host.conj x)) := by
  rw [rhoH_apply, rhoH_apply, embT_tauPl, embT_tauPl, plGG_posPl_one D l h P σ hσ z,
    ← D.host.galE_conjE, emb_mul_galE, emb_mul_galE]

theorem samePrime_step : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (lam : Qbar →+* ℂ_[l]), (IsResidueClassZero D l ∨ IsSg D l) →
    ∀ z : Bool × HH D, SamePrime (rhoH D lam (tauPl D (posPl D l z 1))) (rhoC D lam (tauPl D z)) := by
  intro D l _ lam h z a
  have := primeOf_isPrime (rhoH D lam (tauPl D z))
  have := primeOf_liesOver (rhoH D lam (tauPl D z))
  obtain ⟨φ, hφ, -⟩ := exists_frob_step D l h (primeOf (rhoH D lam (tauPl D z)))
  rw [rhoH_posPl_one D l lam h _ φ hφ]
  have hc := AlgHom.IsArithFrobAt.comap_eq hφ
  have := Ideal.ext_iff.1 hc (D.host.conj • a)
  exact this

end GlobalTheory.InertCompare
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.UnlinkedMono

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem noMonodromy_of_mem_weilDeligneListSum : ∀ (l : List (WD h)), (sumList l).mono0 → ∀ y ∈ l, y.mono0
  | [], _, y, hy => by simp at hy
  | z :: l, H, y, hy => by
    have hsum := (WD.monomial_sum_iff z (sumList l)).mp H
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hsum.1
    · exact noMonodromy_of_mem_weilDeligneListSum l hsum.2 y hy

theorem lpTw_one_ne (x : WD h) (hx : 0 < x.lpDim) : x.lpTw 1 ≠ x := GlobalTheory.WeilDeligne.WD.lpTw_one_ne x hx

section
variable {V V' W W' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  [AddCommGroup W'] [Module ℂ W'] [FiniteDimensional ℂ W']

end

end GlobalTheory.UnlinkedMono
end
end

section

open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

namespace GlobalTheory

theorem classPres_dcOp_adjoint_commute : ∀ {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K] [StarRing K] (ι : Γ →* G) (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (P : ClassPres ι S σ ρ J χ) (L : Subgroup G) (x : G) (A A' B : Finset G) (T T' U : Module.End K S.Forms), (∀ γ u u', inner ℂ (ρ γ u) (ρ γ u') = inner ℂ u u') → (∀ k, ‖(χ k : ℂ)‖ = 1) → (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l) → (∀ k : J, (k : G) ∈ L → χ k = 1) → (∀ a ∈ A, a ∈ L) → (∀ a ∈ A', a ∈ L) → IsDC J x A → IsDC J x⁻¹ A' → (∀ f : S.Forms, P.ext ((T f : S.Forms) : S.Cl → S.V) = dcOp A (P.ext (f : S.Cl → S.V))) → (∀ f : S.Forms, P.ext ((T' f : S.Forms) : S.Cl → S.V) = dcOp A' (P.ext (f : S.Cl → S.V))) → (∀ f : S.Forms, P.ext ((U f : S.Forms) : S.Cl → S.V) = dcOp B (P.ext (f : S.Cl → S.V))) → (∀ f g : S.Forms, S.csum ((T f : S.Forms) : S.Cl → S.V) (g : S.Cl → S.V) = S.csum (f : S.Cl → S.V) ((T' g : S.Forms) : S.Cl → S.V)) ∧ ((∀ F ∈ AdForms ι ρ J χ, dcOp A (dcOp B F) = dcOp B (dcOp A F)) → Commute T U) := by
  intro G Γ W K _ _ _ _ _ _ _ ι S σ ρ J χ P L x A A' B T T' U hρ hχ hJ hχL hA hA' hx hx' hT hT' hU
  obtain ⟨hmem, hiso, -, -, hinj⟩ := classPres_basic ι S σ ρ J χ P
  refine ⟨fun f g => ?_, fun hc => ?_⟩
  · apply σ.injective
    rw [← hiso, ← hiso, hT, hT']
    exact GlobalTheory.T.adelicInner_doubleCosetOp_adjoint ι ρ J L χ P.y x A A' hρ hχ P.reps
      (fun c => Finite.of_equiv _ (P.stabI c).toEquiv) hJ hχL hA hA' hx hx' _ (hmem f) _ (hmem g)
  · refine LinearMap.ext fun f => hinj ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, P.extL_apply, P.extL_apply, hT, hU, hU, hT]
    exact hc _ (hmem f)

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

theorem _root_.GlobalTheory.T.kernelDatum_periodIdeal_fg_and_selfDual : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.amb.AA.FG ∧ ∀ u μ i c, IsSdLat ((t.rd u μ).N i c) := by
  first | exact @GlobalTheory.TieLat.tie_AA_fg_and_sd | exact GlobalTheory.TieLat.tie_AA_fg_and_sd | (intros; apply GlobalTheory.TieLat.tie_AA_fg_and_sd <;> assumption)
end
