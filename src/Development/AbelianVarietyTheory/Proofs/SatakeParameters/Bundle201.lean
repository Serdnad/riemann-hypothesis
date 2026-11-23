module

public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle183
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle138
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPowLocKMulInf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle123
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle131
import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Formalism.SharpRestriction.ParConsts
public import Formalism.LocalRingCardinality.Bundle008
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle130
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle092
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle085
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle091
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle195
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle149
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DivUnique

section Abstract

variable {R K : Type} [CommRing R] [CommRing K] {n : ℕ}

theorem read_one {Λ : (Fin n → R) → Prop} {O : R → Prop} {OK : Subring K} {ε : R} (φ : R →+* K) (s : K → R)
    (hs : ∀ t, φ (s t) = t) (hε : φ ε = 1) (hO : ∀ x, O x → φ x ∈ OK) (hO' : ∀ t ∈ OK, O (s t))
    {B B' : Matrix (Fin n) (Fin n) R}
    (h1 : ∀ z : Fin n → R, (∀ i, O (z i)) → Λ (ε • B *ᵥ z))
    (h2 : ∀ y, Λ y → ∃ z : Fin n → R, (∀ i, O (z i)) ∧ ε • y = ε • B' *ᵥ z)
    (w : Fin n → K) (hw : ∀ i, w i ∈ OK) :
    ∃ w' : Fin n → K, (∀ i, w' i ∈ OK) ∧ B.map φ *ᵥ w = B'.map φ *ᵥ w' := by
  have mv : ∀ (M : Matrix (Fin n) (Fin n) R) x, φ ∘ (M *ᵥ x) = M.map φ *ᵥ (φ ∘ x) := fun M x =>
    funext fun i => RingHom.map_mulVec φ M x i
  have sm : ∀ x : Fin n → R, φ ∘ (ε • x) = φ ∘ x := fun x => funext fun i => by simp [hε]
  have ss : φ ∘ (s ∘ w) = w := funext fun i => hs _
  obtain ⟨z, hz, e⟩ := h2 _ (h1 (s ∘ w) fun i => hO' _ (hw i))
  refine ⟨φ ∘ z, fun i => hO _ (hz i), ?_⟩
  calc B.map φ *ᵥ w = φ ∘ (B *ᵥ (s ∘ w)) := by rw [mv, ss]
    _ = φ ∘ (ε • (ε • B *ᵥ (s ∘ w))) := by rw [sm, sm]
    _ = φ ∘ (ε • B' *ᵥ z) := by rw [e]
    _ = B'.map φ *ᵥ (φ ∘ z) := by rw [sm, mv]

theorem read_step {Λ : (Fin n → R) → Prop} {O : R → Prop} {OK : Subring K} {ε : R} (φ : R →+* K) (s : K → R)
    (hs : ∀ t, φ (s t) = t) (hε : φ ε = 1) (hO : ∀ x, O x → φ x ∈ OK) (hO' : ∀ t ∈ OK, O (s t))
    {A B B' : Matrix (Fin n) (Fin n) R} {u u' : Fin n → R}
    (h4 : ∀ z : Fin n → R, (∀ i, O (z i)) → ∃ y, Λ y ∧ ε • A *ᵥ y = ε • B *ᵥ (fun i => u i * z i))
    (h3 : ∀ y, Λ y → ∃ z : Fin n → R, (∀ i, O (z i)) ∧ ε • A *ᵥ y = ε • B' *ᵥ (fun i => u' i * z i))
    (w : Fin n → K) (hw : ∀ i, w i ∈ OK) :
    ∃ w' : Fin n → K, (∀ i, w' i ∈ OK) ∧
      (B.map φ * Matrix.diagonal (fun i => φ (u i))) *ᵥ w =
        (B'.map φ * Matrix.diagonal (fun i => φ (u' i))) *ᵥ w' := by
  have mv : ∀ (M : Matrix (Fin n) (Fin n) R) x, φ ∘ (M *ᵥ x) = M.map φ *ᵥ (φ ∘ x) := fun M x =>
    funext fun i => RingHom.map_mulVec φ M x i
  have sm : ∀ x : Fin n → R, φ ∘ (ε • x) = φ ∘ x := fun x => funext fun i => by simp [hε]
  have hu : ∀ u z : Fin n → R, φ ∘ (fun i => u i * z i) = Matrix.diagonal (fun i => φ (u i)) *ᵥ (φ ∘ z) :=
    fun u z => funext fun i => by simp [Matrix.mulVec_diagonal]
  have ss : φ ∘ (s ∘ w) = w := funext fun i => hs _
  obtain ⟨y, hy, e⟩ := h4 (s ∘ w) fun i => hO' _ (hw i)
  obtain ⟨z, hz, e'⟩ := h3 y hy
  refine ⟨φ ∘ z, fun i => hO _ (hz i), ?_⟩
  calc (B.map φ * Matrix.diagonal (fun i => φ (u i))) *ᵥ w
      = φ ∘ (B *ᵥ (fun i => u i * (s ∘ w) i)) := by rw [mv, hu, ss, Matrix.mulVec_mulVec]
    _ = φ ∘ (ε • B *ᵥ (fun i => u i * (s ∘ w) i)) := (sm _).symm
    _ = φ ∘ (ε • B' *ᵥ (fun i => u' i * z i)) := by rw [← e, e']
    _ = (B'.map φ * Matrix.diagonal (fun i => φ (u' i))) *ᵥ (φ ∘ z) := by
      rw [sm, mv, hu, Matrix.mulVec_mulVec]

theorem coset (OK : Subring K) {b b' c c' T T' U : Matrix (Fin n) (Fin n) K}
    (hb : c * b = 1) (hb' : c' * b' = 1) (hT : T' * T = 1)
    (H1 : ∀ y : Fin n → K, (∀ i, y i ∈ OK) → ∃ z : Fin n → K, (∀ i, z i ∈ OK) ∧ b *ᵥ y = b' *ᵥ z)
    (H2 : ∀ y : Fin n → K, (∀ i, y i ∈ OK) → ∃ z : Fin n → K, (∀ i, z i ∈ OK) ∧ b' *ᵥ y = b *ᵥ z)
    (H3 : ∀ y : Fin n → K, (∀ i, y i ∈ OK) → ∃ z : Fin n → K, (∀ i, z i ∈ OK) ∧ (b * T) *ᵥ y = (b' * U) *ᵥ z)
    (H4 : ∀ y : Fin n → K, (∀ i, y i ∈ OK) → ∃ z : Fin n → K, (∀ i, z i ∈ OK) ∧ (b' * U) *ᵥ y = (b * T) *ᵥ z) :
    ∃ k₁ ∈ (Formalism.UG.bc (n := Fin n) OK.subtype).range, ∃ k₂ ∈ (Formalism.UG.bc (n := Fin n) OK.subtype).range,
      k₁.1 * T * k₂.1 = U := by
  obtain ⟨M, hM⟩ := GlobalTheory.PlaceDiv.exists_factor OK b b' H1
  obtain ⟨N, hN⟩ := GlobalTheory.PlaceDiv.exists_factor OK b' b H2
  obtain ⟨M₂, hM₂⟩ := GlobalTheory.PlaceDiv.exists_factor OK (b * T) (b' * U) H3
  obtain ⟨N₂, hN₂⟩ := GlobalTheory.PlaceDiv.exists_factor OK (b' * U) (b * T) H4
  have hMN : M.map OK.subtype * N.map OK.subtype = 1 := by
    calc M.map OK.subtype * N.map OK.subtype = c' * b' * (M.map OK.subtype * N.map OK.subtype) := by
          rw [hb', Matrix.one_mul]
      _ = c' * (b' * M.map OK.subtype * N.map OK.subtype) := by simp only [Matrix.mul_assoc]
      _ = c' * b' := by rw [← hM, ← hN]
      _ = 1 := hb'
  have hl : T' * c * (b * T) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc c, hb, Matrix.one_mul, hT]
  have hNM : N₂.map OK.subtype * M₂.map OK.subtype = 1 := by
    calc N₂.map OK.subtype * M₂.map OK.subtype
        = T' * c * (b * T) * (N₂.map OK.subtype * M₂.map OK.subtype) := by rw [hl, Matrix.one_mul]
      _ = T' * c * (b * T * N₂.map OK.subtype * M₂.map OK.subtype) := by simp only [Matrix.mul_assoc]
      _ = T' * c * (b * T) := by rw [← hN₂, ← hM₂]
      _ = 1 := hl
  obtain ⟨k₁, hk₁, e₁⟩ := GlobalTheory.PlaceDiv.mem_range_of_mul_eq_one OK M N hMN
  obtain ⟨k₂, hk₂, e₂⟩ := GlobalTheory.PlaceDiv.mem_range_of_mul_eq_one OK N₂ M₂ hNM
  refine ⟨k₁, hk₁, k₂, hk₂, ?_⟩
  rw [e₁, e₂]
  calc M.map OK.subtype * T * N₂.map OK.subtype = c' * b' * (M.map OK.subtype * T * N₂.map OK.subtype) := by
        rw [hb', Matrix.one_mul]
    _ = c' * (b' * M.map OK.subtype * T * N₂.map OK.subtype) := by simp only [Matrix.mul_assoc]
    _ = c' * (b' * U) := by rw [← hM, ← hN₂]
    _ = U := by rw [← Matrix.mul_assoc, hb', Matrix.one_mul]

end Abstract



theorem div_unique : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E) (d d' : List ℤ) (g : GA D V), IsPrimeIdem P e f → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → d.Pairwise (fun a b => b ≤ a) → d'.Pairwise (fun a b => b ≤ a) → DivAt V e (ϖ : D.host.E) d g → DivAt V e (ϖ : D.host.E) d' g → d = d' := by
  intro D V P e f ϖ d d' g hP h1 h2 hd hd' hD hD'
  have he : e * e = e := by
    rcases id hP with ⟨hs, -⟩ | ⟨rfl, -⟩
    · exact hs.1.1
    · exact ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P _ _ hP).1
  obtain ⟨φ, s, hs, hε, -, hO, hO', hinc⟩ :=
    GlobalTheory.SphLabelOps.exists_component he (GlobalTheory.SphLabelOps.tie_of_isPrimeIdem hP)
  have hee : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, he]
  rw [GlobalTheory.DivDual.divAt_iff] at hD hD'
  obtain ⟨l, B, b1, b2, b3, b4⟩ := hD
  obtain ⟨l', B', b1', b2', b3', b4'⟩ := hD'
  obtain ⟨C, -, c2⟩ := (GlobalTheory.LatIntFacts.int_facts V).2.2 _ B hee fun y hy => (b2 y hy).imp fun _ h => h.2
  obtain ⟨C', -, c2'⟩ := (GlobalTheory.LatIntFacts.int_facts V).2.2 _ B' hee fun y hy => (b2' y hy).imp fun _ h => h.2
  have mp : ∀ X Y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E),
      finPart D e • (X * Y) = finPart D e • (1 : Matrix (Fin V.rank) (Fin V.rank) _) → X.map φ * Y.map φ = 1 := by
    intro X Y hXY
    rw [← Matrix.map_mul, ← Matrix.map_one φ (map_zero φ) (map_one φ)]
    refine Matrix.ext fun i j => ?_
    have := congrArg φ (congrFun (congrFun hXY i) j)
    rwa [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul, hε, one_mul,
      one_mul] at this
  have hv : Formalism.UG.IsUnifV D.host.E P (algebraMap D.host.E _ (ϖ : D.host.E)) :=
    (P.valuedAdicCompletion_eq_valuation' (ϖ : D.host.E)).trans
      ((P.valuation_of_algebraMap ϖ).trans (GlobalTheory.LatIntFacts.intValuation_uniformiser P h1 h2))
  have h0 := Formalism.UG.P.cartan_unif_ne_zero D.host.E P _ hv
  have e1 : ∀ a : List ℤ, (Matrix.diagonal fun i : Fin V.rank =>
      φ (finPart D (incA D ((ϖ : D.host.E) ^ (a.getD i.1 0))))) =
      Formalism.UG.diagPow D.host.E P (algebraMap D.host.E _ (ϖ : D.host.E)) fun i : Fin V.rank => a.getD i.1 0 := by
    intro a
    unfold Formalism.UG.diagPow
    congr 1
    funext i
    rw [hinc, map_zpow₀]
  have hinv : (Matrix.diagonal fun i : Fin V.rank => (algebraMap D.host.E (P.adicCompletion D.host.E) (ϖ : D.host.E)) ^ (-(d.getD i.1 0))) *
      Formalism.UG.diagPow D.host.E P (algebraMap D.host.E _ (ϖ : D.host.E)) (fun i : Fin V.rank => d.getD i.1 0) = 1 := by
    unfold Formalism.UG.diagPow
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← zpow_add₀ h0, neg_add_cancel, zpow_zero]
  obtain ⟨k₁, hk₁, k₂, hk₂, hk⟩ := coset (Formalism.UG.Ov D.host.E P) (b := B.map φ) (b' := B'.map φ)
    (c := C.map φ) (c' := C'.map φ)
    (T := Formalism.UG.diagPow D.host.E P (algebraMap D.host.E _ (ϖ : D.host.E)) fun i : Fin V.rank => d.getD i.1 0)
    (U := Formalism.UG.diagPow D.host.E P (algebraMap D.host.E _ (ϖ : D.host.E)) fun i : Fin V.rank => d'.getD i.1 0)
    (mp _ _ c2) (mp _ _ c2') hinv
    (read_one (Λ := fun y => y ∈ Formalism.L2.NTheta.LamHat V) (O := fun x => x ∈ intAE D) φ s hs hε hO hO' b1 b2')
    (read_one (Λ := fun y => y ∈ Formalism.L2.NTheta.LamHat V) (O := fun x => x ∈ intAE D) φ s hs hε hO hO' b1' b2)
    (by
      rw [← e1, ← e1]
      exact read_step (Λ := fun y => y ∈ Formalism.L2.NTheta.LamHat V) (O := fun x => x ∈ intAE D) φ s hs hε hO hO' b4 b3')
    (by
      rw [← e1, ← e1]
      exact read_step (Λ := fun y => y ∈ Formalism.L2.NTheta.LamHat V) (O := fun x => x ∈ intAE D) φ s hs hε hO hO' b4' b3)
  have anti : ∀ a : List ℤ, a.length = V.rank → a.Pairwise (fun a b => b ≤ a) →
      Antitone fun i : Fin V.rank => a.getD i.1 0 := by
    intro a la ha i j hij
    rcases hij.eq_or_lt with rfl | hlt
    · exact le_rfl
    · have hi : i.1 < a.length := by rw [la]; exact i.2
      have hj : j.1 < a.length := by rw [la]; exact j.2
      simp only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
      exact List.pairwise_iff_getElem.1 ha _ _ hi hj hlt
  have key := Formalism.UG.Final.CartanUnique D.host.E P V.rank _ (Formalism.UG.P.cartan_unif_lt_one D.host.E P _ hv).le hv
    _ _ (anti d l hd) (anti d' l' hd') k₁ hk₁ k₂ hk₂ hk
  refine List.ext_getElem (l.trans l'.symm) fun i hi hi' => ?_
  have := congrFun key ⟨i, by rw [← l]; exact hi⟩
  simpa only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] using this

end GlobalTheory.DivUnique
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

noncomputable section

namespace GlobalTheory.KerTie.MuqUnit

theorem dvd_absNorm_of_mem {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {p : ℕ} (hp : p.Prime)
    (h : ((p : ℕ) : 𝓞 E) ∈ P.asIdeal) : p ∣ Ideal.absNorm P.asIdeal := by
  by_contra hn
  have hc : IsCoprime ((p : ℤ)) ((Ideal.absNorm P.asIdeal : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hn)
  obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom (𝓞 E))
  have h1 : (1 : 𝓞 E) ∈ P.asIdeal := by
    rw [← hab]
    refine P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ ?_) (P.asIdeal.mul_mem_left _ ?_)
    · simpa using h
    · simpa using Ideal.absNorm_mem P.asIdeal
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem exists_coprime_mul_isIntegral {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) (x : K)
    (h : ∀ w : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ w.asIdeal → w.valuation K x ≤ 1) :
    ∃ M : ℕ, M.Coprime p ∧ IsIntegral ℤ ((M : K) * x) := by
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy0, hyint⟩ := halg.exists_integral_multiple
  have hd0 : y.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hy0
  have hdint : IsIntegral ℤ ((y.natAbs : K) * x) := by
    rcases Int.natAbs_eq y with e | e
    · have e2 : ((y.natAbs : ℤ) : K) = (y : K) := congrArg (fun z : ℤ => (z : K)) e.symm
      have : (y.natAbs : K) * x = y • x := by
        rw [zsmul_eq_mul, ← e2, Int.cast_natCast]
      rw [this]; exact hyint
    · have : (y.natAbs : K) * x = -(y • x) := by
        rw [zsmul_eq_mul, ← neg_mul]; congr 1
        have e' : (y : K) = -((y.natAbs : ℤ) : K) := by
          have := congrArg (fun z : ℤ => (z : K)) e
          simpa using this
        rw [e', neg_neg, Int.cast_natCast]
      rw [this]; exact hyint.neg
  obtain ⟨e, M, hpM, hd⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd0 p hp.ne_one
  refine ⟨M, (Nat.Prime.coprime_iff_not_dvd hp).2 hpM |>.symm, ?_⟩
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K ((M : K) * x) fun w => by
    by_cases hw : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal
    · rw [map_mul]
      refine mul_le_one' ?_ (h w hw)
      have := w.valuation_le_one (K := K) (M : 𝓞 K)
      simpa using this
    · obtain ⟨s, hs⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K ((y.natAbs : K) * x) fun v => by
        obtain ⟨t, ht⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 K) (R := ℤ) (B := K)).1 hdint
        rw [← ht]; exact v.valuation_le_one t
      have hp1 : w.valuation K (p : K) = 1 := by
        have := (w.intValuation_eq_one_iff (x := ((p : ℕ) : 𝓞 K))).2 hw
        rw [← map_natCast (algebraMap (𝓞 K) K), HeightOneSpectrum.valuation_of_algebraMap]
        exact this
      have hle : w.valuation K ((y.natAbs : K) * x) ≤ 1 := by rw [← hs]; exact w.valuation_le_one s
      rw [hd, Nat.cast_mul, Nat.cast_pow, mul_assoc, map_mul, map_pow, hp1, one_pow, one_mul] at hle
      exact hle
  rw [← hr]
  exact RingOfIntegers.isIntegral_coe r

theorem intOff_of_val {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (S : Finset ℕ) (x : K)
    (h : ∀ p : ℕ, p.Prime → p ∉ S → ∀ w : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ w.asIdeal → w.valuation K x ≤ 1) :
    IntOff S (σ x) := by
  have hQ : σ x ∈ TaylorLogMetric.Qbar := by
    rw [TaylorLogMetric.Qbar, mem_algebraicClosure_iff']
    exact (Algebra.IsIntegral.isIntegral (R := ℚ) x).map σ.toRatAlgHom
  refine ⟨hQ, fun p hp lam hpS => ?_⟩
  rw [lamC_of_mem lam hQ]
  obtain ⟨M, hM, hint⟩ := exists_coprime_mul_isIntegral hp.out x (h p hp.out hpS)
  have h1 : IsIntegral ℤ ((M : ℂ) * σ x) := by
    have := map_isIntegral_int σ hint
    simpa using this
  have h2 : IsIntegral ℤ ((M : TaylorLogMetric.Qbar) * (⟨σ x, hQ⟩ : TaylorLogMetric.Qbar)) :=
    (isIntegral_algHom_iff ((algebraMap TaylorLogMetric.Qbar ℂ).toIntAlgHom) Subtype.val_injective).1 (by simpa using h1)
  exact GlobalTheory.HeckeVal.norm_le_one_of_denom lam hM h2

end GlobalTheory.KerTie.MuqUnit

namespace GlobalTheory.KerTie.MuqUnit

open GlobalTheory.CharVal

variable {X : Fields} {Pr : Primes X} {m : ℕ} {Ch : Chars X Pr m} {σ₀ : X.K →+* ℂ} {e : X.Tau → ℚ} {j : Fin m}
  {μ : Formalism.L2.Host.HChar X.E}

theorem mu_core_of_conj (hconj : ∀ τ (x : X.E), X.embC σ₀ τ (star x) = starRingEnd ℂ (X.embC σ₀ τ x)) (hPr : Pr.Ok)
    (hμ : IsMu0 Ch σ₀ e j μ) (P : HeightOneSpectrum (𝓞 X.E)) (k : X.Eˣ) {c : X.K}
    (hc : σ₀ c = ((μ.locK P k : ℂˣ) : ℂ)) :
    ∃ (M : ℕ) (z : X.E) (n : X.Tau → ℤ), 0 < M ∧ (∀ τ, (n τ : ℚ) = 2 * e τ) ∧ P.valuation X.E z = P.valuation X.E (k : X.E) ^ M ∧
      (∀ Q : HeightOneSpectrum (𝓞 X.E), Q ≠ P → Q.valuation X.E z = 1) ∧ c ^ (2 * M) = ∏ τ, X.emb τ (z / star z) ^ n τ := by
  classical
  have hg : ∀ i, ((Pr.g i : ℕ) : 𝓞 X.E) ≠ 0 := fun i => by exact_mod_cast (hPr.g_prime i).ne_zero
  obtain ⟨M, z, hM, h1, h2, h3⟩ := GlobalTheory.TamePow.exists_pow_locK_mul_inf X.E μ (divs ((Pr.g 0 : ℕ) : 𝓞 X.E) ∪ divs ((Pr.g 1 : ℕ) : 𝓞 X.E))
    (productRule μ) (fun v hv => hμ.unr v fun i hi => hv (by
      rw [Finset.mem_union, mem_divs (hg 0), mem_divs (hg 1)]
      fin_cases i
      exacts [Or.inl hi, Or.inr hi])) hμ.tame P k
  obtain ⟨n, hn, hinf⟩ := hμ.inf
  refine ⟨M, z, fun τ => -n τ, hM, fun τ => by push_cast; rw [hn]; ring, h1, h2, σ₀.injective ?_⟩
  have h4 : ((μ.locK P k : ℂˣ) : ℂ) ^ M = (((μ.inf z : ℂˣ) : ℂ))⁻¹ := by
    rw [← Units.val_pow_eq_pow_val, eq_inv_of_mul_eq_one_left h3, Units.val_inv_eq_inv_val]
  rw [map_pow, hc, mul_comm 2 M, pow_mul, h4, hinf z, ← Finset.prod_inv_distrib, ← Finset.prod_pow, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_zpow₀, ← zpow_neg, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
  congr 1
  change _ = X.embC σ₀ τ (z / star (z : X.E))
  have h0 : X.embC σ₀ τ (z : X.E) ≠ 0 := by simp
  rw [map_div₀, hconj, div_pow, div_eq_div_iff (pow_ne_zero _ (by simpa using h0)) (by simpa using h0), sq, mul_assoc,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem mu_unit_of_conj (hconj : ∀ τ (x : X.E), X.embC σ₀ τ (star x) = starRingEnd ℂ (X.embC σ₀ τ x)) (hPr : Pr.Ok)
    (hμ : IsMu0 Ch σ₀ e j μ) {P : HeightOneSpectrum (𝓞 X.E)} (k : X.Eˣ) {c : X.K}
    (hc : σ₀ c = ((μ.locK P k : ℂˣ) : ℂ)) {p : ℕ} (hP : ((p : ℕ) : 𝓞 X.E) ∉ P.asIdeal) {w : HeightOneSpectrum (𝓞 X.K)}
    (hw : ((p : ℕ) : 𝓞 X.K) ∈ w.asIdeal) : w.valuation X.K c = 1 := by
  obtain ⟨M, z, n, hM, -, -, h2, h3⟩ := mu_core_of_conj hconj hPr hμ P k hc
  refine unit_of_pow (M := 2 * M) (by omega) ?_
  rw [h3]
  refine val_prod_unit w (fun τ => ?_) n
  have h4 := (natCast_mem_pullW τ w p).2 hw
  rw [map_div₀, ← valuation_conjP, h2 _ (fun e' => hP (e' ▸ h4)), h2 _ (fun e' => hP (e' ▸ (natCast_mem_conjP _ p).2 h4)), div_one]

end GlobalTheory.KerTie.MuqUnit

namespace GlobalTheory.KerTie.MuqUnit

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Y cX}

theorem embC_star (t : KerEntTied ex) (τ : t.X.Tau) (x : t.X.E) :
    t.X.embC t.seam.σ₀ τ (star x) = starRingEnd ℂ (t.X.embC t.seam.σ₀ τ x) := by
  change t.seam.σ₀ (t.X.emb τ (star x)) = starRingEnd ℂ (t.seam.σ₀ (t.X.emb τ x))
  rw [t.seam_ok.1, t.seam_ok.1, t.seam_ok.2]
  exact D.host.conjE_apply (TaylorLogMetric.embT D (t.seam.iT τ)) (t.seam.iE x)

end GlobalTheory.KerTie.MuqUnit

namespace GlobalTheory.KerTie

open MuqUnit

theorem muq_intOff : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → ∀ u μ, (∀ k, D.host.g k ∉ Y.Qp μ) → ∀ (i : ℕ), i < D.R.m → ∀ P : rowSG t.Pr t.sel (t.tup μ), P.1 ∉ t.Pr.vGs → IntOff (t.O u μ).S (t.seam.σ₀ ((t.cst μ).muq (i + 1) P)) ∧ IntOff (t.O u μ).S (t.seam.σ₀ ((t.cst μ).muq (i + 1) P)⁻¹) := by
  intro D L hT Gi Gl K Y cX ex t hmu hval u μ hQg i hi P hP
  have hPQ : P.1 ∈ QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K) := (Finset.mem_union.1 P.2).resolve_left hP
  have hg : ∀ k, ((t.Pr.g k : ℕ) : 𝓞 t.X.E) ∉ P.1.asIdeal := fun k hk =>
    hQg k (t.g_rec k ▸ (t.Q_rec μ (t.Pr.g k)).2 ⟨t.pr_ok.g_prime k, P.1, hPQ, hk⟩)
  have hq := (t.idx_ok μ).muqQ i hi P hP
  have key : ∀ p : ℕ, p.Prime → p ∉ (t.O u μ).S → ∀ w : HeightOneSpectrum (𝓞 t.X.K), ((p : ℕ) : 𝓞 t.X.K) ∈ w.asIdeal →
      w.valuation t.X.K ((t.cst μ).muq (i + 1) P) = 1 := by
    intro p hp hpS w hw
    have hpP : ((p : ℕ) : 𝓞 t.X.E) ∉ P.1.asIdeal := fun h =>
      hpS ((sNum_qOf_rowSG D L hT Gi Gl K Y cX ex t u μ P).2 p hp (dvd_absNorm_of_mem P.1 hp h))
    obtain ⟨e, he⟩ := hmu ⟨i, hi⟩
    have hm := mu_unit_of_conj (embC_star t) t.pr_ok he (Formalism.L2.Host.unif P.1) (hval ⟨i, hi⟩ P.1 hg) hpP hw
    have htw := (GlobalTheory.ColPeriod.twistUnit t.X.F t.X.E t.X.K t.S (t.tup μ) P.1 w).2
    rw [hq, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_inv₀, hm, htw]
    simp
  refine ⟨intOff_of_val _ _ _ fun p hp hpS w hw => (key p hp hpS w hw).le, ?_⟩
  have h2 := intOff_of_val t.seam.σ₀ (t.O u μ).S ((t.cst μ).muq (i + 1) P)⁻¹ fun p hp hpS w hw => by
    rw [map_inv₀, key p hp hpS w hw, inv_one]
  exact h2

end GlobalTheory.KerTie
end
end

section

open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory

theorem nuD_card_le_a_sq : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) ≤ (Fm.L x i).sc.a ^ 2 := by
  intro eps Fm
  obtain ⟨x1, h1⟩ := GlobalTheory.nuRow_nonneg_le_ten_mul eps Fm
  obtain ⟨x2, h2⟩ := GlobalTheory.ShNums.size_rel Fm
  refine ⟨max x1 x2, fun x hx hx1 i u j hj z => ?_⟩
  have hr := h1 x (le_trans (le_max_left _ _) hx) hx1 i u (j + 1)
    (Finset.mem_Icc.2 ⟨by omega, by omega⟩) (tauPl (Fm.D x i) z)
  simp only [Nat.add_sub_cancel] at hr
  obtain ⟨hkN, -, -, -, -, h4, -, -, -, hS⟩ := h2 x (le_trans (le_max_right _ _) hx) hx1 i
  have hsx := Fm.L_x x i hx1
  rw [GlobalTheory.nuD_card_eq_sum_nuRow _ (nuRowOK _) u j hj z]
  have hsum := Finset.sum_le_card_nsmul (Finset.range ((Fm.D x i).R.N j))
    (fun r => DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r) (10 * x * (Fm.L x i).sc.b)
    (fun r hr' => (hr r (Finset.mem_range.1 hr')).2)
  rw [Finset.card_range, nsmul_eq_mul] at hsum
  have hNle : ((Fm.D x i).R.N j : ℝ) ≤ (Fm.D x i).R.N (Fm.D x i).R.m := by
    have : (Fm.D x i).R.N j ≤ (Fm.D x i).R.N (Fm.D x i).R.m := by
      unfold Ranks.N
      have := Nat.mul_le_mul_right ((Fm.D x i).R.t + 1) hj.le
      omega
    exact_mod_cast this
  have hk : (1 : ℝ) ≤ (Fm.D x i).R.k := by
    have := (Fm.D x i).R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ (Fm.D x i).R.k)
  have hN0 : (0 : ℝ) ≤ (Fm.D x i).R.N (Fm.D x i).R.m := Nat.cast_nonneg _
  have hNk := le_mul_of_one_le_left hN0 hk
  have heta := (Fm.L x i).etaSz_pos
  have hb : 0 < (Fm.L x i).sc.b := Real.exp_pos _
  have hN : ((Fm.D x i).R.N j : ℝ) ≤ (Fm.L x i).sc.b / 10 := by linarith
  rw [hsx] at h4
  have hxb : 0 ≤ 10 * x * (Fm.L x i).sc.b := by positivity
  have h5 := mul_le_mul_of_nonneg_right hN hxb
  have ha : (Fm.L x i).sc.a = x * (Fm.L x i).sc.b := by
    unfold Scale.a
    rw [hsx]
  rw [ha]
  have h6 : x * (Fm.L x i).sc.b ^ 2 ≤ x * (x * (Fm.L x i).sc.b ^ 2) :=
    le_mul_of_one_le_left (by positivity) (by linarith)
  nlinarith

end GlobalTheory
end

section

open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.CapBound

theorem row_le (D : D7) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m) (z : Bool × HH D) (r : ℕ) (hr1 : r ≤ 1)
    (hr : r < D.R.k) :
    (((nuD D u j z).rowLen r : ℕ) : ℝ) ≤
      wPl D (j + 1) z - kaJ D (j + 1) + (((D.hcW u (tauPl D z)).u ⟨r, hr⟩ : ℚ) : ℝ) := by
  have hw : wPl D (j + 1) z = (((D.hcW u (tauPl D z)).e ⟨j, hj⟩ : ℚ) : ℝ) := by
    unfold wPl wj
    rw [dite_eq_left (by simpa using hj), D.hcW_e]
    rfl
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hr' : (r : ℝ) ≤ 1 := by exact_mod_cast hr1
  have h2 : r < D.R.N j := by unfold Ranks.N; omega
  rw [nuRowOK D u j hj z r, if_pos h2, RowWeightLemmas.nuRow_head D u j hj _ r hr, hw]
  unfold kaJ Ranks.N
  push_cast
  linarith

theorem cap_le : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), (if IsTopPl (Fm.D x i) z then (((nuD (Fm.D x i) u j z).rowLen 1 : ℕ) : ℝ) else (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ)) ≤ fillG (Fm.Gx x i) (bL (Fm.L x i)) (j + 1) z + cG (Fm.L x i) := by
  intro eps Fm
  obtain ⟨x0, hx0⟩ := GlobalTheory.fill_eq_wPl Fm
  refine ⟨x0, fun x hx hx1 i u j hj z => ?_⟩
  have hk : 5 ≤ (Fm.D x i).R.k := by
    have := (Fm.D x i).R.m_add_three_le_k; have := (Fm.D x i).R.two_le_m; omega
  have hS := (Fm.L x i).Sc_pos
  unfold fillG cG
  rw [hx0 x hx hx1 i j hj z]
  split_ifs with hz
  · have h1 := row_le (Fm.D x i) u j hj z 1 le_rfl (by omega)
    obtain ⟨-, h4⟩ := (Fm.L x i).cloud_u u (tauPl (Fm.D x i) z) ⟨1, by omega⟩ le_rfl (by show 1 + 1 < _; omega)
    linarith
  · have h1 := row_le (Fm.D x i) u j hj z 0 (by omega) (by omega)
    obtain ⟨-, h4⟩ := GlobalTheory.LongRows.u_bounds_off (Fm.params x hx1 i) u _
      (GlobalTheory.LongRows.not_mem_topPlaces _ z hz) 0 (by omega)
    rw [if_pos rfl] at h4
    linarith

end GlobalTheory.CapBound
end
