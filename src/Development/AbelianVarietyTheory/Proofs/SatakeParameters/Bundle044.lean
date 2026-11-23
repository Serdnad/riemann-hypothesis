module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle031
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle039
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle001
public import Formalism.GradedWeylDivisibility.StatementA
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Formalism.LocalToGlobal.Divisibility.Tuples
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle006
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle040
public import Formalism.SatakeDualWeyl.StatementG
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle041
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GaloisOfPrimePowerDegree
public import Mathlib.RingTheory.MvPowerSeries.Substitution
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle005
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Formalism.FormalGroupWitt.FormalGroupWittProofs.Bundle001

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry

theorem _root_.GlobalTheory.T.splitsFinitelyOverScheme_of_isEmpty_pullback : ∀ {Z X V : Scheme.{0}} (f : Z ⟶ X) (y : V ⟶ X), IsEmpty (pullback f y : Scheme.{0}) → GlobalTheory.EtC.Tr.Splits f y := by
  first | (exact @GlobalTheory.EtC.Tr.splits_of_isEmpty_pullback) | (exact GlobalTheory.EtC.Tr.splits_of_isEmpty_pullback) | (intros; apply GlobalTheory.EtC.Tr.splits_of_isEmpty_pullback  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry

theorem _root_.GlobalTheory.T.freeSheaf_sum_sections_eq_of_two_splittings : ∀ (R : Type) [CommRing R] {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} {m m' : ℕ} {s : Fin m → (V ⟶ Z)} {s' : Fin m' → (V ⟶ Z)}, GlobalTheory.EtC.Tr.SplitBy f y s → GlobalTheory.EtC.Tr.SplitBy f y s' → ∑ j, (GlobalTheory.EtC.free R).map (yoneda.map (s j)) = ∑ j, (GlobalTheory.EtC.free R).map (yoneda.map (s' j)) := by
  first | (exact @GlobalTheory.EtC.Tr.sum_sections_eq_of_two_splittings) | (exact GlobalTheory.EtC.Tr.sum_sections_eq_of_two_splittings) | (intros; apply GlobalTheory.EtC.Tr.sum_sections_eq_of_two_splittings  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry

theorem _root_.GlobalTheory.T.splitsFinitelyOverScheme_of_pullback_snd : ∀ {Z X S V : Scheme.{0}} (f : Z ⟶ X) (x : S ⟶ X) (v : V ⟶ S), GlobalTheory.EtC.Tr.Splits (pullback.snd f x) v → GlobalTheory.EtC.Tr.Splits f (v ≫ x) := by
  first | (exact @GlobalTheory.EtC.Tr.splits_of_splits_pullback_snd) | (exact GlobalTheory.EtC.Tr.splits_of_splits_pullback_snd) | (intros; apply GlobalTheory.EtC.Tr.splits_of_splits_pullback_snd  <;> assumption)
end

section


theorem _root_.GlobalTheory.T.howe_duality_of_minguez : GlobalTheory.Published.MinguezThetaGL → GlobalTheory.Published.HoweDualityGL := by
  first | exact @GlobalTheory.HoweBridge.main | exact GlobalTheory.HoweBridge.main | (intros; apply GlobalTheory.HoweBridge.main <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.ValCmp

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.MainNotions.G

abbrev MP (R : Type) [CommRing R] (n : ℕ) : Type := MvPolynomial (Fin n × Fin n) R

def genM (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (MP R n) := Matrix.of fun a s => X (a, s)

def cofAct (R : Type) [CommRing R] (n : ℕ) : MP R n →ₐ[R] MP R n :=
  aeval fun v => (genM R n).adjugate v.2.rev v.1

def nuDual {m : ℕ} (ν : Fin (m + 1) → ℕ) : Fin (m + 1) → ℕ := fun i => ν 0 - ν i.rev

def CofRel (R : Type) [CommRing R] (m : ℕ) (ν : Fin (m + 1) → ℕ) (f g : MP R (m + 1)) : Prop :=
  (genM R (m + 1)).det ^ (∑ i, ν i - ν 0) * g = cofAct R (m + 1) f

def stdN (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (n : ℕ) (ν : Fin n → ℕ) : Submodule O (MP Kf n) :=
  (dualWeyl O n n ν).map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap

def stdD (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (n : ℕ) (ν : Fin n → ℕ) : Submodule O (MP Kf n) :=
  (weyl O n n le_rfl ν).map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap

def rnd (Kf : Type) [Field Kf] {n : ℕ} (e : ℤ) (g : Matrix (Fin n) (Fin n) Kf) : MP Kf n →ₗ[Kf] MP Kf n :=
  g.det ^ (-e) • (rowAct Kf g⁻¹).toLinearMap

def twLat {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {n : ℕ} (e : ℤ) (S : Submodule O (MP Kf n))
    (g : Matrix (Fin n) (Fin n) Kf) : Submodule O (MP Kf n) :=
  S.map ((rnd Kf e g).restrictScalars O)

def PosOk (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (n : ℕ) (ν ν' : Fin n → ℕ) (e e' c : ℤ)
    (tw : Matrix (Fin n) (Fin n) Kf → Matrix (Fin n) (Fin n) Kf) (Ψ : MP Kf n →ₗ[Kf] MP Kf n) : Prop :=
  (∀ f ∈ dualWeyl Kf n n ν, Ψ f = 0 → f = 0) ∧
  (dualWeyl Kf n n ν).map Ψ = dualWeyl Kf n n ν' ∧
  (∀ h : Matrix (Fin n) (Fin n) Kf, IsUnit h.det → ∀ f ∈ dualWeyl Kf n n ν,
    Ψ (rnd Kf e h f) = h.det ^ c • rnd Kf e' (tw h) (Ψ f)) ∧
  (stdN O Kf n ν).map (Ψ.restrictScalars O) = stdN O Kf n ν' ∧
  (stdD O Kf n ν).map (Ψ.restrictScalars O) = stdD O Kf n ν'

end GlobalTheory.ValCmp
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
open TensorProduct Formalism.UG Formalism.UG.P

namespace GlobalTheory.OpenChrRam

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem inv_natCast_mem (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) (hN : (N : 𝓞 F) ∉ v.asIdeal) :
    (N : v.adicCompletion F) ≠ 0 ∧ (N : v.adicCompletion F)⁻¹ ∈ v.adicCompletionIntegers F := by
  have h1 : Valued.v (N : v.adicCompletion F) = 1 := by
    have e : (N : v.adicCompletion F) = algebraMap (𝓞 F) (v.adicCompletion F) (N : 𝓞 F) := by simp
    have e2 : v.valuation F (algebraMap (𝓞 F) F (N : 𝓞 F)) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact (HeightOneSpectrum.intValuation_eq_one_iff).2 hN
    rw [← e2, ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact congrArg _ e
  refine ⟨fun h => by rw [h] at h1; simp at h1, ?_⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1, inv_one]

theorem inertAt_le_congN (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) (hN : (N : 𝓞 F) ∉ v.asIdeal) :
    inertAt E v ≤ congN F E N := by
  rintro x ⟨⟨hx, hx'⟩, hs⟩
  obtain ⟨hN0, hNi⟩ := inv_natCast_mem v N hN
  let u : (RInt F E)ˣ := ⟨⟨x, hx⟩, ⟨(x⁻¹ : (AfE F E)ˣ), hx'⟩, Subtype.ext x.mul_inv, Subtype.ext x.inv_mul⟩
  refine ⟨u, ?_, Units.ext rfl⟩
  have hn : (1 : E) ⊗ₜ[F] afsplitI v (N : v.adicCompletion F)⁻¹ ∈ RInt F E :=
    Subring.subset_closure (Or.inr ⟨⟨_, afsplitI_mem_intAd v _ hNi⟩, rfl⟩)
  refine (mem_kerRed _ u).2 (Ideal.mem_span_singleton'.2 ⟨⟨_, hn⟩ * ((u : RInt F E) - 1), ?_⟩)
  apply Subtype.ext
  show (1 : E) ⊗ₜ[F] afsplitI v (N : v.adicCompletion F)⁻¹ * ((x : AfE F E) - 1) * ((N : RInt F E) : AfE F E)
    = (x : AfE F E) - 1
  rw [SubringClass.coe_natCast, ← sub_eq_zero]
  refine afsplit_inj _ fun w => ?_
  rw [map_sub, map_mul, map_mul, afsplit_prV_tmul, map_natCast]
  by_cases h : w = v
  · subst h
    rw [afsplitI_self, mul_right_comm]
    have : (1 : E) ⊗ₜ[F] (N : w.adicCompletion F)⁻¹ * (N : E ⊗[F] w.adicCompletion F) = 1 := by
      have e : (N : E ⊗[F] w.adicCompletion F) = (1 : E) ⊗ₜ[F] (N : w.adicCompletion F) :=
        (map_natCast (Algebra.TensorProduct.includeRight :
          w.adicCompletion F →ₐ[F] E ⊗[F] w.adicCompletion F) N).symm
      rw [e, Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ hN0, one_mul]
      rfl
    rw [this, one_mul, sub_self]
  · have hw : prV (E := E) w (x : AfE F E) = 1 := by
      have h1 := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hs w) h
      exact congrArg Units.val (MonoidHom.mem_ker.1 h1)
    rw [map_sub, hw, map_one, sub_self, mul_zero, zero_mul, sub_self]

theorem qprime_finite (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (L : Type) [Field L] (ξ : Chr F E L) (h : ξ ∈ openChr F E L) : (Qprime ξ).Finite := by
  obtain ⟨N, hN, hk⟩ := h
  have hne : Ideal.span {(N : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  refine (Ideal.finite_factors hne).subset fun v hv => ?_
  by_contra hc
  refine hv ((inertAt_le_congN v N fun hm => hc ?_).trans hk)
  exact Ideal.dvd_span_singleton.2 hm

end GlobalTheory.OpenChrRam
end

section

open Matrix

namespace GlobalTheory.LatticeDuality

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_int_iff (a : L) : a ∈ Formalism.UG.intL L ↔ Valued.v a ≤ 1 := Iff.rfl

theorem mulVec_int {m n : ℕ} (A : Matrix (Fin m) (Fin n) L) (u : Fin n → L)
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (hu : ∀ i, u i ∈ Formalism.UG.intL L) :
    ∀ i, (A *ᵥ u) i ∈ Formalism.UG.intL L := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (hu j)

theorem one_dim (e z : L)
    (h : ∀ c : L, c ∈ Formalism.UG.intL L → e * c ∈ Formalism.UG.intL L → c * z ∈ Formalism.UG.intL L) :
    ∃ a b : L, a ∈ Formalism.UG.intL L ∧ b ∈ Formalism.UG.intL L ∧ z = a + e * b := by
  by_cases he : e ∈ Formalism.UG.intL L
  · refine ⟨z, 0, ?_, Subring.zero_mem _, by simp⟩
    simpa using h 1 (Subring.one_mem _) (by simpa using he)
  · have he0 : e ≠ 0 := by
      rintro rfl
      exact he (Subring.zero_mem _)
    have hlt : 1 < Valued.v e := not_le.mp ((mem_int_iff e).not.mp he)
    have hinv : e⁻¹ ∈ Formalism.UG.intL L := by
      rw [mem_int_iff, map_inv₀]
      exact inv_le_one_of_one_le₀ hlt.le
    refine ⟨0, e⁻¹ * z, Subring.zero_mem _, h _ hinv ?_, ?_⟩
    · rw [mul_inv_cancel₀ he0]; exact Subring.one_mem _
    · field_simp
      simp

theorem diag_case {m n : ℕ} (d : Fin m → L) (z : Fin n → L)
    (h : ∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) →
      (∀ i, ((Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0)) *ᵥ u) i
        ∈ Formalism.UG.intL L) → (∑ i, u i * z i) ∈ Formalism.UG.intL L) :
    ∃ l : Fin n → L, ∃ w : Fin m → L, (∀ i, l i ∈ Formalism.UG.intL L) ∧ (∀ i, w i ∈ Formalism.UG.intL L) ∧
      z = l + (Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0))ᵀ *ᵥ w := by
  have key : ∀ k : Fin n, ∃ a b : L, a ∈ Formalism.UG.intL L ∧ b ∈ Formalism.UG.intL L ∧
      z k = a + (if hk : (k : ℕ) < m then d ⟨k, hk⟩ else 0) * b := by
    intro k
    apply one_dim
    intro c hc hec
    have := h (Pi.single k c) ?_ ?_
    · simpa [Pi.single_apply] using this
    · intro i
      by_cases hi : i = k
      · subst hi; simpa using hc
      · simp [hi]
    · intro j
      rw [Matrix.mulVec_single]
      by_cases hj : (k : ℕ) = (j : ℕ)
      · have hk : (k : ℕ) < m := hj ▸ j.2
        have : (⟨k, hk⟩ : Fin m) = j := Fin.ext hj
        rw [dite_eq_left hk, this] at hec
        simpa [hj] using hec
      · simp [hj]
  choose a b ha hb hz using key
  refine ⟨a, fun j => if hj : (j : ℕ) < n then b ⟨j, hj⟩ else 0, ha, ?_, ?_⟩
  · intro j
    dsimp only
    split_ifs
    · exact hb _
    · exact Subring.zero_mem _
  · funext k
    rw [hz k, Pi.add_apply]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply]
    by_cases hk : (k : ℕ) < m
    · rw [dite_eq_left hk, Finset.sum_eq_single (⟨k, hk⟩ : Fin m)]
      · simp
      · intro j _ hj
        have : (k : ℕ) ≠ (j : ℕ) := fun e => hj (Fin.ext e.symm)
        simp [this]
      · simp
    · rw [dite_eq_right hk, zero_mul]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      have : (k : ℕ) ≠ (j : ℕ) := fun e => hk (e ▸ j.2)
      simp [this]

theorem dual_subset : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (m n : ℕ) (x : Matrix (Fin m) (Fin n) L)
    (z : Fin n → L),
    (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) → (∑ i, u i * z i) ∈ Formalism.UG.intL L) →
    ∃ l : Fin n → L, ∃ w : Fin m → L, (∀ i, l i ∈ Formalism.UG.intL L) ∧ (∀ i, w i ∈ Formalism.UG.intL L) ∧ z = l + xᵀ *ᵥ w := by
  intro L _ _ m n x z h
  obtain ⟨P, P', Q, Q', d, hP, hP', hQ, hQ', hPP, hQQ, hx⟩ := GlobalTheory.T.smithNormalForm_discreteValuationField L m n x
  set D : Matrix (Fin m) (Fin n) L :=
    Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0) with hD
  have hPP' : P' * P = 1 := mul_eq_one_comm.mp hPP
  have hQQ' : Q' * Q = 1 := mul_eq_one_comm.mp hQQ
  obtain ⟨l, w, hl, hw, hz⟩ := diag_case d (Q'ᵀ *ᵥ z) (by
    intro s hs hDs
    have h1 := h (Q' *ᵥ s) (mulVec_int _ _ hQ' hs) (by
      have : x *ᵥ (Q' *ᵥ s) = P *ᵥ (D *ᵥ s) := by
        rw [hx, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc (P * D), hQQ, Matrix.mul_one]
      rw [this]
      exact mulVec_int _ _ hP hDs)
    have h2 : ∑ i, s i * (Q'ᵀ *ᵥ z) i = ∑ i, (Q' *ᵥ s) i * z i := by
      change s ⬝ᵥ (Q'ᵀ *ᵥ z) = (Q' *ᵥ s) ⬝ᵥ z
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [h2]
    exact h1)
  refine ⟨Qᵀ *ᵥ l, P'ᵀ *ᵥ w, mulVec_int _ _ (fun i j => hQ j i) hl,
    mulVec_int _ _ (fun i j => hP' j i) hw, ?_⟩
  have h3 : z = Qᵀ *ᵥ (Q'ᵀ *ᵥ z) := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hQQ', Matrix.transpose_one, Matrix.one_mulVec]
  have h4 : xᵀ *ᵥ (P'ᵀ *ᵥ w) = Qᵀ *ᵥ (Dᵀ *ᵥ w) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Matrix.transpose_mul, hx,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP', Matrix.one_mul]
  rw [h4, ← Matrix.mulVec_add, ← hz]
  exact h3

end GlobalTheory.LatticeDuality
end

section

open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_ringEquiv_tensor_inert_adicCompletion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (P : HeightOneSpectrum (𝓞 E)), IsInertAt (maximalRealSubfield E) E v P → ∀ σ : P.adicCompletion E →+* P.adicCompletion E, (∀ x : E, σ (algebraMap E (P.adicCompletion E) x) = algebraMap E (P.adicCompletion E) (ReciprocityTheory.ChartRestriction.G.FD.cc x)) → (∀ x, Valued.v (σ x) = Valued.v x) → ∃ ψ : LocAlg v ≃+* P.adicCompletion E, (∀ x : E, ψ (locEmb v x) = algebraMap E (P.adicCompletion E) x) ∧ (∀ z, ψ (locConj v z) = σ (ψ z)) ∧ ∀ z, z ∈ locOrder v ↔ Valued.v (ψ z) ≤ 1 := by
  first | exact @GlobalTheory.InertCompletion.exists_ringEquiv_completion | exact GlobalTheory.InertCompletion.exists_ringEquiv_completion | (intros; apply GlobalTheory.InertCompletion.exists_ringEquiv_completion <;> assumption)
end

section

open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.isInertAt_of_unique_unramified_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (P : HeightOneSpectrum (𝓞 E)), (∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ (x : E)⁻¹ ∉ semiLoc v)) → (∃ x : 𝓞 (maximalRealSubfield E), ∃ y : 𝓞 E, (y : E) = algebraMap (maximalRealSubfield E) E (x : maximalRealSubfield E) ∧ y ∈ P.asIdeal ∧ y ∉ P.asIdeal ^ 2) → IsInertAt (maximalRealSubfield E) E v P := by
  first | exact @GlobalTheory.SelfDualGenus.isInertAt_of_unique_unramified | exact GlobalTheory.SelfDualGenus.isInertAt_of_unique_unramified | (intros; apply GlobalTheory.SelfDualGenus.isInertAt_of_unique_unramified <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.VolAt

open Formalism.MainNotions.G Matrix

def homLat (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k k' : ℕ}
    (A : Submodule W (Fin k → Qq)) (B : Submodule W (Fin k' → Qq)) : Submodule W (Matrix (Fin k') (Fin k) Qq) where
  carrier := {x | ∀ z ∈ A, x *ᵥ z ∈ B}
  zero_mem' := fun z _ => by rw [Matrix.zero_mulVec]; exact B.zero_mem
  add_mem' := fun hx hy z hz => by rw [Matrix.add_mulVec]; exact B.add_mem (hx z hz) (hy z hz)
  smul_mem' := fun c x hx z hz => by
    rw [Matrix.smul_mulVec]
    exact B.smul_mem c (hx z hz)

theorem mem_homLat (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k k' : ℕ}
    (A : Submodule W (Fin k → Qq)) (B : Submodule W (Fin k' → Qq)) (x : Matrix (Fin k') (Fin k) Qq) :
    x ∈ homLat W A B ↔ ∀ z ∈ A, x *ᵥ z ∈ B := Iff.rfl

end GlobalTheory.VolAt
end
end

section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing GlobalTheory.EtC TensorProduct

namespace GlobalTheory.IntClLocal

theorem isLocalRing_of_isIntegral_of_henselian (O : Type) [CommRing O] [HenselianLocalRing O]
    (S : Type) [CommRing S] [IsDomain S] [Algebra O S] [Algebra.IsIntegral O S] : IsLocalRing S := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  have : Module.Finite O (Algebra.adjoin O {a}) :=
    Algebra.finite_adjoin_simple_of_isIntegral (Algebra.IsIntegral.isIntegral a)
  have := GlobalTheory.TameKummer.isLocalRing_of_finite O (Algebra.adjoin O {a})
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self
    (⟨a, Algebra.self_mem_adjoin_singleton O a⟩ : Algebra.adjoin O {a}) with h | h
  · exact Or.inl (h.map (Algebra.adjoin O {a}).val)
  · exact Or.inr (by simpa using h.map (Algebra.adjoin O {a}).val)

end GlobalTheory.IntClLocal
end

section

noncomputable section

namespace GlobalTheory.SubringSeries

open MvPowerSeries Formalism.FG.InjVAux

variable {K : Type} [Field K] {κ : Type}

def intS (A : Subring K) (κ : Type) : Subring (MvPowerSeries κ K) where
  carrier := {F | ∀ n, coeff n F ∈ A}
  mul_mem' := by
    classical
    intro a b ha hb n
    rw [coeff_mul]
    exact A.sum_mem fun x _ => A.mul_mem (ha _) (hb _)
  one_mem' := by
    classical
    intro n
    rw [coeff_one]
    split_ifs
    exacts [A.one_mem, A.zero_mem]
  add_mem' := fun ha hb n => by rw [map_add (f := _)]; exact A.add_mem (ha n) (hb n)
  zero_mem' := fun n => by rw [map_zero]; exact A.zero_mem
  neg_mem' := fun ha n => by rw [map_neg]; exact A.neg_mem (ha n)

variable {A : Subring K}

theorem finsum_mem' {ι : Type} {f : ι → K} (h : ∀ i, f i ∈ A) : ∑ᶠ i, f i ∈ A :=
  finsum_induction (fun x => x ∈ A) A.zero_mem (fun _ _ => A.add_mem) h

theorem subst_mem {ι : Type} {a : ι → MvPowerSeries κ K} (ha : HasSubst a) (hA : ∀ i, a i ∈ intS A κ)
    {E : MvPowerSeries ι K} (hE : E ∈ intS A ι) : subst a E ∈ intS A κ := by
  intro n
  rw [coeff_subst ha]
  refine finsum_mem' fun d => ?_
  rw [smul_eq_mul]
  refine A.mul_mem (hE d) (((intS A κ).prod_mem fun i _ => (intS A κ).pow_mem (hA i) _) n)

section Frob

variable {p : ℕ} {hp : p ≠ 0} {σ : K →+* K}

end Frob

end GlobalTheory.SubringSeries
end
end
