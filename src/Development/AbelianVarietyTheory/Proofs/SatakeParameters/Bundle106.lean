module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Formalism.LocalToGlobal.Divisibility.Bundle001
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle062
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
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Formalism.GaussJetBounds.Bundle001
public import Formalism.GaussJetBounds.Bundle003
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.IsPairFrame
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementC
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementG
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.IsTransSys
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Bundle001
public import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.LamRowCong

open GlobalTheory.TopStep

section Gen

variable {E K : Type} [Field E] [NumberField E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem unitV_det_eq_one (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {t : ℕ} (A : Matrix (Fin t) (Fin t) E)
    (hA : ∀ s s', IntAt P (A s s')) (h1 : A.map (redP P) = 1) : LocE.unitV χ A.det = 1 := by
  have hd : redP P A.det = 1 := by rw [(det_int hA).2, h1, Matrix.det_one]
  have hu : IsUnit (redP P A.det) := hd ▸ isUnit_one
  unfold LocE.unitV
  rw [dite_eq_left hu]
  have : hu.unit = 1 := Units.ext (by simp [hd])
  rw [this, map_one, Units.val_one]

theorem sum_red_zero (M : ℕ → ℕ → E) {B : ℕ}
    (hM : ∀ p p', p < B → p' < B → IntAt P (M p p') ∧ redP P (M p p') = if p = p' then 1 else 0)
    (a b : ℕ → ℕ) (n : ℕ) (hab : ∀ i < n, a i < B ∧ b i < B ∧ a i ≠ b i) :
    IntAt P (∑ i ∈ Finset.range n, M (a i) (b i)) ∧ redP P (∑ i ∈ Finset.range n, M (a i) (b i)) = 0 := by
  have hI : ∀ i ∈ Finset.range n, IntAt P (M (a i) (b i)) := fun i hi => by
    have h := hab i (Finset.mem_range.1 hi)
    exact (hM _ _ h.1 h.2.1).1
  refine ⟨intAt_sum _ hI, ?_⟩
  rw [reduction_sum₂ _ hI]
  refine Finset.sum_eq_zero fun i hi => ?_
  have h := hab i (Finset.mem_range.1 hi)
  rw [(hM _ _ h.1 h.2.1).2, if_neg h.2.2]

theorem prod_blocks_eq_one (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (M : ℕ → ℕ → E) {B r t j : ℕ}
    (hM : ∀ p p', p < B → p' < B → IntAt P (M p p') ∧ redP P (M p p') = if p = p' then 1 else 0)
    (hrj : r + j * t ≤ B) :
    ∏ i ∈ Finset.range j, LocE.unitV (χ i) (Matrix.det (Matrix.of fun s s' : Fin t => M (r + i * t + s.1) (r + i * t + s'.1))) = 1 := by
  refine Finset.prod_eq_one fun i hi => ?_
  have hij : i + 1 ≤ j := Finset.mem_range.1 hi
  have h2 : i * t + t ≤ j * t := by
    have := Nat.mul_le_mul_right t hij
    rwa [Nat.add_mul, one_mul] at this
  have hb : ∀ s : Fin t, r + i * t + s.1 < B := fun s => by
    have := s.2
    omega
  refine unitV_det_eq_one _ _ (fun s s' => (hM _ _ (hb s) (hb s')).1) ?_
  ext s s'
  rw [Matrix.map_apply, Matrix.of_apply, (hM _ _ (hb s) (hb s')).2, Matrix.one_apply]
  by_cases h : s = s'
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun h' => h (Fin.ext (by omega)))]

theorem lamGv_eq_one (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (M : ℕ → ℕ → E)
    {B r t j : ℕ} (hM : ∀ p p', p < B → p' < B → IntAt P (M p p') ∧ redP P (M p p') = if p = p' then 1 else 0)
    (hr : r ≤ B) (hrj : r + j * t ≤ B) : LocE.lamGv ψ₀ χ r t j M = 1 := by
  unfold LocE.lamGv
  rw [(sum_red_zero M hM (fun i => i) (fun i => i + 1) (r - 1) fun i hi => ⟨by omega, by omega, by omega⟩).2,
    AddChar.map_zero_eq_one, one_mul]
  exact prod_blocks_eq_one χ M hM hrj

theorem lamGvS_eq_one (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (M : ℕ → ℕ → E)
    {B k₀ r t j : ℕ} (hM : ∀ p p', p < B → p' < B → IntAt P (M p p') ∧ redP P (M p p') = if p = p' then 1 else 0)
    (hk : k₀ ≤ r) (hr : r ≤ B) (hrj : r + j * t ≤ B) : LocE.lamGvS ψ₀ χ k₀ r t j M = 1 := by
  unfold LocE.lamGvS
  have h1 := sum_red_zero M hM (fun i => i) (fun i => i + 1) (k₀ - 1) fun i hi => ⟨by omega, by omega, by omega⟩
  have h2 := sum_red_zero M hM (fun i => k₀ + i) (fun i => k₀ + i + 1) (r - k₀ - 1)
    fun i hi => ⟨by omega, by omega, by omega⟩
  rw [reduction_add h1.1 h2.1, h1.2, h2.2, add_zero, AddChar.map_zero_eq_one, one_mul]
  exact prod_blocks_eq_one χ M hM hrj

end Gen

section Ent

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem fIdx_lt {k₀ c n p : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) : LocE.fIdx k₀ c n p < n + c := by
  unfold LocE.fIdx
  split_ifs <;> omega

theorem fIdx_inj {k₀ c n p p' : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) (hp' : p' < n + c)
    (h : LocE.fIdx k₀ c n p = LocE.fIdx k₀ c n p') : p = p' := by
  unfold LocE.fIdx at h
  split_ifs at h <;> omega

theorem entB_one_add_q {k₀ n c : ℕ} (hk : k₀ ≤ n) (ex : ℕ → ℕ) (y : HomE E (n + c) (n + c))
    (hy : ∀ x ∈ LocE.lamY P (qOf P) n c ex, y x ∈ LocE.lamY P (qOf P) n c ex) {p p' : ℕ}
    (hp : p < n + c) (hp' : p' < n + c) :
    IntAt P (LocE.entB (qOf P) k₀ c n c n ex ex (LinearMap.id + ((qOf P : ℕ) : E) • y) p p') ∧
      redP P (LocE.entB (qOf P) k₀ c n c n ex ex (LinearMap.id + ((qOf P : ℕ) : E) • y) p p') =
        if p = p' then 1 else 0 := by
  have hQ0 : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero
  have hfl : LocE.fIdx k₀ c n p < n + c := fIdx_lt hk hp
  have hfl' : LocE.fIdx k₀ c n p' < n + c := fIdx_lt hk hp'
  have hb : IntAt P ((((qOf P : ℕ) : E) ^ LocE.scE n ex (LocE.fIdx k₀ c n p))⁻¹ *
      (((qOf P : ℕ) : E) ^ LocE.scE n ex (LocE.fIdx k₀ c n p') *
        y (Loc.eN E (n + c) (LocE.fIdx k₀ c n p')) ⟨_, hfl⟩)) := by
    have h1 := hy _ (GlobalTheory.CongLevel.bvec_mem P (qOf P) hQ0 (n + c) (LocE.scE n ex) (LocE.fIdx k₀ c n p'))
    have h2 := (GlobalTheory.CongLevel.mem_sclLat P (qOf P) (n + c) _ _).1 h1 ⟨_, hfl⟩
    rw [map_smul, Pi.smul_apply, smul_eq_mul] at h2
    exact h2
  have key : LocE.entB (qOf P) k₀ c n c n ex ex (LinearMap.id + ((qOf P : ℕ) : E) • y) p p' =
      (if p = p' then 1 else 0) + ((qOf P : ℕ) : E) * ((((qOf P : ℕ) : E) ^ LocE.scE n ex (LocE.fIdx k₀ c n p))⁻¹ *
      (((qOf P : ℕ) : E) ^ LocE.scE n ex (LocE.fIdx k₀ c n p') *
        y (Loc.eN E (n + c) (LocE.fIdx k₀ c n p')) ⟨_, hfl⟩)) := by
    unfold LocE.entB Loc.atN
    rw [dite_eq_left hfl, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    by_cases hpp : p = p'
    · subst hpp
      have : Loc.eN E (n + c) (LocE.fIdx k₀ c n p) ⟨_, hfl⟩ = 1 := by simp [Loc.eN]
      rw [this, if_pos rfl, sub_self, zpow_zero, mul_one]
      have h0 := zpow_ne_zero (LocE.scE n ex (LocE.fIdx k₀ c n p)) hQ0
      field_simp
    · have hff : LocE.fIdx k₀ c n p ≠ LocE.fIdx k₀ c n p' := fun h => hpp (fIdx_inj hk hp hp' h)
      have : Loc.eN E (n + c) (LocE.fIdx k₀ c n p') ⟨_, hfl⟩ = 0 := by simp [Loc.eN, hff]
      rw [this, if_neg hpp, zero_add, zero_add, zpow_sub₀ hQ0]
      have h0 := zpow_ne_zero (LocE.scE n ex (LocE.fIdx k₀ c n p)) hQ0
      field_simp
  have hd : IntAt P (if p = p' then (1 : E) else 0) := by
    split_ifs
    · exact intAt_one
    · exact intAt_zero
  have hqb := (intAt_nat (P := P) (qOf P)).mul hb
  rw [key]
  refine ⟨hd.add hqb, ?_⟩
  rw [reduction_add hd hqb, reduction_mul (intAt_nat _) hb, reduction_absNorm_eq_zero, zero_mul, add_zero]
  split_ifs
  · exact reduction_one₂
  · exact reduction_zero

end Ent

theorem lamRow_one_add_q : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∈ Pr.vGs → ∀ y : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j), (∀ x ∈ lamYat (Pr := Pr) (R := R) j P, y x ∈ lamYat (Pr := Pr) (R := R) j P) → lamRow Ch mu sharp j P (LinearMap.id + (qOf P : X.E) • y) = 1 := by
  intro X Pr R Ch S mu sharp j P hP y hy
  have hm := R.two_le_m
  have hk : R.k ≤ R.N j := by unfold Ranks.N; omega
  have hkr : R.k ≤ R.r := by unfold Ranks.r; omega
  have hNj : R.N j = R.k + j * R.t + j := by unfold Ranks.N; ring
  have hr : R.r ≤ R.N j + cOf R j := by
    rw [hNj]
    unfold Ranks.r cOf
    generalize j * R.t = u
    omega
  have hrj : R.r + j * R.t ≤ R.N j + cOf R j := by
    rw [hNj]
    unfold Ranks.r cOf
    generalize j * R.t = u
    omega
  have hy' : ∀ x ∈ LocE.lamY P (qOf P) (R.N j) (cOf R j) (fun i => i + 1),
      y x ∈ LocE.lamY P (qOf P) (R.N j) (cOf R j) (fun i => i + 1) := by
    intro x hx
    have h := hy x (by unfold lamYat; rw [if_pos hP]; exact hx)
    unfold lamYat at h
    rw [if_pos hP] at h
    exact h
  have hM := fun p p' (hp : p < R.N j + cOf R j) (hp' : p' < R.N j + cOf R j) =>
    entB_one_add_q (k₀ := R.k) hk (fun i => i + 1) y hy' hp hp'
  unfold lamRow
  rw [if_pos hP]
  cases sharp
  · simp only [Bool.false_eq_true, if_false]
    unfold LocE.lamGB
    exact lamGv_eq_one _ _ _ hM hr hrj
  · simp only [if_true]
    unfold LocE.lamGBS
    exact lamGvS_eq_one _ _ _ hM hkr hr hrj

end GlobalTheory.LamRowCong
end
end

section

open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

namespace GlobalTheory

namespace NormalFamily

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem adjoint_apply_eq_zero {S : Module.End ℂ E} (h : Commute S (LinearMap.adjoint S)) {v : E}
    (hv : S v = 0) : LinearMap.adjoint S v = 0 := by
  have e : S (LinearMap.adjoint S v) = LinearMap.adjoint S (S v) := LinearMap.congr_fun h.eq v
  rw [← inner_self_eq_zero (𝕜 := ℂ), LinearMap.adjoint_inner_right, e, hv, map_zero, inner_zero_left]

theorem apply_eq_zero_of_pow {S : Module.End ℂ E} (h : Commute S (LinearMap.adjoint S)) (k : ℕ) {v : E}
    (hv : (S ^ k) v = 0) : S v = 0 := by
  induction k generalizing v with
  | zero =>
    have : v = 0 := by simpa using hv
    rw [this, map_zero]
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply] at hv
    have h1 := adjoint_apply_eq_zero h (ih hv)
    rw [← inner_self_eq_zero (𝕜 := ℂ), ← LinearMap.adjoint_inner_left, h1, inner_zero_left]

theorem adjoint_sub_smul (T : Module.End ℂ E) (a : ℂ) :
    LinearMap.adjoint (T - a • (1 : Module.End ℂ E)) =
      LinearMap.adjoint T - (starRingEnd ℂ a) • (1 : Module.End ℂ E) := by
  rw [map_sub, LinearEquiv.map_smulₛₗ]
  congr 2
  exact star_one (Module.End ℂ E)

theorem commute_sub_smul {T : Module.End ℂ E} (h : Commute T (LinearMap.adjoint T)) (a : ℂ) :
    Commute (T - a • (1 : Module.End ℂ E)) (LinearMap.adjoint (T - a • (1 : Module.End ℂ E))) := by
  rw [adjoint_sub_smul]
  exact (h.sub_right ((Commute.one_right T).smul_right _)).sub_left ((Commute.one_left _).smul_left a)

theorem maxGenEigenspace_eq {T : Module.End ℂ E} (h : Commute T (LinearMap.adjoint T)) (a : ℂ) :
    T.maxGenEigenspace a = T.eigenspace a := by
  ext v
  rw [Module.End.mem_maxGenEigenspace, Module.End.mem_eigenspace_iff]
  constructor
  · rintro ⟨k, hk⟩
    have := apply_eq_zero_of_pow (commute_sub_smul h a) k hk
    simpa [sub_eq_zero] using this
  · intro hv
    exact ⟨1, by simp [hv]⟩

theorem eigenspace_isOrtho {T : Module.End ℂ E} (h : Commute T (LinearMap.adjoint T)) {a b : ℂ}
    (hab : a ≠ b) : T.eigenspace a ⟂ T.eigenspace b := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro v hv w hw
  rw [Module.End.mem_eigenspace_iff] at hv hw
  have h0 : (T - a • (1 : Module.End ℂ E)) v = 0 := by simp [hv]
  have h1 := adjoint_apply_eq_zero (commute_sub_smul h a) h0
  have h2 : inner ℂ v ((T - a • (1 : Module.End ℂ E)) w) = 0 := by
    rw [← LinearMap.adjoint_inner_left, h1, inner_zero_left]
  have h3 : (T - a • (1 : Module.End ℂ E)) w = (b - a) • w := by simp [hw, sub_smul]
  rw [h3, inner_smul_right, mul_eq_zero] at h2
  exact h2.resolve_left (sub_ne_zero.2 hab.symm)

end NormalFamily

theorem normalFamily_orthogonal_decomposition :
    ∀ {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (op : I → Module.End ℂ E), PairComm op → (∀ i, ∃ i', op i' = LinearMap.adjoint (op i)) → (∀ x, eigAt op x = ⨅ i, (op i).eigenspace (x i)) ∧ (⨆ x, eigAt op x) = ⊤ ∧ ∀ x x', x ≠ x' → eigAt op x ⟂ eigAt op x' := by
  intro E I _ _ _ op hc hadj
  have hn : ∀ i, Commute (op i) (LinearMap.adjoint (op i)) := fun i => by
    obtain ⟨i', hi'⟩ := hadj i
    rw [← hi']
    exact hc i i'
  have h1 : ∀ x, eigAt op x = ⨅ i, (op i).eigenspace (x i) := fun x =>
    iInf_congr fun i => NormalFamily.maxGenEigenspace_eq (hn i) (x i)
  refine ⟨h1, iSup_eigAt_eq_top hc fun i => Module.End.iSup_maxGenEigenspace_eq_top (op i), ?_⟩
  intro x x' hx
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  rw [h1, h1]
  exact (NormalFamily.eigenspace_isOrtho (hn i) hi).mono (iInf_le _ i) (iInf_le _ i)

end GlobalTheory
end

section

open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

noncomputable section

namespace GlobalTheory.FormsDescent

section General

variable {K V ι : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]

def coordMap (F : Subfield K) (b : Module.Basis ι K V) (φ : K →ₗ[F] K) (v : V) : V :=
  ∑ i, φ (b.repr v i) • b i

theorem repr_coordMap (F : Subfield K) (b : Module.Basis ι K V) (φ : K →ₗ[F] K) (v : V) (i : ι) :
    b.repr (coordMap F b φ v) i = φ (b.repr v i) := by
  unfold coordMap
  rw [b.repr_sum_self]

theorem coordMap_sum (F : Subfield K) (b : Module.Basis ι K V) (φ : K →ₗ[F] K) {α : Type} [Fintype α]
    (x : α → K) (w : α → V) (hw : ∀ a i, b.repr (w a) i ∈ F) :
    coordMap F b φ (∑ a, x a • w a) = ∑ a, φ (x a) • w a := by
  apply b.repr.injective
  ext i
  rw [repr_coordMap]

  simp only [map_sum, map_smul, Finset.sum_apply', Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h := φ.map_smul (⟨b.repr (w a) i, hw a i⟩ : F) (x a)
  simp only [Subfield.smul_def, smul_eq_mul] at h
  rw [mul_comm (x a), h, mul_comm]

theorem map_coordMap (F : Subfield K) (b : Module.Basis ι K V) (φ : K →ₗ[F] K) (g : V →ₗ[K] V)
    (hg : ∀ i j, b.repr (g (b j)) i ∈ F) (v : V) :
    g (coordMap F b φ v) = coordMap F b φ (g v) := by
  have h1 : g v = ∑ j, b.repr v j • g (b j) := by
    conv_lhs => rw [← b.sum_repr v]

    simp only [map_sum, map_smul]
  rw [h1, coordMap_sum F b φ _ _ (fun a i => hg i a)]

  simp only [coordMap, map_sum, map_smul]

theorem exists_retraction (F : Subfield K) :
    ∃ φ : K →ₗ[F] K, (∀ x, φ x ∈ F) ∧ ∀ x ∈ F, φ x = x := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F K)
    (LinearMap.ker_eq_bot.2 (algebraMap F K).injective)
  refine ⟨(Algebra.linearMap F K).comp g, fun x => (g x).2, fun x hx => ?_⟩
  have h := LinearMap.congr_fun hg ⟨x, hx⟩
  have h' : g x = ⟨x, hx⟩ := h
  show ((g x : F) : K) = x
  rw [h']

end General

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)

theorem hasRatBasis_of_act
    (h : ∀ c (γ : S.Gam c) i j, S.bV.repr (S.ρ c γ (S.bV j)) i ∈ cmMax K) : S.HasRatBasis := by
  classical
  haveI : Module.Finite (cmMax K) K := Module.Finite.of_restrictScalars_finite ℚ (cmMax K) K
  let e := Module.finBasis (cmMax K) K
  let s : Set S.Forms := {f | S.IsRat (f : S.Cl → S.V)}
  have hs : ⊤ ≤ Submodule.span K s := by
    intro f _
    let φ : Fin (Module.finrank (cmMax K) K) → (K →ₗ[cmMax K] K) :=
      fun k => (Algebra.linearMap (cmMax K) K).comp (e.coord k)
    let g : Fin (Module.finrank (cmMax K) K) → S.Forms := fun k =>
      ⟨fun c => coordMap (cmMax K) S.bV (φ k) ((f : S.Cl → S.V) c), fun c γ => by
        rw [map_coordMap (cmMax K) S.bV (φ k) (S.ρ c γ) (h c γ), f.2 c γ]⟩
    have hf : f = ∑ k, e k • g k := by
      apply Subtype.ext
      funext c
      apply S.bV.repr.injective
      ext i

      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, map_sum, map_smul,
      Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul, g, repr_coordMap]
      conv_lhs => rw [← e.sum_repr (S.bV.repr ((f : S.Cl → S.V) c) i)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_comm]
      rfl
    rw [hf]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    intro c i
    show S.bV.repr (coordMap (cmMax K) S.bV (φ k) ((f : S.Cl → S.V) c)) i ∈ cmMax K
    rw [repr_coordMap]
    exact (e.coord k _).2
  let b := Module.Basis.ofSpan hs
  refine ⟨b.reindex (b.indexEquiv (Module.finBasis K S.Forms)), fun i => ?_⟩
  rw [Module.Basis.reindex_apply]
  exact Module.Basis.ofSpan_subset hs ⟨_, rfl⟩

theorem repr_mem_of_isRat (h : S.HasRatBasis) (f : S.Forms) (hf : S.IsRat (f : S.Cl → S.V)) (a : Fin S.dim) :
    S.basis.repr f a ∈ cmMax K := by
  have hb : ∀ i, S.IsRat (S.basis i : S.Cl → S.V) := by
    have : S.basis = h.choose := by
      unfold CSD.basis
      exact dif_pos h
    rw [this]
    exact h.choose_spec
  obtain ⟨φ, h1, h2⟩ := exists_retraction (cmMax K)
  have key : f = ∑ a, φ (S.basis.repr f a) • S.basis a := by
    apply Subtype.ext
    funext c
    have e1 : (f : S.Cl → S.V) c = ∑ a, S.basis.repr f a • (S.basis a : S.Cl → S.V) c := by
      conv_lhs => rw [← S.basis.sum_repr f]
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
    have e2 : coordMap (cmMax K) S.bV φ ((f : S.Cl → S.V) c) = (f : S.Cl → S.V) c := by
      apply S.bV.repr.injective
      ext i
      rw [repr_coordMap, h2 _ (hf c i)]
    rw [← e2, e1, coordMap_sum (cmMax K) S.bV φ _ _ (fun a i => hb a c i)]
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
  have : S.basis.repr f a = φ (S.basis.repr f a) := by
    conv_lhs => rw [key]
    rw [S.basis.repr_sum_self]
  rw [this]
  exact h1 _

end GlobalTheory.FormsDescent

namespace GlobalTheory

theorem forms_rat : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K), ((∀ c (γ : S.Gam c) i j, S.bV.repr (S.ρ c γ (S.bV j)) i ∈ cmMax K) → S.HasRatBasis) ∧ ∀ T : Module.End K S.Forms, S.HasRatBasis → (∀ f : S.Forms, S.IsRat (f : S.Cl → S.V) → S.IsRat ((T f : S.Forms) : S.Cl → S.V)) → ∀ a b, LinearMap.toMatrix S.basis S.basis T a b ∈ cmMax K := by
  intro K _ _ _ S
  refine ⟨FormsDescent.hasRatBasis_of_act S, fun T h hT a b => ?_⟩
  rw [LinearMap.toMatrix_apply]
  refine FormsDescent.repr_mem_of_isRat S h _ (hT _ ?_) a
  have : S.basis = h.choose := by
    unfold CSD.basis
    exact dif_pos h
  rw [this]
  exact h.choose_spec b

end GlobalTheory
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

namespace GlobalTheory

theorem locBasisW_clear_den : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (ρ : D.host.E →+* ℂ_[p]) (N N' : ℕ) (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : Matrix (Fin N) (Fin N) D.host.E) (P' : Matrix (Fin N') (Fin N') D.host.E), L₁.FG → TaylorLogMetric.EqAt D p L L₁ → TaylorLogMetric.EqAt D p L' L₁' → TaylorLogMetric.LocBasisW D ρ L P → TaylorLogMetric.LocBasisW D ρ L' P' → ∃ σ σ' : 𝓞 D.host.E, ‖ρ (σ : D.host.E)‖ = 1 ∧ ‖ρ (σ' : D.host.E)‖ = 1 ∧ (∀ (a : Fin N) (x : Fin N → D.host.E), x ∈ L₁ → ∃ o : 𝓞 D.host.E, (o : D.host.E) = (σ : D.host.E) * ∑ j, P⁻¹ a j * x j) ∧ ∀ b : Fin N', (fun i => (σ' : D.host.E) * P' i b) ∈ L₁' := by
  first
  | exact @_root_.GlobalTheory.CoprimeUnitMultipliers.exists_unit_multipliers
  | exact _root_.GlobalTheory.CoprimeUnitMultipliers.exists_unit_multipliers
  | (apply _root_.GlobalTheory.CoprimeUnitMultipliers.exists_unit_multipliers <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoprimeUnitMultipliers.exists_unit_multipliers <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoprimeUnitMultipliers.exists_unit_multipliers <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoprimeUnitMultipliers.exists_unit_multipliers ..)

end GlobalTheory
end
