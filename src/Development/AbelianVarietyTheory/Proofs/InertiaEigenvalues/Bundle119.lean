module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import GroundTheory.GlobalFields.TateThesis.AdelicChar
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle093
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle095
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle096
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle094
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.RamificationInertia.Galois
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
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep
open scoped ContDiff

namespace GlobalTheory.SchurExt

def idemHom {R : Type} [CommRing R] (e : R) (he : IsIdempotentElem e) : R →ₙ+* R where
  toFun x := e * x
  map_mul' x y := by
    change e * (x * y) = e * x * (e * y)
    calc e * (x * y) = (e * e) * (x * y) := by rw [he.eq]
      _ = e * x * (e * y) := by ring
  map_zero' := mul_zero e
  map_add' x y := mul_add e x y

variable {E : Type} [Field E] [NumberField E]


open Classical in
def idemSf (S : Finset (HeightOneSpectrum (𝓞 E))) : Af E :=
  ⟨fun w => if w ∈ S then 1 else 0, Filter.Eventually.of_forall fun w => by
    by_cases h : w ∈ S
    · simp only [h, if_true]; exact one_mem _
    · simp only [h, if_false]; exact zero_mem _⟩

theorem isIdempotentElem_idemSf (S : Finset (HeightOneSpectrum (𝓞 E))) : IsIdempotentElem (idemSf S) := by
  classical
  refine Subtype.ext (funext fun w => ?_)
  change (if w ∈ S then (1 : w.adicCompletion E) else 0) * (if w ∈ S then 1 else 0) = if w ∈ S then 1 else 0
  split_ifs <;> simp

def idemS (S : Finset (HeightOneSpectrum (𝓞 E))) : Ad E := ((1 : InfiniteAdeleRing E), idemSf S)

theorem isIdempotentElem_idemS (S : Finset (HeightOneSpectrum (𝓞 E))) : IsIdempotentElem (idemS S) :=
  Prod.ext (mul_one _) (isIdempotentElem_idemSf S).eq

def prS (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) : GA E a →* GA E a :=
  cornerGL a (idemHom (idemS S) (isIdempotentElem_idemS S))

def prO (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) : GA E a →* GA E a :=
  cornerGL a (idemHom (1 - idemS S) (isIdempotentElem_idemS S).one_sub)

def prSf (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) : GL (Fin a) (Af E) →* GL (Fin a) (Af E) :=
  cornerGL a (idemHom (idemSf S) (isIdempotentElem_idemSf S))

def prOf (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) : GL (Fin a) (Af E) →* GL (Fin a) (Af E) :=
  cornerGL a (idemHom (1 - idemSf S) (isIdempotentElem_idemSf S).one_sub)

def eqv (m r : ℕ) : Fin (m + r + 1 + 1) ≃ Fin (m + 1) ⊕ Fin (r + 1) :=
  (finCongr (by omega)).trans finSumFinEquiv.symm

section Blocks

variable {R : Type} [CommRing R] {m r : ℕ}

def blk (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    Matrix (Fin (m + 1) ⊕ Fin (r + 1)) (Fin (m + 1) ⊕ Fin (r + 1)) R :=
  M.submatrix (eqv m r).symm (eqv m r).symm

def unblk (P : Matrix (Fin (m + 1) ⊕ Fin (r + 1)) (Fin (m + 1) ⊕ Fin (r + 1)) R) :
    Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R :=
  P.submatrix (eqv m r) (eqv m r)

def Aof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  (blk M).toBlocks₁₁

def Bof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Matrix (Fin (m + 1)) (Fin (r + 1)) R :=
  (blk M).toBlocks₁₂

def Cof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Matrix (Fin (r + 1)) (Fin (m + 1)) R :=
  (blk M).toBlocks₂₁

def Dof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  (blk M).toBlocks₂₂

def Xof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Matrix (Fin (m + 1)) (Fin (r + 1)) R :=
  Bof M * (Dof M)⁻¹

def Yof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Matrix (Fin (r + 1)) (Fin (m + 1)) R :=
  (Dof M)⁻¹ * Cof M

def Scof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Aof M - Bof M * (Dof M)⁻¹ * Cof M

theorem unblk_blk (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : unblk (blk M) = M := by
  ext i j; simp [unblk, blk]

theorem blk_unblk (P : Matrix (Fin (m + 1) ⊕ Fin (r + 1)) (Fin (m + 1) ⊕ Fin (r + 1)) R) : blk (unblk P) = P := by
  ext i j; simp [unblk, blk]

end Blocks


open Classical in
def mkGL {R : Type} [CommRing R] {k : ℕ} (M : Matrix (Fin k) (Fin k) R) : GL (Fin k) R :=
  if h : IsUnit M.det then Matrix.nonsingInvUnit M h else 1

theorem coe_mkGL {R : Type} [CommRing R] {k : ℕ} {M : Matrix (Fin k) (Fin k) R} (h : IsUnit M.det) :
    ((mkGL M : GL (Fin k) R) : Matrix (Fin k) (Fin k) R) = M := by
  rw [mkGL, dite_eq_left h]; rfl

def psi (x : Ad E) : ℂ := (GroundTheory.Global.adelicChar E x : ℂ)

variable [_root_.NumberField.IsTotallyComplex E]

def chiF {m r : ℕ} (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ) (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E)) : ℂ :=
  open Classical in
  (χ (fun i j => pInf E (Y i j)) : ℂ) *
    (if ∀ i j, pFin E (Y i j) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E then 1 else 0)

def schurF {m r : ℕ} (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ)
    (g : GA E (m + r + 1 + 1)) : ℂ :=
  open Classical in
  if IsUnit (Dof (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det then
    psi (Xof (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) 0) *
      β (mkGL (Scof (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))) *
      b₁ (mkGL (Dof (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))) *
      chiF χ (Yof (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))
  else 0

def extB {m r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ)
    (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ) (Φ : GA E (m + r + 1 + 1) → ℂ) (g : GA E (m + r + 1 + 1)) : ℂ :=
  schurF β b₁ χ (prS S _ g) * Φ (prO S _ g)

end GlobalTheory.SchurExt
end
end

section


theorem _root_.GlobalTheory.T.normalizedAbsValueLocalFieldUnit_map_homeomorph : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k'), Continuous i → Continuous i.symm → ∀ x : kˣ, GlobalTheory.SplitWeil.nabs k' (Units.map i.toRingHom.toMonoidHom x) = GlobalTheory.SplitWeil.nabs k x := by
  first | exact @GlobalTheory.SplitWeil.nabs_map_of_homeomorph | exact GlobalTheory.SplitWeil.nabs_map_of_homeomorph | (intros; apply GlobalTheory.SplitWeil.nabs_map_of_homeomorph <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.NT

open NumberField IsDedekindDomain

theorem isUnramifiedAt_of_unramIn {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] {𝔭 : HeightOneSpectrum (𝓞 K)} (h : UnramIn L 𝔭) (P : Ideal (𝓞 L)) [P.IsPrime]
    [P.LiesOver 𝔭.asIdeal] : Algebra.IsUnramifiedAt (𝓞 K) P := by
  have : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ K L
  have := 𝔭.isMaximal
  have hu : P.under (𝓞 K) = 𝔭.asIdeal := (Ideal.over_def P 𝔭.asIdeal).symm
  have : (P.under (𝓞 K)).IsMaximal := by rw [hu]; infer_instance
  have : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔭.ne_bot
  have : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P)
  have h1 : P.inertia (L ≃ₐ[K] L) = ⊥ :=
    (Subgroup.eq_bot_iff_forall _).2 fun τ hτ => h τ ⟨P, inferInstance, inferInstance, hτ⟩
  have h2 := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) 𝔭.asIdeal P
  rw [h1, Subgroup.card_bot, Ideal.ramificationIdxIn_eq_ramificationIdx _ P (L ≃ₐ[K] L)] at h2
  exact Ideal.ramificationIdx_eq_one_iff.1 h2.symm

end GlobalTheory.NT

end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem gl_lc_sc (F : Type) [NontriviallyNormedField F] [LocallyCompactSpace F] (r : ℕ) :
    LocallyCompactSpace (GL (Fin r) F) ∧ SecondCountableTopology (GL (Fin r) F) := by
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) F) :=
    inferInstanceAs (SecondCountableTopology (Fin r → Fin r → F))
  haveI : LocallyCompactSpace (Matrix (Fin r) (Fin r) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin r → Fin r → F))
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) F)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin r) (Fin r) F)).symm.secondCountableTopology
  exact ⟨Units.isClosedEmbedding_embedProduct.locallyCompactSpace,
    Units.isEmbedding_embedProduct.secondCountableTopology⟩

theorem gl_unimodular : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E), (letI := M.mG; M.μG.IsMulRightInvariant) := by
  intro F E _ _ _ _ hU r M
  haveI : LocallyCompactSpace F := hU.lcF
  obtain ⟨h1, h2⟩ := gl_lc_sc F r
  letI := M.mG
  haveI := M.bG
  haveI := M.haarG
  have hmod : ∀ a : GL (Fin r) F, Measure.modularCharacterFun a = 1 := by
    intro a
    refine GlobalTheory.SplitFlip.hom_eq_one_of_center
      (Measure.modularCharacter : GL (Fin r) F →* NNReal) (fun z hz => ?_) a
    change Measure.modularCharacterFun z = 1
    have e : Measure.map (fun x : GL (Fin r) F => x * z)
        (Measure.haar : Measure (GL (Fin r) F)) = Measure.haar := by
      rw [show (fun x : GL (Fin r) F => x * z) = fun x => z * x from
        funext fun x => (hz x).symm, map_mul_left_eq_self]
    rw [Measure.modularCharacterFun_eq_haarScalarFactor (Measure.haar : Measure (GL (Fin r) F)) z]
    simp only [e, Measure.haarScalarFactor_self]
  refine ⟨fun g => ?_⟩
  rw [Measure.isMulLeftInvariant_eq_smul (Measure.map (· * g) M.μG) M.μG,
    ← Measure.modularCharacterFun_eq_haarScalarFactor, hmod, one_smul]

end GlobalTheory.JR
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.RowSmooth

theorem row_smooth : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (T : R × R → ℂ), IsTest T → ∃ U ∈ 𝓝 (0 : R), ∀ k : SpecialLinearGroup (Fin 2) R, (∀ i j, ((k : Matrix (Fin 2) (Fin 2) R) - 1) i j ∈ U) → ∀ c u : R, T (c * k 0 0 + u * k 1 0, c * k 0 1 + u * k 1 1) = T (c, u) := by
  intro R _ _ _ T hT
  classical
  obtain ⟨V, hV, hVT⟩ := GlobalTheory.TestFn.unif_const (R × R) T hT
  have hC : IsCompact (tsupport T) := hT.2
  let φ : (R × R × R × R) → R × R → R × R := fun e v =>
    (v.1 * e.1 + v.2 * e.2.2.1, v.1 * e.2.1 + v.2 * e.2.2.2)
  have hφ : Continuous (fun z : (R × R × R × R) × (R × R) => φ z.1 z.2) := by
    simp only [φ]; fun_prop
  have hev : ∀ᶠ e in 𝓝 (0 : R × R × R × R), ∀ v ∈ tsupport T, φ e v ∈ V := by
    refine hC.eventually_forall_of_forall_eventually (P := fun e v => φ e v ∈ V) ?_
    intro v _
    have h0 : φ 0 v = 0 := by simp [φ]
    have : V ∈ 𝓝 (φ (0 : R × R × R × R) v) := by rw [h0]; exact hV
    exact hφ.continuousAt (x := ((0 : R × R × R × R), v)) this
  obtain ⟨A₁, hA₁, S₁, hS₁, hsub₁⟩ := mem_nhds_prod_iff.mp (show _ ∈ 𝓝 ((0 : R), ((0 : R), (0 : R), (0 : R))) from hev)
  obtain ⟨A₂, hA₂, S₂, hS₂, hsub₂⟩ := mem_nhds_prod_iff.mp hS₁
  obtain ⟨A₃, hA₃, A₄, hA₄, hsub₃⟩ := mem_nhds_prod_iff.mp hS₂
  set U₀ : Set R := A₁ ∩ A₂ ∩ A₃ ∩ A₄ with hU₀def
  have hU₀ : U₀ ∈ 𝓝 (0 : R) := inter_mem (inter_mem (inter_mem hA₁ hA₂) hA₃) hA₄
  have key : ∀ a b c d : R, a ∈ U₀ → b ∈ U₀ → c ∈ U₀ → d ∈ U₀ → ∀ v ∈ tsupport T,
      T (v + φ (a, b, c, d) v) = T v := by
    intro a b c d ha hb hc hd v hv
    have hmem : ((a, b, c, d) : R × R × R × R) ∈ {e | ∀ v ∈ tsupport T, φ e v ∈ V} :=
      hsub₁ ⟨ha.1.1.1, hsub₂ ⟨hb.1.1.2, hsub₃ ⟨hc.1.2, hd.2⟩⟩⟩
    exact hVT v _ (hmem v hv)
  refine ⟨U₀ ∩ (fun x => -x) ⁻¹' U₀, inter_mem hU₀
    (continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hU₀)), ?_⟩
  intro k hk c u
  have hdet : k 0 0 * k 1 1 - k 0 1 * k 1 0 = 1 := by
    have := k.2; rw [Matrix.det_fin_two] at this; exact this
  have e00 := hk 0 0
  have e01 := hk 0 1
  have e10 := hk 1 0
  have e11 := hk 1 1
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), sub_zero] at e00 e01 e10 e11
  by_cases hv : (c, u) ∈ tsupport T
  · have := key (k 0 0 - 1) (k 0 1) (k 1 0) (k 1 1 - 1) e00.1 e01.1 e10.1 e11.1 (c, u) hv
    rw [← this]
    congr 1
    simp only [φ, Prod.mk_add_mk]
    ext <;> simp <;> ring
  by_cases hw : (c * k 0 0 + u * k 1 0, c * k 0 1 + u * k 1 1) ∈ tsupport T
  · have := key (k 1 1 - 1) (-k 0 1) (-k 1 0) (k 0 0 - 1) e11.1 e01.2 e10.2 e00.1 _ hw
    rw [← this]
    congr 1
    simp only [φ, Prod.mk_add_mk]
    ext
    · simp; linear_combination c * hdet
    · simp; linear_combination u * hdet
  · rw [image_eq_zero_of_notMem_tsupport hv, image_eq_zero_of_notMem_tsupport hw]

end GlobalTheory.RowSmooth
end

section

noncomputable section

namespace GlobalTheory.PMonE

open Finset

theorem norm_mulVec_le_one_of_integral_matrix {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    (A : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (x : m → F) (hx : Integral x) (i : m) :
    ‖A.mulVec x i‖ ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun j _ => ?_)
  rw [norm_mul]
  exact mul_le_one₀ (hA i j) (norm_nonneg _) (hx j)

theorem integralNormVector_pow_sub_mulVec {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    (A : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (q : ℕ) (x : m → F) (hx : Integral x) :
    Integral (fun i => x i ^ q - A.mulVec x i) := by
  intro i
  have h1 : ‖x i ^ q‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hx i)
  have h2 := norm_mulVec_le_one_of_integral_matrix A hA x hx i
  calc ‖x i ^ q - A.mulVec x i‖ = ‖x i ^ q + -A.mulVec x i‖ := by rw [sub_eq_add_neg]
    _ ≤ max ‖x i ^ q‖ ‖-A.mulVec x i‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := by rw [norm_neg]; exact max_le h1 h2

theorem additiveSystemFrobeniusPowerSum_zero {F : Type} [NormedField F] {m : Type} [Fintype m] (q D : ℕ) (hq : 0 < q)
    (U : ℕ → Matrix m m F) : gsum q D U (fun _ => 0) = 0 := by
  unfold gsum
  refine Finset.sum_eq_zero (fun n _ => ?_)
  have : (fun _ : m => (0 : F) ^ q ^ n) = 0 := by
    funext i; simp [zero_pow (pow_pos hq n).ne']
  rw [this, Matrix.mulVec_zero]

theorem gl1 : GLOnto 1 ∧ GLCount 1 := by
  constructor
  · intro F _ _ _ _ p _ _ m _ _ e D he hD M hM b hb
    obtain ⟨A, U, hA, hU0, hUn, -, hfac⟩ := GlobalTheory.T.additiveSystem_preparation_normalForm_one F p m e D he hD M hM
    obtain ⟨y, ⟨hy, hyb⟩, -⟩ := GlobalTheory.T.existsUnique_integral_additiveSystemFrobeniusPowerSum_eq F p m e D he U hU0 hUn b hb
    obtain ⟨x, hx, hxy⟩ := GlobalTheory.T.exists_integral_solution_frobenius_sub_mulVec_eq F p m e he A hA y hy
    refine ⟨x, hx, ?_⟩
    rw [hfac]
    have : (fun i => x i ^ p ^ e - A.mulVec x i) = y := funext hxy
    rw [this, hyb]
  · intro F _ _ _ _ p _ _ m _ _ e D he hD M hM hdet
    obtain ⟨A, U, hA, hU0, hUn, hM0, hfac⟩ := GlobalTheory.T.additiveSystem_preparation_normalForm_one F p m e D he hD M hM
    have hAdet : A.det ≠ 0 := by
      intro h
      apply hdet
      rw [hM0, Matrix.det_neg, Matrix.det_mul, h, mul_zero, mul_zero]
    obtain ⟨hInt, hcard⟩ := GlobalTheory.T.lang_count_frobenius_eq_mulVec_solutions F p m e he A hA hAdet
    have hq : 0 < p ^ e := pow_pos (Fact.out : p.Prime).pos e
    obtain ⟨z, -, hz⟩ := GlobalTheory.T.existsUnique_integral_additiveSystemFrobeniusPowerSum_eq F p m e D he U hU0 hUn 0 (fun i => by simp)
    have key : ∀ x : m → F, Integral x →
        (gsum (p ^ e) D M x = 0 ↔ ∀ i, x i ^ p ^ e = A.mulVec x i) := by
      intro x hx
      rw [hfac]
      constructor
      · intro h0
        have h1 := hz _ ⟨integralNormVector_pow_sub_mulVec A hA (p ^ e) x hx, h0⟩
        have h2 := hz (fun _ => 0) ⟨fun i => by simp, additiveSystemFrobeniusPowerSum_zero _ D hq U⟩
        intro i
        have := congrFun (h1.trans h2.symm) i
        exact sub_eq_zero.mp this
      · intro h
        have : (fun i => x i ^ p ^ e - A.mulVec x i) = fun _ => 0 := funext fun i => by rw [h i, sub_self]
        rw [this]
        exact additiveSystemFrobeniusPowerSum_zero _ D hq U
    have eqv : {x : m → F // Integral x ∧ gsum (p ^ e) D M x = 0} ≃
        {x : m → F // ∀ i, x i ^ p ^ e = A.mulVec x i} :=
      { toFun := fun x => ⟨x.1, (key x.1 x.2.1).mp x.2.2⟩
        invFun := fun x => ⟨x.1, hInt x.1 x.2, (key x.1 (hInt x.1 x.2)).mpr x.2⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
    rw [Nat.card_congr eqv, hcard, mul_one]

end GlobalTheory.PMonE

end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.isLocallyConstantCompactSupport_partialFourierGLBlock : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f' : Gl r F → ℂ, IsTest f' → IsTest (fourG M ψ f') := by
  first | exact @GlobalTheory.JR.fourG_isTest | exact GlobalTheory.JR.fourG_isTest | (intros; apply GlobalTheory.JR.fourG_isTest <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.unitaryOrbit_proper_of_invertible_krylovColumns : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Ω : Set (Inv r F)) (s : Inv r F → Hn r F E) (h : Inv r F → Matrix (Fin r) (Fin r) E), IsCompact Ω → ContinuousOn s Ω → ContinuousOn h Ω → (∀ a ∈ Ω, IsUnit (h a).det ∧ Bm (s a).toGl = h a) → ∀ C : Set (Hn r F E), IsCompact C → IsCompact {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C} := by
  first | exact @GlobalTheory.JR.orbit_proper_of_columns | exact GlobalTheory.JR.orbit_proper_of_columns | (intros; apply GlobalTheory.JR.orbit_proper_of_columns <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.jacquetRallisTransferFactor_glBorderedConjugationAction_integral : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] (n : ℕ) (k : GL (Fin n) F), k ∈ glO n F → ∀ Y : Gl n F, omega (act k Y) = omega Y := by
  first | exact @GlobalTheory.JR.omega_act_glO | exact GlobalTheory.JR.omega_act_glO | (intros; apply GlobalTheory.JR.omega_act_glO <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.unitIndicatorGLBlock_glBorderedConjugationAction_integral : ∀ (F : Type) [NormedField F] [IsUltrametricDist F] (n : ℕ) (k : GL (Fin n) F), k ∈ glO n F → ∀ Y : Gl n F, unitG n F (act k Y) = unitG n F Y := by
  first | exact @GlobalTheory.JR.GLift.unitG_act | exact GlobalTheory.JR.GLift.unitG_act | (intros; apply GlobalTheory.JR.GLift.unitG_act <;> assumption)
end

section

open GlobalTheory.PMonE

theorem _root_.GlobalTheory.T.additiveSystem_surjectivity_and_count_order_zero : GLOnto 0 ∧ GLCount 0 := by
  first | exact @GlobalTheory.PMonE.glOnto_zero_and_glCount_zero | exact GlobalTheory.PMonE.glOnto_zero_and_glCount_zero | (intros; apply GlobalTheory.PMonE.glOnto_zero_and_glCount_zero <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_compact_unitaries_integral_orbit_of_hankelDet_ne_zero : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {n : ℕ} (Y : Hn n F E), Delta (inv Y.toGl) ≠ 0 → ∃ K : Set (Matrix.unitaryGroup (Fin n) E), IsCompact K ∧ ∀ g, unitU n F E (actU g Y) ≠ 0 → g ∈ K := by
  first | exact @GlobalTheory.JR.SuppBdd.exists_compact_of_integral | exact GlobalTheory.JR.SuppBdd.exists_compact_of_integral | (intros; apply GlobalTheory.JR.SuppBdd.exists_compact_of_integral <;> assumption)
end
