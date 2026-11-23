module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.UnitaryPlaceSplit

theorem mix_mul {S A : Type} [CommRing S] [Ring A] [Algebra S A] {e : S} (he : e * e = e) (x y z w : A) :
    (e • x + (1 - e) • y) * (e • z + (1 - e) • w) = e • (x * z) + (1 - e) • (y * w) := by
  have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h0' : (1 - e) * e = 0 := by rw [mul_comm, h0]
  have h1 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h0, sub_zero]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, he, h0, h0', h1, zero_smul, add_zero,
    zero_add]

variable {F : Type} [Field F] [NumberField F]

def idemAt (v : Pl (F := F)) : AF F := LinearMap.inr F (Ainf F) (Af F) (singleFin v 1)

theorem evFin_idemAt (v : Pl (F := F)) : evFin F v (idemAt v) = 1 := evalV_singleFin_self v 1

theorem idemAt_mul_self (v : Pl (F := F)) : idemAt v * idemAt v = idemAt v := by
  refine Prod.ext (show (0 : Ainf F) * 0 = 0 from mul_zero 0) ?_
  change singleFin v 1 * singleFin v 1 = singleFin v 1
  rw [← singleFin_mul, one_mul]

theorem mul_idemAt_of_evFin (v : Pl (F := F)) {u : AF F} (hu : evFin F v u = 0) : u * idemAt v = 0 := by
  refine Prod.ext (show u.1 * (0 : Ainf F) = 0 from mul_zero _) ?_
  change u.2 * singleFin v 1 = 0
  refine af_ext fun w => ?_
  rw [map_mul, map_zero]
  by_cases h : w = v
  · subst h
    have : evalV F w u.2 = 0 := hu
    rw [this, zero_mul]
  · rw [evalV_singleFin_ne h, mul_zero]

end GlobalTheory.UnitaryPlaceSplit

end

namespace GlobalTheory.UnitaryPlaceSplit

open Matrix

theorem exists_split_at (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (v : Pl (F := F)) (g : UA σ J) :
    ∃ g₁ g₂ : UA σ J, g = g₁ * g₂ ∧ At (evFin F v) (mat g₁ - 1) ∧
      ∀ u : AF F, At (evFin F v) u → u • (mat g₂ - 1) = 0 := by
  have hee : idemAt v * idemAt v = idemAt v := idemAt_mul_self v
  set e : AF F := idemAt v with he_def
  set G : Matrix (Fin n) (Fin n) (AE F E) := ((g.1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))
    with hG
  set Gi : Matrix (Fin n) (Fin n) (AE F E) :=
    ((g.1⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) with hGi
  have hGGi : G * Gi = 1 := Units.mul_inv g.1
  have hGiG : Gi * G = 1 := Units.inv_mul g.1
  have split : ∀ X : Matrix (Fin n) (Fin n) (AE F E), X = e • X + (1 - e) • X := fun X => by
    rw [← add_smul, add_sub_cancel, one_smul]
  set M : Matrix (Fin n) (Fin n) (AE F E) := e • G + (1 - e) • 1 with hM
  set N : Matrix (Fin n) (Fin n) (AE F E) := e • Gi + (1 - e) • 1 with hN
  have hMN : M * N = 1 := by rw [hM, hN, mix_mul hee, hGGi, mul_one, ← split]
  have hNM : N * M = 1 := by rw [hM, hN, mix_mul hee, hGiG, mul_one, ← split]
  let g1gl : GL (Fin n) (AE F E) := ⟨M, N, hMN, hNM⟩
  have hmem : g1gl ∈ UG (cA σ) (incM F J) := by
    change Mᵀ * incM F J * M.map (cA σ) = incM F J
    have hg : Gᵀ * incM F J * G.map (cA σ) = incM F J := g.2
    have hT : Mᵀ = e • Gᵀ + (1 - e) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
      rw [hM, transpose_add, transpose_smul, transpose_smul, transpose_one]
    have hc : M.map (cA σ) = e • G.map (cA σ) + (1 - e) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
      rw [← AlgHom.mapMatrix_apply, hM, map_add (f := _), map_smul, map_smul, map_one, AlgHom.mapMatrix_apply]
    rw [hT, hc, split (incM F J), mix_mul hee, mix_mul hee, hg, one_mul, mul_one]
  let g₁ : UA σ J := ⟨g1gl, hmem⟩
  have hm1 : mat g₁ - 1 = e • (G - 1) := by
    change M - 1 = _
    rw [hM, smul_sub, sub_smul, one_smul]
    abel
  have hm2 : mat (g₁⁻¹ * g) - 1 = (1 - e) • (G - 1) := by
    change N * G - 1 = _
    conv_lhs => rw [split G]
    rw [hN, mix_mul hee, hGiG, one_mul, smul_sub, sub_smul (1 : AF F) e (1 : Matrix (Fin n) (Fin n) (AE F E)), one_smul]
    abel
  refine ⟨g₁, g₁⁻¹ * g, (mul_inv_cancel_left g₁ g).symm, fun u hu => ?_, fun u hu => ?_⟩
  · rw [hm1, smul_smul, mul_idemAt_of_evFin v hu, zero_smul]
  · have h1 : (1 - e) • u = 0 := hu (1 - e) (by rw [map_sub, map_one, he_def, evFin_idemAt, sub_self])
    rw [hm2, smul_smul, mul_comm, ← smul_eq_mul, h1, zero_smul]

end GlobalTheory.UnitaryPlaceSplit
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory.CartanEx

open scoped ComplexOrder

private lemma map_star_mul' {l m k : Type} [Fintype m] (X : Matrix l m ℂ) (Y : Matrix m k ℂ) :
    (X * Y).map star = X.map star * Y.map star := by
  ext i j; simp [Matrix.mul_apply, star_sum]

private lemma map_star_star {l m : Type} (X : Matrix l m ℂ) : (X.map star).map star = X := by
  ext i j; simp

private lemma map_star_one {m : Type} [DecidableEq m] : (1 : Matrix m m ℂ).map star = 1 := by
  ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]

private lemma star_mulVec_map {l m : Type} [Fintype m] (X : Matrix l m ℂ) (v : m → ℂ) :
    star (X *ᵥ v) = X.map star *ᵥ star v := by
  ext i; simp [Matrix.mulVec, dotProduct, star_sum]

theorem exists_isCartan : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (r s : ℕ), HasSig M r s → ∃ θ, IsCartan M θ := by
  intro n M r s ⟨hn, A, hA⟩
  set D : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ := Matrix.fromBlocks 1 0 0 (-1) with hD
  have hDD : D * D = 1 := by simp [hD, Matrix.fromBlocks_multiply]
  have hDT : Dᵀ = D := by simp [hD, Matrix.fromBlocks_transpose]
  have hDs : D.map star = D := by
    simp only [hD, Matrix.fromBlocks_map]
    congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> simp
  clear_value D
  set L := D * Aᵀ * M with hLdef
  clear_value L
  have hL : L * A.map star = 1 := by
    rw [hLdef, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Aᵀ, hA, hDD]
  have e : Fin n ≃ Fin r ⊕ Fin s := (finSumFinEquiv.trans (finCongr hn)).symm
  have hR : A.map star * L = 1 := (Matrix.mul_eq_one_comm_of_equiv e.symm).mp hL
  have hR' : A * L.map star = 1 := by
    have := congrArg (fun X => Matrix.map X star) hR
    simpa only [map_star_mul', map_star_star, map_star_one] using this
  have hL' : L.map star * A = 1 := by
    have := congrArg (fun X => Matrix.map X star) hL
    simpa only [map_star_mul', map_star_star, map_star_one] using this
  refine ⟨A * D * L.map star, ?_, ?_, ?_⟩
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (L.map star) A, hL', Matrix.one_mul, ← Matrix.mul_assoc D D, hDD, Matrix.one_mul, hR']
  · have hDL : D * L = Aᵀ * M := by
      rw [hLdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hDD, Matrix.one_mul]
    calc (A * D * L.map star)ᵀ * M * (A * D * L.map star).map star
        = (L.map star)ᵀ * D * (Aᵀ * M * A.map star) * (D * L) := by
          rw [Matrix.transpose_mul, Matrix.transpose_mul, map_star_mul', map_star_mul', map_star_star, hDs, hDT]
          simp only [Matrix.mul_assoc]
      _ = (A * L.map star)ᵀ * M := by
          rw [hA, hDL, Matrix.mul_assoc (L.map star)ᵀ D D, hDD, Matrix.mul_one, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = M := by rw [hR', Matrix.transpose_one, Matrix.one_mul]
  · intro x hx
    set a := L.map star *ᵥ x with ha_def
    have hxa : x = A *ᵥ a := by rw [ha_def, Matrix.mulVec_mulVec, hR', Matrix.one_mulVec]
    have ha : a ≠ 0 := by
      intro h; apply hx; rw [hxa, h, Matrix.mulVec_zero]
    have hθx : (A * D * L.map star) *ᵥ x = A *ᵥ (D *ᵥ a) := by
      rw [ha_def, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    have key : ∀ b c : Fin r ⊕ Fin s → ℂ, (A *ᵥ b) ⬝ᵥ M *ᵥ (A.map star *ᵥ c) = b ⬝ᵥ (Aᵀ * M * A.map star) *ᵥ c := by
      intro b c
      rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
        ← Matrix.dotProduct_mulVec, Matrix.mul_assoc]
    have hval : ((A * D * L.map star) *ᵥ x) ⬝ᵥ M *ᵥ star x = a ⬝ᵥ star a := by
      rw [hθx]
      conv_lhs => rw [hxa, star_mulVec_map]
      rw [key, hA, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hDT, hDD, Matrix.vecMul_one]
    rw [hval]
    exact (Complex.pos_iff.mp (Matrix.dotProduct_self_star_pos_iff.mpr ha)).1

end GlobalTheory.CartanEx
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertLocFrame

theorem uAt_of_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F)) (n : ℕ) (X : Spc F E n) (L : Type) [Field L]
    (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) →
      ∀ (g : UA σ X.J) (A : Matrix (Fin n) (Fin n) L),
        mat g = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + A.map ι → g ∈ UAt σ X (evFin F v) := by
  intro F E _ _ _ _ _ σ v n X L _ ι hι g A hg u hu
  have hent : ∀ i j, (mat g - 1) i j = ι ((A - 1) i j) := by
    intro i j
    rw [hg]
    by_cases h : i = j
    · subst h
      simp [Matrix.one_apply, map_sub]
      abel
    · simp [Matrix.one_apply, h, map_sub]
  ext i j
  have h1 : At (evFin F v) ((mat g - 1) i j) := (hι _).2 ⟨_, (hent i j).symm⟩
  simpa using h1 u hu

end GlobalTheory.InertLocFrame
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertSph

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def latAt {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : AddSubgroup (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  AddSubgroup.closure {z | ∃ a : AF F, At (evFin F v) a ∧ evFin F v a ∈ v.adicCompletionIntegers F ∧
    ∃ y ∈ W.L, z = a • fun i => inclR (F := F) (AF F) (y i)}

def KAt (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : Set (UA σ W.J) :=
  {h | h ∈ UAt σ W (evFin F v) ∧ ∀ z ∈ latAt W v, mat h *ᵥ z ∈ latAt W v ∧ mat h⁻¹ *ᵥ z ∈ latAt W v}

theorem one_mem_KAt (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : (1 : UA σ W.J) ∈ KAt σ W v := by
  refine ⟨?_, fun z hz => ?_⟩
  · intro u _
    show u • (mat (1 : UA σ W.J) - 1) = 0
    simp [mat]
  · simp [mat, hz]

end GlobalTheory.InertSph
end
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ContMapReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem continuous_evInf (w : InfinitePlace F) : Continuous (evInf F w) := by
  show Continuous (fun a : AF F => a.1 w)
  exact (continuous_apply w).comp continuous_fst

def phiW (w : InfinitePlace F) : AF F →+* ℂ :=
  (InfinitePlace.Completion.extensionEmbedding w).comp (evInf F w).toRingHom

theorem continuous_phiW (w : InfinitePlace F) : Continuous (phiW (F := F) w) :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_evInf w)

theorem piInf_smul {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) (x : AE F E) :
    piInf τ (a • x) = phiW w a * piInf τ x := by
  rw [Algebra.smul_def, map_mul]
  congr 1
  simp [piInf, compInf, infEmb, phiW, Algebra.TensorProduct.algebraMap_apply]

theorem continuous_piInf {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (piInf (E := E) τ) := by
  letI : Module (AF F) ℂ := Module.compHom ℂ (phiW (F := F) w)
  haveI : ContinuousSMul (AF F) ℂ := ⟨by
    show Continuous (fun p : AF F × ℂ => phiW w p.1 * p.2)
    exact ((continuous_phiW w).comp continuous_fst).mul continuous_snd⟩
  let L : AE F E →ₗ[AF F] ℂ :=
    { toFun := piInf τ
      map_add' := map_add _
      map_smul' := fun a x => by rw [piInf_smul]; rfl }
  exact IsModuleTopology.continuous_of_linearMap L

theorem contmap {σ : E →ₐ[F] E} {β : Type} [Fintype β] [DecidableEq β] {J : Matrix β β (AE F E)}
    (γ : Multiplicative ℝ →* UG (cA σ) J) (hγ : Continuous γ) (w : InfinitePlace F) (τ : EmbOver E w) :
    Continuous (fun t : ℝ => ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf τ)) := by
  have h1 : Continuous (fun t : ℝ => ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E))) :=
    Units.continuous_val.comp (continuous_subtype_val.comp (hγ.comp continuous_ofAdd))
  exact h1.matrix_map (continuous_piInf τ)

end GlobalTheory.ContMapReal

end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.PolarSB

open MeasureTheory ComplexConjugate

variable {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ]

theorem integrable_mul_conj {f h : X → ℂ} (hf : f ∈ SB X) (hh : h ∈ SB X) :
    Integrable (fun x => f x * conj (h x)) μ := by
  have cf : Continuous f := hf.1.continuous
  have ch : Continuous h := hh.1.continuous
  exact (cf.mul (Complex.continuous_conj.comp ch)).integrable_of_hasCompactSupport
    (hf.2.mul_right)

theorem conj_mem {h : X → ℂ} (hh : h ∈ SB X) : (fun y => conj (h y)) ∈ SB X :=
  ⟨hh.1.comp _, hh.2.comp_left (map_zero _)⟩

theorem self_eq {g : X → ℂ} (hg : g ∈ SB X) :
    ENNReal.ofReal (∫ x, ‖g x‖ ^ 2 ∂μ) = ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ ∧
    (∫ x, g x * conj (g x) ∂μ) = ((∫ x, ‖g x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  have hi : Integrable (fun x => g x * conj (g x)) μ := integrable_mul_conj μ hg hg
  have hn : Integrable (fun x => ‖g x‖ ^ 2) μ := by
    have := hi.norm
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  constructor
  · rw [ofReal_integral_eq_lintegral_ofReal hn (Filter.Eventually.of_forall fun x => by positivity)]
    congr 1; funext x
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  · rw [← integral_complex_ofReal]
    congr 1; funext x
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem expand {f h : X → ℂ} (hf : f ∈ SB X) (hh : h ∈ SB X) (c : ℂ) :
    ∫ x, (c • h + f) x * conj ((c • h + f) x) ∂μ =
      c * conj c * ∫ x, h x * conj (h x) ∂μ + c * ∫ x, h x * conj (f x) ∂μ +
      conj c * ∫ x, f x * conj (h x) ∂μ + ∫ x, f x * conj (f x) ∂μ := by
  have e : (fun x => (c • h + f) x * conj ((c • h + f) x)) =
      fun x => (c * conj c) * (h x * conj (h x)) + c * (h x * conj (f x)) +
        conj c * (f x * conj (h x)) + f x * conj (f x) := by
    funext x; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul]; ring
  rw [e, integral_add, integral_add, integral_add, integral_const_mul, integral_const_mul,
    integral_const_mul]
  all_goals first
    | exact integrable_mul_conj μ hf hf
    | exact (integrable_mul_conj μ hh hh).const_mul _
    | exact (integrable_mul_conj μ hh hf).const_mul _
    | exact (integrable_mul_conj μ hf hh).const_mul _
    | exact ((integrable_mul_conj μ hh hh).const_mul _).add ((integrable_mul_conj μ hh hf).const_mul _)
    | exact (((integrable_mul_conj μ hh hh).const_mul _).add
        ((integrable_mul_conj μ hh hf).const_mul _)).add ((integrable_mul_conj μ hf hh).const_mul _)

end GlobalTheory.PolarSB


open MeasureTheory ComplexConjugate in
theorem GlobalTheory.PolarSB.pairing_eq : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl (F := F))
    (T : ((κ → Fv F v) → ℂ) → (κ → Fv F v) → ℂ),
    (∀ φ ∈ SB (κ → Fv F v), T φ ∈ SB (κ → Fv F v)) →
    (∀ φ ∈ SB (κ → Fv F v), ∀ φ' ∈ SB (κ → Fv F v), ∀ c : ℂ, T (c • φ + φ') = c • T φ + T φ') →
    ∀ μ : @MeasureTheory.Measure (κ → Fv F v) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    (∀ φ ∈ SB (κ → Fv F v), ∫⁻ y, ‖T φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ → Fv F v),
      ∫ x, T φ₁ x * starRingEnd ℂ (T (fun y => starRingEnd ℂ (φ₂ y)) x) ∂μ = ∫ x, φ₁ x * φ₂ x ∂μ := by
  open MeasureTheory ComplexConjugate in
  intro F _ _ κ _ v T hSB hlin μ hμ hnorm φ₁ h₁ φ₂ h₂
  letI : MeasurableSpace (κ → Fv F v) := borel _
  haveI : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  set w : (κ → Fv F v) → ℂ := fun y => starRingEnd ℂ (φ₂ y) with hw
  have hwSB : w ∈ SB (κ → Fv F v) := GlobalTheory.PolarSB.conj_mem h₂
  have hN : ∀ g ∈ SB (κ → Fv F v),
      ∫ x, T g x * conj (T g x) ∂μ = ∫ x, g x * conj (g x) ∂μ := by
    intro g hg
    obtain ⟨a1, a2⟩ := GlobalTheory.PolarSB.self_eq μ hg
    obtain ⟨b1, b2⟩ := GlobalTheory.PolarSB.self_eq μ (hSB g hg)
    rw [a2, b2]
    congr 1
    have := hnorm g hg
    rw [← a1, ← b1] at this
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun _ => by positivity)
      (integral_nonneg fun _ => by positivity)).1 this
  have key : ∀ c : ℂ,
      c * ∫ x, T w x * conj (T φ₁ x) ∂μ + conj c * ∫ x, T φ₁ x * conj (T w x) ∂μ =
      c * ∫ x, w x * conj (φ₁ x) ∂μ + conj c * ∫ x, φ₁ x * conj (w x) ∂μ := by
    intro c
    have hm : c • w + φ₁ ∈ SB (κ → Fv F v) := add_mem (Submodule.smul_mem _ c hwSB) h₁
    have e1 := hN _ hm
    rw [hlin w hwSB φ₁ h₁ c, GlobalTheory.PolarSB.expand μ h₁ hwSB c,
      GlobalTheory.PolarSB.expand μ (hSB _ h₁) (hSB _ hwSB) c, hN _ h₁, hN _ hwSB] at e1
    linear_combination e1
  have k1 := key 1
  have kI := key Complex.I
  simp only [map_one, one_mul, Complex.conj_I] at k1 kI
  have hfin : ∫ x, T φ₁ x * conj (T w x) ∂μ = ∫ x, φ₁ x * conj (w x) ∂μ := by
    linear_combination (k1 + Complex.I * kI) / 2 +
      (-(∫ x, T w x * conj (T φ₁ x) ∂μ) + ∫ x, T φ₁ x * conj (T w x) ∂μ
        + ∫ x, w x * conj (φ₁ x) ∂μ - ∫ x, φ₁ x * conj (w x) ∂μ) / 2 * Complex.I_sq
  rw [hfin]
  simp [hw]
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory

theorem sesquilinearFormOfGram_eq_conj_swap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ e, σ (σ e) = e) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (x w : Fin n → E),
    (∀ i j, σ (J j i) = J i j) → form σ J x w = σ (form σ J w x) := by
  intro F E _ _ _ _ _ σ hσ n J x w hJ

  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem not_fg_top_ringOfIntegers (E : Type) [Field E] [NumberField E] :
    ¬ (⊤ : Submodule (𝓞 E) E).FG := by
  intro h
  haveI : Module.Finite (𝓞 E) E := ⟨h⟩
  haveI : Module.Finite ℤ E := Module.Finite.trans (𝓞 E) E
  have hi : IsIntegral ℤ (algebraMap ℚ E (2⁻¹ : ℚ)) := Algebra.IsIntegral.isIntegral _
  rw [isIntegral_algebraMap_iff ] at hi
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  have h2 : ((2 * y : ℤ) : ℚ) = 1 := by
    push_cast
    rw [show (algebraMap ℤ ℚ y) = (y : ℚ) from rfl] at hy
    rw [hy]; norm_num
  have : 2 * y = 1 := by exact_mod_cast h2
  omega

theorem selfDual_pair_nondeg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ e, σ (σ e) = e) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), L.FG →
    (∀ i j, σ (J j i) = J i j) → (∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (form σ J y x)) →
    ∀ x : Fin n → E, x ≠ 0 → ∃ z ∈ L, form σ J z x ≠ 0 := by
  intro F E _ _ _ _ _ σ hσ n J L hL hJ hdual x hx
  by_contra hcon
  push_neg at hcon
  have hxw : ∀ w ∈ L, form σ J x w = 0 := fun w hw => by
    rw [sesquilinearFormOfGram_eq_conj_swap F E σ hσ n J x w hJ, hcon w hw, map_zero]
  have hmem : ∀ c : E, c • x ∈ L := fun c => by
    rw [hdual]
    intro w hw
    have : form σ J (c • x) w = c * form σ J x w := by
      simp [form, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    rw [this, hxw w hw, mul_zero]
    exact isIntegral_zero
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h; push_neg at h; exact hx (funext h)
  let f : (Fin n → E) →ₗ[𝓞 E] E := (LinearMap.proj i : (Fin n → E) →ₗ[E] E).restrictScalars (𝓞 E)
  have htop : L.map f = ⊤ := by
    rw [eq_top_iff]
    intro e _
    refine ⟨(e / x i) • x, hmem _, ?_⟩
    simp [f, div_mul_cancel₀ _ hi]
  exact not_fg_top_ringOfIntegers E (htop ▸ hL.map f)

end GlobalTheory
end
