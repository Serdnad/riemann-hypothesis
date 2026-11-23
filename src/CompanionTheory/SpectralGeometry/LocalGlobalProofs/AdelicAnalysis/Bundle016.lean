module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.LocInf

def posU (ι : Type) : Subgroup (ι → ℝ)ˣ where
  carrier := {u | ∀ i, 0 < (u : ι → ℝ) i}
  mul_mem' := fun {a b} ha hb i => by
    simpa using mul_pos (ha i) (hb i)
  one_mem' := fun i => by simp
  inv_mem' := by
    intro u hu i
    have h1 : ((u⁻¹ : (ι → ℝ)ˣ) : ι → ℝ) i * (u : ι → ℝ) i = 1 := by
      have := congrFun (u.inv_mul) i
      simpa using this
    exact (pos_iff_pos_of_mul_pos (h1 ▸ one_pos)).2 (hu i)

theorem isOpen_pos (ι : Type) [Finite ι] : IsOpen {x : ι → ℝ | ∀ i, 0 < x i} := by
  have h1 : {x : ι → ℝ | ∀ i, 0 < x i} = ⋂ i, {x : ι → ℝ | 0 < x i} := by
    ext x
    simp
  rw [h1]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)

theorem isOpen_posU (ι : Type) [Fintype ι] : IsOpen (posU ι : Set (ι → ℝ)ˣ) :=
  (isOpen_pos ι).preimage Units.continuous_val

theorem isOpenEmbedding_sq (ι : Type) [Fintype ι] :
    IsOpenEmbedding (fun u : posU ι => ((u : (ι → ℝ)ˣ) ^ 2 : (ι → ℝ)ˣ)) := by
  have hv : IsOpenEmbedding (Units.val : (ι → ℝ)ˣ → (ι → ℝ)) := Units.isOpenEmbedding_val
  refine (IsOpenEmbedding.of_comp_iff _ hv).1 ?_
  set j : posU ι → (ι → ℝ) := fun u => ((u : (ι → ℝ)ˣ) : ι → ℝ) with hjdef
  have hj : IsOpenEmbedding j := hv.comp (isOpen_posU ι).isOpenEmbedding_subtypeVal
  set g : posU ι → (ι → ℝ) := Units.val ∘ (fun u : posU ι => ((u : (ι → ℝ)ˣ) ^ 2 : (ι → ℝ)ˣ)) with hgdef
  have hg : Continuous g :=
    Units.continuous_val.comp (continuous_subtype_val.pow 2)
  let r : (ι → ℝ) → (ι → ℝ) := fun x i => Real.sqrt (x i)
  have hr : Continuous r := continuous_pi fun i => (continuous_apply i).sqrt
  have hrg : r ∘ g = j := by
    funext u i
    have hu : 0 < ((u : (ι → ℝ)ˣ) : ι → ℝ) i := u.2 i
    simp [r, g, j, Real.sqrt_sq hu.le]
  have hind : IsInducing g := IsInducing.of_comp hg hr (by rw [hrg]; exact hj.isInducing)
  have hinj : Function.Injective g := Function.Injective.of_comp (f := r) (by rw [hrg]; exact hj.injective)
  have hrange : Set.range g = {x : ι → ℝ | ∀ i, 0 < x i} := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩ i
      have hu : 0 < ((u : (ι → ℝ)ˣ) : ι → ℝ) i := u.2 i
      simpa [g] using pow_pos hu 2
    · intro hx
      have hs : ∀ i, 0 < Real.sqrt (x i) := fun i => Real.sqrt_pos.2 (hx i)
      let w : (ι → ℝ)ˣ :=
        ⟨fun i => Real.sqrt (x i), fun i => (Real.sqrt (x i))⁻¹,
          by funext i; simp [(hs i).ne'], by funext i; simp [(hs i).ne']⟩
      refine ⟨⟨w, fun i => hs i⟩, ?_⟩
      funext i
      simp [g, w, Real.sq_sqrt (hx i).le]
  exact ⟨⟨hind, hinj⟩, by rw [hrange]; exact isOpen_pos ι⟩

variable (F : Type) [Field F] [NumberField F]

def eInf (h : IsTotallyReal F) : Ainf F ≃+* (InfinitePlace F → ℝ) :=
  RingEquiv.piCongrRight fun w => InfinitePlace.Completion.ringEquivRealOfIsReal (h.isReal w)

omit [NumberField F] in
theorem continuous_eInf (h : IsTotallyReal F) : Continuous (eInf F h) := by
  show Continuous (fun (x : ∀ w : InfinitePlace F, w.Completion) (w : InfinitePlace F) =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (h.isReal w) (x w))
  exact continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (h.isReal w)).continuous.comp (continuous_apply w)

omit [NumberField F] in
theorem continuous_eInf_symm (h : IsTotallyReal F) : Continuous (eInf F h).symm := by
  show Continuous (fun (x : InfinitePlace F → ℝ) (w : InfinitePlace F) =>
    (InfinitePlace.Completion.ringEquivRealOfIsReal (h.isReal w)).symm (x w))
  exact continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (h.isReal w)).symm.continuous.comp (continuous_apply w)

def hInf (h : IsTotallyReal F) : Ainf F ≃ₜ (InfinitePlace F → ℝ) where
  toEquiv := (eInf F h).toEquiv
  continuous_toFun := continuous_eInf F h
  continuous_invFun := continuous_eInf_symm F h

def uInf (h : IsTotallyReal F) : (Ainf F)ˣ ≃ₜ (InfinitePlace F → ℝ)ˣ where
  toEquiv := (Units.mapEquiv (eInf F h).toMulEquiv).toEquiv
  continuous_toFun := Continuous.units_map _ (continuous_eInf F h)
  continuous_invFun := Continuous.units_map _ (continuous_eInf_symm F h)

end GlobalTheory.CompanionTheory.SW.LocInf


open GlobalTheory.CompanionTheory.SW.LocInf in
theorem GlobalTheory.CompanionTheory.SW.isLocR_Ainf : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → IsLocR (Ainf F) := by
  intro F _ _ h
  have hT2 : T2Space (Ainf F) := inferInstanceAs (T2Space (∀ w : InfinitePlace F, w.Completion))
  have hSC : SecondCountableTopology (Ainf F) := (hInf F h).secondCountableTopology
  have hArt : IsArtinianRing (Ainf F) := inferInstanceAs (IsArtinianRing (∀ w : InfinitePlace F, w.Completion))
  have hRed : IsReduced (Ainf F) := inferInstanceAs (IsReduced (∀ w : InfinitePlace F, w.Completion))
  have hval : IsOpenEmbedding (Units.val : (Ainf F)ˣ → Ainf F) := by
    have h1 : IsOpenEmbedding (Units.val : (InfinitePlace F → ℝ)ˣ → (InfinitePlace F → ℝ)) :=
      Units.isOpenEmbedding_val
    have h2 := ((hInf F h).symm.isOpenEmbedding.comp h1).comp (uInf F h).isOpenEmbedding
    convert h2 using 1
    funext u
    exact ((eInf F h).symm_apply_apply _).symm
  refine ⟨inferInstance, inferInstance, hSC, hT2, hArt, hRed, hval,
    (posU (InfinitePlace F)).comap (Units.map (eInf F h).toMonoidHom), ?_, ?_⟩
  · exact (isOpen_posU (InfinitePlace F)).preimage (uInf F h).continuous
  · let S := (posU (InfinitePlace F)).comap (Units.map (eInf F h).toMonoidHom)
    let T : S ≃ₜ posU (InfinitePlace F) :=
      (uInf F h).subtype (fun x => Iff.rfl)
    have h2 := ((uInf F h).symm.isOpenEmbedding.comp (isOpenEmbedding_sq (InfinitePlace F))).comp
      T.isOpenEmbedding
    convert h2 using 1
    funext u
    apply (uInf F h).injective
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
    exact map_pow (Units.map (eInf F h).toMonoidHom) (u : (Ainf F)ˣ) 2
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.HermOne

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem exists_ne (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra hc
  push_neg at hc
  obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace E))
  have hreal : w.IsReal := by
    rw [← NumberField.InfinitePlace.mk_embedding w, NumberField.InfinitePlace.isReal_mk_iff,
      NumberField.ComplexEmbedding.isReal_iff]
    refine RingHom.ext fun x ↦ ?_
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    change star (w.embedding x) = w.embedding x
    rw [← h.2.2.2, hc]
  exact NumberField.InfinitePlace.not_isReal_iff_isComplex.2 (h.2.1.isComplex w) hreal

theorem exists_eq_algebraMap (h : IsCMExt F E σ) {x : E} (hx : σ x = x) :
    ∃ β : F, x = algebraMap F E β := by
  by_contra hc
  push_neg at hc
  have hli : LinearIndependent F ![(1 : E), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    have ht : t = 0 := by
      by_contra ht
      have htE : algebraMap F E t ≠ 0 := (map_ne_zero _).2 ht
      apply hc (-(s / t))
      rw [map_neg, map_div₀]
      field_simp
      linear_combination hst
    refine ⟨?_, ht⟩
    rw [ht, map_zero, zero_mul, add_zero] at hst
    exact (map_eq_zero_iff _ (algebraMap F E).injective).1 hst
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by
    rw [Fintype.card_fin, h.2.2.1]
  obtain ⟨y, hy⟩ := exists_ne h
  have hid : σ.toLinearMap = LinearMap.id := by
    refine (basisOfLinearIndependentOfCardEqFinrank hli hcard).ext fun i ↦ ?_
    fin_cases i <;> simp [hx]
  exact hy (by simpa using LinearMap.congr_fun hid y)

end GlobalTheory.CompanionTheory.SW.HermOne

namespace GlobalTheory.CompanionTheory.SW

theorem hermOne_eq_scal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (T : Matrix (Fin 1) (Fin 1) E) (hT : ∀ a b, σ (T b a) = T a b), ∃ β : F, T = (fun _ _ => algebraMap F E β) ∧ (T.det ≠ 0 → β ≠ 0) ∧ ∀ (R : Type) [CommRing R] [Algebra F R], hermOf R σ T hT = hermScal R σ (algebraMap F R β) := by
  intro F E _ _ _ _ _ σ h T hT
  obtain ⟨β, hβ⟩ := HermOne.exists_eq_algebraMap h (hT 0 0)
  have hTβ : T = fun _ _ => algebraMap F E β := by
    funext a b
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
    exact hβ
  refine ⟨β, hTβ, fun hd hb => hd ?_, fun R _ _ => ?_⟩
  · rw [Matrix.det_fin_one, hβ, hb, map_zero]
  · apply Subtype.ext
    funext a b
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
    change inclR R (T 0 0) = (algebraMap F R β) ⊗ₜ[F] (1 : E)
    rw [hβ, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    simp [inclR, TensorProduct.smul_tmul]

end GlobalTheory.CompanionTheory.SW
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.CoordMat

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem trace_one_tmul [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] (e : E) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = algebraMap F R (Algebra.trace F E e) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

def traceGram (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E) :
    Matrix (Fin M × Fin d) (Fin M × Fin d) F :=
  fun p q => Algebra.trace F E (σ (b p.2) * J p.1 q.1 * b q.2)

def coordL (R : Type) [CommRing R] [Algebra F R] (M : ℕ) {d : ℕ} (b : Module.Basis (Fin d) F E) :
    (Fin M → R ⊗[F] E) ≃ₗ[R] (Fin M × Fin d → R) :=
  (LinearEquiv.piCongrRight fun _ => (Algebra.TensorProduct.basis R b).equivFun).trans
    (LinearEquiv.curry R R (Fin M) (Fin d)).symm

theorem coordL_apply (R : Type) [CommRing R] [Algebra F R] (M : ℕ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (x : Fin M → R ⊗[F] E) (p : Fin M × Fin d) :
    coordL R M b x p = (Algebra.TensorProduct.basis R b).repr (x p.1) p.2 := rfl

theorem trace_expand [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {d : ℕ}
    (b : Module.Basis (Fin d) F E) (u v : R ⊗[F] E) (e : E) :
    Algebra.trace R (R ⊗[F] E) (sigR R σ u * inclR R e * v) =
      ∑ k, ∑ l, (Algebra.TensorProduct.basis R b).repr u k *
        (algebraMap F R (Algebra.trace F E (σ (b k) * e * b l)) *
          (Algebra.TensorProduct.basis R b).repr v l) := by
  have hx : ∀ z : R ⊗[F] E, z = ∑ k, (Algebra.TensorProduct.basis R b).repr z k • ((1 : R) ⊗ₜ[F] b k) := by
    intro z
    conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr z]
    simp only [Algebra.TensorProduct.basis_apply]
  have hs : ∀ (r : R) (w : R ⊗[F] E), sigR R σ (r • w) = r • sigR R σ w := by
    intro r w
    exact map_smul (Algebra.TensorProduct.map (AlgHom.id R R) (σ : E →ₐ[F] E)) r w
  generalize hcu : (Algebra.TensorProduct.basis R b).repr u = cu
  generalize hcv : (Algebra.TensorProduct.basis R b).repr v = cv
  have hu : u = ∑ k, cu k • ((1 : R) ⊗ₜ[F] b k) := by rw [← hcu]; exact hx u
  have hv : v = ∑ k, cv k • ((1 : R) ⊗ₜ[F] b k) := by rw [← hcv]; exact hx v

  rw [hu, hv, map_sum, Finset.sum_mul, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_

  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h1 : sigR R σ ((1 : R) ⊗ₜ[F] b k) = (1 : R) ⊗ₜ[F] σ (b k) := by simp [sigR]
  have h2 : inclR R e = (1 : R) ⊗ₜ[F] e := rfl
  rw [hs, h1, h2, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, map_smul, map_smul,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul,
    trace_one_tmul, smul_eq_mul, smul_eq_mul]
  ring

theorem trace_hR [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M d : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E) (x y : Fin M → R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) (hR R σ J x y) =
      coordL R M b x ⬝ᵥ (traceGram σ J b).map (algebraMap F R) *ᵥ coordL R M b y := by

  simp only [hR, hform, map_sum, JR, Matrix.map_apply, trace_expand R σ b]
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, coordL_apply, traceGram, Matrix.map_apply,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

theorem hform_mulVec {A : Type} [CommRing A] (s : A →+* A) {M : ℕ} (J g : Matrix (Fin M) (Fin M) A)
    (x y : Fin M → A) :
    hform s J (g *ᵥ x) (g *ᵥ y) = hform s (cT s g * J * g) x y := by
  have h : ∀ (K : Matrix (Fin M) (Fin M) A) (u v : Fin M → A), hform s K u v = (s ∘ u) ⬝ᵥ (K *ᵥ v) := by
    intro K u v
    simp [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hc : s ∘ (g *ᵥ x) = (g.map s) *ᵥ (s ∘ x) := by
    funext i
    exact RingHom.map_mulVec s g x i
  rw [h, h, hc, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]
  simp only [cT, Matrix.mul_assoc]

theorem matrix_ext_dot {ι A : Type} [Fintype ι] [DecidableEq ι] [CommRing A] (P Q : Matrix ι ι A)
    (h : ∀ u v : ι → A, u ⬝ᵥ P *ᵥ v = u ⬝ᵥ Q *ᵥ v) : P = Q := by
  ext p q
  simpa using h (Pi.single p 1) (Pi.single q 1)

theorem dot_conj {ι A : Type} [Fintype ι] [CommRing A] (g P : Matrix ι ι A) (u v : ι → A) :
    u ⬝ᵥ (gᵀ * P * g) *ᵥ v = (g *ᵥ u) ⬝ᵥ P *ᵥ (g *ᵥ v) := by
  rw [← Matrix.vecMul_transpose g u, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem traceGram_isSymm [FiniteDimensional F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M d : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j) (b : Module.Basis (Fin d) F E) :
    (traceGram σ J b).IsSymm := by
  let e : E ≃ₐ[F] E := AlgEquiv.ofBijective σ
    ⟨σ.toRingHom.injective, fun x => ⟨σ x, hσ x⟩⟩
  refine Matrix.IsSymm.ext fun p q => ?_
  simp only [traceGram]
  have hm : e (σ (b q.2) * J q.1 p.1 * b p.2) = σ (b p.2) * J p.1 q.1 * b q.2 := by
    change σ (σ (b q.2) * J q.1 p.1 * b p.2) = _
    rw [map_mul, map_mul, hσ, hJ]
    ring
  exact (Algebra.trace_eq_of_algEquiv e _).symm.trans (congrArg _ hm)

theorem traceGram_det_ne_zero [FiniteDimensional F E] [Algebra.IsSeparable F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0)
    (b : Module.Basis (Fin d) F E) : (traceGram σ J b).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hBv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  apply hv
  let y : Fin M → E := fun j => ∑ l, v (j, l) • b l
  have h1 : ∀ i k, Algebra.trace F E (σ (b k) * (J *ᵥ y) i) = 0 := by
    intro i k
    have h := congrFun hBv (i, k)
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, traceGram, Pi.zero_apply] at h
    rw [← h]

    simp only [Matrix.mulVec, dotProduct, y, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mul_smul_comm, mul_smul_comm, map_smul, smul_eq_mul, mul_comm, mul_assoc]
  have h2 : ∀ i z, Algebra.trace F E (z * (J *ᵥ y) i) = 0 := by
    intro i z
    have hz : z = ∑ k, b.repr (σ z) k • σ (b k) := by
      have h := congrArg σ (b.sum_repr (σ z))

      rw [hσ, map_sum] at h
      exact h.symm.trans (Finset.sum_congr rfl fun k _ => map_smul σ _ _)

    rw [hz, Finset.sum_mul, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [smul_mul_assoc, map_smul, h1, smul_zero]
  have h3 : J *ᵥ y = 0 := by
    funext i
    refine (traceForm_nondegenerate F E).1 _ fun z => ?_
    rw [Algebra.traceForm_apply, mul_comm]
    exact h2 i z
  have h4 := Matrix.eq_zero_of_mulVec_eq_zero hJ h3
  funext p
  exact Fintype.linearIndependent_iff.mp b.linearIndependent (fun l => v (p.1, l)) (congrFun h4 p.1) p.2

theorem hR_mat (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J) (x y : Fin M → R ⊗[F] E) :
    hR R σ J ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x)
      ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ y) = hR R σ J x y := by
  have hm : cT (sigR R σ) (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
      (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J := (show HR R σ J from h).2
  rw [hR, hform_mulVec, hm, hR]

end Alg

theorem coord_orthogonal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ B : Matrix (Fin M × Fin d) (Fin M × Fin d) F, B.IsSymm ∧ B.det ≠ 0 ∧ ∀ (R : Type) [CommRing R] [Algebra F R] (h : HA R σ J), ∃ g : Matrix (Fin M × Fin d) (Fin M × Fin d) R, gᵀ * B.map (algebraMap F R) * g = B.map (algebraMap F R) ∧ ∀ X : Fin 1 → Fin M → R ⊗[F] E, (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (actW R σ J h X 0 p.1) p.2) = g *ᵥ fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (X 0 p.1) p.2 := by
  intro F E _ _ _ _ _ σ hCM M J hJ d b
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have hσ : ∀ x, σ (σ x) = x := by
    intro x
    let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom
    apply τ.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  refine ⟨traceGram σ J b, traceGram_isSymm σ hσ J hJ.1 b, traceGram_det_ne_zero σ hσ J hJ.2 b,
    fun R _ _ h => ?_⟩
  let c := coordL (F := F) (E := E) R M b
  let T : (Fin M → R ⊗[F] E) →ₗ[R] (Fin M → R ⊗[F] E) :=
    (Matrix.mulVecLin (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E))).restrictScalars R
  let g : Matrix (Fin M × Fin d) (Fin M × Fin d) R :=
    LinearMap.toMatrix' (c.toLinearMap ∘ₗ T ∘ₗ c.symm.toLinearMap)
  have hg : ∀ x, g *ᵥ c x = c ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x) := by
    intro x
    simp [g, T, LinearMap.toMatrix'_mulVec]
  refine ⟨g, ?_, fun X => (hg (X 0)).symm⟩
  refine matrix_ext_dot _ _ fun u v => ?_
  obtain ⟨x, rfl⟩ := c.surjective u
  obtain ⟨y, rfl⟩ := c.surjective v
  rw [dot_conj, hg, hg]
  have hx := trace_hR R σ J b x y
  have hy := trace_hR R σ J b ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x)
    ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ y)
  rw [hR_mat] at hy
  exact hy.symm.trans hx

end GlobalTheory.CompanionTheory.SW.CoordMat
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem exists_sqrt_near_unit : ∀ (R : Type) [CommRing R] [TopologicalSpace R], IsLocR R → ∀ x : Rˣ,
    ∃ (B₀ : Set R) (a : R → Rˣ), IsOpen B₀ ∧ (x : R) ∈ B₀ ∧ ContinuousOn a B₀ ∧
      (∀ y, y ∉ B₀ → a y = 1) ∧ (∀ y ∈ B₀, y = ((a y : Rˣ) : R) ^ 2 * (x : R)) ∧ a (x : R) = 1 := by
  classical
  intro R _ _ hR x
  obtain ⟨htr, -, -, -, -, -, hval, U, -, hq⟩ := hR

  let h : R ≃ₜ R :=
    { toFun := fun y => y * (x : R)
      invFun := fun y => y * ((x⁻¹ : Rˣ) : R)
      left_inv := fun y => by simp [mul_assoc]
      right_inv := fun y => by simp [mul_assoc]
      continuous_toFun := continuous_id.mul continuous_const
      continuous_invFun := continuous_id.mul continuous_const }
  let f : U → R := fun u => (((u : Rˣ) ^ 2 : Rˣ) : R) * (x : R)
  have hf : IsOpenEmbedding f :=
    h.isOpenEmbedding.comp (hval.comp hq)
  have hf1 : f 1 = (x : R) := by simp [f]
  let a : R → Rˣ := fun y => if y ∈ Set.range f then ((Function.invFun f y : U) : Rˣ) else 1
  have haf : ∀ u : U, a (f u) = (u : Rˣ) := by
    intro u
    have : Function.invFun f (f u) = u := Function.leftInverse_invFun hf.injective u
    simp only [a, Set.mem_range_self, if_true, this]
  refine ⟨Set.range f, a, hf.isOpen_range, ⟨1, hf1⟩, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨u, rfl⟩
    apply ContinuousAt.continuousWithinAt
    rw [← hf.continuousAt_iff]
    have : a ∘ f = fun u : U => (u : Rˣ) := funext haf
    rw [this]
    exact continuous_subtype_val.continuousAt
  · intro y hy
    simp only [a, if_neg hy]
  · rintro _ ⟨u, rfl⟩
    rw [haf]
    simp [f]
  · have := haf 1
    rw [hf1] at this
    simpa using this

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end
end
