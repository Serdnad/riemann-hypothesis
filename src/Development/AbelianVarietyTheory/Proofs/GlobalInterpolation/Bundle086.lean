module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle011
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle079
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
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
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelChainSharpColumnValuationOwnChainIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle070
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation
open nonZeroDivisors
noncomputable section
namespace GlobalTheory.CharVal.Vp
variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem conjP_conjP' (P : HeightOneSpectrum (𝓞 E)) : conjPrime₂ (conjPrime₂ P) = P := by
  ext x
  rw [mem_conjP, mem_conjP, cO_cO]

omit [StarRing E] in
theorem ne0 (P : HeightOneSpectrum (𝓞 E)) : (P.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero.2 P.ne_bot

omit [StarRing E] in
theorem maxV_self (P : HeightOneSpectrum (𝓞 E)) :
    MaxV P ((P.asIdeal : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) (WithZero.exp (-1 : ℤ)) := by
  constructor
  · intro a ha
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    have := (P.intValuation_le_pow_iff_mem r 1).2 (by simpa using hr)
    simpa using this
  · obtain ⟨r, hr⟩ := P.intValuation_exists_uniformizer
    refine ⟨algebraMap _ _ r, (FractionalIdeal.mem_coeIdeal _).2 ⟨r, ?_, rfl⟩, ?_⟩
    · have := (P.intValuation_le_pow_iff_mem r 1).1 (by simpa using hr.le)
      simpa using this
    · rw [HeightOneSpectrum.valuation_of_algebraMap, hr]

omit [StarRing E] in
theorem maxV_ne (Q P : HeightOneSpectrum (𝓞 E)) (h : Q ≠ P) :
    MaxV Q ((P.asIdeal : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) 1 := by
  constructor
  · intro a ha
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
    exact Q.valuation_le_one r
  · have : ¬ P.asIdeal ≤ Q.asIdeal := fun hle =>
      h (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top hle).symm)
    obtain ⟨r, hr, hr'⟩ := SetLike.not_le_iff_exists.1 this
    exact ⟨algebraMap _ _ r, (FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩,
      (HeightOneSpectrum.valuation_eq_one_iff_notMem Q).2 hr'⟩

omit [StarRing E] in
theorem maxV_inv {Q P : HeightOneSpectrum (𝓞 E)} {γ : WithZero (Multiplicative ℤ)} (h0 : γ ≠ 0)
    (h : MaxV Q ((P.asIdeal : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) γ) :
    MaxV Q (((P.asIdeal : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) γ⁻¹ :=
  h.inv h0 (by rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ (ne0 P), FractionalIdeal.coe_one])

theorem mem_vp (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    x ∈ vpIdeal P ↔ ∀ r ∈ (conjPrime₂ P).asIdeal, ∃ s ∈ P.asIdeal, algebraMap _ E s = x * algebraMap _ E r := by
  unfold vpIdeal
  rw [← div_eq_mul_inv, FractionalIdeal.mem_coe, FractionalIdeal.mem_div_iff_of_ne_zero (ne0 _)]
  constructor
  · intro h r hr
    exact (FractionalIdeal.mem_coeIdeal _).1 (h _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩))
  · intro h y hy
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact (FractionalIdeal.mem_coeIdeal _).2 (h r hr)

theorem star_mem_vp (P : HeightOneSpectrum (𝓞 E)) (x : E) (h : x ∈ vpIdeal P) : star x ∈ vpIdeal (conjPrime₂ P) := by
  rw [mem_vp] at h ⊢
  intro r hr
  rw [conjP_conjP'] at hr
  obtain ⟨s, hs, e⟩ := h (cO E r) (by rwa [mem_conjP, cO_cO])
  refine ⟨cO E s, by rwa [mem_conjP, cO_cO], ?_⟩
  have e1 : algebraMap _ E (cO E s) = star (algebraMap _ E s) := rfl
  have e2 : algebraMap _ E (cO E r) = star (algebraMap _ E r) := rfl
  rw [e1, e, e2, star_mul, star_star, mul_comm]

theorem detLat_vp (P : HeightOneSpectrum (𝓞 E)) : detLat (vpLat P) = vpIdeal P := by
  unfold detLat
  rw [← Submodule.span_eq (vpIdeal P)]
  congr 1
  ext x
  constructor
  · rintro ⟨A, hA, rfl⟩
    have := hA _ (single_mem_stdLat (E := E) (0 : Fin 1) 1)
    rw [Matrix.det_fin_one]
    simpa [vpLat, Matrix.mulVec_single] using this
  · intro hx
    refine ⟨Matrix.of fun _ _ => x, fun v hv => ?_, by simp⟩
    obtain ⟨r, hr⟩ := (mem_stdLat v).1 hv 0
    have : (Matrix.of fun _ _ => x : Matrix (Fin 1) (Fin 1) E).mulVec v 0 = r • x := by
      simp [Matrix.mulVec, dotProduct, ← hr, Algebra.smul_def, mul_comm]
    show (Matrix.of fun _ _ => x : Matrix (Fin 1) (Fin 1) E).mulVec v 0 ∈ vpIdeal P
    rw [this]
    exact (vpIdeal P).smul_mem r hx

theorem vp_main : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)), P ≠ conjPrime₂ P → (∃ J : Submodule (𝓞 E) E, (∀ x, x ∈ J ↔ star x ∈ vpIdeal P) ∧ vpIdeal P * J = 1) ∧ MaxV P (vpIdeal P) (WithZero.exp (-1 : ℤ)) ∧ MaxV (conjPrime₂ P) (vpIdeal P) (WithZero.exp (1 : ℤ)) ∧ (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q ≠ conjPrime₂ P → MaxV Q (vpIdeal P) 1) ∧ detLat (vpLat P) = vpIdeal P := by
  intro E _ _ _ P hP
  refine ⟨⟨vpIdeal (conjPrime₂ P), fun x => ⟨fun h => ?_, fun h => ?_⟩, ?_⟩, ?_, ?_, fun Q h1 h2 => ?_, detLat_vp P⟩
  · have := star_mem_vp _ _ h
    rwa [conjP_conjP'] at this
  · simpa using star_mem_vp _ _ h
  · unfold vpIdeal
    rw [conjP_conjP', ← FractionalIdeal.coe_mul, mul_assoc, inv_mul_cancel_left₀ (ne0 _), mul_inv_cancel₀ (ne0 _),
      FractionalIdeal.coe_one]
  · have := (maxV_self P).mul (maxV_inv one_ne_zero (maxV_ne P _ hP))
    rw [inv_one, mul_one, ← FractionalIdeal.coe_mul] at this
    exact this
  · have := (maxV_ne _ P hP.symm).mul (maxV_inv WithZero.exp_ne_zero (maxV_self (conjPrime₂ P)))
    rw [one_mul, ← WithZero.exp_neg, neg_neg, ← FractionalIdeal.coe_mul] at this
    exact this
  · have := (maxV_ne Q P h1).mul (maxV_inv one_ne_zero (maxV_ne Q _ h2))
    rw [inv_one, mul_one, ← FractionalIdeal.coe_mul] at this
    exact this

end GlobalTheory.CharVal.Vp
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation

noncomputable section

namespace GlobalTheory.IdealTransport

section General

variable {R R' M M' : Type} [CommRing R] [CommRing R'] [AddCommGroup M] [AddCommGroup M'] [Module R M] [Module R' M']
  (φ : R ≃+* R') (f : M ≃+ M') (h : ∀ r m, f (r • m) = φ r • f m)

include h

theorem span_image_le_of (N : Submodule R M) (N' : Submodule R' M') (S : Set M) (hS : N = Submodule.span R S)
    (hN : ∀ m ∈ S, f m ∈ N') : Submodule.span R' (f '' (N : Set M)) ≤ N' := by
  rw [Submodule.span_le]
  rintro _ ⟨m, hm, rfl⟩
  show f m ∈ N'
  have hm' : m ∈ Submodule.span R S := hS ▸ hm
  clear hm
  induction hm' using Submodule.span_induction with
  | mem x hx => exact hN x hx
  | zero => rw [map_zero]; exact N'.zero_mem
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact N'.add_mem hx hy
  | smul r x _ hx => rw [h]; exact N'.smul_mem _ hx

theorem span_image_span (S : Set M) :
    Submodule.span R' (f '' (Submodule.span R S : Set M)) = Submodule.span R' (f '' S) := by
  apply le_antisymm
  · exact span_image_le_of φ f h _ _ S rfl fun m hm => Submodule.subset_span ⟨m, hm, rfl⟩
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem mem_span_image (N : Submodule R M) (x : M') :
    x ∈ Submodule.span R' (f '' (N : Set M)) ↔ f.symm x ∈ N := by
  have hsm : ∀ (r : R') (y : M'), f.symm (r • y) = φ.symm r • f.symm y := by
    intro r y
    apply f.injective
    rw [h, AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, hm, rfl⟩ := hy
      simpa using hm
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact N.add_mem hy hz
    | smul r y _ hy => rw [hsm]; exact N.smul_mem _ hy
  · intro hx
    exact Submodule.subset_span ⟨f.symm x, hx, by simp⟩

end General

section Fields

variable {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] (e : E ≃+* E')

theorem map_smul_int (r : 𝓞 E) (x : E) : e (r • x) = RingOfIntegers.mapRingEquiv e r • e x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  rfl

abbrev trI (I : Submodule (𝓞 E) E) : Submodule (𝓞 E') E' := Submodule.span (𝓞 E') (e '' (I : Set E))

abbrev trL {n : ℕ} (N : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E') (Fin n → E') :=
  Submodule.span (𝓞 E') ((fun (x : Fin n → E) (i : Fin n) => e (x i)) '' (N : Set (Fin n → E)))

theorem mem_trI (I : Submodule (𝓞 E) E) (x : E') : x ∈ trI e I ↔ e.symm x ∈ I := mem_span_image (RingOfIntegers.mapRingEquiv e) e.toAddEquiv (map_smul_int e) I x

theorem trI_span (S : Set E) : trI e (Submodule.span (𝓞 E) S) = Submodule.span (𝓞 E') (e '' S) := span_image_span (RingOfIntegers.mapRingEquiv e) e.toAddEquiv (map_smul_int e) S

theorem mem_trL {n : ℕ} (N : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E') :
    x ∈ trL e N ↔ (fun i => e.symm (x i)) ∈ N := mem_span_image (RingOfIntegers.mapRingEquiv e) (AddEquiv.piCongrRight fun _ : Fin n => e.toAddEquiv)
    (fun r v => funext fun i => map_smul_int e r (v i)) N x

theorem trI_mul (I J : Submodule (𝓞 E) E) : trI e (I * J) = trI e I * trI e J := by
  rw [Submodule.mul_eq_span_mul_set I J, trI_span, Set.image_mul]
  exact (Submodule.span_mul_span _ _ _).symm

theorem trI_singleton (y : E) : trI e (Submodule.span (𝓞 E) {y}) = Submodule.span (𝓞 E') {e y} := by
  rw [trI_span, Set.image_singleton]

theorem trI_one : trI e 1 = 1 := by
  conv_lhs => rw [Submodule.one_eq_span]
  rw [trI_singleton, map_one, ← Submodule.one_eq_span]

theorem trI_surj (J : Submodule (𝓞 E') E') : ∃ I, trI e I = J := by
  refine ⟨Submodule.span (𝓞 E) (e.symm '' (J : Set E')), ?_⟩
  rw [trI_span, Set.image_image]
  simp only [RingEquiv.apply_symm_apply, Set.image_id']
  exact Submodule.span_eq J

theorem mem_one_iff (x : E') : x ∈ (1 : Submodule (𝓞 E') E') ↔ e.symm x ∈ (1 : Submodule (𝓞 E) E) := by
  rw [← trI_one e, mem_trI]

theorem map_mulVec' {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (v : Fin n → E) :
    (A.map e).mulVec (fun i => e (v i)) = fun i => e (A.mulVec v i) := by
  funext i

  simp [Matrix.mulVec, dotProduct, map_sum]

theorem det_map' {n : ℕ} (A : Matrix (Fin n) (Fin n) E) : (A.map e).det = e A.det := (RingHom.map_det (e : E →+* E') A).symm

theorem carries_iff {n : ℕ} (N : Submodule (𝓞 E) (Fin n → E)) (A : Matrix (Fin n) (Fin n) E) :
    (∀ v ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E') E')), (A.map e).mulVec v ∈ trL e N) ↔
      ∀ v ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)), A.mulVec v ∈ N := by
  constructor
  · intro H v hv
    have hv' : (fun i => e (v i)) ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E') E')) := by
      rw [Submodule.mem_pi] at hv ⊢
      intro i hi
      rw [mem_one_iff e, RingEquiv.symm_apply_apply]
      exact hv i hi
    have hA := H _ hv'
    rw [map_mulVec' e A v, mem_trL] at hA
    simpa using hA
  · intro H v hv
    have hv' : (fun i => e.symm (v i)) ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) := by
      rw [Submodule.mem_pi] at hv ⊢
      intro i hi
      rw [← mem_one_iff e]
      exact hv i hi
    have hmv : (A.map e).mulVec v = fun i => e (A.mulVec (fun i => e.symm (v i)) i) := by
      have hk := map_mulVec' e A (fun i => e.symm (v i))
      simp only [RingEquiv.apply_symm_apply] at hk
      exact hk
    rw [hmv, mem_trL]
    simpa using H _ hv'

theorem det_set {n : ℕ} (N : Submodule (𝓞 E) (Fin n → E)) :
    {x | ∃ A : Matrix (Fin n) (Fin n) E', (∀ v ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E') E')),
        A.mulVec v ∈ trL e N) ∧ x = A.det} =
      e '' {x | ∃ A : Matrix (Fin n) (Fin n) E, (∀ v ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)),
        A.mulVec v ∈ N) ∧ x = A.det} := by
  ext x
  constructor
  · rintro ⟨A', hA', rfl⟩
    have hmap : (A'.map e.symm).map e = A' := by
      ext i j
      simp
    refine ⟨(A'.map e.symm).det, ⟨A'.map e.symm, ?_, rfl⟩, ?_⟩
    · rw [← carries_iff e N, hmap]
      exact hA'
    · rw [← det_map', hmap]
  · rintro ⟨y, ⟨A, hA, rfl⟩, rfl⟩
    exact ⟨A.map e, (carries_iff e N A).mpr hA, (det_map' e A).symm⟩

end Fields

theorem transport : ∀ (D : D7) (X : Fields) (s : Seam D X), (∀ (I : Submodule (𝓞 X.E) X.E) (x : D.host.E), x ∈ idTo s I ↔ s.iE.symm x ∈ I) ∧ (∀ I J : Submodule (𝓞 X.E) X.E, idTo s (I * J) = idTo s I * idTo s J) ∧ idTo s 1 = 1 ∧ (∀ y : X.E, idTo s (Submodule.span (𝓞 X.E) {y}) = Submodule.span (𝓞 D.host.E) {s.iE y}) ∧ (∀ 𝔞 : TaylorLogMetric.IdE D, ∃ I, idTo s I = 𝔞) ∧ ∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)), TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N) = idTo s (detLat N) := by
  intro D X s
  refine ⟨fun I x => mem_trI s.iE I x, fun I J => trI_mul s.iE I J, trI_one s.iE,
    fun y => trI_singleton s.iE y, trI_surj s.iE, fun n N => ?_⟩
  calc TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N)
      = Submodule.span (𝓞 D.host.E) (s.iE '' {x | ∃ A : Matrix (Fin n) (Fin n) X.E,
          (∀ v ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 X.E) X.E)), A.mulVec v ∈ N) ∧
            x = A.det}) := by
        rw [← det_set s.iE N]
        rfl
    _ = idTo s (detLat N) := (trI_span s.iE _).symm

end GlobalTheory.IdealTransport
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

theorem _root_.GlobalTheory.T.unfoldingCharacterArgument_comp_unipotentRadicals : (∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)), (∃ t : Loc.FC n' c' n c → F, x = Loc.xx1 xj t) ↔ ((∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v)) ∧ x (Loc.eN F (n' + c') n') = Loc.eN F (n + c) n ∧ ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s)) → ∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ r ∈ Loc.R1 F n c, ∀ r' ∈ Loc.R1 F n' c', ∃ d : F, ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (t : Loc.FC n' c' n c → F), Loc.chArg (r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap) = Loc.chArg (Loc.xx1 xj t) + d := by
  first | exact @GlobalTheory.Proof.unfoldingCharacterArgument_comp_unipotentRadicals.chArg_comp | exact GlobalTheory.Proof.unfoldingCharacterArgument_comp_unipotentRadicals.chArg_comp | (intros; apply GlobalTheory.Proof.unfoldingCharacterArgument_comp_unipotentRadicals.chArg_comp <;> assumption)
end

section

open Formalism.BasicNotions Classical NumberField IsDedekindDomain Matrix GlobalTheory.LvT GlobalTheory.LvT.Inh
open Formalism.MainNotions.product_first_zeroth_parts (Ow ten blk CSpan IntSpan wSh)
open Formalism.L2.Col (conjPrime₂ PosStar hStd UF Sp)

namespace GlobalTheory.LvT.Inh.ResFin

theorem infinite_places (K : Type) [Field K] [NumberField K] : Infinite (HeightOneSpectrum (𝓞 K)) := by
  have h : ∀ p : Nat.Primes, ∃ la : HeightOneSpectrum (𝓞 K), la.asIdeal.comap (algebraMap ℤ (𝓞 K)) =
      Ideal.span {((p : ℕ) : ℤ)} := fun p => by
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
    obtain ⟨M, hM, hc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) (Ideal.span {((p : ℕ) : ℤ)})
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 K)).injective_int]; exact bot_le)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩, hc⟩
  choose f hf using h
  refine Infinite.of_injective f fun p q hpq => ?_
  have e : Ideal.span {((p : ℕ) : ℤ)} = Ideal.span {((q : ℕ) : ℤ)} := by rw [← hf p, ← hf q, hpq]
  have := Int.associated_iff_natAbs.1 (Ideal.span_singleton_eq_span_singleton.1 e)
  exact Subtype.ext (by simpa using this)

end GlobalTheory.LvT.Inh.ResFin
end
