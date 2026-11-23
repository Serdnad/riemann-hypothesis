module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle007
import GroundTheory.GlobalFields.Bundle001
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DualLatticeParametrization
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle013
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle014
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Std.Tactic.BVDecide.Normalize.Prop
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle006

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.MeasProj

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]

theorem repr_map {d : ℕ} (b : Module.Basis (Fin d) F E) (f : R →ₐ[F] S) (y : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis S b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) y) k =
      f ((Algebra.TensorProduct.basis R b).repr y k) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  | add x y hx hy => simp [map_add (f := _), hx, hy]

variable [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace S] [IsTopologicalRing S]

theorem continuous_mapTens {d : ℕ} (b : Module.Basis (Fin d) F E) (f : R →ₐ[F] S) (hf : Continuous f) :
    Continuous (Algebra.TensorProduct.map f (AlgHom.id F E) : R ⊗[F] E → S ⊗[F] E) := by
  rw [(TopK.isHomeomorph_coord S b).isInducing.continuous_iff]
  refine continuous_pi fun k => ?_
  simp only [Function.comp_def, repr_map]
  exact hf.comp ((continuous_apply k).comp (TopK.isHomeomorph_coord R b).continuous)

theorem continuous_mapTup {d n M : ℕ} (b : Module.Basis (Fin d) F E) (f : R →ₐ[F] S) (hf : Continuous f) :
    Continuous (fun (X : Fin n → Fin M → R ⊗[F] E) (a : Fin n) (i : Fin M) =>
      Algebra.TensorProduct.map f (AlgHom.id F E) (X a i)) :=
  continuous_pi fun a => continuous_pi fun i =>
    (continuous_mapTens b f hf).comp ((continuous_apply i).comp (continuous_apply a))


omit [IsTopologicalRing S] [TopologicalSpace S] [CommRing S] [Algebra F S] in
def tupHomeo {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ) :
    (Fin n → Fin M → R ⊗[F] E) ≃ₜ (Fin n → Fin M → Fin d → R) :=
  Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ => TopK.coordHomeo R b

end Gen

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem continuous_fstA : Continuous (fstA F) := continuous_fst

theorem continuous_sndA : Continuous (sndA F) := continuous_snd

theorem continuous_evalV (v : HeightOneSpectrum (𝓞 F)) : Continuous (evalV F v) :=
  RestrictedProduct.continuous_eval v

theorem coord_projInf {d n M : ℕ} (b : Module.Basis (Fin d) F E) (X : Fin n → Fin M → AF F ⊗[F] E)
    (a : Fin n) (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Ainf F) b).repr (projInf X a i) k =
      ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k).1 :=
  repr_map b (fstA F) _ k

theorem coord_projFin {d n M : ℕ} (b : Module.Basis (Fin d) F E) (X : Fin n → Fin M → AF F ⊗[F] E)
    (a : Fin n) (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Af F) b).repr (projFin X a i) k =
      ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k).2 :=
  repr_map b (sndA F) _ k

theorem coord_projV {d n M : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (X : Fin n → Fin M → Af F ⊗[F] E) (a : Fin n) (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (projV v X a i) k =
      ((Algebra.TensorProduct.basis (Af F) b).repr (X a i) k) v :=
  repr_map b (evalV F v) _ k

theorem latV_eq {d n M : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) =
      tupHomeo b n M ⁻¹' (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.pi Set.univ fun _ =>
        (v.adicCompletionIntegers F : Set (Fv F v))) := by
  ext Y
  simp only [latV, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
  rfl

theorem isCompact_latV {d n M : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  have hc : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
    isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace (v.adicCompletionIntegers F)))
  rw [latV_eq, (tupHomeo b n M).isCompact_preimage]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hc

theorem isOpen_latV {d n M : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  have ho : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  rw [latV_eq]
  refine IsOpen.preimage (tupHomeo b n M).continuous ?_
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => ho

theorem projV_mem_latV_iff {d n M : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (X : Fin n → Fin M → Af F ⊗[F] E) :
    projV v X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) ↔
      ∀ a i k, ((Algebra.TensorProduct.basis (Af F) b).repr (X a i) k) v ∈
        v.adicCompletionIntegers F := by
  simp only [latV, Set.mem_setOf_eq, coord_projV]

end Adelic

section Adelic2

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem isOpen_intOff {d n M : ℕ} (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpen (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E)) := by
  have hA : IsOpen {x : Af F | ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _)
      (p := fun v => v ∉ S)
  have hE : (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E)) = ⋂ a, ⋂ i, ⋂ k,
      (fun X : Fin n → Fin M → AF F ⊗[F] E =>
        sndA F ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k)) ⁻¹'
        {x : Af F | ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers F} := by
    ext X
    simp only [intOff, Set.mem_setOf_eq, projV_mem_latV_iff, coord_projFin, Set.mem_iInter,
      Set.mem_preimage]
    exact ⟨fun h a i k v hv => h v hv a i k, fun h v hv a i k => h a i k v hv⟩
  rw [hE]
  refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i =>
    isOpen_iInter_of_finite fun k => hA.preimage (continuous_sndA.comp ?_)
  exact (continuous_apply k).comp ((TopK.isHomeomorph_coord (AF F) b).continuous.comp
    ((continuous_apply i).comp (continuous_apply a)))

theorem eventually_mem_latV {d n M : ℕ} (b : Module.Basis (Fin d) F E)
    (X : Fin n → Fin M → Af F ⊗[F] E) :
    ∀ᶠ v in Filter.cofinite, projV v X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  simp only [projV_mem_latV_iff, Filter.eventually_all]
  intro a i k
  exact ((Algebra.TensorProduct.basis (Af F) b).repr (X a i) k).2

theorem ext_proj {d n M : ℕ} (b : Module.Basis (Fin d) F E) (X Y : Fin n → Fin M → AF F ⊗[F] E)
    (h1 : projInf X = projInf Y) (h2 : ∀ v, projV v (projFin X) = projV v (projFin Y)) : X = Y := by
  funext a i
  apply (Algebra.TensorProduct.basis (AF F) b).repr.injective
  ext k
  refine Prod.ext (α := Ainf F) (β := Af F) ?_ ?_
  · rw [← coord_projInf, ← coord_projInf, h1]
  · refine Subtype.ext (funext fun v => ?_)
    have e : ∀ T : Fin n → Fin M → AF F ⊗[F] E, ((Algebra.TensorProduct.basis (AF F) b).repr (T a i) k).2 v =
        (Algebra.TensorProduct.basis (Fv F v) b).repr (projV v (projFin T) a i) k := fun T => by
      rw [coord_projV, coord_projFin]
    have h3 : (Algebra.TensorProduct.basis (Fv F v) b).repr (projV v (projFin X) a i) k =
        (Algebra.TensorProduct.basis (Fv F v) b).repr (projV v (projFin Y) a i) k := by rw [h2 v]
    exact (e X).trans (h3.trans (e Y).symm)

def glueFin (z : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v)
    (h : ∀ᶠ v in Filter.cofinite, z v ∈ v.adicCompletionIntegers F) : Af F :=
  (⟨z, h⟩ : RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite)

theorem exists_glue {d n M : ℕ} (b : Module.Basis (Fin d) F E) (Y : Fin n → Fin M → Ainf F ⊗[F] E)
    (Z : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E))
    (hZ : ∀ᶠ v in Filter.cofinite, Z v ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E))) :
    ∃ X : (Fin n → Fin M → AF F ⊗[F] E), projInf X = Y ∧ ∀ v, projV v (projFin X) = Z v := by
  have ev : ∀ a i k, ∀ᶠ v in Filter.cofinite,
      (Algebra.TensorProduct.basis (Fv F v) b).repr (Z v a i) k ∈ v.adicCompletionIntegers F :=
    fun a i k => hZ.mono fun v hv => hv a i k
  let x : Fin n → Fin M → Fin d → AF F := fun a i k =>
    pairA F ((Algebra.TensorProduct.basis (Ainf F) b).repr (Y a i) k)
      (glueFin (fun v => (Algebra.TensorProduct.basis (Fv F v) b).repr (Z v a i) k) (ev a i k))
  let X : Fin n → Fin M → AF F ⊗[F] E := fun a i =>
    (Algebra.TensorProduct.basis (AF F) b).equivFun.symm (x a i)
  have hX : ∀ a i k, (Algebra.TensorProduct.basis (AF F) b).repr (X a i) k = x a i k := fun a i k =>
    congrFun ((Algebra.TensorProduct.basis (AF F) b).equivFun.apply_symm_apply (x a i)) k
  refine ⟨X, ?_, fun v => ?_⟩
  · funext a i
    apply (Algebra.TensorProduct.basis (Ainf F) b).repr.injective
    ext k
    rw [coord_projInf, hX]
    rfl
  · funext a i
    apply (Algebra.TensorProduct.basis (Fv F v) b).repr.injective
    ext k
    rw [coord_projV, coord_projFin, hX]
    rfl

theorem continuous_sizeTup {d n M : ℕ} (b : Module.Basis (Fin d) F E) :
    Continuous (sizeTup b : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ) := by
  unfold sizeTup sizeInf
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun v _ => continuous_norm.comp ?_
  exact (continuous_apply (A := fun v : InfinitePlace F => v.Completion) v).comp
    ((continuous_apply k).comp ((TopK.isHomeomorph_coord (Ainf F) b).continuous.comp
      ((continuous_apply i).comp (continuous_apply a))))

end Adelic2

theorem proj_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), Continuous (projInf : (Fin n → Fin M → AF F ⊗[F] E) → _) ∧ Continuous (projFin : (Fin n → Fin M → AF F ⊗[F] E) → _) ∧ (∀ v, Continuous (projV v : (Fin n → Fin M → Af F ⊗[F] E) → _)) ∧ (∀ v, IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) ∧ IsOpen (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E))) ∧ (∀ S, IsOpen (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E))) ∧ (∀ X : (Fin n → Fin M → Af F ⊗[F] E), ∀ᶠ v in Filter.cofinite, projV v X ∈ latV b v) ∧ (∀ X Y : (Fin n → Fin M → AF F ⊗[F] E), projInf X = projInf Y → (∀ v, projV v (projFin X) = projV v (projFin Y)) → X = Y) ∧ (∀ (Y : (Fin n → Fin M → Ainf F ⊗[F] E)) (Z : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ᶠ v in Filter.cofinite, Z v ∈ latV b v) → ∃ X : (Fin n → Fin M → AF F ⊗[F] E), projInf X = Y ∧ ∀ v, projV v (projFin X) = Z v) ∧ Continuous (sizeTup b : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ) := by
  intro F E _ _ _ _ _ σ _ d b n M
  exact ⟨continuous_mapTup b (fstA F) continuous_fstA, continuous_mapTup b (sndA F) continuous_sndA,
    fun v => continuous_mapTup b (evalV F v) (continuous_evalV v),
    fun v => ⟨isCompact_latV b v, isOpen_latV b v⟩, fun S => isOpen_intOff b S,
    fun X => eventually_mem_latV b X, fun X Y => ext_proj b X Y,
    fun Y Z h => exists_glue b Y Z h, continuous_sizeTup b⟩

end GlobalTheory.CompanionTheory.SW.MeasProj
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GramAlg

section Gen

variable {A : Type} [CommRing A] {M n : ℕ}

def colM (X : Fin n → Fin M → A) : Matrix (Fin M) (Fin n) A := fun i a => X a i

theorem colM_injective : Function.Injective (colM : (Fin n → Fin M → A) → _) := by
  intro X Y h
  funext a i
  exact congrFun (congrFun h i) a

theorem hform_eq_entry (s : A →+* A) (J : Matrix (Fin M) (Fin M) A) (X : Fin n → Fin M → A)
    (a b : Fin n) :
    hform s J (X a) (X b) = (cT s (colM X) * J * colM X) a b := by
  simp only [hform, Matrix.mul_apply, cT, colM, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  exact Finset.sum_comm

theorem mul_shape {p q r s t u : Type} [Fintype q] [Fintype r] [Fintype s] [Fintype t]
    (a : Matrix p q A) (b : Matrix q r A) (c : Matrix r s A) (d : Matrix s t A) (e : Matrix t u A) :
    (((a * b : Matrix p r A) * c : Matrix p s A) * (d * e : Matrix s u A) : Matrix p u A) =
      ((a * ((b * c : Matrix q s A) * d : Matrix q t A) : Matrix p t A) * e : Matrix p u A) := by
  simp only [Matrix.mul_assoc]

theorem cT_cT (s : A →+* A) (hs : ∀ x, s (s x) = x) {m p : Type} (B : Matrix m p A) :
    cT s (cT s B) = B := by
  ext i j
  simp [cT, hs]

end Gen

section Conj

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigma_invol [NumberField F] [NumberField E] {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (x : E) :
    σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  apply τ.injective
  rw [hσ.2.2.2 τ, hσ.2.2.2 τ, star_star]

variable (R : Type) [CommRing R] [Algebra F R]

theorem sigR_invol {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (x : R ⊗[F] E) :
    sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, h]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

variable {M n : ℕ}

theorem gramR_eq (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J X =
      (cT (sigR R σ) (colM X) * JR R J : Matrix (Fin n) (Fin M) (R ⊗[F] E)) * colM X := by
  ext a b
  exact hform_eq_entry _ _ X a b

theorem colM_rmul (X : Fin n → Fin M → R ⊗[F] E) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    colM (rmul R X g) = colM X * g := by
  ext i a
  simp [colM, rmul, Matrix.mul_apply]

theorem colM_actTup (g : GL (Fin M) (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E) :
    colM (actTup R g X) = (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * colM X := by
  ext i a
  simp [colM, actTup, Matrix.mulVec, dotProduct, Matrix.mul_apply]

end Conj

theorem gram_algebra : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] (n : ℕ), (∀ (X : Fin n → Fin M → R ⊗[F] E) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)), gramR R σ J (rmul R X g) = cT (sigR R σ) g * gramR R σ J X * g) ∧ (∀ (X : Fin n → Fin M → R ⊗[F] E) (g g' : Matrix (Fin n) (Fin n) (R ⊗[F] E)), rmul R (rmul R X g) g' = rmul R X (g * g')) ∧ (∀ X : Fin n → Fin M → R ⊗[F] E, rmul R X 1 = X) ∧ (∀ (S : HermR R σ n) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)), cT (sigR R σ) g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g ∈ HermR R σ n) ∧ ∀ (J' : Matrix (Fin M) (Fin M) E) (g : GL (Fin M) (R ⊗[F] E)), JR R J' = cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) → ∀ X : Fin n → Fin M → R ⊗[F] E, gramR R σ J (actTup R g X) = gramR R σ J' X := by
  intro F E _ _ _ _ _ σ hσ M J _ R _ _ n
  have hs : ∀ x : R ⊗[F] E, sigR R σ (sigR R σ x) = x := sigR_invol R (sigma_invol hσ)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X g
    rw [gramR_eq, gramR_eq, colM_rmul, cT_mul]
    exact mul_shape _ _ _ _ _
  · intro X g g'
    apply colM_injective
    rw [colM_rmul, colM_rmul, colM_rmul, Matrix.mul_assoc]
  · intro X
    apply colM_injective
    rw [colM_rmul, Matrix.mul_one]
  · intro S g
    have hS : cT (sigR R σ) (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = S := by
      ext a b
      exact S.2 a b
    have key : cT (sigR R σ) (cT (sigR R σ) g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g)
        = cT (sigR R σ) g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g := by
      rw [cT_mul, cT_mul, cT_cT _ hs, hS, Matrix.mul_assoc]
    intro a b
    exact congrFun (congrFun key a) b
  · intro J' g hJ X
    rw [gramR_eq, gramR_eq, colM_actTup, cT_mul, hJ]
    exact mul_shape _ _ _ _ _

end GlobalTheory.CompanionTheory.SW.GramAlg
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem _root_.GlobalTheory.T.dual_lattice_parametrization : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι F) (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ), B.det ≠ 0 → 0 < N → ∃ e : (ι × InfinitePlace F → ℤ) → ι → F, (∀ n i v, (N : ℚ) * Algebra.trace ℚ F ((b v : F) * (B *ᵥ e n) i) = n (i, v)) ∧ ∀ y : ι → F, (∀ i v, ∃ m : ℤ, (N : ℚ) * Algebra.trace ℚ F ((b v : F) * (B *ᵥ y) i) = m) → ∃ n, e n = y := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.DualLattice.exists_dual_param | exact GlobalTheory.CompanionTheory.SW.ThW.DualLattice.exists_dual_param | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.DualLattice.exists_dual_param <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem _root_.GlobalTheory.T.totally_real_integral_basis_exists : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → Nonempty (Module.Basis (InfinitePlace F) ℤ (𝓞 F)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.exists_integralBasis_infinitePlace | exact GlobalTheory.CompanionTheory.SW.ThW.exists_integralBasis_infinitePlace | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.exists_integralBasis_infinitePlace <;> assumption)
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.infinite_product_renormalization : ∀ (ι : Type) [DecidableEq ι] (a : ι → ℝ) (c : Finset ι → ℝ≥0) (S₁ : Finset ι), (∀ v, 0 ≤ a v) → Summable (fun v => |a v - 1|) → (∀ S, S₁ ⊆ S → ∀ v, v ∉ S → (c S : ℝ) = c (insert v S) * a v) → ∃ (c₀ : ℝ≥0) (S₀ : Finset ι), S₁ ⊆ S₀ ∧ ∀ S, S₀ ⊆ S → (0 < ∏' v : {v // v ∉ S}, a v.1) ∧ (c S : ℝ) = c₀ * ∏' v : {v // v ∉ S}, a v.1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.TailConst.exists_const_mul_tail | exact GlobalTheory.CompanionTheory.SW.TailConst.exists_const_mul_tail | (intros; apply GlobalTheory.CompanionTheory.SW.TailConst.exists_const_mul_tail <;> assumption)
end
