module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1348
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameAdelicLatticeAtFinitePlaceOfInert
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

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.adeleLinearEquiv_maps_open_finite_subgroup_to_open : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) ≃ₗ[AdeleRing (𝓞 F) F] ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)))
    (M : AddSubgroup ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F))), IsOpen (M : Set ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F))) →
      ∃ M' : AddSubgroup ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (M' : Set ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F))) ∧
        ∀ m' ∈ M', ∃ m ∈ M, B (GlobalTheory.WeilAdm.finE2 F m) = GlobalTheory.WeilAdm.finE2 F m' := by
  first | exact @GlobalTheory.WeilAdm.fintrans | exact GlobalTheory.WeilAdm.fintrans | (intros; apply GlobalTheory.WeilAdm.fintrans <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.adeleLinearEquiv_restricts_realLinearEquiv_archimedean : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) ≃ₗ[AdeleRing (𝓞 F) F] ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F))),
      ∃ L : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) ≃ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
        ∀ v, B (GlobalTheory.WeilAdm.mixedSpaceVecPairAsAdeles F v) = GlobalTheory.WeilAdm.mixedSpaceVecPairAsAdeles F (L v) := by
  first | exact @GlobalTheory.WeilAdm.infLin_main | exact GlobalTheory.WeilAdm.infLin_main | (intros; apply GlobalTheory.WeilAdm.infLin_main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.eq_finset_sum_pureTensor_coset_indicator : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F))
    (K : Set (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) → IsCompact (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) → IsCompact K →
      ∃ R : Finset (κ → FiniteAdeleRing (𝓞 F) F),
        (∀ r ∈ R, Set.indicator {y | y - r ∈ U} (fun _ => (1 : ℂ)) ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧
        ∀ Φ : (κ → AdeleRing (𝓞 F) F) → ℂ, (∀ x, ∀ u ∈ U, Φ (x + GlobalTheory.WeilAdm.finE F u) = Φ x) →
          (∀ x, (fun i => (x i).2) ∉ K → Φ x = 0) →
            Φ = ∑ r ∈ R, GlobalTheory.WeilM.pureA F (GlobalTheory.WeilAdm.slice F Φ r) (Set.indicator {y | y - r ∈ U} fun _ => (1 : ℂ)) := by
  first | exact @GlobalTheory.WeilAdm.eq_sum_pureA_coset_indicator | exact GlobalTheory.WeilAdm.eq_sum_pureA_coset_indicator | (intros; apply GlobalTheory.WeilAdm.eq_sum_pureA_coset_indicator <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_linear_model_archimedean_schroedinger_standard : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ a, ψ (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0) : AdeleRing (𝓞 F) F) =
      Complex.exp (2 * Real.pi * Complex.I * β a)) →
    (∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0) → ∀ (κ : Type) [Fintype κ],
    ∃ (n : ℕ) (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F))
      (P : (Fin n ⊕ Fin n → ℝ) ≃ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))),
      ∀ w (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ),
        GlobalTheory.WeilAdm.schrInf F ψ (P w) φ ∘ Q = GlobalTheory.RealWeil.rhoFun w (φ ∘ Q) := by
  first | exact @GlobalTheory.WeilAdm.RealModel.exists_model | exact GlobalTheory.WeilAdm.RealModel.exists_model | (intros; apply GlobalTheory.WeilAdm.RealModel.exists_model <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.mem_tensorLatticeAtPlace_iff_frame_coordinates_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F)) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      Function.Injective ι → (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) →
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) →
      ∀ (PV : GL (Fin n) L) (PW : GL (Fin d) L), (∀ x : Fin n → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((PV : Matrix (Fin n) (Fin n) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt X v) → (∀ x : Fin d → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((PW : Matrix (Fin d) (Fin d) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt W v) →
      ∀ z, z ∈ latAtV X W v ↔ ∃ u : Matrix (Fin d) (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) ∧
        GlobalTheory.InertLocFrame.xm ι PV PW u = z := by
  first | exact @GlobalTheory.InertLocFrame.mem_latAtV_iff_xm | exact GlobalTheory.InertLocFrame.mem_latAtV_iff_xm | (intros; apply GlobalTheory.InertLocFrame.mem_latAtV_iff_xm <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.VacTransportLeft

section Alg

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type} [Fintype α] [Fintype β]

theorem hTens_eq_left (JA : Matrix α α A) (JB : Matrix β β A) (x y : Matrix α β A) :
    hTens c JA JB x y = ∑ j, ∑ l, JB j l * (xᵀ * JA * y.map c) j l := by
  simp only [hTens, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm, Finset.sum_comm (γ := β)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem symp_mul_left [DecidableEq α] (ξ : A) (JA : Matrix α α A) (JB : Matrix β β A) (g : Matrix α α A)
    (hg : gᵀ * JA * g.map c = JA) (x y : Matrix α β A) :
    symp c ξ JA JB (g * x) (g * y) = symp c ξ JA JB x y := by
  have e : (g * x)ᵀ * JA * (g * y).map c = xᵀ * JA * y.map c := by
    have hm : (g * y).map c = g.map c * y.map c := Matrix.map_mul (f := c.toRingHom)
    rw [hm, Matrix.transpose_mul]
    calc xᵀ * gᵀ * JA * (g.map c * y.map c) = xᵀ * (gᵀ * JA * g.map c) * y.map c := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg]
  unfold symp
  rw [hTens_eq_left, hTens_eq_left, e]

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem vecMulVec_mem_left {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {y : Fin d → E} (hy : y ∈ W.L)
    {z : Fin n → AE F E} (hz : z ∈ GlobalTheory.InertSph.latAt X v) :
    Matrix.vecMulVec z (fun i => inclR (F := F) (AF F) (y i)) ∈ latAtV X W v := by
  let f : (Fin n → AE F E) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    { toFun := fun z => Matrix.vecMulVec z (fun i => inclR (F := F) (AF F) (y i))
      map_zero' := by ext i j; simp [Matrix.vecMulVec_apply]
      map_add' := fun z z' => by ext i j; simp [Matrix.vecMulVec_apply, add_mul] }
  have : GlobalTheory.InertSph.latAt X v ≤ (latAtV X W v).comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, hai, x, hx, rfl⟩
    refine AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, y, hy, ?_⟩
    ext i j
    simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, incM,
      Matrix.map_apply, map_mul, Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply]
    ring
  exact this hz

theorem inv_mul_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {k : UA σ X.J}
    (hk : k ∈ GlobalTheory.InertSph.KAt σ X v) {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X W v) :
    mat k⁻¹ * γ ∈ latAtV X W v := by
  let f : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    { toFun := fun γ => mat k⁻¹ * γ
      map_zero' := by simp
      map_add' := fun γ γ' => by simp [Matrix.mul_add] }
  have : latAtV X W v ≤ (latAtV X W v).comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, hai, x, hx, y, hy, rfl⟩
    show mat k⁻¹ * (a • incM F (Matrix.vecMulVec x y)) ∈ latAtV X W v
    have hz : (a • fun i => inclR (F := F) (AF F) (x i)) ∈ GlobalTheory.InertSph.latAt X v :=
      AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, rfl⟩
    have e : mat k⁻¹ * (a • incM F (Matrix.vecMulVec x y)) =
        Matrix.vecMulVec (mat k⁻¹ *ᵥ (a • fun i => inclR (F := F) (AF F) (x i)))
          (fun j => inclR (F := F) (AF F) (y j)) := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, Matrix.mulVec,
        dotProduct, Pi.smul_apply, incM, Matrix.map_apply, map_mul, Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [e]
    exact vecMulVec_mem_left X W v hy (hk.2 _ hz).2
  exact this hγ

theorem transport_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v, ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • φ)) → Acts (evFin F v) (om (k, 1)) φ φ₁ →
      (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ₁
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • φ₁)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v k hk θ _ φ hφ φ₁ _ hfix hact γ hγ r hr
  have etens : ∀ (c : ℂ) (f : (Fin a × Fin (a + a') → Fv F v) → ℂ),
      tens (evFin F v) (c • f) r = c • tens (evFin F v) f r := fun c f => by
    funext x; simp only [tens, Pi.smul_apply, smul_eq_mul]; ring
  by_cases h0 : φ₁ = 0
  · subst h0
    funext x
    simp [Darboux.rho, schr, tens]
  have hr' : Rest (evFin F v) φ r := GlobalTheory.RestCofactor.rest_of_rest v φ₁ φ r h0 hφ hr
  have hS := IsUWeilPair.isUSplitting hT.weil
  have hγ' : mat k⁻¹ * γ ∈ latAtV G.V G.W v := inv_mul_mem G.V G.W v hk hγ
  have hback : actAB (cA σ) (k, (1 : UA σ G.W.J)) (mat k⁻¹ * γ) = γ := by
    change mat k * (mat k⁻¹ * γ) * (1 : Matrix _ _ _)ᵀ = γ
    have e : mat k * mat k⁻¹ = 1 := Units.mul_inv k.1
    rw [Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc, e, Matrix.one_mul]
  have hsy := symp_mul_left (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) (mat k⁻¹)
    (k⁻¹).2 γ γ
  have h1 := hS.impl (k, 1) (mat k⁻¹ * γ) _ hr'.2
  rw [hback, hfix _ hγ' r hr', hsy, etens, map_smul, hact r hr'] at h1
  rw [← h1, etens]

end GlobalTheory.VacTransportLeft

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.VacTransport

section Alg

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in
theorem hTens_eq (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JA JB x y = ∑ i, ∑ k, JA i k * (x * JB * (y.map c)ᵀ) i k := by
  unfold hTens
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  ring


omit [DecidableEq α] [DecidableEq β] in
theorem symp_mul_transpose (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (h : Matrix β β E)
    (hh : hᵀ * JB * h.map c = JB) (x y : Matrix α β E) :
    symp (R := R) c ξ JA JB (x * hᵀ) (y * hᵀ) = symp (R := R) c ξ JA JB x y := by
  unfold symp
  rw [hTens_eq, hTens_eq]
  have e : (y * hᵀ).map c = y.map c * (hᵀ).map c := Matrix.map_mul (f := c.toRingHom)
  have e2 : x * hᵀ * JB * ((y * hᵀ).map c)ᵀ = x * JB * (y.map c)ᵀ := by
    rw [e, Matrix.transpose_mul, ← Matrix.transpose_map, Matrix.transpose_transpose]
    conv_rhs => rw [← hh]
    simp only [Matrix.mul_assoc]
  rw [e2]

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem vecMulVec_mem {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl (F := F)) {x : Fin n → E} (hx : x ∈ X.L)
    {z : Fin d → AE F E} (hz : z ∈ GlobalTheory.InertSph.latAt Y v) :
    Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) z ∈ latAtV X Y v := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hv, y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, hv, x, hx, y, hy, ?_⟩
    ext i j
    simp [Matrix.vecMulVec_apply, incM]
  | zero =>
    have e : Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (0 : Fin d → AE F E) = 0 := by
      ext i j
      simp [Matrix.vecMulVec_apply]
    rw [e]; exact zero_mem _
  | add z z' _ _ h h' => rw [Matrix.vecMulVec_add]; exact add_mem h h'
  | neg z _ h => rw [Matrix.vecMulVec_neg]; exact neg_mem h

theorem mul_transpose_mem {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl (F := F)) (h : Matrix (Fin d) (Fin d) (AE F E))
    (hh : ∀ z ∈ GlobalTheory.InertSph.latAt Y v, h *ᵥ z ∈ GlobalTheory.InertSph.latAt Y v)
    {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X Y v) : γ * hᵀ ∈ latAtV X Y v := by
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hv, x, hx, y, hy, rfl⟩ := hz
    have hm : (a • fun i => inclR (F := F) (AF F) (y i)) ∈ GlobalTheory.InertSph.latAt Y v :=
      AddSubgroup.subset_closure ⟨a, ha, hv, y, hy, rfl⟩
    have e : a • incM F (Matrix.vecMulVec x y) =
        Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (a • fun i => inclR (F := F) (AF F) (y i)) := by
      ext i j
      simp [Matrix.vecMulVec_apply, incM]
    rw [e, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
    exact vecMulVec_mem X Y v hx (hh _ hm)
  | zero => rw [Matrix.zero_mul]; exact zero_mem _
  | add z z' _ _ h h' => rw [Matrix.add_mul]; exact add_mem h h'
  | neg z _ h => rw [Matrix.neg_mul]; exact neg_mem h

omit [NumberField E] in
theorem tens_smul {R κ : Type} (ev : AF F → R) (c : ℂ) (φ : (κ → R) → ℂ) (r : (κ → AF F) → ℂ) :
    tens ev (c • φ) r = c • tens ev φ r := by
  funext x
  simp only [tens, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • φ)) → Acts (evFin F v) (om (1, k)) φ φ₁ →
      (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ₁
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • φ₁)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v k hk θ _ φ hφ φ₁ _ hfix hact γ hγ r hr
  by_cases h0 : φ₁ = 0
  · subst h0
    funext x
    simp [Darboux.rho, schr, tens]
  have hr' : Rest (evFin F v) φ r := GlobalTheory.RestCofactor.rest_of_rest v φ₁ φ r h0 hφ hr
  have hS := IsUWeilPair.isUSplitting hT.weil
  have hγ' : γ * (mat k⁻¹)ᵀ ∈ latAtV G.V G.W v := mul_transpose_mem G.V G.W v _ (fun z hz => (hk.2 z hz).2) hγ
  have hback : actAB (cA σ) ((1 : UA σ G.V.J), k) (γ * (mat k⁻¹)ᵀ) = γ := by
    change (1 : Matrix _ _ _) * (γ * (mat k⁻¹)ᵀ) * (mat k)ᵀ = γ
    have e : mat k * mat k⁻¹ = 1 := Units.mul_inv k.1
    rw [Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, e, Matrix.transpose_one, Matrix.mul_one]
  have hsy := symp_mul_transpose (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) (mat k⁻¹)
    (k⁻¹).2 γ γ
  have h1 := hS.impl (1, k) (γ * (mat k⁻¹)ᵀ) _ hr'.2
  rw [hback, hfix _ hγ' r hr', hsy, tens_smul, map_smul, hact r hr'] at h1
  rw [← h1, tens_smul]

end GlobalTheory.VacTransport

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.cayleyTransform_mem_unitaryLatticeStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (W : Spc F E d) (v : Pl (F := F)) (Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evFin F v) Y →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 →
    (∃ M : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (1 + Y) * M = 1 ∧ M * (1 + Y) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    (∃ M : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (1 - Y) * M = 1 ∧ M * (1 - Y) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    ∃ h ∈ GlobalTheory.InertSph.KAt σ W v, mat h * (1 + Y) = 1 - Y := by
  first | exact @GlobalTheory.CayleyStab.cayley_mem_KAt | exact GlobalTheory.CayleyStab.cayley_mem_KAt | (intros; apply GlobalTheory.CayleyStab.cayley_mem_KAt <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.inv_two_smul_mem_adelicLatticeAtFinitePlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (W : Spc F E d)
    (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal → ∀ z ∈ GlobalTheory.InertSph.latAt W v, (⅟(2 : AF F)) • z ∈ GlobalTheory.InertSph.latAt W v := by
  first | exact @GlobalTheory.InertSph.invTwo_smul_mem_latAt | exact GlobalTheory.InertSph.invTwo_smul_mem_latAt | (intros; apply GlobalTheory.InertSph.invTwo_smul_mem_latAt <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.mem_latticeStabilizer_of_frame_conj_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F)) (n : ℕ) (X : Spc F E n) (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      Function.Injective ι → (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) →
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) →
      ∀ P : GL (Fin n) L, (∀ x : Fin n → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((P : Matrix (Fin n) (Fin n) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt X v) →
      ∀ (g : UA σ X.J) (K K' : Matrix (Fin n) (Fin n) L), (∀ i j, K i j ∈ Formalism.UG.intL L) →
        (∀ i j, K' i j ∈ Formalism.UG.intL L) →
        mat g = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) +
          ((P : Matrix (Fin n) (Fin n) L) * K * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map ι →
        mat g⁻¹ = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) +
          ((P : Matrix (Fin n) (Fin n) L) * K' * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map ι →
        g ∈ GlobalTheory.InertSph.KAt σ X v := by
  first | exact @GlobalTheory.InertKatFrame.mem_KAt_of_frame | exact GlobalTheory.InertKatFrame.mem_KAt_of_frame | (intros; apply GlobalTheory.InertKatFrame.mem_KAt_of_frame <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.exists_pow_idempotent_adelicLattice_mod_prime : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (W : Spc F E d),
    W.L.IsLattice E → ∀ (v : Pl (F := F)) (p : ℕ), 0 < p → (p : 𝓞 F) ∈ v.asIdeal →
    ∀ f : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (∀ z ∈ GlobalTheory.InertSph.latAt W v, f *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    ∃ N : ℕ, 0 < N ∧ ∀ z ∈ GlobalTheory.InertSph.latAt W v, ∃ y ∈ GlobalTheory.InertSph.latAt W v, (f ^ (2 * N)) *ᵥ z - (f ^ N) *ᵥ z = p • y := by
  first | exact @GlobalTheory.LatIdem.exists_pow_idem | exact GlobalTheory.LatIdem.exists_pow_idem | (intros; apply GlobalTheory.LatIdem.exists_pow_idem <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_frame_adelicLatticeAtFinitePlace_of_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ (n : ℕ) (X : Spc F E n), X.L.IsFullLattice E →
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      Function.Injective ι → (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) →
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) →
      ∃ P : GL (Fin n) L, (∀ x : Fin n → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((P : Matrix (Fin n) (Fin n) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt X v) := by
  first | exact @GlobalTheory.InertLocBasis.exists_basis_at_inert | exact GlobalTheory.InertLocBasis.exists_basis_at_inert | (intros; apply GlobalTheory.InertLocBasis.exists_basis_at_inert <;> assumption)
end
