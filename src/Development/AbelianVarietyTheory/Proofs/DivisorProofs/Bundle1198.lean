module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigCellFactorisationDoubledUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialOfLocal
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SiegelThetaInvT

private theorem invTranspose_abstract {E A n : Type} [Field E] [CommRing A] [Fintype n] [DecidableEq n]
    (ι : E →+* A) (c : A →+* A) (G J : Matrix n n E) (hG : G.det ≠ 0) (x : E) (hx : x ≠ 0) (ξ : A)
    (hξ : ξ • J.map ι = (x • G⁻¹).map ι) (M N : Matrix n n A) (hMN : M * N = 1) (hNM : N * M = 1)
    (hb : Mᵀ * J.map ι * M.map c = J.map ι) :
    (Nᵀ.map c)ᵀ * G.map ι * Nᵀ = G.map ι := by
  have hdet : IsUnit G.det := isUnit_iff_ne_zero.2 hG
  have hKG : G⁻¹.map ι * G.map ι = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hGK : G.map ι * G⁻¹.map ι = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hsm : (x • G⁻¹).map ι = ι x • G⁻¹.map ι := by
    ext i j
    simp [smul_eq_mul, map_mul]
  have hd : ι x⁻¹ * ι x = 1 := by rw [← map_mul, inv_mul_cancel₀ hx, map_one]
  generalize G⁻¹.map ι = K at hKG hGK hsm
  generalize G.map ι = G' at hKG hGK ⊢
  have h1 : ι x • (Mᵀ * K * M.map c) = ι x • K := by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← hsm, ← hξ, Matrix.mul_smul, Matrix.smul_mul, hb]
  have h2 : Mᵀ * K * M.map c = K := by
    have := congrArg (fun X => ι x⁻¹ • X) h1
    simpa only [smul_smul, hd, one_smul] using this
  have hcNM : N.map c * M.map c = 1 := by
    rw [← Matrix.map_mul, hNM]
    exact Matrix.map_one _ (map_zero c) (map_one c)
  have hX : N.map c * G' * Nᵀ * K = 1 := by
    calc N.map c * G' * Nᵀ * K = N.map c * G' * Nᵀ * (Mᵀ * K * M.map c) := by rw [h2]
      _ = N.map c * G' * ((M * N)ᵀ * K) * M.map c := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = N.map c * M.map c := by
          rw [hMN, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_assoc (N.map c), hGK, Matrix.mul_one]
      _ = 1 := hcNM
  have hT : (Nᵀ.map c)ᵀ = N.map c := rfl
  rw [hT]
  calc N.map c * G' * Nᵀ = N.map c * G' * Nᵀ * (K * G') := by rw [hKG, Matrix.mul_one]
    _ = G' := by rw [← Matrix.mul_assoc, hX, Matrix.one_mul]

private def invT {A n : Type} [CommRing A] [Fintype n] [DecidableEq n] (m : GL n A) : GL n A :=
  ⟨(m⁻¹).1ᵀ, m.1ᵀ, by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩

private theorem sigR_eq_cA {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) (x : AF F ⊗[F] E) : sigR (AF F) σ x = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

private theorem invT_mem_HR {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {r : ℕ}
    (G J : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (x : E) (hx : x ≠ 0) (ξ : AF F ⊗[F] E)
    (hξ : ξ • incM F J = incM F (x • G⁻¹))
    (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (incM F J)) :
    ∃ g : HR (AF F) σ G, g.1.1 = (b⁻¹).1.1ᵀ := by
  obtain ⟨m, hm⟩ := b
  have hb : m.1ᵀ * incM F J * m.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) = incM F J := hm
  have hc : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ : AF F ⊗[F] E → AF F ⊗[F] E) = sigR (AF F) σ :=
    funext fun y => (sigR_eq_cA σ y).symm
  rw [hc] at hb
  have key := invTranspose_abstract (inclR (F := F) (AF F)) (sigR (AF F) σ) G J hG x hx ξ hξ m.1 (m⁻¹).1
    (Units.mul_inv m) (Units.inv_mul m) hb
  exact ⟨⟨invT m, key⟩, rfl⟩

theorem _root_.GlobalTheory.T.exists_unitary_invTranspose_of_scaledInverseGram : ∀ (D : D7) (V : HSp D) (J : Matrix (Fin V.rank) (Fin V.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E), ξ • incM D.host.F J = incM D.host.F (D.host.xi0 • V.gram⁻¹) →
    ∀ b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F J),
      ∃ g : GA D V, Formalism.L2.Theta.mt V g = (b⁻¹).1.1ᵀ := by
  intro D V J ξ hξ b
  obtain ⟨g, hg⟩ := invT_mem_HR D.sp.cm.sig V.gram J (GlobalTheory.Doubling.isHermND_gram V).2 D.host.xi0
    (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D) ξ hξ b
  exact ⟨g, hg⟩

end GlobalTheory.SiegelThetaInvT
end
end

section

noncomputable section

namespace GlobalTheory.ThK.ConeEuler.UnitsOpen

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

section Lemmas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isOpen_integral_everywhere : IsOpen {z : AE F E | ∀ v : Pl F, compFin F E v z ∈ intLoc F E v} := by
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  let S : AddSubgroup (AE F E) :=
    { carrier := {z | ∀ v : Pl F, compFin F E v z ∈ intLoc F E v}
      zero_mem' := fun v => by rw [map_zero]; exact zero_mem _
      add_mem' := fun ha hb v => by rw [map_add]; exact add_mem (ha v) (hb v)
      neg_mem' := fun ha v => by rw [map_neg]; exact neg_mem (ha v) }
  let b := integralBasis E
  let φ : (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → AF F) →ₗ[AF F] AE F E :=
    Fintype.linearCombination (AF F) fun i => (1 : AF F) ⊗ₜ[F] b i
  have hφ : ∀ a, φ a = ∑ i, a i ⊗ₜ[F] b i := fun a => by
    simp only [φ, Fintype.linearCombination_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hq : ∀ (c : ℚ) (a : AF F) (x : E), a ⊗ₜ[F] (c • x) = (algebraMap F (AF F) (c : F) * a) ⊗ₜ[F] x := fun c a x => by
    rw [show c • x = (c : F) • x by rw [Rat.cast_smul_eq_qsmul], ← TensorProduct.smul_tmul, Algebra.smul_def]
  have hsurj : Function.Surjective φ := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul a x =>
      refine ⟨fun i => algebraMap F (AF F) (b.repr x i : F) * a, ?_⟩
      rw [hφ]
      conv_rhs => rw [← b.sum_repr x, TensorProduct.tmul_sum]
      exact Finset.sum_congr rfl fun i _ => (hq _ _ _).symm
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨c, rfl⟩ := hy
      exact ⟨a + c, map_add _ _ _⟩
  let W : Set (AF F) := {a | ∀ v, evFin F v a ∈ v.adicCompletionIntegers F}
  have ho : IsOpen W :=
    (RestrictedProduct.isOpen_forall_mem fun v : HeightOneSpectrum (𝓞 F) =>
      Valued.isOpen_valuationSubring (v.adicCompletion F)).preimage continuous_snd
  have hopen : IsOpen (φ '' Set.univ.pi fun _ => W) :=
    (IsModuleTopology.isOpenQuotientMap_of_surjective hsurj).isOpenMap _
      (isOpen_set_pi Set.finite_univ fun _ _ => ho)
  have hsub : φ '' (Set.univ.pi fun _ => W) ⊆ (S : Set (AE F E)) := by
    rintro _ ⟨a, ha, rfl⟩ v

    rw [hφ, map_sum]
    refine sum_mem fun i _ => ?_
    rw [show b i = ((RingOfIntegers.basis E i : 𝓞 E) : E) from integralBasis_apply E i]
    exact tmul_mem_intLoc (ha i (Set.mem_univ i) v) _
  have h0 : (0 : AE F E) ∈ φ '' (Set.univ.pi fun _ => W) :=
    ⟨0, fun i _ v => by simp, map_zero φ⟩
  exact (AddSubgroup.isOpen_of_mem_nhds S (g := 0) (Filter.mem_of_superset (hopen.mem_nhds h0) hsub) :
    IsOpen (S : Set (AE F E)))

end Lemmas

end GlobalTheory.ThK.ConeEuler.UnitsOpen

namespace GlobalTheory.ThK.ConeEuler

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

end GlobalTheory.ThK.ConeEuler
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section
namespace GlobalTheory.ThetaRatGen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem inclR_inj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 F) (K := F))

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem exists_eval_ne (ψ : Polynomial E) (hψ : ψ ≠ 0) : ∃ t : F, ψ.eval (algebraMap F E t) ≠ 0 := by
  classical
  haveI : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
  have hinf : (Set.range (algebraMap F E)).Infinite := Set.infinite_range_of_injective (algebraMap F E).injective
  obtain ⟨y, ⟨t, rfl⟩, hy⟩ := hinf.exists_notMem_finset ψ.roots.toFinset
  refine ⟨t, fun h => hy ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hψ]
  exact h

theorem hyp1 : ∀ ψ : Polynomial E, (∀ (Ω : Type) [Field Ω] (φ : E →+* Ω), φ 1 = 1 → ψ.map φ ≠ 0) →
    ∃ t : F, IsUnit ((1 : E) * ψ.eval (algebraMap F E t) + (1 - 1)) := by
  intro ψ h
  have hψ : ψ ≠ 0 := by simpa using h E (RingHom.id E) (map_one _)
  obtain ⟨t, ht⟩ := exists_eval_ne (F := F) ψ hψ
  exact ⟨t, by simpa using ht⟩

theorem invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem exists_anti {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ ρ : E, ρ ≠ 0 ∧ σ ρ = -ρ := by
  have hne : σ ≠ AlgHom.id F E := by
    intro hσ
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have := h.2.1
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have := h.2.2.2 τ x
    rw [hσ] at this
    simpa [ComplexEmbedding.conjugate_coe_eq] using this.symm
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra hc
    push_neg at hc
    exact hne (AlgHom.ext hc)
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩
  rw [map_sub, invol h]
  ring

variable (F) in
theorem incM_mul {m n k : Type} [Fintype n] (A : Matrix m n E) (B : Matrix n k E) :
    incM F (A * B) = incM F A * incM F B := Matrix.map_mul

variable (F) in
theorem incM_dbl {β : Type} (J : Matrix β β E) : incM F (dbl J) = dbl (incM F J) := by
  ext i j
  cases i <;> cases j <;> simp [incM, dbl]

theorem incM_map (σ : E →ₐ[F] E) {m n : Type} (A : Matrix m n E) : (incM F A).map (cA σ) = incM F (A.map σ) := by
  ext i j
  simp [incM, cA_inclR]

variable (F) in
theorem incM_transpose {m n : Type} (A : Matrix m n E) : (incM F A)ᵀ = incM F Aᵀ := rfl

variable (F) in
theorem incM_diag {β : Type} [DecidableEq β] :
    incM F (Matrix.fromRows (1 : Matrix β β E) (1 : Matrix β β E)) = Matrix.fromRows (1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) 1 := by
  simp [incM, Matrix.fromRows_map]

variable (F) in
theorem incM_nabla {β : Type} [DecidableEq β] :
    incM F (Matrix.fromRows (1 : Matrix β β E) (-1 : Matrix β β E)) = Matrix.fromRows (1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (-1) := by
  simp [incM, Matrix.fromRows_map, Matrix.map_neg _ (map_neg (inclR (F := F) (E := E) (AF F)))]

theorem incM_inj {m n : Type} {A B : Matrix m n E} (h : incM F A = incM F B) : A = B := by
  ext i j
  exact inclR_inj (congrFun (congrFun h i) j)

def up (σ : E →ₐ[F] E) {b : ℕ} (JB : Matrix (Fin b) (Fin b) E) (p : UG σ (dbl JB)) : UG (cA σ) (dbl (incM F JB)) :=
  ⟨Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) p.1, by
    have hp : ((p.1 : Matrix _ _ E))ᵀ * dbl JB * (p.1 : Matrix _ _ E).map σ = dbl JB := p.2
    show (incM F (p.1 : Matrix _ _ E))ᵀ * dbl (incM F JB) * (incM F (p.1 : Matrix _ _ E)).map (cA σ) = dbl (incM F JB)
    rw [incM_map, ← incM_dbl, incM_transpose, ← incM_mul, ← incM_mul, hp]⟩

theorem up_mul (σ : E →ₐ[F] E) {b : ℕ} (JB : Matrix (Fin b) (Fin b) E) (p q : UG σ (dbl JB)) :
    up σ JB (p * q) = up σ JB p * up σ JB q :=
  Subtype.ext (map_mul _ _ _)

theorem down (σ : E →ₐ[F] E) {b : ℕ} (JB : Matrix (Fin b) (Fin b) E) (g : UG (cA σ) (dbl (incM F JB)))
    (g₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E)
    (hg : ((g : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix _ _ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F g₀) :
    ∃ g₁ : UG σ (dbl JB), ((g₁ : GL (Fin b ⊕ Fin b) E) : Matrix _ _ E) = g₀ ∧ g = up σ JB g₁ := by
  have hdet : IsUnit g₀.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have hu : IsUnit (g.1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).det :=
      (Matrix.isUnit_iff_isUnit_det (g.1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))).mp (Units.isUnit _)
    have e : (incM F g₀).det = inclR (F := F) (AF F) g₀.det := (RingHom.map_det _ _).symm
    rw [hg, e, h0, map_zero, isUnit_zero_iff] at hu
    exact zero_ne_one (inclR_inj (F := F) (E := E) (by rw [map_zero, map_one]; exact hu))
  have hu : IsUnit g₀ := (Matrix.isUnit_iff_isUnit_det _).mpr hdet
  have hmem : hu.unit ∈ UG σ (dbl JB) := by
    show (hu.unit : Matrix _ _ E)ᵀ * dbl JB * (hu.unit : Matrix _ _ E).map σ = dbl JB
    rw [IsUnit.unit_spec]
    have h2 : ((g : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix _ _ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ * dbl (incM F JB) *
        ((g : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix _ _ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).map (cA σ) = dbl (incM F JB) := g.2
    rw [hg, incM_map, ← incM_dbl, incM_transpose, ← incM_mul, ← incM_mul] at h2
    exact incM_inj h2
  refine ⟨⟨hu.unit, hmem⟩, IsUnit.unit_spec hu, Subtype.ext (Units.ext ?_)⟩
  rw [hg]
  exact (congrArg (incM F) (IsUnit.unit_spec hu)).symm

end GlobalTheory.ThetaRatGen

namespace GlobalTheory.ThetaRatGen

theorem gen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (b : ℕ) (JB : Matrix (Fin b) (Fin b) E) (ε : ℤˣ), (∀ i j, σ (JB j i) = ((ε : ℤ) : E) * JB i j) → JB.det ≠ 0 → ∀ (g : UG (cA σ) (dbl (incM F JB))) (g₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E), ((g : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = incM F g₀ → ∃ (p q p' : UG (cA σ) (dbl (incM F JB))) (p₀ q₀ p₀' : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) (t s t' : GL (Fin b) (AE F E)), ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = incM F p₀ ∧ ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = incM F q₀ ∧ ((p' : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = incM F p₀' ∧ ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * diagCols (Fin b) = diagCols (Fin b) * (t : Matrix (Fin b) (Fin b) (AE F E)) ∧ ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) = Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) * (s : Matrix (Fin b) (Fin b) (AE F E)) ∧ ((p' : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * diagCols (Fin b) = diagCols (Fin b) * (t' : Matrix (Fin b) (Fin b) (AE F E)) ∧ g = p * q * p' := by
  intro F E _ _ _ _ _ σ hσ b JB ε hJ hdet g g₀ hg
  haveI : Invertible (2 : E) := invertibleOfNonzero two_ne_zero
  obtain ⟨g₁, -, rfl⟩ := down σ JB g g₀ hg
  set G : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E := (g₁.1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) with hG
  set H : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E :=
    ((g₁.1⁻¹ : GL (Fin b ⊕ Fin b) E) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) with hH
  set Nt : Matrix (Fin b) (Fin b ⊕ Fin b) E := Matrix.fromCols 1 (-1) with hNt
  set N : Matrix (Fin b ⊕ Fin b) (Fin b) E := Matrix.fromRows 1 (-1) with hN
  set Dt : Matrix (Fin b) (Fin b ⊕ Fin b) E := Matrix.fromCols 1 1 with hDt
  set Δ : Matrix (Fin b ⊕ Fin b) (Fin b) E := Matrix.fromRows 1 1 with hΔ
  have hGH : G * H = 1 := by rw [hG, hH, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hNN : Nt * N = (2 : E) • 1 := by
    rw [hNt, hN, Matrix.fromCols_mul_fromRows]
    simp [two_smul]
  have e2' : Δ * Dt + N * Nt = (2 : E) • 1 := GlobalTheory.BigCell.e2
  have hPQ : (Nt * G * N) * ((4 : E)⁻¹ • (Nt * H * N)) + (Nt * G * Δ) * ((4 : E)⁻¹ • (Dt * H * N)) = 1 := by
    calc _ = (4 : E)⁻¹ • (Nt * G * (Δ * Dt + N * Nt) * H * N) := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, smul_add, Matrix.mul_assoc]
          abel
      _ = 1 := by
          rw [e2']
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
          rw [show Nt * G * H * N = Nt * N by rw [Matrix.mul_assoc Nt G H, hGH, Matrix.mul_one], hNN, smul_smul]
          norm_num
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.T.exists_corner_unit_of_right_inverse' (F := F) (1 : E) (mul_one 1) hyp1 _ _ _ _ hPQ
  obtain ⟨ρ, hρ0, hρ⟩ := exists_anti hσ
  have hJ' : (JB.map (σ : E →+* E))ᵀ = ((ε : ℤ) : E) • JB := by
    ext i j
    simp [hJ]
  obtain ⟨x, hxS, hx⟩ := GlobalTheory.T.exists_conj_skew_det_unit_of_avoidance' (F := F) (σ : E →+* E) (invol hσ) (fun t => σ.commutes t) 1 hyp1 ρ
    (isUnit_iff_ne_zero.mpr hρ0) hρ JB ε hJ' (isUnit_iff_ne_zero.mpr hdet) _ _ x₀ hx₀
  obtain ⟨p, hpΔ, hcorner⟩ := GlobalTheory.T.siegelUnipotent_antidiagonal_corner (R₀ := F) σ JB x hxS
  have hunit : IsUnit (Matrix.fromCols (1 : Matrix (Fin b) (Fin b) E) (-1 : Matrix (Fin b) (Fin b) E) *
      (((g₁ * p : UG σ (dbl JB)) : GL (Fin b ⊕ Fin b) E) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) *
      Matrix.fromRows (1 : Matrix (Fin b) (Fin b) E) (-1 : Matrix (Fin b) (Fin b) E)).det := by
    rw [Subgroup.coe_mul, Units.val_mul, hcorner]
    have hx' : IsUnit (Nt * G * N + Nt * G * Δ * x).det := by simpa using hx
    exact hx'
  obtain ⟨p₀, q₀, t, s, hp₀, hq₀, hpq⟩ := GlobalTheory.BigCell.bigCell_factor F E σ (Fin b) JB (g₁ * p) hunit
  have hg₁ : g₁ = p₀ * q₀ * p⁻¹ := eq_mul_inv_of_mul_eq hpq
  have hpinv : ((p⁻¹ : UG σ (dbl JB)).1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) *
      (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) E) = (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) E) := by
    have h1 : (p.1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) * (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) E) =
        (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) E) := by
      exact hpΔ.trans (Matrix.mul_one _)
    calc _ = ((p⁻¹ : UG σ (dbl JB)).1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) *
          ((p.1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) *
            (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) E)) := by rw [h1]
      _ = diagCols (Fin b) := by
          rw [← Matrix.mul_assoc, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one,
            Matrix.one_mul]
  refine ⟨up σ JB p₀, up σ JB q₀, up σ JB p⁻¹, p₀.1, q₀.1, (p⁻¹).1,
    Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) t,
    Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) s, 1, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · have h := congrArg (incM F) hp₀
    rw [incM_mul, incM_mul, incM_diag] at h
    exact h
  · have h := congrArg (incM F) hq₀
    rw [incM_mul, incM_mul, incM_nabla] at h
    exact h
  · have h := congrArg (incM F) hpinv
    rw [incM_mul, diagCols, incM_diag] at h
    exact h.trans (Matrix.mul_one _).symm
  · rw [hg₁, up_mul, up_mul]

end GlobalTheory.ThetaRatGen
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
open Filter Topology

noncomputable section

namespace GlobalTheory.UnitaryCutoff

section Mix

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

def mix (e : R) (A : Matrix ι ι R) : Matrix ι ι R := e • A + (1 - e) • (1 : Matrix ι ι R)

theorem mix_mul_mul {e : R} (he : e * e = e) (A C B : Matrix ι ι R) :
    mix e A * C * mix e B = e • (A * C * B) + (1 - e) • C := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h1, sub_zero]
  simp only [mix, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one,
    he, h1, h2, h3, zero_smul, add_zero, zero_add]

theorem mix_mul {e : R} (he : e * e = e) (A B : Matrix ι ι R) :
    mix e A * mix e B = e • (A * B) + (1 - e) • (1 : Matrix ι ι R) := by
  have := mix_mul_mul he A 1 B
  rwa [Matrix.mul_one, Matrix.mul_one] at this

theorem mix_transpose (e : R) (A : Matrix ι ι R) : (mix e A)ᵀ = mix e Aᵀ := by
  simp [mix, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one]

theorem mix_map {S : Type} [CommRing S] [Algebra S R] (c : R →ₐ[S] R) {e : R} (hc : c e = e) (A : Matrix ι ι R) :
    (mix e A).map c = mix e (A.map c) := by
  ext i j
  simp only [mix, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  split_ifs <;> simp [hc]

end Mix

section Adele

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tendsto_mix_fin {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (AE F E)) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) =>
      mix (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)) M) atTop (𝓝 M) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h := (GlobalTheory.LocalGlobalChar.tendsto_eps_tens ((M - 1) i j)).add_const ((1 : Matrix ι ι (AE F E)) i j)
  rw [Matrix.sub_apply, sub_add_cancel] at h
  refine h.congr fun S => ?_
  simp only [mix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end Adele

theorem exists_approx : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {ι : Type} [Fintype ι] [DecidableEq ι] (J₀ : Matrix ι ι (AE F E)) (g : UG (cA σ) J₀), ∃ q : Finset (HeightOneSpectrum (𝓞 F)) → UG (cA σ) J₀, (∀ S, ((q S).1.1 : Matrix ι ι (AE F E)) = algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) • (g.1.1 : Matrix ι ι (AE F E)) + (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)) • (1 : Matrix ι ι (AE F E))) ∧ Tendsto q atTop (𝓝 g) := by
  intro F E _ _ _ _ _ σ ι _ _ J₀ g
  let e : Finset (HeightOneSpectrum (𝓞 F)) → AE F E := fun S => algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)
  have he : ∀ S, e S * e S = e S := fun S => by
    simp only [e]; rw [← map_mul, GlobalTheory.LocalGlobalChar.eps_mul_self]
  have hc : ∀ S, cA σ (e S) = e S := fun S => (cA σ).commutes _
  have hg : (g.1.1)ᵀ * J₀ * (g.1.1).map (cA σ) = J₀ := g.2
  have hs : ∀ S, e S • (1 : Matrix ι ι (AE F E)) + (1 - e S) • 1 = 1 := fun S => by
    rw [← add_smul, add_sub_cancel, one_smul]
  let u : Finset (HeightOneSpectrum (𝓞 F)) → GL ι (AE F E) := fun S =>
    ⟨mix (e S) g.1.1, mix (e S) g.1.inv, by rw [mix_mul (he S), g.1.val_inv, hs],
      by rw [mix_mul (he S), g.1.inv_val, hs]⟩
  have hu : ∀ S, u S ∈ UG (cA σ) J₀ := fun S => by
    show (mix (e S) g.1.1)ᵀ * J₀ * (mix (e S) g.1.1).map (cA σ) = J₀
    rw [mix_transpose, mix_map (cA σ) (hc S), mix_mul_mul (he S), hg,
      ← add_smul, add_sub_cancel, one_smul]
  refine ⟨fun S => ⟨u S, hu S⟩, fun S => rfl, ?_⟩
  refine (Topology.IsEmbedding.subtypeVal.tendsto_nhds_iff).2 ?_
  refine (Units.isEmbedding_embedProduct.tendsto_nhds_iff).2 ?_
  refine Tendsto.prodMk_nhds (tendsto_mix_fin g.1.1) ?_
  exact (MulOpposite.continuous_op.tendsto _).comp (tendsto_mix_fin g.1.inv)

end GlobalTheory.UnitaryCutoff

end
end
