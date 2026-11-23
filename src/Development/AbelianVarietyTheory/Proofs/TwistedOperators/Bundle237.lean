module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle178
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle036
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle055
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle042
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle040
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle230
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonCharacterDetEqOneInertPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1449
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle191
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle028
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle228
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle328
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle272
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle015

@[expose] public section

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical Matrix

namespace GlobalTheory.QuadFam

open GlobalTheory.RealWeil

theorem coordAll (hP : GlobalTheory.Published.RealMetaplecticRepresentation) (l : Type) [Fintype l] [DecidableEq l]
    (A : ℝ → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)) (T : ℝ → Sch l →ₗ[ℂ] Sch l)
    (hA : ∀ w, Continuous fun t => A t w) (hT : ∀ s t f, T (s + t) f = T s (T t f)) (hT0 : ∀ f, T 0 f = f)
    (hI : ∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(T t f₁) = rhoFun (A t w) ⇑(T t f))
    (hiso : ∀ t f, ∫ x, ‖T t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) (hpt : ∀ f y, Continuous fun t => T t f y) :
    ∃ (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (c : ℂ), ∀ f y, HasDerivAt (fun t => T t f y) (quad X f y + c * f y) 0 := by
  obtain ⟨hs, hgrp, h0⟩ := GlobalTheory.T.symplectic_and_flow_of_intertwining_unitary l A T hT hT0 hI hiso
  cases isEmpty_or_nonempty l with
  | inl hl =>
    have hq : ∀ f y, quad (0 : Matrix (l ⊕ l) (l ⊕ l) ℝ) f y = 0 := fun f y => by simp [quad]
    obtain ⟨c, hc⟩ := GlobalTheory.T.isometryFamilies_derivatives_differ_by_scalar_at_zero l (fun t w => A t w) T (fun _ => LinearMap.id) (fun f y => quad 0 f y) hT hT0
      (fun _ _ _ => rfl) (fun _ => rfl) hgrp h0 hI
      (fun t w f f₁ h => by
        rw [LinearMap.id_apply, LinearMap.id_apply, h, Subsingleton.elim (A t w) w]) hiso
      (fun _ _ => rfl) hpt (fun f y => by rw [hq]; exact hasDerivAt_const _ _)
    exact ⟨0, c, hc⟩
  | inr hl =>
    let M : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ := fun t => LinearMap.toMatrix' (A t)
    have hM : ∀ t w, M t *ᵥ w = A t w := fun t w => LinearMap.toMatrix'_mulVec (A t) w
    have hMc : Continuous M := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [M, LinearMap.toMatrix'_apply]
      exact (continuous_apply i).comp (hA _)
    have hM0 : M 0 = 1 := by
      have : A 0 = LinearMap.id := LinearMap.ext h0
      simp only [M, this, LinearMap.toMatrix'_id]
    have hMm : ∀ s t, M (s + t) = M s * M t := by
      intro s t
      have : A (s + t) = (A s).comp (A t) := LinearMap.ext (hgrp s t)
      simp only [M, this, LinearMap.toMatrix'_comp]
    obtain ⟨X, hX⟩ := GlobalTheory.T.continuous_matrix_oneParameterGroup_eq_exp _ M hMc hM0 hMm
    have hsp : X ∈ LieAlgebra.Symplectic.sp l ℝ := by
      refine GlobalTheory.T.mem_symplecticLieAlgebra_of_exp_smul_mem_symplecticGroup l X fun t => ?_
      obtain ⟨N, hN⟩ := GlobalTheory.exists_symplecticGroup_of_sympl l (A t) (hs t)
      have e : Matrix.toLin' (N : Matrix (l ⊕ l) (l ⊕ l) ℝ) = A t := LinearMap.ext fun w => by
        rw [Matrix.toLin'_apply, hN]
      have e2 : (N : Matrix (l ⊕ l) (l ⊕ l) ℝ) = M t := by
        simp only [M, ← e, LinearMap.toMatrix'_toLin']
      rw [← hX t, ← e2]
      exact N.2
    obtain ⟨U, hU, hU0, hUI, hUiso, hUd⟩ := GlobalTheory.T.metaplectic_oneParameter_schwartz_intertwining hP l X hsp
    have hB : ∀ t w, NormedSpace.exp (t • X) *ᵥ w = A t w := fun t w => by rw [← hX, hM]
    obtain ⟨c, hc⟩ := GlobalTheory.T.isometryFamilies_derivatives_differ_by_scalar_at_zero l (fun t w => A t w) T U (fun f y => quad X f y) hT hT0 hU hU0 hgrp h0 hI
      (fun t w f f₁ h => by rw [hUI t w f f₁ h, hB]) hiso hUiso hpt hUd
    exact ⟨X, c, hc⟩

theorem deriv_quad : GlobalTheory.Published.RealMetaplecticRepresentation → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V), μ.IsAddHaarMeasure → ∀ (P : V → V → ℝ), IsPairing P →
    ∀ (A : ℝ → (V × V) →ₗ[ℝ] (V × V)) (T : ℝ → 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ)),
    (∀ v, Continuous fun t => A t v) →
    (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) →
    (∀ t v (f f₁ : 𝓢(V, ℂ)), ⇑f₁ = schrF P v ⇑f → ⇑(T t f₁) = schrF P (A t v) ⇑(T t f)) →
    (∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    (∀ f y, Continuous fun t => T t f y) →
    (∀ f φ : 𝓢(V, ℂ), Continuous fun t => ∫ x, T t f x * starRingEnd ℂ (φ x) ∂μ) →
    ∃ (m : ℕ) (a b : Fin m → V × V) (c : Fin m → ℂ) (c₀ : ℂ), ∀ (f : 𝓢(V, ℂ)) (g₁ g₂ : Fin m → 𝓢(V, ℂ)),
      (∀ i y, g₁ i y = fderiv ℝ (⇑f) y (b i).1 - 2 * Real.pi * Complex.I * (P y (b i).2 : ℂ) * f y) →
      (∀ i y, g₂ i y = fderiv ℝ (⇑(g₁ i)) y (a i).1 - 2 * Real.pi * Complex.I * (P y (a i).2 : ℂ) * g₁ i y) →
      ∀ y, HasDerivAt (fun t => T t f y) (∑ i, c i * g₂ i y + c₀ * f y) 0 := by
  intro hP V _ _ _ _ _ μ hμ P hp A T hA hT hT0 hI hiso hpt _
  exact GlobalTheory.T.realPairingSpace_result_of_schrodingerCoordinates V μ hμ P hp _ rfl (fun A' T' => coordAll hP (Fin _) A' T') A T hA hT hT0 hI hiso hpt

end GlobalTheory.QuadFam
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SplitDetChr

open GlobalTheory.LFun GlobalTheory.Doubling

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem at_inFin (v : Pl (F := F)) (a : Fv F v) : At (evFin F v) (inFin v a) := by
  intro u hu
  have h := GlobalTheory.InertDetChr.at_inFin_one (F := F) v u hu
  rw [smul_eq_mul] at h ⊢
  rw [show a = 1 * a from (one_mul a).symm, inFin_mul, ← mul_assoc, h, zero_mul]

theorem compFin_smul_inclR (v : Pl (F := F)) (a : AF F) (y : E) :
    compFin F E v (a • inclR (F := F) (AF F) y) = evFin F v a ⊗ₜ[F] y := by
  rw [Algebra.smul_def, map_mul, GlobalTheory.InertDetChr.compFin_algebraMap]
  have : compFin F E v (inclR (F := F) (AF F) y) = (1 : Fv F v) ⊗ₜ[F] y := by
    show Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] y) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]; rfl
  rw [this]
  simp [Algebra.TensorProduct.algebraMap_apply]

theorem comp_mem_latLoc {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) {z : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)}
    (hz : z ∈ GlobalTheory.InertSph.latAt W v) : compFin F E v ∘ z ∈ latLoc F W.L v := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, ha, y, hy, rfl⟩ := hz
    convert tmul_mem_latLoc ha hy using 1
    funext i
    exact compFin_smul_inclR v a (y i)
  | zero =>
    convert zero_mem (latLoc F W.L v) using 1
    funext i; exact map_zero _
  | add x y _ _ hx hy =>
    convert add_mem hx hy using 1
    funext i; exact map_add _ _ _
  | neg x _ hx =>
    convert neg_mem hx using 1
    funext i; exact map_neg _ _

theorem mulVec_mem_latLoc {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (g : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hg : ∀ z ∈ GlobalTheory.InertSph.latAt W v, g *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    ∀ y ∈ latLoc F W.L v, (compFin F E v).mapMatrix g *ᵥ y ∈ latLoc F W.L v := by
  intro y hy
  refine latLoc_induction (p := fun y => (compFin F E v).mapMatrix g *ᵥ y ∈ latLoc F W.L v)
    (fun a ha x hx => ?_) (by rw [Matrix.mulVec_zero]; exact zero_mem _)
    (fun _ _ h h' => by rw [Matrix.mulVec_add]; exact add_mem h h')
    (fun _ h => by rw [Matrix.mulVec_neg]; exact neg_mem h) hy
  have hz : (inFin v a • fun i => inclR (F := F) (AF F) (x i)) ∈ GlobalTheory.InertSph.latAt W v :=
    AddSubgroup.subset_closure ⟨inFin v a, at_inFin v a, by rwa [GlobalTheory.InertDetChr.evFin_inFin_self], x, hx, rfl⟩
  have e1 : (fun i => a ⊗ₜ[F] x i) = compFin F E v ∘ (inFin v a • fun i => inclR (F := F) (AF F) (x i)) := by
    funext i
    show _ = compFin F E v (inFin v a • inclR (F := F) (AF F) (x i))
    rw [compFin_smul_inclR, GlobalTheory.InertDetChr.evFin_inFin_self]
  rw [e1]
  have e2 : (compFin F E v).mapMatrix g *ᵥ (compFin F E v ∘ (inFin v a • fun i => inclR (F := F) (AF F) (x i))) =
      compFin F E v ∘ (g *ᵥ (inFin v a • fun i => inclR (F := F) (AF F) (x i))) :=
    funext fun i => (RingHom.map_mulVec (compFin F E v) g _ i).symm
  rw [e2]
  exact comp_mem_latLoc W v (hg _ hz)

theorem det_mem_intLoc {d : ℕ} {L : Submodule (𝓞 E) (Fin d → E)} {v : Pl (F := F)} (P : GL (Fin d) (Fv F v ⊗[F] E))
    (hP : ∀ y : Fin d → Fv F v ⊗[F] E, (∀ i, y i ∈ intLoc F E v) ↔ P.1 *ᵥ y ∈ latLoc F L v)
    (g : GL (Fin d) (Fv F v ⊗[F] E)) (hg : ∀ y ∈ latLoc F L v, g.1 *ᵥ y ∈ latLoc F L v) :
    ((Matrix.GeneralLinearGroup.det g : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ intLoc F E v := by
  set Q : Matrix (Fin d) (Fin d) (Fv F v ⊗[F] E) := (P⁻¹ * g * P).1 with hQ
  have hent : ∀ i j, Q i j ∈ intLoc F E v := by
    intro i j
    have h1 : P.1 *ᵥ (Pi.single j 1) ∈ latLoc F L v := (hP _).1 (fun k => by
      by_cases e : k = j
      · subst e; simp
      · simp [e])
    have h2 := (hP (Q *ᵥ Pi.single j 1)).2 (by
      rw [hQ, Matrix.mulVec_mulVec, ← Units.val_mul, ← mul_assoc, mul_inv_cancel_left, Units.val_mul,
        ← Matrix.mulVec_mulVec]
      exact hg _ h1)
    have := h2 i
    rwa [Matrix.mulVec_single_one, Matrix.col_apply] at this
  let Q' : Matrix (Fin d) (Fin d) (intLoc F E v) := fun i j => ⟨Q i j, hent i j⟩
  have hQ' : (intLoc F E v).subtype.mapMatrix Q' = Q := rfl
  have hdet : Q.det = ((Matrix.GeneralLinearGroup.det g : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) := by
    rw [hQ, ← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_mul, map_inv,
      mul_comm _ (Matrix.GeneralLinearGroup.det P), ← mul_assoc, mul_inv_cancel, one_mul]
  rw [← hdet, ← hQ', ← RingHom.map_det]
  exact (Matrix.det Q').2

end GlobalTheory.SplitDetChr
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitChooseHerm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def scaleSpc {d : ℕ} (V : Spc F E d) (δ : E) : Spc F E d where
  J := δ • V.J
  L := V.L
  θ := V.θ
  bas := V.bas

theorem incM_smul {d : ℕ} (δ : E) (J : Matrix (Fin d) (Fin d) E) :
    incM F (δ • J) = inclR (F := F) (AF F) δ • incM F J := by
  ext i j
  simp [incM, Matrix.map_apply, Matrix.smul_apply, map_mul]

theorem dbl_smul {d : ℕ} (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (X : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : dbl (c • X) = c • dbl X := by
  simp [dbl, Matrix.fromBlocks_smul, smul_neg]

end GlobalTheory.SplitChooseHerm

namespace GlobalTheory.SplitChooseHerm

theorem exists_admissible_unipotent_split_place_hermitian : (∀ {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) O),
    IsUnit (Matrix.fromBlocks A B C D).det → ∃ X : Matrix (Fin n) (Fin n) O, IsUnit (A + X * C).det) →
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (V : Spc F E d) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ V v,
      ∃ Y : Matrix (Fin d) (Fin d) (AE F E), At (evFin F v) Y ∧
        (∀ z ∈ GlobalTheory.InertSph.latAt V v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt V v) ∧
        Yᵀ * incM F V.J + incM F V.J * Y.map (cA σ) = 0 ∧
        ∃ M : Matrix (Fin d) (Fin d) (AE F E), M * (GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂))) = 1 ∧
          ∀ z ∈ GlobalTheory.InertSph.latAt V v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt V v := by
  intro _ F E _ _ _ _ _ σ B d V r s hB hV v hv hψ h2 g hg
  obtain ⟨π₁, π₂, b₁, b₂, hP, S, hS, hSe⟩ := GlobalTheory.T.hermitian_selfDual_lattice_split_place_dictionary σ B V r s hB hV v hv hψ
  obtain ⟨δ, hδ, u, hu⟩ := GlobalTheory.T.exists_cmSkew_element_unit_at_finitePlace σ hB.cm v π₁ hP.2.2.1
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    have h0 : ((u : v.adicCompletionIntegers F) : Fv F v) = 0 := by rw [hu, map_zero, map_zero]
    exact u.ne_zero (Subtype.ext h0)
  have hcu : inclR (F := F) (AF F) δ⁻¹ * inclR (F := F) (AF F) δ = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hδ0, map_one]
  have h2' : IsUnit (2 : v.adicCompletionIntegers F) := by
    have := (GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v (2 : 𝓞 F)).2 h2
    rwa [map_ofNat] at this
  let W' : Spc F E d := scaleSpc V δ
  have hskew : ∀ i j, σ (W'.J j i) = -W'.J i j := by
    intro i j
    show σ (δ * V.J j i) = -(δ * V.J i j)
    rw [map_mul, hδ, hV.herm]
    ring
  have hS' : ∃ S' : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), IsUnit S'.det ∧
      S'.map (fun x => (x : Fv F v)) =
        (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W'.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) := by
    refine ⟨(u : v.adicCompletionIntegers F) • S, ?_, ?_⟩
    · rw [Matrix.det_smul]
      exact (u.isUnit.pow _).mul hS
    · have e1 : (incM F W'.J).map π₁ = π₁ (inclR (F := F) (AF F) δ) • (incM F V.J).map π₁ := by
        show (incM F (δ • V.J)).map π₁ = _
        rw [incM_smul]
        ext i j
        simp [Matrix.map_apply, Matrix.smul_apply]
      rw [e1, Matrix.mul_smul, Matrix.smul_mul, ← hSe, ← hu]
      ext i j
      simp [Matrix.map_apply, Matrix.smul_apply]
  let g' : GlobalTheory.DblVac.UD σ W' := ⟨g.1, by
    have h := g.2
    change ((g.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)))ᵀ * dbl (incM F V.J) *
      (g.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (cA σ) = dbl (incM F V.J) at h
    change ((g.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)))ᵀ * dbl (incM F (δ • V.J)) *
      (g.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (cA σ) = dbl (incM F (δ • V.J))
    rw [incM_smul, dbl_smul, Matrix.mul_smul, Matrix.smul_mul, h]⟩
  have hg' : g' ∈ GlobalTheory.DblVac.KD σ W' v := hg
  obtain ⟨Y, hYat, hYlat, hYadm, M, hM, hMlat⟩ :=
    GlobalTheory.T.splitPlace_bigCell_exists_admissible_inverse_alt GlobalTheory.T.exists_dual_pair_isUnit_det_blocks' σ W' v hskew h2' π₁ π₂ b₁ b₂ hP hS' g' hg'
  refine ⟨Y, hYat, hYlat, ?_, M, hM, hMlat⟩
  change Yᵀ * incM F (δ • V.J) + incM F (δ • V.J) * Y.map (cA σ) = 0 at hYadm
  rw [incM_smul, Matrix.mul_smul, Matrix.smul_mul, ← smul_add] at hYadm
  have h3 := congrArg (fun X => inclR (F := F) (AF F) δ⁻¹ • X) hYadm
  simp only [smul_smul, hcu, one_smul, smul_zero] at h3
  exact h3

end GlobalTheory.SplitChooseHerm
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitProjChart

variable {D : D7} {v : FinPl D}

def emb (φ : SplitProj D v) : D.host.E →ₐ[D.host.F] Fv D.host.F v :=
  (φ.restrictScalars D.host.F).comp Algebra.TensorProduct.includeRight

theorem emb_apply (φ : SplitProj D v) (x : D.host.E) : emb φ x = rdQ φ x := rfl

theorem splitProj_emb (φ : SplitProj D v) : GlobalTheory.AdelicU.splitProj (emb φ) = φ := by
  refine AlgHom.ext fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x =>
    rw [GlobalTheory.AdelicU.splitProj_tmul, emb_apply, rdQ, ← smul_eq_mul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul,
      mul_one]

theorem chart_idem (φ : SplitProj D v) : GlobalTheory.SplitHecke.Chart (GlobalTheory.EmbChart.idem (emb φ)) v (rdA φ) := by
  have h := GlobalTheory.EmbChart.chart_idem (emb φ)
  rw [splitProj_emb] at h
  exact h

theorem rdA_idem (φ : SplitProj D v) : rdA φ (GlobalTheory.EmbChart.idem (emb φ)) = 1 := by
  change φ (GlobalTheory.AdelicU.compFin D.host.F D.host.E v (GlobalTheory.EmbChart.idem (emb φ))) = 1
  rw [GlobalTheory.EmbChart.compFin_idem]
  nth_rewrite 1 [← splitProj_emb φ]
  exact GlobalTheory.AdelicU.splitProj_splitIdem _ _

theorem eq_idem {φ : SplitProj D v} {e : AE D} (he : IsIdemOf φ e) : e = GlobalTheory.EmbChart.idem (emb φ) := by
  refine (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero he.1 (GlobalTheory.EmbChart.isSplitIdem_idem _)).resolve_right fun h => ?_
  have := congrArg (rdA φ) h
  rw [map_mul, he.2.2, rdA_idem, map_zero, mul_one] at this
  exact one_ne_zero this

theorem rdE_toEAf (φ : SplitProj D v) (a : AE D) : rdE φ (toEAf D a) = rdA φ a := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem rdA_incA (φ : SplitProj D v) (x : D.host.E) : rdA φ (incA D x) = rdQ φ x := by
  change φ (GlobalTheory.AdelicU.evFin D.host.F v 1 ⊗ₜ x) = _
  rw [map_one]; rfl

theorem continuous_rdA (φ : SplitProj D v) : Continuous (rdA φ) := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  refine IsModuleTopology.continuous_of_ringHom (R := AF D.host.F) (rdA φ) ?_
  have h1 : Continuous (GlobalTheory.AdelicU.evFin D.host.F v) := (RestrictedProduct.continuous_eval v).comp continuous_snd
  exact h1.congr fun y => ((chart_idem φ).2.2.1 y).symm

theorem chart_rdA : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → GlobalTheory.SplitHecke.Chart e v (rdA φ) ∧ (∀ a : AE D, rdE φ (toEAf D a) = rdA φ a) ∧ (∀ x : D.host.E, rdA φ (incA D x) = rdQ φ x) ∧ Continuous (rdA φ) ∧ ∀ e', IsIdemOf φ e' → e' = e :=
  fun _ _ φ _ he => ⟨eq_idem he ▸ chart_idem φ, rdE_toEAf φ, rdA_incA φ, continuous_rdA φ,
    fun _ he' => (eq_idem he').trans (eq_idem he).symm⟩

end GlobalTheory.SplitProjChart

end
end

section

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.Pj
  Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoActRoad

section Lattice

variable {D : D7} {V : HSp D}

variable {β : GL (Fin V.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}

theorem le_of_half {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {l : Level H} {Pg : Finset (Pl D.host.E)}
    (h : l.Mb = ∏ w ∈ Pg, w.asIdeal) {w : Pl D.host.E} (hw : w ∈ Pg) : l.Mb ≤ w.asIdeal :=
  h.le.trans (Ideal.prod_le_inf.trans (Finset.inf_le hw))

end Lattice

section Group

variable {D : D7} {V : HSp D} (β : GL (Fin V.rank) (EAf D))

variable {β} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {H H' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}

theorem liftsExist_of_half (hβ : IsSDFrame V β Λ 1) (l : Level H) (L : LevDat D.host.E ℂ V.rank) (hQ : L.Q = ∅)
    (h : l.Mb = ∏ w ∈ L.Pg, w.asIdeal) : LiftsExist V β L := by
  obtain ⟨c, hc⟩ := hβ
  refine GlobalTheory.ParahoricLift.liftsExist _ _ _ _ _ hc (fun PP h1 PP' h' => ?_) (hQ ▸ Finset.disjoint_empty_right _)
  rcases h' with h' | h'
  · exact GlobalTheory.LevelAction.not_isConjPl l (le_of_half h h1) (le_of_half h h')
  · exact absurd (hQ ▸ h') (Finset.notMem_empty _)

end Group

section Record

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}


open Classical in
theorem exists_half_prod {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : Level H) (hM : l.M = D.host.g 0 * D.host.g 1) :
    (∀ Pg : Finset (Pl D.host.E), (∀ w, w ∈ Pg ↔ l.Mb ≤ w.asIdeal) → l.Mb = ∏ w ∈ Pg, w.asIdeal) ∧
      ∃ Pg : Finset (Pl D.host.E), l.Mb = ∏ w ∈ Pg, w.asIdeal := by
  have hprod := l.prod
  rw [hM] at hprod
  have hs : Squarefree l.Mb := (hprod ▸ GlobalTheory.CoverHalf.squarefree_span_g D : Squarefree (l.Mb * _)).of_mul_left
  refine ⟨fun Pg h => GlobalTheory.CoverHalf.eq_prod_of_squarefree hs _ h,
    (Ideal.finite_factors hs.ne_zero).toFinset, GlobalTheory.CoverHalf.eq_prod_of_squarefree hs _ fun w => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le]

theorem mem_Pg_iff {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) (w : Pl D.host.E) :
    w ∈ L.Pg ↔ (GlobalTheory.HalfOnRecord.designLevel L.C.P).Mb ≤ w.asIdeal := by
  rw [hL.Pg, GlobalTheory.HalfOnRecord.designLevel_Mb, GlobalTheory.CoverHalf.prod_map_le_iff]
  rfl

theorem designLevel_prod {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) :
    (GlobalTheory.HalfOnRecord.designLevel L.C.P).Mb = ∏ w ∈ L.Pg, w.asIdeal :=
  (exists_half_prod _ rfl).1 _ (mem_Pg_iff hL)

theorem levelLiftsExist_gridVertexSpaces {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) (i : Fin D.R.m) :
    LiftsExist (Wc D i) (L.βW i) (L.datWp i L.triv) :=
  liftsExist_of_half (hL.βW i) (GlobalTheory.HalfOnRecord.designLevel L.C.P) _ rfl (designLevel_prod hL)

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)

end Record

section Main

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

open GlobalTheory.IndefiniteRowSideFullHecke.LevelGroupLifts (LevGrp IsGeoRep UnitConstEquivariant)
open GlobalTheory.IndefiniteRowSideFullHecke.GeometricConstantEquiv (Cusp IsGeo ReadTwist KeepsIntegral ConstEquiv GeoActAt)

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}

end Main

end GlobalTheory.GeoActRoad
end
end
