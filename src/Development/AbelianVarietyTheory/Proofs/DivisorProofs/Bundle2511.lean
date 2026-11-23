module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2136
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle265
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelSumEqFinsumRegularRationalClasses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1757
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1756
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1741
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1767
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2388
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2482
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2153
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1922
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertSphLeft

open GlobalTheory.InertSph

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hTens_eq_left {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type} [Fintype α]
    [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (x y : Matrix α β A) :
    hTens c JA JB x y = ∑ j, ∑ l, JB j l * (xᵀ * JA * y.map c) j l := by
  simp only [hTens, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm, Finset.sum_comm (γ := β)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem symp_mul_left {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (c : A →ₐ[R] A) {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] (ξ : A) (JA : Matrix α α A)
    (JB : Matrix β β A) (g : Matrix α α A) (hg : gᵀ * JA * g.map c = JA) (x : Matrix α β A) :
    symp c ξ JA JB (g * x) (g * x) = symp c ξ JA JB x x := by
  have e : (g * x)ᵀ * JA * (g * x).map c = xᵀ * JA * x.map c := by
    have hm : (g * x).map c = g.map c * x.map c := Matrix.map_mul (f := c.toRingHom)
    rw [hm, Matrix.transpose_mul]
    calc xᵀ * gᵀ * JA * (g.map c * x.map c) = xᵀ * (gᵀ * JA * g.map c) * x.map c := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg]
  unfold symp
  rw [hTens_eq_left, hTens_eq_left, e]

variable {σ : E →ₐ[F] E}

theorem vecMulVec_mem_latAtV_left {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {y : Fin d → E} (hy : y ∈ W.L)
    {z : Fin n → AE F E} (hz : z ∈ latAt X v) :
    Matrix.vecMulVec z (fun i => inclR (F := F) (AF F) (y i)) ∈ latAtV X W v := by
  let f : (Fin n → AE F E) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    { toFun := fun z => Matrix.vecMulVec z (fun i => inclR (F := F) (AF F) (y i))
      map_zero' := by ext i j; simp [Matrix.vecMulVec_apply]
      map_add' := fun z z' => by ext i j; simp [Matrix.vecMulVec_apply, add_mul] }
  have : latAt X v ≤ (latAtV X W v).comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, hai, x, hx, rfl⟩
    refine AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, y, hy, ?_⟩
    ext i j
    simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, incM,
      Matrix.map_apply, map_mul, Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply]
    ring
  exact this hz

theorem mul_left_inv_mem_latAtV {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {g : UA σ X.J}
    (hg : g ∈ KAt σ X v) {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X W v) :
    mat g⁻¹ * γ ∈ latAtV X W v := by
  let f : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    { toFun := fun γ => mat g⁻¹ * γ
      map_zero' := by simp
      map_add' := fun γ γ' => by simp [Matrix.mul_add] }
  have : latAtV X W v ≤ (latAtV X W v).comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, hai, x, hx, y, hy, rfl⟩
    show mat g⁻¹ * (a • incM F (Matrix.vecMulVec x y)) ∈ latAtV X W v
    have hz : (a • fun i => inclR (F := F) (AF F) (x i)) ∈ latAt X v :=
      AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, rfl⟩
    have e : mat g⁻¹ * (a • incM F (Matrix.vecMulVec x y)) =
        Matrix.vecMulVec (mat g⁻¹ *ᵥ (a • fun i => inclR (F := F) (AF F) (x i)))
          (fun j => inclR (F := F) (AF F) (y j)) := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, Matrix.mulVec,
        dotProduct, Pi.smul_apply, incM, Matrix.map_apply, map_mul, Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [e]
    exact vecMulVec_mem_latAtV_left X W v hy (hg.2 _ hz).2
  exact this hγ

theorem acts_vacCond_of_mem_KAt_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (θ : 𝓞 E), (θ : E) + σ θ = 1 → ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v,
      ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om' (k, 1)) φ φ₁ →
        (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) φ
          (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • φ)) →
        (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) φ₁
          (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • φ₁)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v θ hθ k hk φ hφ φ₁ hφ₁ hAct hvac γ hγ r hr
  have hS := IsUWeilPair.isUSplitting hTr.weil'
  have etens : ∀ (c : ℂ) (f : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      tens (evFin F v) (c • f) r = c • tens (evFin F v) f r := fun c f => by
    funext x; simp only [tens, Pi.smul_apply, smul_eq_mul]; ring
  by_cases h0 : φ₁ = 0
  · subst h0
    have e0 : tens (evFin F v) (0 : (Fin a' × Fin (a + a') → Fv F v) → ℂ) r = 0 := by
      funext x; simp [tens]
    rw [smul_zero, e0]
    funext x
    simp [Darboux.rho, schr]
  have hrφ : Rest (evFin F v) φ r := GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v φ₁ φ r h0 hφ hr
  set γ' := actAB (cA σ) (k⁻¹, (1 : UA σ G.W.J)) γ
  have eγ' : γ' = mat k⁻¹ * γ := by
    simp [γ', actAB, mat]
  have hγ' : γ' ∈ latAtV G.V' G.W v := by
    rw [eγ']; exact mul_left_inv_mem_latAtV G.V' G.W v hk hγ
  have hsym : symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ' γ' =
      symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ := by
    rw [eγ']
    exact symp_mul_left (cA σ) _ _ _ (mat k⁻¹) (k⁻¹).2 γ
  have e1 : actAB (cA σ) (k, (1 : UA σ G.W.J)) γ' = γ := by
    simp only [γ', actAB]
    simp [← Matrix.mul_assoc]
  have hi := hS.impl (k, (1 : UA σ G.W.J)) γ' _ hrφ.2
  rw [e1] at hi
  rw [← hAct r hrφ, ← hi, hvac γ' hγ' r hrφ, hsym, etens, map_smul, hAct r hrφ, etens]

end GlobalTheory.InertSphLeft

namespace GlobalTheory.InertSphLeft

theorem vac_fixed_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v, Acts (evFin F v) (om' (k, 1)) (G.M'.vac v) (G.M'.vac v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hw hv k hk
  obtain ⟨hSB, -, θ, hθ, hvac⟩ := hTr.geo.hM'.vac v
  obtain ⟨S, hS⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' B G X om om' hTr v k hk.1
  obtain ⟨hφ₁, hact⟩ := hS _ hSB
  have h1 := acts_vacCond_of_mem_KAt_left F E σ B a a' G X om om' hTr v θ hθ k hk _ hSB _ hφ₁ hact hvac
  obtain ⟨c, hc'⟩ := GlobalTheory.T.inertPlace_schwartzBruhat_vacuumCondition_eq_smul F E σ B a a' G X om om' hTr v w hw θ hθ hvac _ hφ₁ h1
  rw [hc'] at hact
  have hc := GlobalTheory.T.inertPlace_latticeStabilizer_vacuumScalar_eq_one F E σ B a a' G X om om' hTr v w hw hv k hk c hact
  rwa [hc, one_smul] at hact

end GlobalTheory.InertSphLeft
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.doubledWeilRep_fixes_integralUnipotent_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T → ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M'.co dd →
      IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ n ∈ GlobalTheory.InertDbl.NabD σ G.W v, omd n (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  first | exact @GlobalTheory.NabFix.nab_fix | exact GlobalTheory.NabFix.nab_fix | (intros; apply GlobalTheory.NabFix.nab_fix <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

theorem _root_.GlobalTheory.T.weilDatumTransport_archimedeanSlice_schwartz_bounds : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → ∀ Φ ∈ schA F κ, ∀ (y : κ → FiniteAdeleRing (𝓞 F) F) p0 (k n : ℕ), ∃ C : ℝ,
      ∀ᶠ p in nhds p0, ∀ x : κ → mixedEmbedding.mixedSpace F,
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖ ≤ C := by
  first | exact @GlobalTheory.WeilContF.slice_bounds | exact GlobalTheory.WeilContF.slice_bounds | (intros; apply GlobalTheory.WeilContF.slice_bounds <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.kernelSum_eq_finsum_regular_rationalClasses : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → (∃ w ∈ S, ∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) → kernSum S lam K' f = ∑ᶠ c : TwCl (MonoidHom.id (UE E n)), if c.rep.1.val.charpoly.Separable then chW lam c.rep.1.val.charpoly * clsSum S K' f c.rep else 0 := by
  first | exact @GlobalTheory.BCT.Regroup.kernSum_eq_finsum_classes | exact GlobalTheory.BCT.Regroup.kernSum_eq_finsum_classes | (intros; apply GlobalTheory.BCT.Regroup.kernSum_eq_finsum_classes <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TraceBlocks

section Assembly
variable {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem trOn_eqvM (ι : H →* G) (hι : Function.Injective ι) (ρ : Representation ℂ H V) (K K' : Subgroup G) (F : G → ℂ)
    (hF : ∀ k ∈ K', ∀ x, F (k * x) = F x ∧ F (x * k) = F x) (hsupp : {q : G ⧸ K' | F q.out ≠ 0}.Finite)
    (hdc : Finite (DoubleCoset.Quotient (ι.range : Set G) (K' : Set G)))
    (hst : ∀ x : G, Finite (ι.range ⊓ K'.map (MulAut.conj x).toMonoidHom : Subgroup G)) :
    trOn (eqvM ι ρ K') (levOp (rightReg ℂ G V) K K' F LinearMap.id) =
      ((K'.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : DoubleCoset.Quotient (ι.range : Set G) (K' : Set G),
        ((stabCard ι K' (Quotient.out q) : ℂ))⁻¹ *
          ∑ᶠ h : H, F ((Quotient.out q)⁻¹ * ι h * Quotient.out q) * LinearMap.trace ℂ V (ρ h) := by
  classical
  have hR : ∀ k ∈ K', ∀ x, F (x * k) = F x := fun k hk x => (hF k hk x).2
  have hmaps := GlobalTheory.T.heckeOperator_preserves_equivariantRightInvariant G H V ι ρ K K' F hF
  unfold trOn
  rw [dite_eq_left hmaps]
  haveI : Fintype (DoubleCoset.Quotient (ι.range : Set G) (K' : Set G)) := Fintype.ofFinite _
  set T := levOp (rightReg ℂ G V) K K' F LinearMap.id with hT
  set M := eqvM ι ρ K' with hM
  let x : DoubleCoset.Quotient (ι.range : Set G) (K' : Set G) → G := fun q => Quotient.out q
  let e : DoubleCoset.Quotient (ι.range : Set G) (K' : Set G) → (M →ₗ[ℂ] V) :=
    fun q => (LinearMap.proj (R := ℂ) (φ := fun _ : G => V) (x q)).comp M.subtype
  let s : DoubleCoset.Quotient (ι.range : Set G) (K' : Set G) → (V →ₗ[ℂ] M) :=
    fun q => (secM ι ρ K' (x q)).codRestrict M (fun v => GlobalTheory.T.equivariantDoubleCosetSection_mem_equivariant G H V ι ρ K' (x q) v)
  have hid : ∑ q, s q ∘ₗ e q = LinearMap.id := by
    ext φ : 1
    apply Subtype.ext
    have := GlobalTheory.T.equivariantFunction_eq_finsum_doubleCosetSections G H V ι hι ρ K' hdc hst φ.1 φ.2
    rw [finsum_eq_sum_of_fintype] at this
    simpa [s, e, x] using this
  have h1 : ∀ φ : M, φ = ∑ q, s q (e q φ) := fun φ => by
    conv_lhs => rw [← LinearMap.id_apply (R := ℂ) φ, ← hid]
    simp
  haveI : Module.Finite ℂ M := by
    refine Module.Finite.of_injective (LinearMap.pi e) fun a b hab => ?_
    rw [h1 a, h1 b]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [show e q a = e q b from congrFun hab q]
  have htr : LinearMap.trace ℂ M (T.restrict hmaps) =
      ∑ q, LinearMap.trace ℂ V (e q ∘ₗ T.restrict hmaps ∘ₗ s q) := by
    have hsum : T.restrict hmaps ∘ₗ (∑ q, s q ∘ₗ e q) = ∑ q, (T.restrict hmaps ∘ₗ s q) ∘ₗ e q := by
      ext φ : 1

      simp [LinearMap.sum_apply, map_sum]

    conv_lhs => rw [← LinearMap.comp_id (T.restrict hmaps), ← hid, hsum, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [LinearMap.trace_comp_comm']
  rw [htr, finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hfin := GlobalTheory.T.finite_rationalPoints_conj_in_support G H ι hι K' F hR hsupp (x q) (hst _)
  have hsub : ∀ {β : Type} [AddCommMonoid β] (g : H → β), (∀ h, F ((x q)⁻¹ * ι h * x q) = 0 → g h = 0) →
      Function.support g ⊆ hfin.toFinset := fun g hg h hh => by
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    exact fun h0 => hh (hg h h0)
  have hA : e q ∘ₗ T.restrict hmaps ∘ₗ s q = ((K'.relIndex K : ℕ) : ℂ)⁻¹ • ((stabCard ι K' (x q) : ℂ))⁻¹ •
      ∑ h ∈ hfin.toFinset, F ((x q)⁻¹ * ι h * x q) • ρ h := by
    ext v
    have := GlobalTheory.T.heckeOperator_equivariantDoubleCosetSection_basePoint G H V ι hι ρ K K' F hR hsupp (x q) (hst _) hfin v
    rw [finsum_eq_sum_of_support_subset _ (hsub _ fun h h0 => by simp [h0])] at this
    simpa [e, s, LinearMap.restrict_apply, LinearMap.sum_apply] using this

  rw [hA, LinearMap.map_smul, LinearMap.map_smul, map_sum, smul_eq_mul, smul_eq_mul,
  finsum_eq_sum_of_support_subset _ (hsub (fun h => F ((x q)⁻¹ * ι h * x q) * LinearMap.trace ℂ V (ρ h))
    fun h h0 => by simp [h0])]
  simp only [map_smul, smul_eq_mul, x]

end Assembly

end GlobalTheory.BCT.TraceBlocks

namespace GlobalTheory.BCT.TraceBlocks

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem finPtHom_injective : Function.Injective (finPtHom (E := E) (n := n)) := by
  intro a b h
  have h1 : finGL E n (ratF E n a.1) = finGL E n (ratF E n b.1) := by
    have := congrArg (fun k : finU (E := E) (n := n) => (k : UA E n).1) h
    simpa only [finPtHom_apply, FinPtLoc.finPt_eq] using this
  have h2 : ratF E n a.1 = ratF E n b.1 := by
    have := congrArg (GeneralLinearGroup.map (pFin E)) h1
    simpa using this
  obtain ⟨w⟩ : Nonempty (HeightOneSpectrum (𝓞 E)) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 E)
    exact ⟨⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)⟩⟩
  haveI : Nontrivial (Af E) := (pLoc E w).domain_nontrivial
  apply Subtype.ext
  apply Units.ext
  ext i j
  exact (algebraMap E (Af E)).injective (congrArg (fun g : GL (Fin n) (Af E) => g.val i j) h2)

theorem finPtHom_range : (finPtHom (E := E) (n := n)).range = ratFinU E n := by
  ext k
  constructor
  · rintro ⟨γ, rfl⟩
    refine ⟨γ.1, γ.2, ?_⟩
    have := FinPtLoc.finPt_eq γ
    exact (congrArg Subtype.val this).symm
  · rintro ⟨g, hg, he⟩
    refine ⟨⟨g, hg⟩, Subtype.ext (Subtype.ext ?_)⟩
    rw [finPtHom_apply, FinPtLoc.finPt_eq]
    exact he

end GlobalTheory.BCT.TraceBlocks


open GlobalTheory.BCT.TraceBlocks in
theorem GlobalTheory.BCT.TrKer.trOn_vecM_hopM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → trOn (GlobalTheory.BCT.TrKer.vecM S lam K') (GlobalTheory.BCT.TrKer.hopM S lam K' f) = (((globLev S K').relIndex (globLev S (KL n)) : ℕ) : ℂ)⁻¹ * ∑ᶠ q : DoubleCoset.Quotient (ratFinU E n : Set (finU (E := E) (n := n))) (globLev S K' : Set (finU (E := E) (n := n))), ((Nat.card (ratFinU E n ⊓ (globLev S K').map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup (finU (E := E) (n := n))) : ℂ))⁻¹ * ∑ᶠ γ : UE E n, globFn S f ((Quotient.out q)⁻¹ * finPt γ * Quotient.out q) * LinearMap.trace ℂ _ (GlobalTheory.BCT.TrKer.wAt lam γ⁻¹) := by
  intro E _ _ _ hU n _ S hS lam K' hK f hf
  have hV : GlobalTheory.BCT.TrKer.vecM S lam K' = eqvM finPtHom (wDual lam) (globLev S K') := rfl
  have hT : GlobalTheory.BCT.TrKer.hopM S lam K' f =
      levOp (rightReg ℂ (finU (E := E) (n := n)) (Module.Dual ℂ (GlobalTheory.BCT.TrKer.Wsp lam))) (globLev S (KL n)) (globLev S K')
        (globFn S f) LinearMap.id := rfl
  have hF := globFn_inv S K' f fun w => (hf.1 w).2
  have hdc : Finite (DoubleCoset.Quotient ((finPtHom (E := E) (n := n)).range : Set (finU (E := E) (n := n)))
      (globLev S K' : Set (finU (E := E) (n := n)))) := by
    rw [finPtHom_range]
    exact GlobalTheory.T.finite_doubleCoset_definiteUnitaryRational_of_isOpen E n _ (GlobalTheory.T.isOpen_productOfLocalLevelsUnitary E hU n S K' hK)
  have hst : ∀ x : finU (E := E) (n := n), Finite ((finPtHom (E := E) (n := n)).range ⊓
      (globLev S K').map (MulAut.conj x).toMonoidHom : Subgroup (finU (E := E) (n := n))) := fun x => by
    rw [finPtHom_range]
    exact GlobalTheory.T.finite_definiteUnitary_rational_inf_conj_level E hU n S hS K' hK x
  rw [hV, hT, trOn_eqvM finPtHom finPtHom_injective (wDual lam) _ _ _ hF (GlobalTheory.T.finite_productOfLocalFunctionsUnitary_ne_zero E hU n S K' hK f hf) hdc hst]
  have htr : ∀ γ : UE E n, LinearMap.trace ℂ _ (wDual lam γ) = LinearMap.trace ℂ _ (GlobalTheory.BCT.TrKer.wAt lam γ⁻¹) :=
    fun γ => LinearMap.trace_transpose' _
  simp only [htr, finPtHom_apply, stabCard]
  rw [finPtHom_range]
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.VacShape

theorem vacuum_eq_smul_indicator : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E))
    (θ : 𝓞 D.host.E) (hθ : (θ : D.host.E) + D.sp.cm.sig θ = 1)
    (φ₀ : (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) (h0 : φ₀ ∈ GlobalTheory.WeilM.SB _) (hne : φ₀ ≠ 0)
    (hfix : (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) φ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • φ₀)))
    (huniq : ∀ ψ₀ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁), (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) ψ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • ψ₀)) → ∃ c : ℂ, ψ₀ = c • φ₀),
    ∃ (ι : ((Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) → ℂ))
      (P : GL (Fin a') (Fv D.host.F Bs.v₁)) (Λ : Submodule 𝒪[Fv D.host.F Bs.v₁] (Fin (a + a') → Fv D.host.F Bs.v₁)) (c : ℂ),
      Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι ∧ ∀ Y, ι φ₀ Y = c * (matLat (Fin a') Λ : Set _).indicator 1 (P.val * Y) := by
  intro D a a' Bs Γ X om om' hTr L₁ L₂ θ hθ φ₀ h0 hne hfix huniq
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_linearModel_intertwiner_goodSplitPlace Bs Γ X om om' hTr
  have hfSB : ι φ₀ ∈ GlobalTheory.WeilM.SB _ := hι.bij.mapsTo h0
  have hf0 : ι φ₀ ≠ 0 := by
    intro h
    apply hne
    refine hι.bij.injOn h0 (zero_mem _) ?_
    rw [h, map_zero]
  have hinv : ∀ s ∈ GlobalTheory.VacShape.Sa Bs Γ L₁ L₂, ∀ Y, ι φ₀ (Y + s) = ι φ₀ Y := by
    rintro _ ⟨u, hu, hu0, rfl⟩ Y
    have hat := (GlobalTheory.LatVac.latAtV_at_stable _ _ _).1 u hu
    have hA := hfix u hu
    rw [GlobalTheory.T.traceSymplectic_self_zero_splitSupported Bs Γ X om om' hTr u hat (Or.inl hu0), mul_zero, AddChar.map_zero_eq_one, one_smul] at hA
    exact (hι.trans u hat hu0 φ₀ h0 φ₀ h0 hA Y).symm
  have hsupp : ∀ Y ∉ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂, ι φ₀ Y = 0 := by
    intro Y hY
    simp only [GlobalTheory.VacShape.Bd, Set.mem_setOf_eq, not_forall] at hY
    obtain ⟨x, hx, hx0, rfl, u, hu, hu0, hne1⟩ := hY
    have hat := (GlobalTheory.LatVac.latAtV_at_stable _ _ _).1 u hu
    have hB := hfix u hu
    rw [GlobalTheory.T.traceSymplectic_self_zero_splitSupported Bs Γ X om om' hTr u hat (Or.inr hu0), mul_zero, AddChar.map_zero_eq_one, one_smul] at hB
    have hm := hι.mult u hat hu0 φ₀ h0 φ₀ h0 hB x hx hx0
    by_contra h
    exact hne1 ((mul_eq_right₀ h).mp hm.symm)
  obtain ⟨c, hc, hop, hcp⟩ := GlobalTheory.T.schwartzBruhat_matrices_invariant_supported_eq_smul Bs.v₁ _ _ (GlobalTheory.T.latticePairingTrivialMatrices_sub_mem Bs Γ X om om' hTr L₁ L₂) (ι φ₀) hfSB hf0 hinv hsupp
    (GlobalTheory.T.schwartzBruhat_invariant_supported_eq_smul_vacuum Bs Γ X om om' hTr L₁ L₂ θ hθ ι hι φ₀ h0 hne hfix huniq)
  obtain ⟨P, Λ, hPΛ⟩ := GlobalTheory.T.closure_vanishing_lattice_eq_row_lattice_matrices Bs Γ X om om' hTr L₁ L₂ hop hcp
  refine ⟨ι, P, Λ, c, hι, fun Y => ?_⟩
  have hY := congrFun hc Y
  rw [Pi.smul_apply, smul_eq_mul] at hY
  rw [hY]
  congr 1
  by_cases h : Y ∈ closure (GlobalTheory.VacShape.Sa Bs Γ L₁ L₂ : Set _)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show P.val * Y ∈ (matLat (Fin a') Λ : Set _) from (hPΛ Y).1 h)]
    rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show P.val * Y ∉ (matLat (Fin a') Λ : Set _) from fun h' => h ((hPΛ Y).2 h'))]

end GlobalTheory.VacShape

end
end
