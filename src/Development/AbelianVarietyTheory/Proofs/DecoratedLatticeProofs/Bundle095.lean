module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle026
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle025
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModelsAreCoverSeries
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReducedBasisBoundedTypeOfInstance
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle092
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle065
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResidueSupportSinglePlaceToConjugatePairPosition
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle093
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle015
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum

@[expose] public section

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
open scoped InnerProductSpace
open GlobalTheory.CoverModel GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix

noncomputable section

namespace GlobalTheory.RealPar.CoverFactor

theorem signCompat_of_blockOrd {p q n : ℕ} {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) :
    SignCompat ε e := by
  rintro (a | a)
  · simpa using h.1 a
  · simpa using h.2.1 a

theorem dictionary : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (U : URep T) (σ : Matrix (Fin n) (Fin n) ℂ → (U.H →L[ℂ] U.H)), BlockOrd e ε → Factors U e σ → IsURepOn (UJset ε) σ ∧ (IrrU U → IsIrredOn (UJset ε) σ) ∧ (∀ x, KFin T U.π x ↔ IsKFin ε σ x) ∧ (∀ Y, Y ∈ upq p q ↔ Formalism.REAL.inG ε (Matrix.reindex e e Y)) ∧ (∀ Y ∈ upq p q, ∀ t : ℝ, U.π (T.expt (t • Y)) = σ (NormedSpace.exp (t • Matrix.reindex e e Y))) ∧ ∀ k ∈ Formalism.REAL.Kset ε, ∃ x ∈ T.Kset, U.π x = σ k := by
  intro p q n e ε T U σ h hF
  have hφ : IsFormIso ε (plainMat e) := isFormIso_plainMat (signCompat_of_blockOrd h)
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · have := hF 1
    rw [map_one, map_one] at this
    rw [this]
    simp
  · intro a ha b hb
    obtain ⟨x, rfl⟩ := h.cov_surj T ha
    obtain ⟨y, rfl⟩ := h.cov_surj T hb
    have := hF (x * y)
    rw [map_mul, map_mul, hF x, hF y] at this
    rw [← ContinuousLinearMap.mul_def, this]
    simp [Matrix.submatrix_mul_equiv]
  · intro g hg v
    obtain ⟨x, rfl⟩ := h.cov_surj T hg
    rw [← hF x]
    exact U.isom x v
  · intro v
    refine CoverURep.continuousOn_of_cover h T _ ?_
    simpa only [← hF _] using U.cont v
  · intro hI S hS hst
    refine hI.2 S hS fun x v hv => ?_
    rw [hF x]
    exact hst _ (h.cov_mem T x) v hv
  · intro x
    have := kFin_iff (s := RingHom.id ℂ) hφ (T := T) (π := U.π) (σ := σ) (LinearIsometryEquiv.refl ℂ U.H)
      (c := fun _ => 1) (fun _ => one_ne_zero) (fun g y => by rw [one_smul, hF g]; rfl) x
    exact this.symm
  · intro Y
    exact (hφ.mem_lie Y).symm
  · intro Y hY t
    rw [hF, T.expt_cov _ (KStabLie.smul_mem_upq hY t)]
    exact congrArg σ (hφ.exp Y t).symm
  · intro k hk
    obtain ⟨x, hx⟩ := hφ.surj T (mem_K_iff.1 hk).1
    refine ⟨x, (hφ.mem_K T x).1 (hx ▸ hk), ?_⟩
    rw [hF x]
    exact congrArg σ hx

end GlobalTheory.RealPar.CoverFactor

end
end

section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RegSch.EmbLevel

open Formalism.UG

section Ring

variable {A B : Type} [CommRing A] [CommRing B] {σ : A →+* A} {τ : B →+* B} {φ : A →+* B}

theorem cT_map (hφ : ∀ x, φ (σ x) = τ (φ x)) {m p : Type} (M : Matrix m p A) :
    (cT σ M).map φ = cT τ (M.map φ) := by
  funext i j
  exact hφ (M j i)

theorem conj_mem_iff {n : ℕ} (b g : GL (Fin n) B) :
    b⁻¹ * g * b ∈ UJ τ (1 : Matrix (Fin n) (Fin n) B) ↔
      cT τ g.1 * (cT τ (b⁻¹).1 * (b⁻¹).1) * g.1 = cT τ (b⁻¹).1 * (b⁻¹).1 := by
  have h1 : b.1 * (b⁻¹).1 = 1 := b.mul_inv
  have h2 : (b⁻¹).1 * b.1 = 1 := b.inv_mul
  have h3 : cT τ (b⁻¹).1 * cT τ b.1 = 1 := by rw [← cT_mul, h1, cT_one]
  have h4 : cT τ b.1 * cT τ (b⁻¹).1 = 1 := by rw [← cT_mul, h2, cT_one]
  change cT τ ((b⁻¹).1 * g.1 * b.1) * 1 * ((b⁻¹).1 * g.1 * b.1) = 1 ↔ _
  have e : cT τ ((b⁻¹).1 * g.1 * b.1) * 1 * ((b⁻¹).1 * g.1 * b.1) =
      cT τ b.1 * (cT τ g.1 * (cT τ (b⁻¹).1 * (b⁻¹).1) * g.1) * b.1 := by
    simp only [cT_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [e]
  generalize cT τ g.1 * (cT τ (b⁻¹).1 * (b⁻¹).1) * g.1 = X
  constructor
  · intro h
    calc X = (cT τ (b⁻¹).1 * cT τ b.1) * X * (b.1 * (b⁻¹).1) := by rw [h1, h3, Matrix.one_mul, Matrix.mul_one]
      _ = cT τ (b⁻¹).1 * (cT τ b.1 * X * b.1) * (b⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, Matrix.mul_one]
  · rintro rfl
    rw [← Matrix.mul_assoc, h4, Matrix.one_mul, h2]

theorem conj_bc_mem_iff (hφ : ∀ x, φ (σ x) = τ (φ x)) {n : ℕ} (c g : GL (Fin n) A) :
    (bc φ c)⁻¹ * bc φ g * bc φ c ∈ UJ τ (1 : Matrix (Fin n) (Fin n) B) ↔
      (cT σ g.1 * (cT σ (c⁻¹).1 * (c⁻¹).1) * g.1).map φ = (cT σ (c⁻¹).1 * (c⁻¹).1).map φ := by
  rw [conj_mem_iff, ← map_inv]
  simp only [Matrix.map_mul, cT_map hφ]
  rfl

end Ring

section Lattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in
theorem compInf_sigR (σ : E →ₐ[F] E) (w : InfinitePlace F) (x : AF F ⊗[F] E) :
    compInf F E w (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ x) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (compInf F E w x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a e => rfl

omit [NumberField E] in
theorem mem_levelAll_iff (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (c : GL (Fin n) (AF F ⊗[F] E)) (g : GAd σ J) : g ∈ levelAll σ J L c ↔
    (∀ v y, y ∈ latLoc F L v ↔ (GlobalTheory.AdelicU.matHom _ σ J g).1.map (compFin F E v) *ᵥ y ∈ latLoc F L v) ∧
      ∀ w, (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) (GlobalTheory.AdelicU.matHom _ σ J g).1 *
          (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) (c⁻¹).1 * (c⁻¹).1) * (GlobalTheory.AdelicU.matHom _ σ J g).1).map (compInf F E w) =
        (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) (c⁻¹).1 * (c⁻¹).1).map (compInf F E w) := by
  refine mem_levelAll.trans (and_congr Iff.rfl (forall_congr' fun w => ?_))
  rw [mem_stabArch, matHom_projArch]
  exact conj_bc_mem_iff (compInf_sigR σ w) c _

end Lattice

variable {D : D7}

end GlobalTheory.RegSch.EmbLevel

end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.AdelicU

theorem exists_single_mem_latLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ c : Fv F v, c ≠ 0 ∧
      ∀ i : Fin n, (Pi.single i (c ⊗ₜ[F] (1 : E)) : Fin n → Fv F v ⊗[F] E) ∈ latLoc F L v := by
  exact _root_.GlobalTheory.LocalLatticeIntegral.exists_single_mem_latLoc L v

end GlobalTheory.AdelicU
end

section

noncomputable section

namespace GlobalTheory.ChainOnto.SatHeckeChar

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

theorem heckeVec_eq_smul_of_isSatVecGL :
    ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (B : Multiset ℂˣ),
      ∀ φ ∈ Hecke ℂ (KGL w (n := n)), ∃ z : ℂ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V),
          IsSatVecGL w ρ x B → heckeVec ρ (KGL w (n := n)) φ x = z • x := by
  intro E _ _ w n B φ hφ
  by_cases hB : B.card = n
  · obtain ⟨α, rfl⟩ : ∃ α : Fin n → ℂˣ, Finset.univ.val.map α = B := by
      obtain ⟨l, rfl⟩ := Quot.exists_rep B
      obtain rfl : l.length = n := hB
      exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
    obtain ⟨x₀, hx₀⟩ := (hasSatGL_psFunGL (w := w) α).exists_vec
    obtain ⟨z, hz, -⟩ := SatCompare.exists_eigenvalue_GL hx₀ hx₀ φ hφ
    refine ⟨z, fun V _ _ ρ x hx => ?_⟩
    obtain ⟨c, e1, e2⟩ := SatCompare.exists_eigenvalue_GL hx₀ hx φ hφ
    have e : z = c := smul_left_injective ℂ hx₀.1 (hz.symm.trans e1)
    rw [e2, e]
  · exact ⟨0, fun V _ _ ρ x hx => absurd hx.2.2.1 hB⟩

end GlobalTheory.ChainOnto.SatHeckeChar

end
end

section

open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.KJAvg

theorem eval_bounded_on_box {σ : Type} (p : MvPolynomial σ ℂ) (M : σ → ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : σ → ℂ, (∀ v, ‖x v‖ ≤ M v) → ‖eval x p‖ ≤ B := by
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨‖c‖, norm_nonneg _, fun x _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨B1, h1, hB1⟩ := hp; obtain ⟨B2, h2, hB2⟩ := hq
    exact ⟨B1 + B2, by positivity, fun x hx => by
      rw [map_add (f := _)]; exact (norm_add_le _ _).trans (add_le_add (hB1 x hx) (hB2 x hx))⟩
  | mul_X p n hp =>
    obtain ⟨B, h0, hB⟩ := hp
    refine ⟨B * max (M n) 0, by positivity, fun x hx => ?_⟩
    rw [map_mul, eval_X, norm_mul]
    exact mul_le_mul (hB x hx) ((hx n).trans (le_max_left _ _)) (norm_nonneg _) h0

def univSubst {ι : Type} [Fintype ι] {a b : ℕ} (P : FP ι a b) :
    MvPolynomial (ι × Fin b × Fin a) (MvPolynomial (ι × Fin a × Fin a) ℂ) :=
  aeval (fun v => ∑ j, C (X (v.1, v.2.2, j)) * X (v.1, v.2.1, j)) P

theorem mvZ_one_eq_map_univSubst {ι : Type} [Fintype ι] {a b : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (P : FP ι a b) :
    mvZ g (fun _ => 1) P = map (eval fun w => g w.1 w.2.1 w.2.2) (univSubst P) := by
  have : (mvZ g (fun _ => (1 : Matrix (Fin b) (Fin b) ℂ)) : FP ι a b →ₐ[ℂ] FP ι a b) =
      (MvPolynomial.mapAlgHom (aeval fun w : ι × Fin a × Fin a => g w.1 w.2.1 w.2.2)).comp
        (aeval (fun v => ∑ j, C (X (v.1, v.2.2, j)) * X (v.1, v.2.1, j))) := by
    apply MvPolynomial.algHom_ext
    intro v

    simp only [mvZ, aeval_X, AlgHom.comp_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    apply_ite C, C_0, map_sum, map_mul, mapAlgHom_apply, map_C, map_X]
    rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq', coe_aeval_eq_eval]
  have h := DFunLike.congr_fun this P
  rw [h]; rfl

theorem linear_eq_sum_coeff {σ : Type} (Λ : MvPolynomial σ ℂ →ₗ[ℂ] ℂ) (S : Finset (σ →₀ ℕ)) (p : MvPolynomial σ ℂ)
    (hp : p.support ⊆ S) : Λ p = ∑ m ∈ S, AddMonoidAlgebra.coeff p m * Λ (monomial m 1) := by
  conv_lhs => rw [p.as_sum]

  rw [map_sum, Finset.sum_subset hp]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [show monomial m (AddMonoidAlgebra.coeff p m) = AddMonoidAlgebra.coeff p m • monomial m (1 : ℂ) by rw [smul_monomial, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
  · intro m _ hm
    simp [notMem_support_iff.mp hm]

section
variable {ι : Type} [Fintype ι] {a : ℕ} {K : Type} [Group K] [TopologicalSpace K]
  {r : K → ι → Matrix (Fin a) (Fin a) ℂ}

theorem ontoUni_one (hr : OntoUni r) (τ : ι) : r 1 τ = 1 := by
  have hm : r 1 τ * r 1 τ = r 1 τ := by rw [← hr.mul, one_mul]
  have hu : star (r 1 τ) * r 1 τ = 1 := (Matrix.mem_unitaryGroup_iff'.mp (hr.uni 1 τ))
  calc r 1 τ = (star (r 1 τ) * r 1 τ) * r 1 τ := by rw [hu, one_mul]
    _ = star (r 1 τ) * (r 1 τ * r 1 τ) := by rw [mul_assoc]
    _ = 1 := by rw [hm, hu]

theorem ontoUni_inv (hr : OntoUni r) (k : K) (τ : ι) : (r k τ)⁻¹ = r k⁻¹ τ :=
  Matrix.inv_eq_left_inv (by rw [← hr.mul, inv_mul_cancel, ontoUni_one hr])

theorem integrable_avg_term [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsFiniteMeasure ν]
    (hr : OntoUni r) (p : MvPolynomial (ι × Fin a × Fin a) ℂ) (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    Integrable (fun k => eval (fun w => r k⁻¹ w.1 w.2.1 w.2.2) p * evalAt (fun τ => r k τ * y τ) F) ν := by
  simp only [evalAt]
  have hc : Continuous (fun k => eval (fun w => r k⁻¹ w.1 w.2.1 w.2.2) p *
      eval (fun x => (r k x.1 * y x.1) x.2.1 x.2.2) F) := by
    apply Continuous.mul
    · exact (MvPolynomial.continuous_eval p).comp (continuous_pi fun w =>
        (((continuous_apply w.1).comp (hr.cont.comp continuous_inv))).matrix_elem _ _)
    · exact (MvPolynomial.continuous_eval F).comp (continuous_pi fun w =>
        ((((continuous_apply w.1).comp hr.cont)).matrix_mul continuous_const).matrix_elem _ _)
  obtain ⟨B1, h1, hB1⟩ := GlobalTheory.KJAvg.eval_bounded_on_box p (fun _ => 1)
  obtain ⟨B2, h2, hB2⟩ := GlobalTheory.KJAvg.eval_bounded_on_box F (fun w => ∑ l, ‖y w.1 l w.2.2‖)
  refine Integrable.of_bound hc.aestronglyMeasurable (B1 * B2) (Filter.Eventually.of_forall fun k => ?_)
  rw [norm_mul]
  refine mul_le_mul (hB1 _ fun w => entry_norm_bound_of_unitary (hr.uni _ _) _ _) (hB2 _ fun w => ?_)
    (norm_nonneg _) h1
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (entry_norm_bound_of_unitary (hr.uni _ _) _ _)

end

theorem avg_span : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (hab : a ≤ b), 0 < a → ∀ (lam : ι → DomWeight a) (n : ι → ℕ) (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] (r : K → ι → Matrix (Fin a) (Fin a) ℂ), OntoUni r → ∀ (y : ι → Matrix (Fin a) (Fin a) ℂ) (P : FP ι a b), ∃ (m : ℕ) (y' : Fin m → ι → Matrix (Fin b) (Fin b) ℂ) (s : Fin m → ℂ), (∀ j, IsInv (y' j)) ∧ ∀ F ∈ Vn lam n, ∀ Λ : FP ι a b →ₗ[ℂ] ℂ, ∫ k, Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) P) * evalAt (fun τ => r k τ * y τ) F ∂ν = ∑ j, s j * Λ (subY hab (y' j) F) := by
  intro ι _ a b hab ha lam n K _ _ _ _ _ ν _ _ r hr y P
  obtain ⟨-, hcomp, -, -, -, hev, -, -⟩ := GlobalTheory.T.fockSubstitution_identities ι a b hab
  let S := (univSubst P).support
  let c : (ι × Fin b × Fin a →₀ ℕ) → K → ℂ := fun m k =>
    eval (fun w => r k⁻¹ w.1 w.2.1 w.2.2) (AddMonoidAlgebra.coeff (univSubst P) m)
  have hΛ : ∀ (Λ : FP ι a b →ₗ[ℂ] ℂ) k, Λ (mvZ (fun τ => r k⁻¹ τ) (fun _ => 1) P) =
      ∑ m ∈ S, c m k * Λ (monomial m 1) := by
    intro Λ k
    rw [mvZ_one_eq_map_univSubst, linear_eq_sum_coeff Λ S _ (support_map_subset _ _)]
    simp only [coeff_map]
    rfl
  have hint : ∀ m F, Integrable (fun k => c m k * evalAt (fun τ => r k τ * y τ) F) ν :=
    fun m F => integrable_avg_term ν hr _ y F
  let φ : (ι × Fin b × Fin a →₀ ℕ) → PY ι a →ₗ[ℂ] ℂ := fun m =>
    { toFun := fun F => ∫ k, c m k * evalAt (fun τ => r k τ * y τ) F ∂ν
      map_add' := fun F G => by
        have e : ∀ k, c m k * evalAt (fun τ => r k τ * y τ) (F + G) =
            c m k * evalAt (fun τ => r k τ * y τ) F + c m k * evalAt (fun τ => r k τ * y τ) G := by
          intro k; simp only [evalAt, map_add (f := _), mul_add]
        simp only [e]
        exact integral_add (hint m F) (hint m G)
      map_smul' := fun t F => by
        have e : ∀ k, c m k * evalAt (fun τ => r k τ * y τ) (t • F) =
            t * (c m k * evalAt (fun τ => r k τ * y τ) F) := by
          intro k; simp only [evalAt, smul_eval]; ring
        simp only [e, RingHom.id_apply, smul_eq_mul]
        exact integral_const_mul _ _ }
  let Q : PY ι a →ₗ[ℂ] FP ι a b := ∑ m ∈ S, (φ m).smulRight (monomial m 1)
  have hQ : ∀ (Λ : FP ι a b →ₗ[ℂ] ℂ) F, Λ (Q F) =
      ∫ k, Λ (mvZ (fun τ => r k⁻¹ τ) (fun _ => 1) P) * evalAt (fun τ => r k τ * y τ) F ∂ν := by
    intro Λ F
    have e : ∀ k, Λ (mvZ (fun τ => r k⁻¹ τ) (fun _ => 1) P) * evalAt (fun τ => r k τ * y τ) F =
        ∑ m ∈ S, c m k * evalAt (fun τ => r k τ * y τ) F * Λ (monomial m 1) := by
      intro k; rw [hΛ, Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
    simp only [e]
    rw [integral_finsetSum _ (fun m _ => (hint m F).mul_const _)]

    simp only [Q, LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_mul_const]; rfl
  have heq : ∀ u, IsUni u → ∀ F ∈ Vn lam n, Q (lft u F) = mvZ u (fun _ => 1) (Q F) := by
    intro u hu F _
    obtain ⟨k0, rfl⟩ := hr.onto u hu
    ext m'
    have h1 := hQ (lcoeff ℂ m') (lft (r k0) F)
    have h2 := hQ ((lcoeff ℂ m').comp (mvZ (r k0) (fun _ => 1)).toLinearMap) F
    simp only [lcoeff_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply] at h1 h2
    rw [h1, h2]
    conv_rhs => rw [← integral_mul_left_eq_self _ k0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    have e1 : (fun τ => r (k0 * k)⁻¹ τ * r k0 τ) = fun τ => r k⁻¹ τ := by
      funext τ; rw [← hr.mul]; congr 2; group
    have e2 : (fun τ => r (k0 * k) τ * y τ) = fun τ => r k0 τ * (r k τ * y τ) := by
      funext τ; rw [hr.mul, mul_assoc]
    dsimp only
    rw [hev, hcomp, e1, e2, mul_one]
  obtain ⟨m, y', s, hinv, hspan⟩ := GlobalTheory.T.howeSpan_families_of_places ι a b hab ha lam n Q heq
  refine ⟨m, y', s, hinv, fun F hF Λ => ?_⟩
  simp_rw [ontoUni_inv hr]

  rw [← hQ, hspan F hF, map_sum]
  simp [map_smul]

end GlobalTheory.KJAvg
end
end

section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

theorem _root_.GlobalTheory.T.shortVectorCuspUnipotentCover_all_instances : ∀ I : AutInst, ShortCusp I := by
  first | exact @GlobalTheory.CuspGeo.shortCusp_all | exact GlobalTheory.CuspGeo.shortCusp_all | (intros; apply GlobalTheory.CuspGeo.shortCusp_all <;> assumption)
end

section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

theorem _root_.GlobalTheory.T.existsReducedBasisBoundedType_of_instance : ∀ I : AutInst, RedBasis I := by
  first | exact @GlobalTheory.CuspGeo.redBasis_holds | exact GlobalTheory.CuspGeo.redBasis_holds | (intros; apply GlobalTheory.CuspGeo.redBasis_holds <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

theorem _root_.GlobalTheory.T.bessel_step_position_one_finite : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c P : ℕ) (_ : 1 ≤ P) (_ : P ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (ρ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))) (_ : IsSrc μ ρ') (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (e : GL (n' ⊕ Fin (c + 1)) k →₀ ℂ) (_ : SrcComb ψ ν P ρ' Φ e) (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : BilPos ψ μ P σ B) (F : A) (z : GL (n' ⊕ Fin (c + 1)) k → ℂ), (∀ g ∈ e.support, IsQuotInt ν μX μG P (tInt ψ ν μ P σ B F (om μ g 1 Φ.1)) (z g)) → IsQuotInt ν μX μG 1 (tIntOne ψ ν μ P σ B F Φ.1) (comb e z) := by
  first | exact @GlobalTheory.PosOne.quotInt_one_comb | exact GlobalTheory.PosOne.quotInt_one_comb | (intros; apply GlobalTheory.PosOne.quotInt_one_comb <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

theorem _root_.GlobalTheory.T.exists_bilinear_position_middle_vertex : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ) (_ : c + 1 = 2 * ρ) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ₁ μ₂ : kˣ →* ℂˣ) (_ : IsOpen (μ₁.ker : Set kˣ)) (_ : IsOpen (μ₂.ker : Set kˣ)) (m₁ : Measure (GL n₁ k)) [m₁.IsHaarMeasure] (G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)) [G₁.IsHaarMeasure] (m₂ : Measure (GL n₂ k)) [m₂.IsHaarMeasure] (G₂ : Measure (GL (n₂ ⊕ Fin c) k)) [G₂.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : TriPos ψ μ₁ μ₂ ρ σ T) (F : A) (ρ₁ : Representation ℂ (GL (n₁ ⊕ Fin (c + 1)) k) (SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k))) (_ : IsSrc μ₂ ρ₁), ∃ b : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ, BilPos ψ μ₁ ρ ρ₁ b ∧ (∀ Ψ (Φ₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)), IsQuotInt ν m₂ G₂ ρ (tInt ψ ν μ₂ ρ σ (T Ψ) F Φ₂.1) (b Ψ Φ₂)) ∧ ∀ Ψ (Φ₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)), IsQuotInt ν m₂ G₂ 1 (tIntOne ψ ν μ₂ ρ σ (T Ψ) F Φ₂.1) (toOne ν ρ₁ ρ (b Ψ) Φ₂) := by
  first | exact @GlobalTheory.PosOne.MidVertex.exists_bilPos_mid | exact GlobalTheory.PosOne.MidVertex.exists_bilPos_mid | (intros; apply GlobalTheory.PosOne.MidVertex.exists_bilPos_mid <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.residueSupport_single_place_to_conjugatePair_position : ∀ (D : D7) (Pg : Finset (Pl D.host.E)), (∀ PP ∈ Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP') → ∀ R : Formalism.L2.Herm.intAf D.host.F D.host.E → Prop, (∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ Q' : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q'.asIdeal → Q' ≠ Q → resS D.host.F Q' s = 0) ∧ R s) → ∀ PP ∈ Pg, (∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ PP' ∈ Pg, (PP' ≠ PP → resS D.host.F PP' s = 0) ∧ resS D.host.F PP' (sigInt (instOf D) s) = 0) ∧ R s) ∧ ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ PP' ∈ Pg, resS D.host.F PP' s = 0 ∧ (PP' ≠ PP → resS D.host.F PP' (sigInt (instOf D) s) = 0)) ∧ R s := by
  first | exact @GlobalTheory.ConjSlot.intersection_update_fsHerm_neg_one | exact GlobalTheory.ConjSlot.intersection_update_fsHerm_neg_one | (intros; apply GlobalTheory.ConjSlot.intersection_update_fsHerm_neg_one <;> assumption)
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unitaryUnn_subgroup_eq_top_of_leviUnipotentWeyl : ∀ (D : D7) (n : ℕ) (S : Subgroup (GlobalTheory.StdUnn.G D n)), (∀ (g : GlobalTheory.StdUnn.G D n) (a : GL (Fin n) (AE D)), GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 a.1 0 0 (GlobalTheory.MixModel.adj (a⁻¹).1) → g ∈ S) → (∀ (g : GlobalTheory.StdUnn.G D n) (b : Mx D n n), GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 1 b 0 1 → g ∈ S) → (∀ g : GlobalTheory.StdUnn.G D n, GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 0 1 (-1) 0 → g ∈ S) → S = ⊤ := by
  first | exact @GlobalTheory.StdUnn.eq_top_of_levi_unip_weyl | exact GlobalTheory.StdUnn.eq_top_of_levi_unip_weyl | (intros; apply GlobalTheory.StdUnn.eq_top_of_levi_unip_weyl <;> assumption)
end
