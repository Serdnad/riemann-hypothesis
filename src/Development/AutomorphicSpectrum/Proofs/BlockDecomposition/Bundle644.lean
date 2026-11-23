module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Development.AutomorphicArithmetic.LocalEmbeddings.OppLagr
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle032
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle043
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle025
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle026
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle058
public import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
import GroundTheory.GlobalFields.Adele.Bundle002
import GroundTheory.GlobalFields.TateThesis.AdeleMeasurable
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
public import Development.WeilBound.ThetaLifts.Reductions.SiegelAbs
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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

noncomputable section

namespace GlobalTheory.CompanionTheory.RgEisCM

open scoped TensorProduct NNReal Matrix NumberField.AdeleRing
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open PositivityTheory.RgEis

section Transport

variable {R R' : Type} [CommRing R] [CommRing R'] {ι : Type} [Fintype ι] [DecidableEq ι]

def glEquiv (e : R ≃+* R') : GL ι R ≃* GL ι R' := Units.mapEquiv (RingEquiv.mapMatrix e).toMulEquiv

theorem coe_glEquiv (e : R ≃+* R') (g : GL ι R) :
    ((glEquiv e g : GL ι R') : Matrix ι ι R') = (g : Matrix ι ι R).map e := rfl

theorem coe_glEquiv_inv (e : R ≃+* R') (g : GL ι R) :
    (((glEquiv e g)⁻¹ : GL ι R') : Matrix ι ι R') = ((g⁻¹ : GL ι R) : Matrix ι ι R).map e := by
  rw [← map_inv]; rfl

theorem mem_stab_iff (e : R ≃+* R') (s : Set ι) (g : GL ι R) :
    g ∈ stab R s ↔ glEquiv e g ∈ stab R' s := by
  change (∀ r ∉ s, ∀ c ∈ s, _ ∧ _) ↔ (∀ r ∉ s, ∀ c ∈ s, _ ∧ _)
  simp only [coe_glEquiv, coe_glEquiv_inv, Matrix.map_apply, EmbeddingLike.map_eq_zero_iff]

variable {E : Type} [Field E]

theorem mem_kGL_iff (A : Ad E R) (B : Ad E R') (e : R ≃+* R') (hO : ∀ x, x ∈ A.O ↔ e x ∈ B.O)
    (hφ : ∀ w, ∃ w', ∀ x, A.φ w x = B.φ w' (e x)) (hφ' : ∀ w', ∃ w, ∀ x, A.φ w x = B.φ w' (e x)) (g : GL ι R) :
    g ∈ A.kGL ι ↔ glEquiv e g ∈ B.kGL ι := by
  change ((∀ r c, _ ∧ _) ∧ ∀ w, _) ↔ ((∀ r c, _ ∧ _) ∧ ∀ w, _)
  simp only [coe_glEquiv, coe_glEquiv_inv, Matrix.map_apply, hO]
  refine and_congr_right fun _ => ⟨fun h w' => ?_, fun h w => ?_⟩
  · obtain ⟨w, hw⟩ := hφ' w'
    have : ((g : Matrix ι ι R).map e).map (B.φ w') = (g : Matrix ι ι R).map (A.φ w) := by
      ext r c; simp [hw]
    rw [this]; exact h w
  · obtain ⟨w', hw⟩ := hφ w
    have : (g : Matrix ι ι R).map (A.φ w) = ((g : Matrix ι ι R).map e).map (B.φ w') := by
      ext r c; simp [hw]
    rw [this]; exact h w'

theorem iwa_transport (A : Ad E R) (B : Ad E R') (e : R ≃+* R') (hk : ∀ g : GL ι R, g ∈ A.kGL ι ↔ glEquiv e g ∈ B.kGL ι)
    (s : Set ι) (h : Iwa (stab R' s) (B.kGL ι)) : Iwa (stab R s) (A.kGL ι) := by
  intro g
  obtain ⟨p, hp, k, hk', hg⟩ := h (glEquiv e g)
  refine ⟨(glEquiv e).symm p, ?_, (glEquiv e).symm k, ?_, ?_⟩
  · rw [mem_stab_iff e]; simpa using hp
  · rw [hk]; simpa using hk'
  · apply (glEquiv e).injective
    simp [hg]

variable [TopologicalSpace R] [TopologicalSpace R']

theorem continuous_glEquiv (e : R ≃+* R') (h : Continuous e) : Continuous (glEquiv (ι := ι) e) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id h)

theorem kcpt_transport (A : Ad E R) (B : Ad E R') (e : R ≃+* R') (h1 : Continuous e) (h2 : Continuous e.symm)
    (hk : ∀ g : GL ι R, g ∈ A.kGL ι ↔ glEquiv e g ∈ B.kGL ι) (h : IsCompact (B.kGL ι : Set (GL ι R'))) :
    IsCompact (A.kGL ι : Set (GL ι R)) := by
  let H : GL ι R ≃ₜ GL ι R' :=
    { toEquiv := (glEquiv e).toEquiv
      continuous_toFun := continuous_glEquiv e h1
      continuous_invFun := continuous_glEquiv e.symm h2 }
  have : (A.kGL ι : Set (GL ι R)) = H ⁻¹' (B.kGL ι : Set (GL ι R')) := by
    ext g; exact hk g
  rw [this]
  exact H.isCompact_preimage.2 h

end Transport

section CM

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_inclR (σ : E →ₐ[F] E) (x : E) :
    cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
  simp [cA, inclR, Algebra.TensorProduct.map_tmul]

theorem cA_cA {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul a x => simp [cA, Algebra.TensorProduct.map_tmul, GlobalTheory.OppLagr.conj_conj h]
  | add x y hx hy => simp [map_add (f := _), hx, hy]

theorem continuous_cA (σ : E →ₐ[F] E) : Continuous (cA σ) := by
  haveI : Module.Finite (AF F) (AE F E) := inferInstance
  exact IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap

theorem cA_mem_intHat (σ : E →ₐ[F] E) {z : AE F E} (hz : z ∈ intHat F E) : cA σ z ∈ intHat F E := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, h1, h2, o, rfl⟩ := hz
    have ho : IsIntegral ℤ (σ (o : E)) := (RingOfIntegers.isIntegral_coe o).map σ
    refine AddSubgroup.subset_closure ⟨a, h1, h2, (⟨σ o, ho⟩ : 𝓞 E), ?_⟩
    rw [map_smul, cA_inclR]
    rfl
  | zero => simp [zero_mem]
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

end CM

theorem cmGood : StdGood → Dict → DictInf → CMGood := by
  intro hS hD hI F E _ _ _ _ _ σ χ c hcm _ hχ hres
  have hs := hS E
  obtain ⟨d1, d2, d3, d4, -⟩ := hD F E
  have hO : ∀ x, x ∈ (adCM σ χ).O ↔ eqv F E x ∈ (adStd E).O := fun x => Iff.rfl
  have hk : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : GL ι (AE F E)),
      g ∈ (adCM σ χ).kGL ι ↔ glEquiv (eqv F E) g ∈ (adStd E).kGL ι := fun ι _ _ g =>
    mem_kGL_iff _ _ _ hO (fun w => ⟨w, fun _ => rfl⟩) (fun w => ⟨w, fun _ => rfl⟩) g
  have hu : Continuous (Units.map (eqv F E).toRingHom.toMonoidHom) := Continuous.units_map _ d1
  have hi : ∀ x : Eˣ, Units.map (eqv F E).toRingHom.toMonoidHom (Units.map (inclR (F := F) (AF F)).toMonoidHom x) =
      Units.map (adStd E).i.toMonoidHom x := fun x => Units.ext (d3 x)
  obtain ⟨ξ, hξ⟩ := GlobalTheory.OppLagr.exists_isQuad hcm
  refine ⟨⟨?_, ?_, ?_, ?_, hχ.1, hχ.2, ?_, ?_⟩, cA_cA hcm, continuous_cA σ, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    apply hs.iinj
    change algebraMap E 𝔸[E] x = algebraMap E 𝔸[E] y
    rw [← d3, ← d3]
    exact congrArg _ hxy
  · intro x y
    change (adStd E).lg (Units.map _ (x * y)) = _
    rw [map_mul]
    exact hs.lgmul _ _
  · exact hs.lgcont.comp hu
  · intro x
    exact (congrArg (adStd E).lg (hi x)).trans (hs.lgi x)
  · intro ι _ _
    exact kcpt_transport _ _ (eqv F E) d1 d2 (hk ι) (hs.kcpt ι)
  · intro ι _ _ s
    exact iwa_transport _ _ (eqv F E) (hk ι) s (hs.iwa ι s)
  · intro x hx
    have h1 : finOne F • x ∈ intHat F E := (d4 x).1 hx
    refine (d4 _).2 ?_
    have h2 := cA_mem_intHat σ h1
    rwa [map_smul] at h2
  · intro w x
    exact (hI F E σ hcm).1 w x
  · intro x
    exact ⟨σ x, cA_inclR σ x⟩
  · intro x
    exact ResEtaPow.map_conj hξ hres x

end GlobalTheory.CompanionTheory.RgEisCM
end
end

section

open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal

noncomputable section
namespace GlobalTheory.CompanionTheory.BinaryDil

theorem fibre_unit_dilation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 0 < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)), laminf.IsAddHaarMeasure → ∀ (minf : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)), GlobalTheory.CompanionTheory.SW.IsGramFib (Ainf F) σ J 1 (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf 1 M) (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf 1) minf → ∀ (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → ∀ s t : Ainf F, IsUnit t → minf (GlobalTheory.CompanionTheory.SW.hermScal (Ainf F) σ (t ^ 2 * s)) = ((∏ w, ‖e t w‖₊) ^ (2 * M - 2)) • (minf (GlobalTheory.CompanionTheory.SW.hermScal (Ainf F) σ s)).map (fun X p i => algebraMap (Ainf F) (Ainf F ⊗[F] E) t * X p i) := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM d b lam hlam m hm e he s t ht
  have hloc : GlobalTheory.CompanionTheory.SW.IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hσ.1
  obtain ⟨i1, i2, i3, i4, i5, -, -, hB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Ainf F) d b lam hlam
  have hd : d = 2 := by
    rw [← hσ.2.2.1, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  set N : ℝ≥0 := ∏ w, ‖e t w‖₊ with hN
  have hN0 : N ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun w _ => ?_
    have : IsUnit (e t) := ht.map e
    exact nnnorm_ne_zero_iff.2 (Pi.isUnit_iff.1 this w).ne_zero
  have hN2 : ∏ w, ‖e (t ^ 2) w‖₊ = N ^ 2 := by
    rw [hN, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun w _ => ?_
    simp [map_pow]
  have hs1 := GlobalTheory.T.archimedean_haar_scaling_norm F e he lam hlam t ht
  have hs2 := GlobalTheory.T.archimedean_haar_scaling_norm F e he lam hlam (t ^ 2) (ht.pow 2)
  rw [hN2] at hs2
  have hk := GlobalTheory.T.coordinate_measure_scaling_tensor F E σ hσ M 2 b lam hlam t ht _ hs1
  let g : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E) := Matrix.of fun _ _ => algebraMap (Ainf F) (Ainf F ⊗[F] E) t
  have hg : IsUnit g.det := by
    rw [Matrix.det_fin_one]
    exact ht.map (algebraMap (Ainf F) (Ainf F ⊗[F] E))
  have hrm : (fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => GlobalTheory.CompanionTheory.SW.rmul (Ainf F) X g) =
      fun X p i => algebraMap (Ainf F) (Ainf F ⊗[F] E) t * X p i := by
    funext X p i
    simp only [GlobalTheory.CompanionTheory.SW.rmul, Fin.sum_univ_one, g, Matrix.of_apply]
    rw [Subsingleton.elim p 0, mul_comm]
  have hsig : sigR (Ainf F) σ (algebraMap (Ainf F) (Ainf F ⊗[F] E) t) = algebraMap (Ainf F) (Ainf F ⊗[F] E) t := by
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
  let τ : HermR (Ainf F) σ 1 → HermR (Ainf F) σ 1 := fun S =>
    ⟨fun i j => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t ^ 2) * (S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) i j, by
      intro i j
      have := S.2 i j
      show sigR (Ainf F) σ (_ * _) = _ * _
      rw [map_mul, this, map_pow, map_pow, hsig]⟩
  have hτe : ∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) i j =
      algebraMap (Ainf F) (Ainf F ⊗[F] E) (t ^ 2) * (S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) i j := fun _ _ _ => rfl
  have hτm : Measurable τ := by
    haveI : BorelSpace (HermR (Ainf F) σ 1) := ⟨rfl⟩
    have : Continuous τ := by
      refine Continuous.subtype_mk ?_ _
      refine continuous_pi fun i => continuous_pi fun j => ?_
      exact continuous_const.mul ((continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val))
    exact this.measurable
  have hc := GlobalTheory.T.hermitian_measure_scaling_transform F E σ hσ 2 b lam hlam (t ^ 2) (ht.pow 2) _ hs2 τ hτm hτe
  have hτ : ∀ S, (τ S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) = HeckeCharacterZeroLocus.SiegelWeilU.cT (sigR (Ainf F) σ) g * S * g := by
    intro S
    ext i j
    rw [hτe, map_pow, GlobalTheory.CompanionTheory.SW.Dil.cT_scalar _ _ hsig]
  have key := GlobalTheory.T.gram_fiber_measures_rmul_equivariant F E σ hσ M J hJ (Ainf F) hloc 1 (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam 1 M)
    (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam 1) m (hW 1 M) (hH 1) hm g hg τ hτ _ _
    (by rw [hrm]; exact hk) hc (GlobalTheory.CompanionTheory.SW.hermScal (Ainf F) σ s)
  have hτs : τ (GlobalTheory.CompanionTheory.SW.hermScal (Ainf F) σ s) = GlobalTheory.CompanionTheory.SW.hermScal (Ainf F) σ (t ^ 2 * s) := by
    apply Subtype.ext
    funext i j
    change algebraMap (Ainf F) (Ainf F ⊗[F] E) (t ^ 2) * (s ⊗ₜ[F] (1 : E)) = (t ^ 2 * s) ⊗ₜ[F] (1 : E)
    simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
  rw [hτs, hrm] at key
  have e1 : (N ^ (2 * M)) * (N⁻¹ ^ (2 * M)) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hN0, one_pow]
  have e2 : (N ^ (2 * M)) * (N ^ 2)⁻¹ = N ^ (2 * M - 2) := by
    obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
    have : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [this, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hN0), mul_one]
    simp
  have key2 := congrArg (fun μ' => (N ^ (2 * M)) • μ') key
  simp only [smul_smul] at key2
  rw [e1, e2, one_smul] at key2
  exact key2

theorem dilation_inf_binary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F)), IsStdInf li →
  ∀ (mi : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin 2 → Ainf F ⊗[F] E)),
  IsGramFib (Ainf F) σ J 1 (coordW (Ainf F) b li 1 2) (coordHerm (Ainf F) σ b li 1) mi →
  ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ ε : ℝ, 0 < ε → ∀ (s : Ainf F) (φ : (Fin 1 → Fin 2 → Ainf F ⊗[F] E) → ℝ), Continuous φ →
  ENNReal.ofReal (ε ^ (4 * Module.finrank ℚ F)) * ∫⁻ X, ENNReal.ofReal (φ (PositivityTheory.Rg.Mass.dil θ ε X)) ∂(mi (hermScal (Ainf F) σ s)) =
    ENNReal.ofReal ((ε ^ 2) ^ Module.finrank ℚ F) * ∫⁻ X, ENNReal.ofReal (φ X) ∂(mi (hermScal (Ainf F) σ (θ (ε ^ 2) * s))) := by
  intro F E _ _ _ _ _ σ hσ J hJ d b li hli mi hm θ hθ ε hε s φ hφ
  obtain ⟨-, e, -, he, -, habs, -⟩ := GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hσ.1
  obtain ⟨i1, i2, i3, i4, -, -, -, hB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  haveI : BorelSpace (Fin 1 → Fin 2 → Ainf F ⊗[F] E) := hB 1 2
  set t : Ainf F := θ ε with ht_def
  have ht : IsUnit t := (isUnit_iff_ne_zero.2 hε.ne').map θ
  have key := fibre_unit_dilation F E σ hσ 2 J hJ (by norm_num) d b li hli.1 mi hm e he s t ht
  set n := Module.finrank ℚ F with hn
  have hw : ∀ w, ‖e t w‖₊ = ε.toNNReal := by
    intro w
    have h1 := (PositivityTheory.PlacePermOperatorBicommutantSpan.theta_real F hσ.1).2 θ hθ ε w
    have h2 := habs t w
    apply NNReal.eq
    rw [coe_nnnorm, Real.norm_eq_abs, h2, Real.coe_toNNReal _ hε.le]
    rw [show ‖t w‖ = ‖θ ε w‖ from rfl, h1, abs_of_pos hε]
  have hN : ∏ w, ‖e t w‖₊ = ε.toNNReal ^ n := by
    have hc : Fintype.card (InfinitePlace F) = n := by
      have := hσ.1
      rw [hn, IsTotallyReal.finrank F, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
        IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
    rw [Finset.prod_congr rfl fun w _ => hw w, Finset.prod_const, Finset.card_univ, hc]
  have hs : θ (ε ^ 2) * s = t ^ 2 * s := by rw [map_pow]
  have hD : Continuous (fun (X : Fin 1 → Fin 2 → Ainf F ⊗[F] E) p i => algebraMap (Ainf F) (Ainf F ⊗[F] E) t * X p i) :=
    continuous_pi fun p => continuous_pi fun i =>
      continuous_const.mul ((continuous_apply i).comp (continuous_apply p))
  have hf : Measurable (fun X => ENNReal.ofReal (φ X)) := hφ.measurable.ennreal_ofReal
  rw [hs, key, lintegral_smul_measure, lintegral_map hf hD.measurable, hN]
  have hdil : ∀ X, PositivityTheory.Rg.Mass.dil θ ε X = fun p i => algebraMap (Ainf F) (Ainf F ⊗[F] E) t * X p i := by
    intro X
    funext p i
    simp [PositivityTheory.Rg.Mass.dil, Algebra.TensorProduct.algebraMap_apply, ht_def]
  simp only [hdil]
  rw [ENNReal.smul_def, smul_eq_mul, ← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [NNReal.coe_pow, Real.coe_toNNReal _ hε.le]
  ring

end GlobalTheory.CompanionTheory.BinaryDil

end
end

section

set_option linter.unusedSectionVars false

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.SiegelAssemble

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}


variable (F E) in
abbrev phiInf : AF F ⊗[F] E →ₐ[F] Ainf F ⊗[F] E := Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)


variable (F E) in
abbrev phiFin : AF F ⊗[F] E →ₐ[F] Af F ⊗[F] E := Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)


omit [NumberField E] in
theorem tens_ext {z z' : AF F ⊗[F] E} (h₁ : phiInf F E z = phiInf F E z') (h₂ : phiFin F E z = phiFin F E z') :
    z = z' := by
  obtain ⟨y, hy⟩ : ∃ y : AF F ⊗[F] E, y = z - z' + 1 := ⟨_, rfl⟩
  have := GlobalTheory.AutFunCounterexample.tens_inj (F := F) (E := E) (A := Ainf F) (B := Af F) (n := 1)
    (Matrix.of fun _ _ => y)
    (by
      ext i j
      rw [Subsingleton.elim i j, Matrix.one_apply_eq]
      change phiInf F E y = 1
      rw [hy, map_add (f := _), map_sub, h₁, sub_self, zero_add, map_one])
    (by
      ext i j
      rw [Subsingleton.elim i j, Matrix.one_apply_eq]
      change phiFin F E y = 1
      rw [hy, map_add (f := _), map_sub, h₂, sub_self, zero_add, map_one])
  have h3 : z - z' + 1 = 1 := hy.symm.trans (congrFun (congrFun this 0) 0)
  exact sub_eq_zero.1 (add_right_cancel (h3.trans (zero_add 1).symm))

omit [NumberField E] in
theorem matrix_tens_ext {a b : Type} {P Q : Matrix a b (AF F ⊗[F] E)} (h₁ : P.map (phiInf F E) = Q.map (phiInf F E))
    (h₂ : P.map (phiFin F E) = Q.map (phiFin F E)) : P = Q :=
  Matrix.ext fun i j => tens_ext (congrFun (congrFun h₁ i) j) (congrFun (congrFun h₂ i) j)

omit [NumberField E] in
theorem mat_projInf (g : GAd σ J) : (matHom _ σ J (projInf σ J g)).1 = (matHom _ σ J g).1.map (phiInf F E) := rfl

omit [NumberField E] in
theorem mat_projFin (g : GAd σ J) : (matHom _ σ J (projFin σ J g)).1 = (matHom _ σ J g).1.map (phiFin F E) := rfl

theorem mem_minPar_of_parts {p q : GAd σ J} (hp : p ∈ minPar σ J X) (h₁ : projInf σ J q = projInf σ J p)
    (h₂ : projFin σ J q = 1) : q ∈ minPar σ J X := by
  obtain ⟨B, hB, e⟩ := hp
  let e₀ : AF F ⊗[F] E := (((1 : Ainf F), (0 : Af F)) : AF F) ⊗ₜ[F] (1 : E)
  have e₁ : phiInf F E e₀ = 1 := rfl
  have e₂ : phiFin F E e₀ = 0 := TensorProduct.zero_tmul _ _
  let B' : Matrix (Fin r) (Fin r) (AF F ⊗[F] E) :=
    Matrix.of fun i j => (1 : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)) i j +
      e₀ * (B i j - (1 : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)) i j)
  have b₁ : B'.map (phiInf F E) = B.map (phiInf F E) := Matrix.ext fun i j => by
    simp [B', e₁]
  have b₂ : B'.map (phiFin F E) = 1 := Matrix.ext fun i j => by
    by_cases hij : i = j
    · subst hij; simp [B', e₂]
    · simp [B', e₂, Matrix.one_apply_ne hij]
  refine ⟨B', fun i j hij => ?_, matrix_tens_ext ?_ ?_⟩
  · have hne : i ≠ j := fun e => by subst e; exact lt_irrefl _ hij
    simp [B', hB hij, Matrix.one_apply_ne hne]
  · rw [Matrix.map_mul, Matrix.map_mul, ← mat_projInf, h₁, mat_projInf, b₁, ← Matrix.map_mul, e, Matrix.map_mul]
  · rw [Matrix.map_mul, Matrix.map_mul, ← mat_projFin, h₂, b₂]
    simp

theorem commute_of_mem {a b : GAd σ J} (ha : a ∈ infPts σ J) (hb : b ∈ finPts σ J) : Commute a b := by
  have ha' : a ∈ (ofInf σ J).range := by rw [range_ofInf]; exact ha
  have hb' : b ∈ (ofFin σ J).range := by rw [range_ofFin]; exact hb
  obtain ⟨x, rfl⟩ := ha'
  obtain ⟨y, rfl⟩ := hb'
  exact commute_ofInf_ofFin σ J x y

theorem mul_mem_leviMin {a b : GAd σ J} (ha : a ∈ leviMin σ J X Y) (hb : b ∈ leviMin σ J X Y) :
    a * b ∈ leviMin σ J X Y := by
  obtain ⟨d₁, d₁', e₁, e₁'⟩ := ha
  obtain ⟨d₂, d₂', e₂, e₂'⟩ := hb
  refine ⟨d₁ * d₂, d₁' * d₂', ?_, ?_⟩
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, e₂, ← Matrix.mul_assoc, e₁, Matrix.mul_assoc,
      diagonal_mul_diagonal]
    rfl
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, e₂', ← Matrix.mul_assoc, e₁', Matrix.mul_assoc,
      diagonal_mul_diagonal]
    rfl

def prodSub (K₁ K₂ : Subgroup (GAd σ J)) (h₁ : K₁ ≤ infPts σ J) (h₂ : K₂ ≤ finPts σ J) : Subgroup (GAd σ J) where
  carrier := (K₁ : Set (GAd σ J)) * (K₂ : Set (GAd σ J))
  one_mem' := ⟨1, K₁.one_mem, 1, K₂.one_mem, one_mul 1⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
    refine ⟨a * a', K₁.mul_mem ha ha', b * b', K₂.mul_mem hb hb', ?_⟩
    have c : b * a' = a' * b := ((commute_of_mem (h₁ ha') (h₂ hb)).eq).symm
    change a * a' * (b * b') = a * b * (a' * b')
    rw [mul_assoc a b, ← mul_assoc b, c, mul_assoc a', mul_assoc]
  inv_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    refine ⟨a⁻¹, K₁.inv_mem ha, b⁻¹, K₂.inv_mem hb, ?_⟩
    change a⁻¹ * b⁻¹ = (a * b)⁻¹
    rw [_root_.mul_inv_rev]
    exact ((commute_of_mem (h₁ (K₁.inv_mem ha)) (h₂ (K₂.inv_mem hb))).eq)

end GlobalTheory.CompanionTheory.SiegelAssemble


open GlobalTheory.CompanionTheory.SiegelAssemble in
theorem GlobalTheory.CompanionTheory.SiegelAssemble.exists_compact_iwasawa : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ K₁ K₂ : Subgroup (GAd σ J), K₁ ≤ infPts σ J → K₂ ≤ finPts σ J → IsCompact (K₁ : Set (GAd σ J)) → IsCompact (K₂ : Set (GAd σ J)) → (∀ g ∈ infPts σ J, ∃ p ∈ minPar σ J X, p ∈ infPts σ J ∧ ∃ k ∈ K₁, g = p * k) → (∀ g ∈ finPts σ J, ∃ p ∈ minPar σ J X, p ∈ finPts σ J ∧ ∃ k ∈ K₂, g = p * k) → (∀ p ∈ minPar σ J X, p ∈ K₁ → p ∈ leviMin σ J X Y) → GoodPosition σ J X Y K₂ → ∃ K : Subgroup (GAd σ J), IsCompact (K : Set (GAd σ J)) ∧ (∀ g, ∃ p ∈ minPar σ J X, ∃ k ∈ K, g = p * k) ∧ GoodPosition σ J X Y K := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW K₁ K₂ h₁ h₂ c₁ c₂ iw₁ iw₂ hlev hgood
  refine ⟨prodSub K₁ K₂ h₁ h₂, (show IsCompact ((K₁ : Set (GAd σ J)) * (K₂ : Set (GAd σ J))) from c₁.mul c₂), fun g => ?_, ?_⟩
  · obtain ⟨p₁, hp₁, hp₁', k₁, hk₁, e₁⟩ := iw₁ (ofInf σ J (projInf σ J g)) (mem_infPts.2 (by simp))
    obtain ⟨p₂, hp₂, hp₂', k₂, hk₂, e₂⟩ := iw₂ (ofFin σ J (projFin σ J g)) (mem_finPts.2 (by simp))
    refine ⟨p₁ * p₂, mul_mem_minimal_parabolic hp₁ hp₂, k₁ * k₂, ⟨k₁, hk₁, k₂, hk₂, rfl⟩, ?_⟩
    have c : k₁ * p₂ = p₂ * k₁ := (commute_of_mem (h₁ hk₁) hp₂').eq
    calc g = ofInf σ J (projInf σ J g) * ofFin σ J (projFin σ J g) := (ofInf_projInf_mul_ofFin_projFin σ J g).symm
      _ = p₁ * (k₁ * p₂) * k₂ := by rw [e₁, e₂]; simp only [mul_assoc]
      _ = p₁ * p₂ * (k₁ * k₂) := by rw [c]; simp only [mul_assoc]
  · rintro _ hp ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    have i₁ : projFin σ J k₁ = 1 := mem_infPts.1 (h₁ hk₁)
    have i₂ : projInf σ J k₂ = 1 := mem_finPts.1 (h₂ hk₂)
    have m₁ : k₁ ∈ minPar σ J X := mem_minPar_of_parts hp (by simp [i₂]) i₁
    have m₂ : k₂ ∈ minPar σ J X := by
      have := mul_mem_minimal_parabolic (inv_mem_minimal_parabolic h hJ hW m₁) hp
      simpa using this
    obtain ⟨m, hm, hmK, u, hu, huK, rfl⟩ := hgood k₂ m₂ hk₂
    exact ⟨k₁ * m, mul_mem_leviMin (hlev k₁ m₁ hk₁) hm, ⟨k₁, hk₁, m, hmK, rfl⟩, u, hu,
      ⟨1, K₁.one_mem, u, huK, one_mul u⟩, by simp only [mul_assoc]⟩

end
end
