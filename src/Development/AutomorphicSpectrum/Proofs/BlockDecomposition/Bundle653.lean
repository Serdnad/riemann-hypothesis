module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle608
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle632
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle062
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle050
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSKfOrb
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle622
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle636
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle638
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle639
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMaxEvenAdaptedLattice
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlagTransitiveOfBase
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle634
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle585
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle459
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle007
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle004
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle005

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.euler_product_measure_eventually_standard : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (M n d : ℕ) (b : Module.Basis (Fin d) F E) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (c : NNReal) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), GlobalTheory.CompanionTheory.SW.IsEulerProd b I c minf m → ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S → ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, Measurable φ → Integrable φ minf → ∀ A : (∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, MeasurableSet (A v)) → (∀ v, m v (A v) ≠ ⊤) → (∀ v, v ∉ S → A v = latV b v) → Integrable (pureN φ A) I ∧ ∫ X, pureN φ A X ∂I = (c : ℂ) * (∫ X, φ X ∂minf) * (∏ v ∈ S, ((m v (A v)).toReal : ℂ)) * ((∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal : ℝ) : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.Euler.integrable_integral_pureN | exact GlobalTheory.CompanionTheory.SiegelND.Coef.Euler.integrable_integral_pureN | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.Euler.integrable_integral_pureN <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.Grams

theorem sub_gramH_mem_latH : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n d : ℕ) (b : Module.Basis (Fin d) F E) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite, ∀ X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)), hermOf (Fv F v) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Fv F v) X ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.latH σ b v n := by
  intro F E _ _ _ _ _ σ hCM M J hJ n d b T hT
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have hb : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      ∀ k, inclR (F := F) (Fv F v) (b k) ∈ Formalism.L2.SG.LocVol.OEv (E := E) v :=
    Filter.eventually_all.2 fun k => Formalism.L2.SG.Pf.NcS.IntWittPf.ev_oev (b k)
  have hJ' : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      ∀ i j, inclR (F := F) (Fv F v) (J i j) ∈ Formalism.L2.SG.LocVol.OEv (E := E) v :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => Formalism.L2.SG.Pf.NcS.IntWittPf.ev_oev (J i j)
  have hT' : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      ∀ a c, inclR (F := F) (Fv F v) (T a c) ∈ Formalism.L2.SG.LocVol.OEv (E := E) v :=
    Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun c => Formalism.L2.SG.Pf.NcS.IntWittPf.ev_oev (T a c)
  have htr : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      ∀ k, algebraMap F (Fv F v) (Algebra.trace F E (b k)) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => Formalism.L2.SG.Pf.NcS.KfOrbPf.ev_int (Algebra.trace F E (b k))
  filter_upwards [Formalism.L2.SG.Pf.NcS.KfOrbPf.ev_int (F := F) (1 / 2), hb, hJ', hT', htr,
    Formalism.L2.SG.Pf.NcS.KfOrbPf.ev_crd_oev (E := E) b] with v hh hbv hJv hTv htrv hc X hX
  have hrepr : ∀ z : Fv F v ⊗[F] E,
      z = ∑ k, (Algebra.TensorProduct.basis (Fv F v) b).repr z k • ((1 : Fv F v) ⊗ₜ[F] b k) := by
    intro z
    conv_lhs => rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr z]
    simp only [Algebra.TensorProduct.basis_apply]
  have hx : ∀ a i, X a i ∈ Formalism.L2.SG.Pf.NcS.IntWittPf.oevRing (E := E) v := by
    intro a i
    rw [hrepr (X a i)]
    refine Subring.sum_mem _ fun k _ => ?_
    exact Formalism.L2.SG.Pf.NcS.IntWittPf.oev_smul' v (hX a i k) (hbv k)
  have hG : ∀ a c, hR (Fv F v) σ J (X a) (X c) ∈ Formalism.L2.SG.Pf.NcS.IntWittPf.oevRing (E := E) v := by
    intro a c
    show ∑ i, ∑ j, sigR (Fv F v) σ (X a i) * JR (Fv F v) J i j * X c j ∈
      Formalism.L2.SG.Pf.NcS.IntWittPf.oevRing (E := E) v
    refine sum_mem fun i _ => sum_mem fun j _ => ?_
    exact mul_mem (mul_mem (Formalism.L2.SG.Pf.NcS.IntWittPf.oev_sigR v σ (hx a i)) (hJv i j)) (hx c j)
  have hS : ∀ a c, ((hermOf (Fv F v) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Fv F v) X :
      HermR (Fv F v) σ n) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a c ∈
      Formalism.L2.SG.Pf.NcS.IntWittPf.oevRing (E := E) v := by
    intro a c
    exact sub_mem (hTv a c) (hG a c)
  have htrace : ∀ z ∈ Formalism.L2.SG.Pf.NcS.IntWittPf.oevRing (E := E) v,
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z ∈ v.adicCompletionIntegers F := by
    intro z hz

    rw [hrepr z, map_sum]
    refine sum_mem fun k _ => ?_
    rw [map_smul, GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.trace_one_tmul_len, smul_eq_mul]
    exact mul_mem (hc _ hz k) (htrv k)
  exact ⟨fun i => mul_mem hh (htrace _ (hS i i)), fun i j _ k => hc _ (hS i j) k⟩

end GlobalTheory.CompanionTheory.SiegelND.Coef.Grams
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

open Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.NcS.KfOrbPf Formalism.L2.SG.Pf.NcS.IntWittPf

private theorem tensorBasis_repr_tmul {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (c : R) (e : E) (m : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (c ⊗ₜ[F] e) m = c * algebraMap F R (b.repr e m) := by
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp [Algebra.smul_def]

private theorem eq_sum_repr_tmul_basis {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (z : R ⊗[F] E) :
    z = ∑ k, ((Algebra.TensorProduct.basis R b).repr z k) ⊗ₜ[F] b k := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr z]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem tensorBasis_repr_sum_mem_of_repr_mem {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (O : Subring R) {ι : Type} (s : Finset ι)
    (f : ι → R ⊗[F] E) (h : ∀ x ∈ s, ∀ m, (Algebra.TensorProduct.basis R b).repr (f x) m ∈ O) (m : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (∑ x ∈ s, f x) m ∈ O := by

  rw [map_sum, Finsupp.finsetSum_apply]
  exact O.sum_mem fun x hx => h x hx m

private theorem tensorBasis_repr_tmul_mem_of_mem {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (O : Subring R) (c : R) (e : E) (hc : c ∈ O)
    (he : ∀ m, algebraMap F R (b.repr e m) ∈ O) (m : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (c ⊗ₜ[F] e) m ∈ O := by
  rw [tensorBasis_repr_tmul]
  exact O.mul_mem hc (he m)

private theorem tensorBasis_repr_mul_mem_of_repr_mem {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (O : Subring R)
    (hb : ∀ k l m, algebraMap F R (b.repr (b k * b l) m) ∈ O) (z w : R ⊗[F] E)
    (hz : ∀ m, (Algebra.TensorProduct.basis R b).repr z m ∈ O)
    (hw : ∀ m, (Algebra.TensorProduct.basis R b).repr w m ∈ O) (m : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (z * w) m ∈ O := by
  rw [eq_sum_repr_tmul_basis b z, eq_sum_repr_tmul_basis b w, Finset.sum_mul_sum]
  refine tensorBasis_repr_sum_mem_of_repr_mem b O _ _ (fun k _ m' => tensorBasis_repr_sum_mem_of_repr_mem b O _ _ (fun l _ m'' => ?_) m') m
  rw [Algebra.TensorProduct.tmul_mul_tmul]
  exact tensorBasis_repr_tmul_mem_of_mem b O _ _ (O.mul_mem (hz k) (hw l)) (hb k l) m''

private theorem tensorBasis_repr_sigR_mem_of_repr_mem {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (O : Subring R) (σ : E →ₐ[F] E)
    (hs : ∀ k m, algebraMap F R (b.repr (σ (b k)) m) ∈ O) (z : R ⊗[F] E)
    (hz : ∀ m, (Algebra.TensorProduct.basis R b).repr z m ∈ O) (m : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (sigR R σ z) m ∈ O := by

  rw [eq_sum_repr_tmul_basis b z, map_sum]
  refine tensorBasis_repr_sum_mem_of_repr_mem b O _ _ (fun k _ m' => ?_) m
  simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  exact tensorBasis_repr_tmul_mem_of_mem b O _ _ (hz k) (hs k) m'

theorem hermOf_sub_gramH_mem_latH : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ),
    2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (T : Matrix (Fin n) (Fin n) E)
    (hT : ∀ a c, σ (T c a) = T a c),
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)),
        hermOf (Fv F v) σ T hT - gramH hCM hJ (Fv F v) X ∈ latH σ b v n := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn d b T hT
  have intF : ∀ t : F, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      algebraMap F (Fv F v) t ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
    intro t
    filter_upwards [GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.sub_qR_mem_integers F E σ hCM M J hJ d b t] with v hv
    have h0 := hv 0 (fun a i k => by simp)
    simpa [qR, hR, Formalism.UG.hform] using h0
  have hdiag := Filter.eventually_all.2 fun i : Fin n =>
    GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.sub_qR_mem_integers F E σ hCM M J hJ d b ((1 / 2) * Algebra.trace F E (T i i))
  have h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k l m,
      algebraMap F (Fv F v) (b.repr (b k * b l) m) ∈ HeightOneSpectrum.adicCompletionIntegers F v :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun l => Filter.eventually_all.2 fun m => intF _
  have h2 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k m,
      algebraMap F (Fv F v) (b.repr (σ (b k)) m) ∈ HeightOneSpectrum.adicCompletionIntegers F v :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun m => intF _
  have h3 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ p q m,
      algebraMap F (Fv F v) (b.repr (J p q) m) ∈ HeightOneSpectrum.adicCompletionIntegers F v :=
    Filter.eventually_all.2 fun p => Filter.eventually_all.2 fun q => Filter.eventually_all.2 fun m => intF _
  have h4 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j m,
      algebraMap F (Fv F v) (b.repr (T i j) m) ∈ HeightOneSpectrum.adicCompletionIntegers F v :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => Filter.eventually_all.2 fun m => intF _
  filter_upwards [hdiag, h1, h2, h3, h4] with v hd hb hs hJv hTv
  intro X hX
  clear intF hdiag h1 h2 h3 h4
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  unfold latH gramH
  refine ⟨fun i => ?_, fun i j _ k => ?_⟩
  · have hX' := hd i (fun _ => X i) (fun _ a k => hX i a k)
    convert hX' using 1
    simp only [AddSubgroup.coe_sub, Matrix.sub_apply, hermOf, gramR, qR, Matrix.map_apply, map_sub, mul_sub]
    congr 1
    simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
    rw [GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.trace_one_tmul_len, map_mul]
  · let O : Subring (Fv F v) := (HeightOneSpectrum.adicCompletionIntegers F v).toSubring
    have gX : ∀ a p m, (Algebra.TensorProduct.basis (Fv F v) b).repr (X a p) m ∈ O := fun a p m => hX a p m
    have gI : ∀ e : E, (∀ m, algebraMap F (Fv F v) (b.repr e m) ∈ O) →
        ∀ m, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) e) m ∈ O := by
      intro e he m
      simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
      rw [tensorBasis_repr_tmul, one_mul]
      exact he m
    have gH : ∀ m, (Algebra.TensorProduct.basis (Fv F v) b).repr (hR (Fv F v) σ J (X i) (X j)) m ∈ O := by
      intro m
      simp only [hR, Formalism.UG.hform, JR, Matrix.map_apply]
      exact tensorBasis_repr_sum_mem_of_repr_mem b O _ _ (fun p _ m' => tensorBasis_repr_sum_mem_of_repr_mem b O _ _ (fun q _ m'' =>
        tensorBasis_repr_mul_mem_of_repr_mem b O hb _ _ (fun m3 => tensorBasis_repr_mul_mem_of_repr_mem b O hb _ _ (tensorBasis_repr_sigR_mem_of_repr_mem b O σ hs _ (gX i p))
          (gI _ (hJv p q)) m3) (gX j q) m'') m') m
    have gT := gI (T i j) (hTv i j)
    simp only [AddSubgroup.coe_sub, Matrix.sub_apply, hermOf, gramR, Matrix.map_apply, map_sub,
      Finsupp.coe_sub, Pi.sub_apply]
    exact O.sub_mem (gT k) (gH k)

end GlobalTheory.CompanionTheory.SiegelND.Coef
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.local_form_hermitian_perfect : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}, IsCMExt F E σ → IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), IsHerm (sigR (Fv F v) σ) (hR (Fv F v) σ J) ∧ IsPerfect (hR (Fv F v) σ J) := by
  first | exact @GlobalTheory.CompanionTheory.KFin.isHerm_isPerfect_hR | exact GlobalTheory.CompanionTheory.KFin.isHerm_isPerfect_hR | (intros; apply GlobalTheory.CompanionTheory.KFin.isHerm_isPerfect_hR <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal

theorem _root_.GlobalTheory.T.max_even_lattice_rank_one_split : ∀ {k R V : Type} [Field k] [CommRing R] [AddCommGroup V] [Module R V] (O : ValuationSubring k) (φ : R ≃+* k × k) (c : R →+* R) (𝔬 : Subring R), (∀ r, φ (c r) = (φ r).swap) → (∀ r, r ∈ 𝔬 ↔ (φ r).1 ∈ O ∧ (φ r).2 ∈ O) → ∀ h : V → V → R, IsHerm c h → ∀ w₀ : V, (∀ x, ∃ r : R, x = r • w₀) → IsUnit (h w₀ w₀) → ∀ L : Submodule 𝔬 V, IsMaxEven c 𝔬 h L → ∀ α β : k, (∀ r : R, r • w₀ ∈ L ↔ (∃ x ∈ O, (φ r).1 = α * x) ∧ (∃ y ∈ O, (φ r).2 = β * y)) → α ≠ 0 ∧ β ≠ 0 ∧ ∃ u : k, u ∈ O ∧ u⁻¹ ∈ O ∧ α * β * (φ (h w₀ w₀)).1 = u := by
  first | exact @GlobalTheory.CompanionTheory.KFin.RankOne.unimodular_coords | exact GlobalTheory.CompanionTheory.KFin.RankOne.unimodular_coords | (intros; apply GlobalTheory.CompanionTheory.KFin.RankOne.unimodular_coords <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal

theorem _root_.GlobalTheory.T.hermitian_split_rank_one : ∀ {k R V : Type} [Field k] [CommRing R] [AddCommGroup V] [Module R V] (φ : R ≃+* k × k) (c : R →+* R), (∀ r, φ (c r) = (φ r).swap) → ∀ h : V → V → R, IsHerm c h → IsPerfect h → (∀ x y, h x x = 0 → h x y ≠ 1) → Subsingleton V ∨ ∃ w₀ : V, (∀ x, ∃ r : R, x = r • w₀) ∧ IsUnit (h w₀ w₀) := by
  first | exact @GlobalTheory.CompanionTheory.KFin.hermSwap_struct | exact GlobalTheory.CompanionTheory.KFin.hermSwap_struct | (intros; apply GlobalTheory.CompanionTheory.KFin.hermSwap_struct <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.levi_matrix_map_base_change : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E} (A A' : Type) [CommRing A] [Algebra F A] [CommRing A'] [Algebra F A'] (φ : A →ₐ[F] A') (M : Matrix (Fin n) (Fin n) (A ⊗[F] E)), leviMat σ J A' X Y (M.map (Algebra.TensorProduct.map φ (AlgHom.id F E))) = (leviMat σ J A X Y M).map (Algebra.TensorProduct.map φ (AlgHom.id F E)) := by
  first | exact @GlobalTheory.CompanionTheory.KFin.leviMat_map | exact GlobalTheory.CompanionTheory.KFin.leviMat_map | (intros; apply GlobalTheory.CompanionTheory.KFin.leviMat_map <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal

theorem _root_.GlobalTheory.T.hermitian_valuation_split_criterion : ∀ {k R V : Type} [Field k] [CommRing R] [Algebra k R] [AddCommGroup V] [Module R V] (c : R →+* R) (𝔬 : Subring R) (W : Valuation R ℝ≥0), (∀ a : R, a ≠ 0 → ∃ b : R, a * b = 1) → (∀ a, c (c a) = a) → (∀ a, c a = a → ∃ x : k, algebraMap k R x = a) → (∀ x : k, c (algebraMap k R x) = algebraMap k R x) → (∀ a, a ∈ 𝔬 ↔ W a ≤ 1) → (∀ a, W (c a) = W a) → (∀ a, W a = 0 → a = 0) → (∀ e : k, W (algebraMap k R e) < 1 → ∃ u : k, u * u + u + e = 0) → ∀ h : V → V → R, IsHerm c h → (∀ z, h z z = 0 → z = 0) → ∀ (z w : V) (a b : R), a ∈ 𝔬 → b ∈ 𝔬 → h z z = a + c a → h w w = b + c b → h z w ∈ 𝔬 := by
  first | exact @GlobalTheory.CompanionTheory.KFin.EvenAniso.pair_mem_of_even | exact GlobalTheory.CompanionTheory.KFin.EvenAniso.pair_mem_of_even | (intros; apply GlobalTheory.CompanionTheory.KFin.EvenAniso.pair_mem_of_even <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.local_hermitian_ring : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)), IsHermRing (sigR (Fv F v) σ) (intLoc F E v) := by
  first | exact @GlobalTheory.CompanionTheory.KFin.RingHyp.isHermRing_intLoc | exact GlobalTheory.CompanionTheory.KFin.RingHyp.isHermRing_intLoc | (intros; apply GlobalTheory.CompanionTheory.KFin.RingHyp.isHermRing_intLoc <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_max_even_adapted_lattice : ∀ {R : Type} [CommRing R] (c : R →+* R) (𝔬 : Subring R), IsHermRing c 𝔬 → ∀ {V : Type} [AddCommGroup V] [Module R V] [Module.Finite R V] (h : V → V → R), IsHerm c h → IsPerfect h → ∀ {r : ℕ} (x y : Fin r → V), IsFrame h x y → ∃ L : Submodule 𝔬 V, IsMaxEven c 𝔬 h L ∧ IsAdapted 𝔬 h x y L := by
  first | exact @GlobalTheory.CompanionTheory.KFin.Adapted.exists_maxEven_adapted | exact GlobalTheory.CompanionTheory.KFin.Adapted.exists_maxEven_adapted | (intros; apply GlobalTheory.CompanionTheory.KFin.Adapted.exists_maxEven_adapted <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.flag_transitive_of_base : ∀ {R : Type} [CommRing R] (c : R →+* R) (𝔬 : Subring R), IsHermRing c 𝔬 → HasBase c 𝔬 → FlagTransitive c 𝔬 := by
  first | exact @GlobalTheory.CompanionTheory.KFin.Flag.flagTransitive | exact GlobalTheory.CompanionTheory.KFin.Flag.flagTransitive | (intros; apply GlobalTheory.CompanionTheory.KFin.Flag.flagTransitive <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

noncomputable section

namespace GlobalTheory.CompanionTheory.FinActS

theorem finprod_sum_split {α β M : Type*} [CommMonoid M] (f : α ⊕ β → M)
    (h₁ : (Function.mulSupport fun x => f (Sum.inl x)).Finite)
    (h₂ : (Function.mulSupport fun x => f (Sum.inr x)).Finite) :
    ∏ᶠ i, f i = (∏ᶠ x, f (Sum.inl x)) * ∏ᶠ x, f (Sum.inr x) := by
  have hu : (Set.univ : Set (α ⊕ β)) = Set.range Sum.inl ∪ Set.range Sum.inr := by
    ext i; cases i <;> simp
  have e₁ : (Set.range (Sum.inl : α → α ⊕ β) ∩ Function.mulSupport f).Finite := by
    refine (h₁.image Sum.inl).subset ?_
    rintro _ ⟨⟨x, rfl⟩, hx⟩
    exact ⟨x, hx, rfl⟩
  have e₂ : (Set.range (Sum.inr : β → α ⊕ β) ∩ Function.mulSupport f).Finite := by
    refine (h₂.image Sum.inr).subset ?_
    rintro _ ⟨⟨x, rfl⟩, hx⟩
    exact ⟨x, hx, rfl⟩
  have hd : Disjoint (Set.range (Sum.inl : α → α ⊕ β)) (Set.range (Sum.inr : β → α ⊕ β)) :=
    Set.disjoint_left.2 (by rintro _ ⟨x, rfl⟩ ⟨y, hy⟩; cases hy)
  rw [← finprod_mem_univ, hu, finprod_mem_union' hd e₁ e₂,
    finprod_mem_range Sum.inl_injective, finprod_mem_range Sum.inr_injective]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem finFn_eq_finprod_factor {S : Set (Pl E)} {φ₁ φ₂ : ∀ w : Pl E, LF a b w} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂)
    (y : Hf E a b) : finFn S φ₁ φ₂ y = ∏ᶠ i : Slot S, sf φ₁ φ₂ i (i.cp a b y) := by
  set g₁ : Pl E → ℂ := fun w => φ₁ w (atW w y) with hg₁
  set g₂ : Pl E → ℂ := fun w => if IsSplitAt w then φ₂ w (atW w (thP E a b y)) else 1 with hg₂
  have o₁ : ∀ᶠ w in cofinite, g₁ w = 1 := by
    filter_upwards [GlobalTheory.CompanionTheory.FinTestTw.eventually_eq_indicator h₁, (GlobalTheory.CompanionTheory.FinTestTw.isRestrW a b).eventually_mem y] with w e m
    have m' : atW w y ∈ (K2 a b w : Set (GLw a w × GLw b w)) := m
    simp only [hg₁]
    rw [e, Set.indicator_of_mem m']
    simp
  have o₂ : ∀ᶠ w in cofinite, φ₂ w (atW w (thP E a b y)) = 1 := by
    filter_upwards [GlobalTheory.CompanionTheory.FinTestTw.eventually_eq_indicator h₂,
      (GlobalTheory.CompanionTheory.FinTestTw.isRestrW a b).eventually_mem (thP E a b y)] with w e m
    have m' : atW w (thP E a b y) ∈ (K2 a b w : Set (GLw a w × GLw b w)) := m
    rw [e, Set.indicator_of_mem m']
    simp
  have f₁ : (Function.mulSupport g₁).Finite := eventually_cofinite.1 o₁
  have f₂' : (Function.mulSupport fun w => φ₂ w (atW w (thP E a b y))).Finite := eventually_cofinite.1 o₂
  have f₂ : (Function.mulSupport g₂).Finite := by
    refine f₂'.subset fun w hw => ?_
    by_cases hs : IsSplitAt w
    · simpa [hg₂, hs, Function.mem_mulSupport] using hw
    · exact absurd (by simp [hg₂, hs]) hw
  have l₁ : (Function.mulSupport fun x : {w // w ∈ S} => g₁ x.1).Finite :=
    (f₁.preimage Subtype.val_injective.injOn).subset fun x hx => hx
  have l₂ : (Function.mulSupport fun x : {w // w ∈ S ∧ IsSplitAt w} => φ₂ x.1 (atW x.1 (thP E a b y))).Finite :=
    (f₂'.preimage Subtype.val_injective.injOn).subset fun x hx => hx
  have hs : ∏ᶠ i : Slot S, sf φ₁ φ₂ i (i.cp a b y) =
      (∏ᶠ x : {w // w ∈ S}, g₁ x.1) * ∏ᶠ x : {w // w ∈ S ∧ IsSplitAt w}, φ₂ x.1 (atW x.1 (thP E a b y)) :=
    finprod_sum_split (fun i : Slot S => sf φ₁ φ₂ i (i.cp a b y)) l₁ l₂
  have c₁ : ∏ᶠ x : {w // w ∈ S}, g₁ x.1 = ∏ᶠ w ∈ S, g₁ w :=
    finprod_subtype_eq_finprod_cond (f := g₁) (fun w => w ∈ S)
  have c₂ : ∏ᶠ x : {w // w ∈ S ∧ IsSplitAt w}, φ₂ x.1 (atW x.1 (thP E a b y)) = ∏ᶠ w ∈ S, g₂ w := by
    have e₀ : ∏ᶠ x : {w // w ∈ S ∧ IsSplitAt w}, φ₂ x.1 (atW x.1 (thP E a b y)) =
        ∏ᶠ x : {w // w ∈ S ∧ IsSplitAt w}, g₂ x.1 :=
      finprod_congr fun x => by simp [hg₂, x.2.2]
    rw [e₀, finprod_subtype_eq_finprod_cond (f := g₂) (fun w => w ∈ S ∧ IsSplitAt w)]
    refine finprod_mem_inter_mulSupport_eq' g₂ {w | w ∈ S ∧ IsSplitAt w} S fun w hw => ?_
    have hsp : IsSplitAt w := by
      by_contra hn
      exact hw (by simp [hg₂, hn])
    exact ⟨fun h => h.1, fun h => ⟨h, hsp⟩⟩
  rw [hs, c₁, c₂]
  exact finprod_mem_mul_distrib' (f₁.subset Set.inter_subset_right) (f₂.subset Set.inter_subset_right)

end GlobalTheory.CompanionTheory.FinActS

end
end
