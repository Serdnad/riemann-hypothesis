module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.UniformTransfer.UnitaryIntegralLevel
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle412
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle011
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import GroundTheory.AutomorphicForms.GLnLocal
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
import GroundTheory.GlobalFields.SemilocalAlgebras.Infinite
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle502
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle504
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle008
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle012
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle013
public import Formalism.RealPlaceAnalysis.Bundle001
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactLieAction
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle503
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle472
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle492
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.UnitNbhd

open PositivityTheory.RgEis (eSF)

section Gen

variable {R A : Type*} [CommRing R] [Nontrivial R] [CommRing A] [Algebra R A] [Module.Free R A] [Module.Finite R A]

theorem exists_mul_eq_norm (a : A) : ∃ c, a * c = algebraMap R A (Algebra.norm R a) := by
  classical
  let b := Module.Free.chooseBasis R A
  let M := Algebra.leftMulMatrix b a
  refine ⟨Matrix.toLin b b M.adjugate 1, ?_⟩
  have h1 : Algebra.norm R a = M.det := Algebra.norm_eq_matrix_det b a
  have h2 : Matrix.toLin b b M = LinearMap.mulLeft R a := by
    simp only [M, Algebra.leftMulMatrix_apply, Matrix.toLin_toMatrix]
    rfl
  have h3 : Matrix.toLin b b M (Matrix.toLin b b M.adjugate 1) = Matrix.toLin b b (M * M.adjugate) 1 := by
    rw [Matrix.toLin_mul b b b]; rfl
  have h4 : a * Matrix.toLin b b M.adjugate 1 = Matrix.toLin b b M (Matrix.toLin b b M.adjugate 1) := by
    rw [h2]; rfl
  rw [h4, h3, Matrix.mul_adjugate, h1, map_smul, Matrix.toLin_one, LinearMap.smul_apply, LinearMap.id_apply, Algebra.algebraMap_eq_smul_one]

theorem continuous_norm [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace A] [IsModuleTopology R A] :
    Continuous (fun a : A => Algebra.norm R a) := by
  classical
  let b := Module.Free.chooseBasis R A
  have h : (fun a : A => Algebra.norm R a) = fun a => (Algebra.leftMulMatrix b a).det := by
    funext a; exact Algebra.norm_eq_matrix_det b a
  rw [h]
  refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
  have : (fun a : A => Algebra.leftMulMatrix b a i j) = (b.coord i) ∘ₗ (LinearMap.mulRight R (b j)) := by
    funext a
    simp [Algebra.leftMulMatrix_eq_repr_mul]
  rw [this]
  exact IsModuleTopology.continuous_of_linearMap _

end Gen

theorem exists_mul_eq_eSF {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (n : AF F)
    (h1 : ∀ w, evInf F w n ≠ 0) (h2 : ∀ v ∈ S, evFin F v n ≠ 0) : ∃ m : AF F, n * m = eSF S := by
  classical
  refine ⟨((fun w => (evInf F w n)⁻¹ : Ainf F), ∑ v ∈ S, singleFin v (evFin F v n)⁻¹), ?_⟩
  rw [GlobalTheory.CompanionTheory.RgEisUnif.EIdemP.eSF_eq]
  refine Prod.ext ?_ (af_ext fun u => ?_)
  · funext w
    exact mul_inv_cancel₀ (h1 w)
  · change evalV F u (n.2 * ∑ v ∈ S, singleFin v (evFin F v n)⁻¹) = evalV F u (∑ v ∈ S, singleFin v 1)

    rw [map_mul, GlobalTheory.CompanionTheory.RgEisUnif.EIdemP.evalV_sum, map_sum]
    split_ifs with h
    · rw [Finset.sum_eq_single_of_mem u h (fun v _ hv => evalV_singleFin_ne (Ne.symm hv) _), evalV_singleFin_self]
      exact mul_inv_cancel₀ (h2 u h)
    · rw [Finset.sum_eq_zero, mul_zero]
      intro v hv
      exact evalV_singleFin_ne (by rintro rfl; exact h hv) _

theorem evInf_eSF {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (w : InfinitePlace F) :
    evInf F w (eSF S) = 1 := by
  rw [GlobalTheory.CompanionTheory.RgEisUnif.EIdemP.eSF_eq]
  rfl

open Classical in
theorem evFin_eSF {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (v : HeightOneSpectrum (𝓞 F)) : evFin F v (eSF S) = if v ∈ S then 1 else 0 := by
  rw [GlobalTheory.CompanionTheory.RgEisUnif.EIdemP.eSF_eq]
  exact GlobalTheory.CompanionTheory.RgEisUnif.EIdemP.evalV_sum S v

theorem compInf_eSF {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (w : InfinitePlace F) :
    compInf F E w (algebraMap (AF F) (AF F ⊗[F] E) (eSF S)) = 1 := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  change (Algebra.TensorProduct.map (evInf F w) (AlgHom.id F E)) _ = 1
  rw [Algebra.TensorProduct.map_tmul, show algebraMap (AF F) (AF F) (eSF S) = eSF S from rfl, evInf_eSF]
  simp [Algebra.TensorProduct.one_def]

open Classical in
theorem compFin_eSF {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) :
    compFin F E v (algebraMap (AF F) (AF F ⊗[F] E) (eSF S)) = if v ∈ S then 1 else 0 := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  change (Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E)) _ = _
  rw [Algebra.TensorProduct.map_tmul, show algebraMap (AF F) (AF F) (eSF S) = eSF S from rfl, evFin_eSF]
  split_ifs <;> simp [Algebra.TensorProduct.one_def]

theorem eq_algebraMap_eSF
    (hc : ∀ (D : D7) (a : AE D), (∀ w, compInf D.host.F D.host.E w a = 0) → (∀ v, cv D v a = 0) → a = 0)
    (D : D7) (S : Finset (Pl D)) (e : AE D) (he : IsIdem S e) :
    e = algebraMap (AF D.host.F) (AE D) (eSF S) := by
  classical
  rw [← sub_eq_zero]
  refine hc D _ (fun w => ?_) (fun v => ?_)
  · rw [RingHom.map_sub, he.1 w, compInf_eSF, sub_self]
  · refine (RingHom.map_sub _ _ _).trans ?_
    rw [he.2 v]
    refine sub_eq_zero.2 ?_
    exact (compFin_eSF S v).symm

theorem exists_open_mul_eq_idem :
    (∀ (D : D7) (a : AE D), (∀ w, compInf D.host.F D.host.E w a = 0) → (∀ v, cv D v a = 0) → a = 0) →
    ∀ (D : D7) (S : Finset (Pl D)) (e : AE D), IsIdem S e → ∃ U : Set (AE D), IsOpen U ∧ 1 ∈ U ∧ ∀ x ∈ U, ∃ b, x * b = e := by
  intro hc D S e he
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have hn := continuous_norm (R := AF D.host.F) (A := AE D)
  have cI : ∀ w, Continuous (evInf D.host.F w) := fun w => (continuous_apply w).comp continuous_fst
  have cF : ∀ v, Continuous (evFin D.host.F v) := fun v => (RestrictedProduct.continuous_eval v).comp continuous_snd
  refine ⟨{a | (∀ w, evInf D.host.F w (Algebra.norm (AF D.host.F) a) ≠ 0) ∧
    ∀ v ∈ S, evFin D.host.F v (Algebra.norm (AF D.host.F) a) ≠ 0}, ?_, ?_, ?_⟩
  · have h : {a : AE D | (∀ w, evInf D.host.F w (Algebra.norm (AF D.host.F) a) ≠ 0) ∧
        ∀ v ∈ S, evFin D.host.F v (Algebra.norm (AF D.host.F) a) ≠ 0} =
        (⋂ w, {a : AE D | evInf D.host.F w (Algebra.norm (AF D.host.F) a) ≠ 0}) ∩
        ⋂ v ∈ S, {a : AE D | evFin D.host.F v (Algebra.norm (AF D.host.F) a) ≠ 0} := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [h]
    refine (isOpen_iInter_of_finite fun w => ?_).inter (isOpen_biInter_finset fun v _ => ?_)
    · exact isOpen_ne_fun ((cI w).comp hn) continuous_const
    · exact isOpen_ne_fun ((cF v).comp hn) continuous_const
  · simp only [Set.mem_setOf_eq, map_one]
    exact ⟨fun _ => one_ne_zero, fun _ _ => one_ne_zero⟩
  · rintro x ⟨h1, h2⟩
    obtain ⟨c, hxc⟩ := exists_mul_eq_norm (R := AF D.host.F) x
    obtain ⟨m, hm⟩ := exists_mul_eq_eSF S _ h1 h2
    refine ⟨c * algebraMap (AF D.host.F) (AE D) m, ?_⟩
    rw [← mul_assoc, hxc, ← map_mul, hm, eq_algebraMap_eSF hc D S e he]

end GlobalTheory.CompanionTheory.UnitNbhd
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.partial_coefficient_rank_zero : ∀ (D : D7) (p : ℕ) (hn : 0 + p = p) (M : Maps D hn) (m : Meas D 0 p) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D 0) (F : G D p → ℂ) (g : G D p), pc M m ψ b₀ F g = F g := by
  first | exact @GlobalTheory.CompanionTheory.PcZero.pc_eq | exact GlobalTheory.CompanionTheory.PcZero.pc_eq | (intros; apply GlobalTheory.CompanionTheory.PcZero.pc_eq <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.partial_coefficient_uniform_limit : PcBound → ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) {ι : Type} (l : Filter ι) (Fs : ι → G D n → ℂ) (A : G D n → ℂ), Continuous A → LeftInv (GF D n) A → (∀ᶠ i in l, Continuous (Fs i) ∧ LeftInv (GF D n) (Fs i)) → (∀ C : Set (G D n), IsCompact C → ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ c ∈ C, ‖Fs i c - A c‖ ≤ ε) → (∀ᶠ i in l, ∀ (y : Mx D ρ p) (g : G D n), pc M m ψ b₀ (Fs i - A) (M.sh y * g) = pc M m ψ b₀ (Fs i) (M.sh y * g) - pc M m ψ b₀ A (M.sh y * g)) → ∀ (g : G D n) (φ : Mx D ρ p → ℂ), Integrable φ m.μ → Tendsto (fun i => FJ M m ψ b₀ (Fs i) g φ) l (𝓝 (FJ M m ψ b₀ A g φ)) := by
  first | exact @GlobalTheory.CompanionTheory.FJLim.fj_tendsto | exact GlobalTheory.CompanionTheory.FJLim.fj_tendsto | (intros; apply GlobalTheory.CompanionTheory.FJLim.fj_tendsto <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

theorem _root_.GlobalTheory.T.strictly_dominant_hecke_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ t : Levi k (Bl d), IsStrictlyDominant k N J d hd t → ∀ T : Module.End ℂ (fixed π J), IsHeckeOp π J (leviEmb k (stdBlocks d hd) t) T → ∀ v : fixed π J, (Submodule.Quotient.mk (v : V) : Jacquet π (unipRad k (stdBlocks d hd))) = 0 → ∃ r : ℕ, (T ^ r) v = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Lbc.heckeOp_nilpotent_on_ker | exact GlobalTheory.CompanionTheory.Lbc.heckeOp_nilpotent_on_ker | (intros; apply GlobalTheory.CompanionTheory.Lbc.heckeOp_nilpotent_on_ker <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

theorem _root_.GlobalTheory.T.jacquet_fixed_vector_lift : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsAdmissible π → ∀ w ∈ fixed (jac (stdBlocks d hd) π) (KM k N J d hd), ∃ v : fixed π J, (Submodule.Quotient.mk (v : V) : Jacquet π (unipRad k (stdBlocks d hd))) = w := by
  first | exact @GlobalTheory.CompanionTheory.JacquetLemma.jacquet_surjective | exact GlobalTheory.CompanionTheory.JacquetLemma.jacquet_surjective | (intros; apply GlobalTheory.CompanionTheory.JacquetLemma.jacquet_surjective <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.EisRat

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem hgt_par_mul {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} (hK : IsHgt K a) {p : G2 σ Y} {t : GL (Fin n) (AE F E)}
    (hp : IsPar p t) (x : G2 σ Y) :
    a (p * x) = (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) * a x := by
  obtain ⟨p', t', hp', k, hk, rfl⟩ := hK.iwa x
  rw [← mul_assoc, hK.val _ _ (hp.mul hp') k hk, hK.val _ _ hp' k hk, map_mul, map_mul]
  push_cast
  rfl

theorem hgt_nonneg {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} (hK : IsHgt K a) (x : G2 σ Y) : 0 ≤ a x := by
  obtain ⟨p, t, hp, k, hk, rfl⟩ := hK.iwa x
  rw [hK.val _ _ hp k hk]
  exact NNReal.coe_nonneg _

theorem absE_ne_zero (u : (AF F ⊗[F] E)ˣ) : ((absE F E u : ℝ) : ℂ) ≠ 0 := by
  have h : absE F E u ≠ 0 := ((absE F E).toHomUnits u).ne_zero
  exact_mod_cast h

theorem law_flat {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} (hK : IsHgt K a) {χ : Chr F E} {s₁ : ℂ} {f : G2 σ Y → ℂ}
    (hf : IsSec K χ s₁ f) (s : ℂ) : Law χ (s + n / 2) (flat a f s₁ s) := by
  intro p t x hp
  have hd := absE_ne_zero (F := F) (E := E) (Matrix.GeneralLinearGroup.det t)
  have h0 : (0 : ℝ) ≤ (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) := NNReal.coe_nonneg _
  have hc : ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ (s + (n : ℂ) / 2) =
      ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ (s - s₁) *
        ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ (s₁ + (n : ℂ) / 2) := by
    rw [← Complex.cpow_add _ _ hd]
    congr 1
    ring
  simp only [_root_.GlobalTheory.ThK.Dbl.flat]
  rw [hgt_par_mul hK hp x, hf.law p t x hp, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg h0 (hgt_nonneg hK x), hc]
  ring

end GlobalTheory.CompanionTheory.EisRat

namespace GlobalTheory.CompanionTheory.EisRat

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

theorem eis_left_rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → IsHecke F E χ → ∀ (t : ℝ) (Ê : ℂ → G2 σ Y → ℂ), (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) → ∀ s : ℂ, t < s.re → ∀ γ ∈ rat2 σ Y, ∀ x, Ê s (γ * x) = Ê s x := by
  intro F E _ _ _ _ _ σ B n Y r s _ _ _ b K a _ _ hK χ s₁ f hf hχ t Ê hs s' hs' γ hγ x
  exact (law_flat hK hf s').eis_rat hχ (hs s' hs') hγ x

end GlobalTheory.CompanionTheory.EisRat

end
end

section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

theorem _root_.GlobalTheory.T.sl2_square_kills_vector : ∀ {n : ℕ} {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (E : Fin n → Fin n → Module.End ℂ Z), Formalism.REAL.GlRel E →
    (∀ x y (f g : Z), ⟪E x y f, g⟫_ℂ = ⟪f, E y x g⟫_ℂ) → ∀ {i j : Fin n}, i ≠ j → ∀ {a : Z}, a ≠ 0 →
    ∀ {p r : ℝ}, E i i a = (p : ℂ) • a → E j j a = (r : ℂ) • a → (∃ m : ℤ, p - r = m) → -1 ≤ p - r →
    (E i j a = 0 ∨ E j i a = 0) → ((E i j) ^ 2) a = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.sl2_square_kills | exact GlobalTheory.CompanionTheory.RealCount.sl2_square_kills | (intros; apply GlobalTheory.CompanionTheory.RealCount.sl2_square_kills <;> assumption)
end

section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

theorem _root_.GlobalTheory.T.exists_compact_lie_action : ∀ {n : ℕ} (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H)), Continuous ρ → (∀ k v, ‖ρ k v‖ = ‖v‖) → ∃ G : Fin n → Fin n → Module.End ℂ H, Formalism.REAL.GlRel G ∧ (∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ) ∧ (∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X → (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ w : H, HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0) := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.DerivRep.derivative_of_rep | exact GlobalTheory.CompanionTheory.RealCount.DerivRep.derivative_of_rep | (intros; apply GlobalTheory.CompanionTheory.RealCount.DerivRep.derivative_of_rep <;> assumption)
end

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG.HwStable

variable {n : ℕ}

theorem weight_shift_real {V : Type} [AddCommGroup V] [Module ℂ V] {K : Fin n → Fin n → Module.End ℂ V}
    (hg : Formalism.REAL.GlRel K) (μ : Fin n → ℝ) {v : V}
    (hv : ∀ c, K c c v = ((μ c : ℝ) : ℂ) • v) {a b : Fin n} (hab : a ≠ b) (c : Fin n) :
    K c c (K a b v) =
      ((μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0) : ℝ) : ℂ) • K a b v := by
  have e : K c c (K a b v) = K a b (K c c v) +
      ((if c = a then K c b else 0) - (if b = c then K a c else 0)) v := by
    rw [← hg c c a b]
    simp [Module.End.mul_apply]
  rw [e, hv c, map_smul]
  by_cases h1 : c = a
  · subst h1
    have h2 : ¬ b = c := fun h => hab h.symm
    have h3 : ¬ c = b := hab
    simp only [↓reduceIte, h2, h3, LinearMap.sub_apply, LinearMap.zero_apply]
    push_cast
    module
  · by_cases h2 : c = b
    · subst h2
      simp only [↓reduceIte, h1, LinearMap.sub_apply, LinearMap.zero_apply]
      push_cast
      module
    · have h3 : ¬ b = c := fun h => h2 h.symm
      simp only [↓reduceIte, h1, h2, h3, sub_zero, LinearMap.zero_apply, add_zero]

section Main

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  {G : Fin n → Fin n → Module.End ℂ H} {N : Submodule ℂ H}

def diagOn (G : Fin n → Fin n → Module.End ℂ H) (N : Submodule ℂ H)
    (hst : ∀ a b, ∀ w ∈ N, G a b w ∈ N) (c : Fin n) : Module.End ℂ N :=
  (G c c).restrict (hst c c)

theorem diagOn_symm (hs : ∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ)
    (hst : ∀ a b, ∀ w ∈ N, G a b w ∈ N) (c : Fin n) : (diagOn G N hst c).IsSymmetric := by
  intro x y
  exact hs c c x.1 y.1

theorem diag_commute (hg : Formalism.REAL.GlRel G) (i j : Fin n) : Commute (G i i) (G j j) := by
  have h := hg i i j j
  by_cases hij : i = j
  · subst hij
    exact Commute.refl _
  · have h' : ¬ j = i := fun h => hij h.symm
    rw [if_neg hij, if_neg h', sub_zero] at h
    exact sub_eq_zero.1 h

theorem diagOn_commute (hg : Formalism.REAL.GlRel G) (hst : ∀ a b, ∀ w ∈ N, G a b w ∈ N) (i j : Fin n) :
    Commute (diagOn G N hst i) (diagOn G N hst j) := by
  have h : G i i * G j j = G j j * G i i := diag_commute hg i j
  show diagOn G N hst i * diagOn G N hst j = diagOn G N hst j * diagOn G N hst i
  ext x
  have := congrArg (fun f : Module.End ℂ H => f x.1) h
  simpa [diagOn, Module.End.mul_apply] using this

def wts (G : Fin n → Fin n → Module.End ℂ H) (N : Submodule ℂ H) : Set (Fin n → ℝ) :=
  {μ | ∃ v ∈ N, v ≠ 0 ∧ ∀ c, G c c v = ((μ c : ℝ) : ℂ) • v}

theorem wts_nonempty (hg : Formalism.REAL.GlRel G) (hs : ∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ)
    (hN : N ≠ ⊥) (hst : ∀ a b, ∀ w ∈ N, G a b w ∈ N) : (wts G N).Nonempty := by
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute (fun c => diagOn_symm hs hst c)
    (fun i j _ => diagOn_commute hg hst i j)
  haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.2 hN
  obtain ⟨χ, hχ⟩ : ∃ χ : Fin n → ℂ, (⨅ c, Module.End.eigenspace (diagOn G N hst c) (χ c)) ≠ ⊥ := by
    by_contra hcon
    push_neg at hcon
    rw [iSup_congr hcon, iSup_bot] at htop
    exact bot_ne_top htop
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  have hev : ∀ c, diagOn G N hst c x = χ c • x := fun c =>
    Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hx c)
  have hre : ∀ c, (((χ c).re : ℝ) : ℂ) = χ c := fun c => by
    have hE : Module.End.HasEigenvalue (diagOn G N hst c) (χ c) :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 (hev c), hx0⟩
    exact Complex.conj_eq_iff_re.1 ((diagOn_symm hs hst c).conj_eigenvalue_eq_self hE)
  refine ⟨fun c => (χ c).re, x.1, x.2, fun h => hx0 (Subtype.ext h), fun c => ?_⟩
  rw [hre c]
  exact congrArg Subtype.val (hev c)

theorem wts_finite (hst : ∀ a b, ∀ w ∈ N, G a b w ∈ N) : (wts G N).Finite := by
  have hfa : ∀ a, Set.Finite {r : ℝ | Module.End.HasEigenvalue (diagOn G N hst a) ((r : ℝ) : ℂ)} := fun a =>
    (Module.End.finite_hasEigenvalue _).preimage (Function.Injective.injOn Complex.ofReal_injective)
  refine (Set.Finite.pi' hfa).subset ?_
  rintro μ ⟨v, hv, h0, hw⟩ a
  exact Module.End.hasEigenvalue_of_hasEigenvector (x := (⟨v, hv⟩ : N))
    ⟨Module.End.mem_eigenspace_iff.2 (Subtype.ext (hw a)), fun h => h0 (congrArg Subtype.val h)⟩

end Main

theorem exists_highest_of_stable : ∀ {n : ℕ} (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (G : Fin n → Fin n → Module.End ℂ H), Formalism.REAL.GlRel G →
    (∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ) → ∀ N : Submodule ℂ H, N ≠ ⊥ →
    (∀ a b, ∀ w ∈ N, G a b w ∈ N) →
    ∃ (μ : Fin n → ℝ) (v : H), v ∈ N ∧ v ≠ 0 ∧ Formalism.REAL.KHighest (fun _ => true) G μ v := by
  intro n H _ _ _ G hg hs N hN hst
  have hfin := wts_finite hst
  obtain ⟨μ, hμ, hmax⟩ := hfin.toFinset.exists_max_image (fun ν => toLex ν)
    (by simpa using wts_nonempty hg hs hN hst)
  obtain ⟨v, hvN, hv0, hw⟩ := hfin.mem_toFinset.1 hμ
  refine ⟨μ, v, hvN, hv0, hw, fun a b hab _ => ?_⟩
  by_contra hne
  let μ' : Fin n → ℝ := fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)
  have hlt : toLex μ < toLex μ' := by
    refine ⟨a, fun j hj => ?_, ?_⟩
    · have h1 : j ≠ a := ne_of_lt hj
      have h2 : j ≠ b := ne_of_lt (lt_trans hj hab)
      show μ j = μ j + (if j = a then 1 else 0) - (if j = b then 1 else 0)
      simp [h1, h2]
    · show μ a < μ a + (if a = a then 1 else 0) - (if a = b then 1 else 0)
      simp [ne_of_lt hab]
  have hin : μ' ∈ wts G N :=
    ⟨G a b v, hst a b v hvN, hne, fun c => weight_shift_real hg μ hw (ne_of_lt hab) c⟩
  exact not_le.2 hlt (hmax μ' (hfin.mem_toFinset.2 hin))

end GlobalTheory.CompanionTheory.RealCountG.HwStable
end
end

section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

theorem _root_.GlobalTheory.T.highest_weight_antitone_alt : ∀ {n : ℕ} (V : Type) [AddCommGroup V] [Module ℂ V] (Kf : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V)
    (ν : Fin n → ℝ) (v : V), Formalism.REAL.GlRel Kf → FiniteDimensional ℂ S → (∀ a b, ∀ w ∈ S, Kf a b w ∈ S) → v ∈ S → v ≠ 0 →
    Formalism.REAL.KHighest (fun _ => true) Kf ν v → Antitone ν := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.highestWeight_antitone_of_finiteDimensional_stable | exact GlobalTheory.CompanionTheory.RealCount.highestWeight_antitone_of_finiteDimensional_stable | (intros; apply GlobalTheory.CompanionTheory.RealCount.highestWeight_antitone_of_finiteDimensional_stable <;> assumption)
end
