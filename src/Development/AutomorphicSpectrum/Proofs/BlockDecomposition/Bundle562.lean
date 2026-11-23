module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle509
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle547
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAuxiliaryStatementB
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
import GroundTheory.LocalFields.PadicLogSeries
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.IsCuspFormDualMap
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspFormConjugateInverse
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.Bundle002
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousAlgebraUniversalProperty
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelUniqueness
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.SplitCpt

theorem cptPart_le_self' {G : Type} [Group G] [TopologicalSpace G] (T : Subgroup G) : cptPart T ≤ T := by
  rw [cptPart, Subgroup.closure_le]
  rintro t ⟨ht, -⟩
  exact ht

theorem mem_map_conj {G : Type} [Group G] (K : Subgroup G) (x c : G) :
    c ∈ K.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * c * x ∈ K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    simpa [mul_assoc] using hk
  · intro h
    refine ⟨_, h, ?_⟩
    simp [mul_assoc]

theorem split_cpt : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (σ : H →* H) (K : Subgroup H) (d d' : H),
  Continuous σ → (∀ g, σ (σ g) = g) → IsOpen (K : Set H) → IsCompact (K : Set H) → (∀ k ∈ K, σ k ∈ K) →
  PositivityTheory.Rg.BcB.G8.Fin.Good (MonoidHom.id H) K (d * σ d') → ∀ y : H × H,
  twCent (swTw σ) (d, d') ⊓ (K.prod K).map (MulAut.conj y).toMonoidHom ≤ cptPart (twCent (swTw σ) (d, d')) ∧
    (twCent (swTw σ) (d, d') ⊓ (K.prod K).map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent (swTw σ) (d, d'))) ≠ 0 := by
  intro H _ _ _ _ σ K d d' _hσc hσ hKo hKc hσK hG y
  set T := twCent (swTw σ) (d, d') with hT
  set Cn := twCent (MonoidHom.id H) (d * σ d') with hCn
  have hKKc : IsCompact (((K.prod K).map (MulAut.conj y).toMonoidHom : Subgroup (H × H)) : Set (H × H)) := by
    rw [Subgroup.coe_map, Subgroup.coe_prod]
    exact (hKc.prod hKc).image (by
      show Continuous fun z : H × H => y * z * y⁻¹
      fun_prop)
  have hKKcl := hKKc.isClosed
  refine ⟨?_, ?_⟩
  · intro t ht
    apply Subgroup.subset_closure
    refine ⟨ht.1, hKKc.of_isClosed_subset isClosed_closure ?_⟩
    exact closure_minimal (fun z hz => (Subgroup.zpowers_le.2 ht.2) hz) hKKcl
  · have hmapC : (cptPart T).map (MonoidHom.fst H H) ≤ cptPart Cn := by
      rw [Subgroup.map_le_iff_le_comap, cptPart, Subgroup.closure_le]
      rintro t ⟨htT, htc⟩
      apply Subgroup.subset_closure
      refine ⟨((mem_twCent_swTw σ hσ d d' t).1 htT).1, ?_⟩
      have hC := htc.image continuous_fst
      refine hC.of_isClosed_subset isClosed_closure (closure_minimal ?_ hC.isClosed)
      rintro _ ⟨k, rfl⟩
      exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩
    set x₃ : H := σ (d'⁻¹ * y.2) with hx₃
    set B : Subgroup H := (Cn ⊓ K.map (MulAut.conj y.1).toMonoidHom) ⊓ (Cn ⊓ K.map (MulAut.conj x₃).toMonoidHom) with hB
    have hB0 : B.relIndex (cptPart Cn) ≠ 0 :=
      Subgroup.relIndex_inf_ne_zero (hG.2 y.1).2 (hG.2 x₃).2
    have hB1 : B.relIndex ((cptPart T).map (MonoidHom.fst H H)) ≠ 0 :=
      mt (Subgroup.relIndex_eq_zero_of_le_right hmapC) hB0
    have hB2 : (B.comap (MonoidHom.fst H H)).relIndex (cptPart T) ≠ 0 := by
      rwa [Subgroup.relIndex_comap]
    have hB3 : (B.comap (MonoidHom.fst H H) ⊓ cptPart T).relIndex (cptPart T) ≠ 0 := by
      rwa [Subgroup.inf_relIndex_right]
    have hle : B.comap (MonoidHom.fst H H) ⊓ cptPart T ≤
        T ⊓ (K.prod K).map (MulAut.conj y).toMonoidHom := by
      rintro c ⟨hcB, hcC⟩
      have hcT : c ∈ T := cptPart_le_self' T hcC
      refine ⟨hcT, ?_⟩
      have h2 := ((mem_twCent_swTw σ hσ d d' c).1 hcT).2
      have hm1 : y.1⁻¹ * c.1 * y.1 ∈ K := (mem_map_conj K _ _).1 hcB.1.2
      have hm3 : x₃⁻¹ * c.1 * x₃ ∈ K := (mem_map_conj K _ _).1 hcB.2.2
      refine (mem_map_conj _ _ _).2 (Subgroup.mem_prod.2 ⟨hm1, ?_⟩)
      have hs := hσK _ hm3
      have e : (y⁻¹ * c * y).2 = σ (x₃⁻¹ * c.1 * x₃) := by
        simp only [Prod.snd_mul, Prod.snd_inv, h2, hx₃, map_mul, map_inv, hσ]
        group
      show (y⁻¹ * c * y).2 ∈ K
      rw [e]
      exact hs
    exact fun h0 => hB3 (Subgroup.relIndex_eq_zero_of_le_left hle h0)

end GlobalTheory.CompanionTheory.SplitCpt
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.LimV

open GlobalTheory.Mem.Chr.CharModel

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem logFin_eq_zero_of_integral (t : (Af E)ˣ)
    (h1 : (t : Af E) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E)
    (h2 : ((t⁻¹ : (Af E)ˣ) : Af E) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) : logFin E t = 0 := by
  have : GlobalTheory.Idele.idealOf t = 1 := by
    rw [← GlobalTheory.Idele.smul_one_eq, GlobalTheory.Idele.smul_eq_self_iff t one_ne_zero]
    intro v
    have e := congrArg Valued.v (GlobalTheory.Idele.idele_apply_mul_inv t v)
    rw [map_mul, map_one] at e
    have a1 : Valued.v ((t : Af E) v) ≤ 1 := GroundTheory.Global.mem_integralFiniteAdeles.1 h1 v
    have a2 : Valued.v (((t⁻¹ : (Af E)ˣ) : Af E) v) ≤ 1 := GroundTheory.Global.mem_integralFiniteAdeles.1 h2 v
    refine le_antisymm a1 ?_
    rw [← e]
    exact mul_le_of_le_one_right' a2
  simp [logFin, this]

theorem det_mem_of_entries {R : Type*} [CommRing R] (S : Subring R) {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (h : ∀ a b, M a b ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply']
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)

theorem logFin_det_of_mem {N : ℕ} {c : GL (Fin N) (Af E)} (hc : c ∈ KO E N) :
    logFin E (GeneralLinearGroup.det c) = 0 := by
  obtain ⟨h1, h2⟩ := (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E N).1 hc
  refine logFin_eq_zero_of_integral _ (det_mem_of_entries _ _ h1) ?_
  rw [← map_inv]
  exact det_mem_of_entries _ _ h2

theorem logNorm_finId (u : (Af E)ˣ) : logNorm E (finId E u) = - logFin E u := by
  have h1 : finPart E (finId E u) = u := Units.ext (by
    change (1 : Af E) - 1 + u = u
    simp)
  have h2 : infPart E (finId E u) = 1 := Units.ext (by
    change (1 : InfiniteAdeleRing E) - 0 + 0 = 1
    simp)
  rw [logNorm, h1, h2, logInf_one, zero_sub]

theorem norm_det_unitary_at {N : ℕ} (k : Kinf E N) (v : InfinitePlace E) :
    ‖((GeneralLinearGroup.det (Unitary.toUnits k) : (Cinf E)ˣ) : Cinf E) v‖ = 1 := by
  have hd : (k : Matrix (Fin N) (Fin N) (Cinf E)).det ∈ unitary (Cinf E) := Matrix.det_of_mem_unitary k.2
  have h : star ((k : Matrix (Fin N) (Fin N) (Cinf E)).det v) * (k : Matrix (Fin N) (Fin N) (Cinf E)).det v = 1 :=
    congrFun (Unitary.star_mul_self_of_mem hd) v
  have h2 := congrArg norm h
  rw [norm_mul, norm_star, norm_one] at h2
  exact (mul_self_eq_one_iff.1 h2).resolve_right (by linarith [norm_nonneg ((k : Matrix (Fin N) (Fin N) (Cinf E)).det v)])

theorem logNorm_det_cf (N : ℕ) (k : Kinf E N) {c : GL (Fin N) (Af E)} (hc : c ∈ KO E N) :
    logNorm E (GeneralLinearGroup.det (cf N k c)) = 0 := by
  rw [cf, map_mul, logNorm_mul, det_infGL, det_finGL, Model.logNorm_infId, logNorm_finId, logFin_det_of_mem hc,
    Finset.sum_eq_zero fun v _ => by rw [norm_det_unitary_at, Real.log_one, mul_zero]]
  simp

theorem chiDet_absC_cf (N : ℕ) (w : ℂ) (k : Kinf E N) {c : GL (Fin N) (Af E)} (hc : c ∈ KO E N) :
    chiDet N (GlobalTheory.CuspRep.Model.absC E w) (cf N k c) = 1 := by
  apply Units.ext
  change Complex.exp (w * (logNorm E (GeneralLinearGroup.det (cf N k c)) : ℂ)) = 1
  rw [logNorm_det_cf N k hc]
  simp

end

theorem absFn_flat : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (w : ℂ),
    FlatFn (absFn (E := E) N w) := by
  intro E _ _ _ N w
  refine ⟨fun x => Units.ne_zero _, fun x k c hc => ?_, ?_⟩
  · simp only [absFn, map_mul, chiDet_absC_cf N w k hc, mul_one]
  · have h : absFn (E := E) N w = (mulChi N (GlobalTheory.CuspRep.Model.absC E w) (oneFn E N)).1 := funext fun x => by
      rw [mulChi_apply]
      simp [absFn, oneFn]
    rw [h]
    exact (mulChi N (GlobalTheory.CuspRep.Model.absC E w) (oneFn E N)).2

end GlobalTheory.CompanionTheory.LimV

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV.SliceR

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

def levelTwo (K : Subgroup (GL (Fin (r + s)) (Af E))) (t : GL (Fin (r + s)) (Af E)) :
    Subgroup (GL (Fin s) (Af E)) :=
  K.comap ((MulAut.conj t⁻¹).toMonoidHom.comp (Slice2.lev2 (Af E) r s))

theorem mem_levelTwo {K : Subgroup (GL (Fin (r + s)) (Af E))} {t : GL (Fin (r + s)) (Af E)}
    {u : GL (Fin s) (Af E)} : u ∈ levelTwo K t ↔ t⁻¹ * lev (Af E) r s (1, u) * t ∈ K := by
  simp [levelTwo, MulAut.conj_apply, Slice2.lev2]

theorem isOpen_levelTwo {K : Subgroup (GL (Fin (r + s)) (Af E))}
    (hK : IsOpen (K : Set (GL (Fin (r + s)) (Af E)))) (t : GL (Fin (r + s)) (Af E)) :
    IsOpen (levelTwo K t : Set (GL (Fin s) (Af E))) := by
  have hc : Continuous fun u : GL (Fin s) (Af E) => t⁻¹ * Slice2.lev2 (Af E) r s u * t :=
    (continuous_const.mul Slice2.continuous_lev2).mul continuous_const
  convert hK.preimage hc using 1
  ext u
  exact mem_levelTwo

def sliceMap (k : Kinf E (r + s)) : (Kinf E (r + s) → ℂ) →ₗ[ℂ] (Kinf E s → ℂ) :=
  LinearMap.funLeft ℂ ℂ fun κ => Slice2.levK E r s κ * k

theorem lev_finGL_right (x : GA E r) (g : GA E s) (u : GL (Fin s) (Af E)) (k : Kinf E (r + s))
    (t : GL (Fin (r + s)) (Af E)) :
    lev (Ad E) r s (x, g * finGL E s u) * cf (r + s) k t =
      lev (Ad E) r s (x, g) * cf (r + s) k t * finGL E (r + s) (t⁻¹ * lev (Af E) r s (1, u) * t) := by
  have hY : finGL E (r + s) (lev (Af E) r s (1, u)) * finGL E (r + s) t =
      finGL E (r + s) t * finGL E (r + s) (t⁻¹ * lev (Af E) r s (1, u) * t) := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  rw [Slice2.lev_mul_right, Slice2.lev_finGL_one, cf, mul_assoc (lev (Ad E) r s (x, g)),
    ← mul_assoc (finGL E (r + s) _), ← infGL_comm, mul_assoc (infGL E (r + s) _), hY]
  simp only [mul_assoc]

theorem lev_infGL_right (x : GA E r) (g : GA E s) (κ : Kinf E s) (k : Kinf E (r + s))
    (t : GL (Fin (r + s)) (Af E)) :
    lev (Ad E) r s (x, g * infGL E s (Unitary.toUnits κ)) * cf (r + s) k t =
      (lev (Ad E) r s (x, g) * finGL E (r + s) t) *
        infGL E (r + s) (Unitary.toUnits (Slice2.levK E r s κ * k)) := by
  rw [Slice2.lev_mul_right, Slice2.lev_infGL_one, cf, map_mul Unitary.toUnits, Slice2.toUnits_levK,
    map_mul (infGL E (r + s)), mul_assoc (lev (Ad E) r s (x, g)) (finGL E (r + s) t), infGL_comm _ t]
  rw [mul_assoc (lev (Ad E) r s (x, g)) (infGL E (r + s) _), ← mul_assoc (infGL E (r + s) _) (finGL E (r + s) t),
    infGL_comm]
  simp only [mul_assoc]

end GlobalTheory.CompanionTheory.LimV.SliceR

theorem GlobalTheory.CompanionTheory.LimV.SliceR.slice_right : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ} (k : Kinf E (r + s)) (t : GL (Fin (r + s)) (Af E)) (K : Subgroup (GL (Fin (r + s)) (Af E))) (W : Submodule ℂ (Kinf E (r + s) → ℂ)), IsOpen (K : Set (GL (Fin (r + s)) (Af E))) → FiniteDimensional ℂ W → ∃ (K₂ : Subgroup (GL (Fin s) (Af E))) (W₂ : Submodule ℂ (Kinf E s → ℂ)), IsOpen (K₂ : Set (GL (Fin s) (Af E))) ∧ FiniteDimensional ℂ W₂ ∧ ∀ f ∈ typeF K W, ∀ x : GA E r, (fun y : GA E s => f (lev (Ad E) r s (x, y) * cf (r + s) k t)) ∈ typeF K₂ W₂ := by
  intro E _ _ _ r s k t K W hK hW
  refine ⟨SliceR.levelTwo K t, W.map (SliceR.sliceMap k), SliceR.isOpen_levelTwo hK t, inferInstance,
    fun f hf x => ⟨fun u hu g => ?_, fun g => ?_⟩⟩
  · change f (lev (Ad E) r s (x, g * finGL E s u) * cf (r + s) k t) = f (lev (Ad E) r s (x, g) * cf (r + s) k t)
    rw [SliceR.lev_finGL_right]
    exact hf.1 _ (SliceR.mem_levelTwo.1 hu) _
  · refine ⟨_, hf.2 (lev (Ad E) r s (x, g) * finGL E (r + s) t), ?_⟩
    funext κ
    change f _ = f (lev (Ad E) r s (x, g * infGL E s (Unitary.toUnits κ)) * cf (r + s) k t)
    rw [SliceR.lev_infGL_right]

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped Topology

namespace GlobalTheory.CompanionTheory.LeviAdm

theorem finiteDimensional_of_smInd_fixed {G W : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W] (H K : Subgroup G)
    (hK : IsOpen (K : Set G)) (σ : Representation ℂ H W) (A : Submodule ℂ W)
    (hA : ∀ c : H, (c : G) ∈ K → ∀ w ∈ A, σ c w = w)
    (hfd : FiniteDimensional ℂ (fixed (smInd H σ) K)) : FiniteDimensional ℂ A := by
  classical
  have key : ∀ p q : H, (p : G)⁻¹ * q ∈ K → ∀ w ∈ A, σ q w = σ p w := by
    intro p q hpq w hw
    have h1 : σ (p⁻¹ * q) w = w := hA _ (by simpa using hpq) w hw
    have h2 : q = p * (p⁻¹ * q) := by group
    calc σ q w = σ (p * (p⁻¹ * q)) w := by rw [← h2]
      _ = σ p (σ (p⁻¹ * q) w) := by rw [map_mul]; rfl
      _ = σ p w := by rw [h1]
  let S : G → Prop := fun x => ∃ p : H, (p : G)⁻¹ * x ∈ K
  let pick : G → H := fun x => if h : S x then h.choose else 1
  have pick_spec : ∀ x, S x → ((pick x : H) : G)⁻¹ * x ∈ K := by
    intro x h
    simp only [pick, dif_pos h]
    exact h.choose_spec
  let F : A →ₗ[ℂ] (G → W) := LinearMap.pi fun x =>
    if S x then (σ (pick x)).comp A.subtype else 0
  have F_pos : ∀ (w : A) x, S x → F w x = σ (pick x) w := by
    intro w x h
    simp [F, h]
  have F_neg : ∀ (w : A) x, ¬ S x → F w x = 0 := by
    intro w x h
    simp [F, h]
  have S_left : ∀ (q : H) x, S x → S (q * x) := by
    rintro q x ⟨p, hp⟩
    exact ⟨q * p, by simpa [mul_assoc] using hp⟩
  have S_right : ∀ c ∈ K, ∀ x, S x → S (x * c) := by
    rintro c hc x ⟨p, hp⟩
    exact ⟨p, by simpa [mul_assoc] using K.mul_mem hp hc⟩
  have hlaw : ∀ w : A, F w ∈ indSpace H σ := by
    intro w q x
    by_cases hx : S x
    · have hqx := S_left q x hx
      rw [F_pos w _ hqx, F_pos w _ hx, ← Module.End.mul_apply, ← map_mul]
      refine key _ _ ?_ w w.2
      have h3 := K.mul_mem (pick_spec x hx) (K.inv_mem (pick_spec _ hqx))
      convert h3 using 1
      simp only [Subgroup.coe_mul]
      group
    · have hqx : ¬ S (q * x) := fun h => hx (by
        have := S_left q⁻¹ _ h
        simpa using this)
      rw [F_neg w _ hqx, F_neg w _ hx, map_zero]
  have hfix : ∀ (w : A), ∀ c ∈ K, ∀ x, F w (x * c) = F w x := by
    intro w c hc x
    by_cases hx : S x
    · have hxc := S_right c hc x hx
      rw [F_pos w _ hxc, F_pos w _ hx]
      refine key _ _ ?_ w w.2
      have h3 := K.mul_mem (K.mul_mem (pick_spec x hx) hc) (K.inv_mem (pick_spec _ hxc))
      convert h3 using 1
      group
    · have hxc : ¬ S (x * c) := fun h => hx (by
        have := S_right c⁻¹ (K.inv_mem hc) _ h
        simpa using this)
      rw [F_neg w _ hxc, F_neg w _ hx]
  have hfix' : ∀ (w : A), ∀ c ∈ K, ind H σ c ⟨F w, hlaw w⟩ = ⟨F w, hlaw w⟩ :=
    fun w c hc => Subtype.ext (funext fun x => hfix w c hc x)
  have hsm : ∀ w : A, (⟨F w, hlaw w⟩ : indSpace H σ) ∈ smoothPart (ind H σ) := fun w =>
    mem_smoothPart_of_nhds (Filter.mem_of_superset (hK.mem_nhds K.one_mem)
      fun c hc => hfix' w c hc)
  have hT : ∀ w : A, (⟨⟨F w, hlaw w⟩, hsm w⟩ : smoothPart (ind H σ)) ∈ fixed (smInd H σ) K := by
    intro w c
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    exact Subtype.ext (hfix' w c c.2)
  let T : A →ₗ[ℂ] fixed (smInd H σ) K :=
    { toFun := fun w => ⟨⟨⟨F w, hlaw w⟩, hsm w⟩, hT w⟩
      map_add' := fun a b => Subtype.ext (Subtype.ext (Subtype.ext (map_add F a b)))
      map_smul' := fun c a => Subtype.ext (Subtype.ext (Subtype.ext (map_smul F c a))) }
  have hS1 : S 1 := ⟨1, by simp [K.one_mem]⟩
  have hF1 : ∀ w : A, F w 1 = w := by
    intro w
    rw [F_pos w 1 hS1]
    refine (key 1 _ ?_ w w.2).trans (by simp)
    have h3 := K.inv_mem (pick_spec 1 hS1)
    simpa using h3
  have hinj : Function.Injective T := by
    intro a b hab
    have h4 : F a = F b := congrArg (fun t : fixed (smInd H σ) K => t.1.1.1) hab
    exact Subtype.ext (by rw [← hF1 a, ← hF1 b, h4])
  exact Module.Finite.of_injective T hinj

theorem isAdmissible_of_parInd : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {s : ℕ} (d : Fin s → ℕ) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W),
    IsSmooth ρ → IsAdmissible (parInd (GlobalTheory.CompanionTheory.BZInd.stdE d) ρ) → IsAdmissible ρ := by
  intro k _ _ _ _ s d W _ _ ρ hρ hA
  refine ⟨hρ, fun L hLo _ => ?_⟩
  let δ := deltaHalf k fun a => Fin (d a)
  let L' : Subgroup (Levi k fun a => Fin (d a)) := L ⊓ δ.ker
  have hL' : IsOpen (L' : Set (Levi k fun a => Fin (d a))) :=
    hLo.inter (isSmoothChar_deltaHalf k)
  have hpre := hL'.preimage (ProdIrr.continuous_leviProj (GlobalTheory.CompanionTheory.BZInd.stdE d))
  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.1 hpre
  have h1 : (1 : GL (Fin (∑ a, d a)) k) ∈ U := by
    have h2 : (1 : parab k (GlobalTheory.CompanionTheory.BZInd.stdE d)) ∈ Subtype.val ⁻¹' U := by
      rw [hUe]
      simpa using L'.one_mem
    exact h2
  obtain ⟨m, -, hm⟩ :=
    (GroundTheory.Automorphic.GLnLocal.hasBasis_nhds_one k (∑ a, d a)).mem_iff.1 (hU.mem_nhds h1)
  have hKo := GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k (∑ a, d a) m
  have hKc := GroundTheory.Automorphic.GLnLocal.isCompact_congruenceSubgroup k (∑ a, d a) m
  refine finiteDimensional_of_smInd_fixed (parab k (GlobalTheory.CompanionTheory.BZInd.stdE d))
    (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k (∑ a, d a) m) hKo
    ((_root_.GlobalTheory.SmGL.twist ρ δ).comp (leviProj k (GlobalTheory.CompanionTheory.BZInd.stdE d))) (fixed ρ L) ?_ (hA.2 _ hKo hKc)
  intro c hc w hw
  have hcL : leviProj k (GlobalTheory.CompanionTheory.BZInd.stdE d) c ∈ L' := by
    have h2 : c ∈ Subtype.val ⁻¹' U := hm hc
    rw [hUe] at h2
    exact h2
  have hδ : δ (leviProj k (GlobalTheory.CompanionTheory.BZInd.stdE d) c) = 1 := MonoidHom.mem_ker.1 hcL.2
  have hw' := hw ⟨_, hcL.1⟩
  rw [MonoidHom.one_apply, Units.val_one, one_smul] at hw'
  show ((δ (leviProj k (GlobalTheory.CompanionTheory.BZInd.stdE d) c) : ℂˣ) : ℂ) •
    ρ (leviProj k (GlobalTheory.CompanionTheory.BZInd.stdE d) c) w = w
  rw [hδ, Units.val_one, one_smul]
  exact hw'

end GlobalTheory.CompanionTheory.LeviAdm
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec PositivityTheory.PRW.GKD

theorem _root_.GlobalTheory.T.cuspForm_conjugate_inverse : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}, ∀ (φ : Sm E a) (hψ : (fun g => star (φ.1 (invA E a g))) ∈ Sm E a), IsCuspForm φ → IsCuspForm (⟨fun g => star (φ.1 (invA E a g)), hψ⟩ : Sm E a) := by
  first | exact @GlobalTheory.CompanionTheory.DualCusp.isCuspForm_conj_invA | exact GlobalTheory.CompanionTheory.DualCusp.isCuspForm_conj_invA | (intros; apply GlobalTheory.CompanionTheory.DualCusp.isCuspForm_conj_invA <;> assumption)
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SWDict

open PositivityTheory.PfSWUS GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd

theorem dictKA_of_parts : PositivityTheory.PfSWUS.DictKAOfParts := by
  intro hF hW hI hM D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k hk
  obtain ⟨N, φs, hsum, hmono⟩ := hF D n V ψ χ θ μ ω H l s ν Φ hS hR k hk
  refine ⟨N, φs, fun j => npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) - n) *
    IfrB V ν (fun x => φs j (HMul.hMul x a.1)) β, ?_, ?_, ?_⟩
  · obtain ⟨t, ht⟩ := hW D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k N φs hmono
    exact ⟨t, fun z hz => by rw [hsum]; exact ht z hz⟩
  · rw [hsum, hI D n V ψ χ θ μ ω H l s ν Φ hS hR β hβ a N φs hmono, Finset.mul_sum]
  · exact fun j => hM D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k hk (φs j) (hmono j)

end GlobalTheory.CompanionTheory.SWDict

end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

theorem _root_.GlobalTheory.T.continuous_algebra_universal_property : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l), ∃ η : (((base l).cont ℤ_[l]).A)ˣ, ((base l).cont ℤ_[l]).sharp η = 1 ∧ PAlg.Hom.f (contShift (base l)) η = ((base l).cont ℤ_[l]).s (ε.e 0) * η ∧ ∀ (A t : PAlg l), t.IsTest → ∀ (φ : A ⟶ t) (u : (t.A)ˣ), t.sharp u = 1 → ∃! ψ : A.cont ℤ_[l] ⟶ t, A.toCont ℤ_[l] ≫ ψ = φ ∧ PAlg.Hom.f ψ (PAlg.Hom.f (contMap A.fromBase ℤ_[l]) η) = u := by
  first | exact @GlobalTheory.CompanionTheory.ContUniv.main | exact GlobalTheory.CompanionTheory.ContUniv.main | (intros; apply GlobalTheory.CompanionTheory.ContUniv.main <;> assumption)
end

section


theorem _root_.GlobalTheory.T.wave_kernel_uniqueness : PositivityTheory.RgBcC.KerUniq := by
  first | exact @GlobalTheory.CompanionTheory.KerUniq.main | exact GlobalTheory.CompanionTheory.KerUniq.main | (intros; apply GlobalTheory.CompanionTheory.KerUniq.main <;> assumption)
end
