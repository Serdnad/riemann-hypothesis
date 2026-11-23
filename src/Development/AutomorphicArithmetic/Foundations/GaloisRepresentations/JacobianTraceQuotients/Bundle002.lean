module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockTriangularOneAddMat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
import GroundTheory.AutomorphicForms.WhittakerGroups
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle003
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.LinearAlgebra.PID
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Finiteness.Nilpotent
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
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

namespace UpperTheory.Gal.Join

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem mem_dcos_iff {K : Subgroup (GL (Fin n) k)} (hK : IwLev K) {t : Fin n → kˣ} (ht : Dom t)
    (g : GL (Fin n) k) :
    g ∈ dcos K t ↔ ∃ u ∈ unipB k (Fin n), u ∈ K ∧ ∃ i ∈ K, g = u * diagT k (Fin n) t * i := by
  refine ⟨?_, fun ⟨u, _, hu, i, hi, e⟩ => ⟨u, hu, i, hi, e⟩⟩
  rintro ⟨a, ha, b, hb, rfl⟩
  obtain ⟨u, hu, d, hd, c, hc, rfl⟩ := hK.fact a ha
  refine ⟨u, hu.2, hu.1, _, mul_mem (mul_mem hd (hK.low t ht c hc)) hb, ?_⟩
  have e : diagT k (Fin n) t * diagT k (Fin n) d = diagT k (Fin n) d * diagT k (Fin n) t := by
    rw [← map_mul, mul_comm, map_mul]
  calc u * diagT k (Fin n) d * c * diagT k (Fin n) t * b
      = u * (diagT k (Fin n) d * diagT k (Fin n) t) * ((diagT k (Fin n) t)⁻¹ * c * diagT k (Fin n) t) * b := by
        group
    _ = _ := by rw [← e]; group

private theorem dcos_eq_image (K : Subgroup (GL (Fin n) k)) (t : Fin n → kˣ) :
    dcos K t = (fun x : GL (Fin n) k × GL (Fin n) k => x.1 * diagT k (Fin n) t * x.2) ''
      ((K : Set (GL (Fin n) k)) ×ˢ (K : Set (GL (Fin n) k))) := by
  ext g
  exact ⟨fun ⟨a, ha, b, hb, e⟩ => ⟨(a, b), ⟨ha, hb⟩, e.symm⟩, fun ⟨x, hx, e⟩ => ⟨x.1, hx.1, x.2, hx.2, e.symm⟩⟩

private theorem isCompact_dcos {K : Subgroup (GL (Fin n) k)} (hK : CO K) (t : Fin n → kˣ) :
    IsCompact (dcos K t) := by
  rw [dcos_eq_image]
  exact (hK.1.prod hK.1).image (by fun_prop)

private theorem isOpen_dcos {K : Subgroup (GL (Fin n) k)} (hK : CO K) (t : Fin n → kˣ) :
    IsOpen (dcos K t) := by
  have e : dcos K t = ⋃ a ∈ (K : Set (GL (Fin n) k)),
      (fun g => (a * diagT k (Fin n) t) * g) '' (K : Set (GL (Fin n) k)) := by
    ext g
    simp only [Set.mem_iUnion, Set.mem_image, exists_prop]
    exact ⟨fun ⟨a, ha, b, hb, e⟩ => ⟨a, ha, b, hb, e.symm⟩, fun ⟨a, ha, b, hb, e⟩ => ⟨a, ha, b, hb, e.symm⟩⟩
  rw [e]
  exact isOpen_biUnion fun a _ => (Homeomorph.mulLeft (a * diagT k (Fin n) t)).isOpenMap _ hK.2

open GlobalTheory.SplitWeil GlobalTheory.IwahoriTraceProof in
private theorem isClosed_unipB : IsClosed (unipB k (Fin n) : Set (GL (Fin n) k)) := by
  have e : (unipB k (Fin n) : Set (GL (Fin n) k)) = (⋂ i, ⋂ j, ⋂ _ : j < i, {g : GL (Fin n) k | g.val i j = 0}) ∩
      ⋂ i, {g : GL (Fin n) k | g.val i i = 1} := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter]
    exact mem_unipB k
  rw [e]
  exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const).inter
    (isClosed_iInter fun i => isClosed_eq (Units.continuous_val.matrix_elem i i) continuous_const)


open GlobalTheory.SplitWeil GlobalTheory.IwahoriTraceProof in
private theorem measure_dcos [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (μ : Measure (GL (Fin n) k))
    [μ.IsHaarMeasure] {K : Subgroup (GL (Fin n) k)} (hK : IwLev K) {t : Fin n → kˣ} (ht : Dom t) :
    μ.real (dcos K t) = μ.real (K : Set (GL (Fin n) k)) * (deltaB t)⁻¹ := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  letI : MeasurableSpace (unipRad k (points (Fin n))) := _root_.borel _
  haveI : BorelSpace (unipRad k (points (Fin n))) := ⟨rfl⟩
  haveI : LocallyCompactSpace (unipRad k (points (Fin n))) :=
    (UnipHaar.unipHomeo (points (Fin n))).isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (unipRad k (points (Fin n))) :=
    (UnipHaar.unipHomeo (points (Fin n))).secondCountableTopology
  let ν : Measure (unipRad k (points (Fin n))) := Measure.haar
  have ho : IsOpen {s : unipRad k (points (Fin n)) | (s : GL (Fin n) k) ∈ K} :=
    hK.co.2.preimage continuous_subtype_val
  have hcl : IsClosed (unipRad k (points (Fin n)) : Set (GL (Fin n) k)) := isClosed_unipB
  have hc : IsCompact {s : unipRad k (points (Fin n)) | (s : GL (Fin n) k) ∈ K} :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK.co.1
  have h1 := measure_mul_eq μ ν hK.co.2 (t := diagT k (Fin n) t)
    (fun u hu => by simpa [unipB] using conj_mem_unipB t⁻¹ hu)
    (fun u hu hI => hK.up t ht u ⟨hI, hu⟩)
    (isCompact_dcos hK.co t).measurableSet (mem_dcos_iff hK ht)
  have h2 := UnipHaar.haar_conj_eq_modulus_mul k (Fin n) (Fin n) (fun _ => Unit) (points (Fin n)) ν
    (leviTorus k (Fin n) t) _ ho.measurableSet
  rw [← deltaB_eq_modulus] at h2
  have h3 := (congrArg (· * μ (dcos K t)) h2).symm.trans h1
  rw [mul_right_comm, ENNReal.mul_left_inj (ho.measure_pos ν ⟨1, one_mem K⟩).ne' hc.measure_lt_top.ne] at h3
  rw [measureReal_def, measureReal_def, ← h3, ENNReal.toReal_mul, ENNReal.toReal_ofReal (deltaB_pos t).le,
    mul_right_comm, mul_inv_cancel₀ (deltaB_pos t).ne', one_mul]

end

end UpperTheory.Gal.Join

theorem UpperTheory.Gal.Join.dcosVol :
    UpperTheory.Gal.Join.DcosVol := by
  intro k _ _ _ _ n _ _ μ _ K hK t ht
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hc := isCompact_dcos hK.co t
  refine ⟨⟨(LocallyConstant.indicator (1 : LocallyConstant (GL (Fin n) k) ℂ) ⟨hc.isClosed, isOpen_dcos hK.co t⟩).2,
    HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩, measure_dcos μ hK ht⟩
end

section

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

private theorem jointEig {ι V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : ι → Module.End ℂ V) (c : ι → ℂ) (hc : ∀ i j, Commute (f i) (f j))
    (h : (⨅ i, Module.End.maxGenEigenspace (f i) (c i) : Submodule ℂ V) ≠ ⊥) :
    ∃ y, y ≠ 0 ∧ ∀ i, f i y = c i • y := by
  classical
  have hcN : ∀ i j, Commute (f i) (f j - c j • (1 : Module.End ℂ V)) := fun i j =>
    (hc i j).sub_right ((Commute.one_right _).smul_right _)
  have hW_inv : ∀ i, ∀ u ∈ (⨅ i, Module.End.maxGenEigenspace (f i) (c i) : Submodule ℂ V),
      f i u ∈ (⨅ i, Module.End.maxGenEigenspace (f i) (c i) : Submodule ℂ V) := by
    intro i u hu
    rw [Module.End.mem_iInf_maxGenEigenspace_iff] at hu ⊢
    intro j
    obtain ⟨k, hk⟩ := hu j
    refine ⟨k, ?_⟩
    rw [← Module.End.mul_apply, ← ((hcN i j).pow_right k).eq, Module.End.mul_apply, hk, map_zero]
  have hex : ∃ n, ∃ U : Submodule ℂ V, U ≠ ⊥ ∧
      U ≤ (⨅ i, Module.End.maxGenEigenspace (f i) (c i) : Submodule ℂ V) ∧
      (∀ i, ∀ u ∈ U, f i u ∈ U) ∧ Module.finrank ℂ U = n :=
    ⟨_, _, h, le_rfl, hW_inv, rfl⟩
  obtain ⟨U, hU0, hUW, hUinv, hUn⟩ := Nat.find_spec hex
  have hker : ∀ i, ∀ u ∈ U, f i u = c i • u := by
    intro i
    have hNU : ∀ m : ℕ, ∀ u ∈ U, ((f i - c i • (1 : Module.End ℂ V)) ^ m) u ∈ U := by
      intro m
      induction m with
      | zero => intro u hu; simpa using hu
      | succ m ih =>
        intro u hu
        rw [pow_succ', Module.End.mul_apply]
        have hv := ih u hu
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
        exact U.sub_mem (hUinv i _ hv) (U.smul_mem _ hv)
    let K : Submodule ℂ V := U ⊓ LinearMap.ker (f i - c i • (1 : Module.End ℂ V))
    have hKinv : ∀ j, ∀ u ∈ K, f j u ∈ K := by
      intro j u hu
      refine ⟨hUinv j u hu.1, ?_⟩
      have h2 : (f i - c i • (1 : Module.End ℂ V)) u = 0 := hu.2
      show (f i - c i • (1 : Module.End ℂ V)) (f j u) = 0
      rw [← Module.End.mul_apply, ← (hcN j i).eq, Module.End.mul_apply, h2, map_zero]
    have hK0 : K ≠ ⊥ := by
      obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
      have hexk : ∃ k, ((f i - c i • (1 : Module.End ℂ V)) ^ k) u = 0 :=
        (Module.End.mem_iInf_maxGenEigenspace_iff f c u).mp (hUW huU) i
      obtain ⟨k, hk, hkmin⟩ : ∃ k, ((f i - c i • (1 : Module.End ℂ V)) ^ k) u = 0 ∧
          ∀ m < k, ((f i - c i • (1 : Module.End ℂ V)) ^ m) u ≠ 0 :=
        ⟨Nat.find hexk, Nat.find_spec hexk, fun m hm => Nat.find_min hexk hm⟩
      have hk0 : k ≠ 0 := by
        rintro rfl
        simp at hk
        exact hu0 hk
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      refine (Submodule.ne_bot_iff K).mpr ⟨((f i - c i • (1 : Module.End ℂ V)) ^ m) u,
        ⟨hNU m u huU, ?_⟩, hkmin m (Nat.lt_succ_self m)⟩
      show (f i - c i • (1 : Module.End ℂ V)) (((f i - c i • (1 : Module.End ℂ V)) ^ m) u) = 0
      rw [← Module.End.mul_apply, ← pow_succ']
      exact hk
    have hle : Nat.find hex ≤ Module.finrank ℂ K :=
      Nat.find_min' hex ⟨K, hK0, le_trans inf_le_left hUW, hKinv, rfl⟩
    have hKU : K = U := Submodule.eq_of_le_of_finrank_eq inf_le_left
      (le_antisymm (Submodule.finrank_mono inf_le_left) (hUn ▸ hle))
    intro u hu
    have hu' : u ∈ K := hKU ▸ hu
    have h3 : (f i - c i • (1 : Module.End ℂ V)) u = 0 := hu'.2
    simpa [sub_eq_zero] using h3
  obtain ⟨y, hyU, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  exact ⟨y, hy0, fun i => hker i y hyU⟩

theorem UpperTheory.Gal.Join.subQuot :
    UpperTheory.Gal.Join.SubQuot := by
  intro T X _ _ _ _ ρ μ
  have hc : ∀ s t : T, Commute (ρ s) (ρ t) := fun s t => by
    show ρ s * ρ t = ρ t * ρ s
    rw [← map_mul, ← map_mul, mul_comm]
  have iff1 : (∃ y, y ≠ 0 ∧ ∀ t : T, ρ t y = (μ t : ℂ) • y) ↔
      (⨅ t, Module.End.maxGenEigenspace (ρ t) (μ t : ℂ) : Submodule ℂ X) ≠ ⊥ := by
    constructor
    · rintro ⟨y, hy0, hy⟩
      refine (Submodule.ne_bot_iff _).mpr ⟨y, ?_, hy0⟩
      rw [Module.End.mem_iInf_maxGenEigenspace_iff]
      intro t
      refine ⟨1, ?_⟩
      simp [hy t]
    · intro h
      exact jointEig (fun t => ρ t) (fun t => (μ t : ℂ)) hc h
  refine ⟨iff1, fun hy => ?_⟩
  have hWne := iff1.mp hy
  let c : T → ℂ := fun t => (μ t : ℂ)
  let Wχ : (T → ℂ) → Submodule ℂ X := fun χ => ⨅ t, Module.End.maxGenEigenspace (ρ t) (χ t)
  let S : Submodule ℂ X := ⨆ χ ∈ {χ : T → ℂ | χ ≠ c}, Wχ χ
  have hind : iSupIndep Wχ :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo _
      (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ)
  have hdisj : Disjoint (Wχ c) S := hind.disjoint_biSup (fun h => h rfl)
  have htop : Wχ c ⊔ S = ⊤ := by
    have h1 : ⨆ χ : T → ℂ, Wχ χ = ⊤ :=
      Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo _
        (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ)
        (fun i => Module.End.iSup_maxGenEigenspace_eq_top _)
    refine eq_top_iff.mpr (h1.symm.le.trans (iSup_le fun χ => ?_))
    by_cases hχ : χ = c
    · subst hχ; exact le_sup_left
    · exact le_sup_of_le_right (le_biSup Wχ (show χ ∈ {χ : T → ℂ | χ ≠ c} from hχ))
  have hWinv : ∀ χ t, ∀ x ∈ Wχ χ, ρ t x ∈ Wχ χ := by
    intro χ t x hx
    simp only [Wχ, Submodule.mem_iInf] at hx ⊢
    intro s
    exact Module.End.mapsTo_maxGenEigenspace_of_comm (hc s t) (χ s) (hx s)
  have hSinv : ∀ t, ∀ x ∈ S, ρ t x ∈ S := by
    intro t
    have : S ≤ S.comap (ρ t) := iSup₂_le fun χ hχ x hx =>
      (le_biSup Wχ hχ) (hWinv χ t x hx)
    exact fun x hx => this hx
  have hNS : ∀ t (k : ℕ), ∀ x ∈ S, ((ρ t - c t • (1 : Module.End ℂ X)) ^ k) x ∈ S := by
    intro t k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      rw [pow_succ', Module.End.mul_apply]
      have hv := ih x hx
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact S.sub_mem (hSinv t _ hv) (S.smul_mem _ hv)
  have hSlt : S < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun hS => hWne ?_
    have : Disjoint (Wχ c) ⊤ := hS ▸ hdisj
    exact disjoint_top.mp this
  obtain ⟨l0, hl00, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hSlt inferInstance
  let g : T → Module.End ℂ (Module.Dual ℂ X) := fun t => Module.Dual.transpose (R := ℂ) (ρ t)
  have hg : ∀ s t, Commute (g s) (g t) := by
    intro s t
    show g s * g t = g t * g s
    ext φ x
    simp only [Module.End.mul_apply, g, Module.Dual.transpose_apply, LinearMap.comp_apply]
    rw [← Module.End.mul_apply, (hc t s).eq, Module.End.mul_apply]
  have hpow : ∀ t (k : ℕ) (φ : Module.Dual ℂ X),
      ((g t - c t • (1 : Module.End ℂ (Module.Dual ℂ X))) ^ k) φ =
        φ ∘ₗ ((ρ t - c t • (1 : Module.End ℂ X)) ^ k) := by
    intro t k
    induction k with
    | zero => intro φ; ext x; simp
    | succ k ih =>
      intro φ
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ]
      ext x
      simp [g, Module.Dual.transpose_apply, Module.End.mul_apply, smul_eq_mul]
  obtain ⟨l, hl0, hl⟩ := jointEig g c hg (by
    refine (Submodule.ne_bot_iff _).mpr ⟨l0, ?_, hl00⟩
    rw [Module.End.mem_iInf_maxGenEigenspace_iff]
    intro t
    refine ⟨Module.finrank ℂ X, ?_⟩
    rw [hpow]
    ext x
    have hx : x ∈ Wχ c ⊔ S := htop ▸ Submodule.mem_top
    obtain ⟨w, hw, s, hs, rfl⟩ := Submodule.mem_sup.mp hx
    have hw' : w ∈ Module.End.maxGenEigenspace (ρ t) (c t) :=
      (Submodule.mem_iInf _).mp hw t
    rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.mem_genEigenspace_nat,
      LinearMap.mem_ker] at hw'
    have hs' : l0 (((ρ t - c t • (1 : Module.End ℂ X)) ^ Module.finrank ℂ X) s) = 0 := by
      have hm := Submodule.mem_map_of_mem (f := l0) (hNS t (Module.finrank ℂ X) s hs)
      rw [hmap] at hm
      exact (Submodule.mem_bot ℂ).mp hm
    simp only [LinearMap.comp_apply, map_add (f := _), hw', map_zero, zero_add, LinearMap.zero_apply]
    exact hs')
  refine ⟨l, hl0, fun t y => ?_⟩
  have := congrArg (fun φ : Module.Dual ℂ X => φ y) (hl t)
  simpa [g, Module.Dual.transpose_apply, smul_eq_mul] using this
end

section

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

theorem UpperTheory.Gal.Join.traceQuot :
    UpperTheory.Gal.Join.TraceQuot := by
  intro V W _ _ _ _ S _ B p T hB hBT hnil
  have hTP : ∀ y ∈ Submodule.map p S, T y ∈ Submodule.map p S := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨B v, hB v, hBT v hv⟩
  have hBS : ∀ v ∈ S, B v ∈ S := fun v _ => hB v
  have hRS : LinearMap.range B ≤ S := by
    rintro _ ⟨v, rfl⟩
    exact hB v
  haveI : FiniteDimensional ℂ (LinearMap.range B) := Submodule.finiteDimensional_of_le hRS
  refine ⟨inferInstance, ?_⟩
  unfold trIn
  rw [dite_eq_left hTP]
  have h1 : LinearMap.trace ℂ (LinearMap.range B) (B.restrict (fun x _ => (⟨x, rfl⟩ : B x ∈ LinearMap.range B)))
      = LinearMap.trace ℂ S (B.restrict hBS) := by
    have key := LinearMap.trace_restrict_eq_of_forall_mem ((LinearMap.range B).comap S.subtype)
      (B.restrict hBS) (fun x => show B x ∈ LinearMap.range B from ⟨x, rfl⟩)
    rw [← key, ← LinearMap.trace_conj' _ (Submodule.comapSubtypeEquivOfLe hRS)]
    congr 1
  rw [h1]
  set q : S →ₗ[ℂ] Submodule.map p S := p.submoduleMap S with hqdef
  have hq : Function.Surjective q := p.submoduleMap_surjective S
  haveI : FiniteDimensional ℂ (Submodule.map p S) := Module.Finite.of_surjective q hq
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  set BS := B.restrict hBS with hBSdef
  set TP := T.restrict hTP with hTPdef
  have hint : q ∘ₗ BS = TP ∘ₗ q := by
    ext x
    exact hBT x.1 x.2
  have hT : TP = q ∘ₗ (BS ∘ₗ s) := by
    rw [← LinearMap.comp_assoc, hint, LinearMap.comp_assoc, hs, LinearMap.comp_id]
  rw [hT, LinearMap.trace_comp_comm']
  set E : S →ₗ[ℂ] S := LinearMap.id - s ∘ₗ q with hEdef
  have hsplit : BS = (BS ∘ₗ s) ∘ₗ q + BS ∘ₗ E := by
    ext x
    simp [hEdef]
  have hqs : ∀ y, q (s y) = y := fun y => LinearMap.congr_fun hs y
  have hqB : ∀ y : S, q y = 0 → q (BS y) = 0 := by
    intro y hy
    have := LinearMap.congr_fun hint y
    simp only [LinearMap.comp_apply] at this
    rw [this, hy, map_zero]
  have hzero : LinearMap.trace ℂ S (BS ∘ₗ E) = 0 := by
    rw [LinearMap.trace_comp_comm']
    have hK : ∀ x, (E ∘ₗ BS) x ∈ LinearMap.ker q := by
      intro x
      simp [hEdef, hqs]
    rw [← LinearMap.trace_restrict_eq_of_forall_mem _ _ hK]
    set f := (E ∘ₗ BS).restrict (fun x _ => hK x) with hfdef
    apply IsNilpotent.eq_zero
    apply LinearMap.isNilpotent_trace_of_isNilpotent
    rw [Module.End.isNilpotent_iff_of_finite]
    intro k
    have hk0 : q k.1 = 0 := k.2
    have hpk : p k.1.1 = 0 := congrArg Subtype.val hk0
    obtain ⟨m, hm⟩ := hnil k.1.1 k.1.2 hpk
    refine ⟨m, ?_⟩
    have step : ∀ n : ℕ, ((f ^ n) k).1.1 = (B ^ n) k.1.1 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
        have hy : q ((f ^ n) k).1 = 0 := ((f ^ n) k).2
        show ((E (BS ((f ^ n) k).1)) : V) = B ((f ^ n) k).1.1
        rw [hEdef, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, hqB _ hy, map_zero, sub_zero]
        rfl
    apply Subtype.ext
    apply Subtype.ext
    rw [step]
    simpa using hm
  conv_lhs => rw [hsplit]
  rw [map_add (f := _), hzero, add_zero]
end

section

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

private theorem rep_mul {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    (a b : G) (w : V) : π (a * b) w = π a (π b w) := by
  rw [map_mul, Module.End.mul_apply]

private theorem exists_unipotent_eq_of_mem_iwLev_of_fixed {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] {n : ℕ}
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (K : Subgroup (GL (Fin n) k)) (hK : IwLev K) (t : Fin n → kˣ) (ht : Dom t) (v : V)
    (hv : v ∈ fixed π K) (g : GL (Fin n) k) (hg : g ∈ K) :
    ∃ u ∈ K ⊓ unipB k (Fin n),
      π g (π (diagT k (Fin n) t) v) = π u (π (diagT k (Fin n) t) v) := by
  obtain ⟨u, hu, d, hd, c, hc, rfl⟩ := hK.fact g hg
  refine ⟨u, hu, ?_⟩
  have h1 : ∀ x : K, π x v = ((1 : K →* ℂˣ) x : ℂ) • v := hv
  have hfix : ∀ h ∈ K, π h v = v := fun h hh => by simpa using h1 ⟨h, hh⟩
  have hc' := hK.low t ht c hc
  have hcomm : diagT k (Fin n) d * diagT k (Fin n) t = diagT k (Fin n) t * diagT k (Fin n) d := by
    rw [← map_mul, ← map_mul, mul_comm]
  have key : u * diagT k (Fin n) d * c * diagT k (Fin n) t =
      u * diagT k (Fin n) t * (diagT k (Fin n) d *
        ((diagT k (Fin n) t)⁻¹ * c * diagT k (Fin n) t)) := by
    calc u * diagT k (Fin n) d * c * diagT k (Fin n) t
        = u * (diagT k (Fin n) d * diagT k (Fin n) t) *
            ((diagT k (Fin n) t)⁻¹ * c * diagT k (Fin n) t) := by group
      _ = u * (diagT k (Fin n) t * diagT k (Fin n) d) *
            ((diagT k (Fin n) t)⁻¹ * c * diagT k (Fin n) t) := by rw [hcomm]
      _ = _ := by group
  rw [← rep_mul π (u * diagT k (Fin n) d * c), key, rep_mul π (u * diagT k (Fin n) t),
    rep_mul π (diagT k (Fin n) d), hfix _ hc', hfix _ hd, rep_mul]

theorem UpperTheory.Gal.Join.heckeMul :
    UpperTheory.Gal.Join.HeckeMul := by
  unfold UpperTheory.Gal.Join.HeckeMul UpperTheory.Gal.Join.ForRep
  intro k _ _ _ _ n V _ _ π K hK e he t ht v hv
  have hN : ∀ u ∈ K ⊓ unipB k (Fin n), ∀ w : V,
      (twKer π (unipB k (Fin n)) 1).mkQ (π u w) = (twKer π (unipB k (Fin n)) 1).mkQ w := by
    intro u hu w
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact Submodule.subset_span ⟨⟨u, (Subgroup.mem_inf.mp hu).2⟩, w, by simp⟩
  refine ⟨fun s hs => ?_, ?_⟩
  · have h2 := he.lin V (e.comp (π (diagT k (Fin n) s))) (π (diagT k (Fin n) t) v) ?_
    · simp only [LinearMap.comp_apply] at h2
      rw [h2, map_mul, rep_mul]
    · intro g hg
      obtain ⟨u, hu, hgu⟩ := exists_unipotent_eq_of_mem_iwLev_of_fixed π K hK t ht v hv g hg
      simp only [LinearMap.comp_apply]
      rw [hgu, ← rep_mul π (diagT k (Fin n) s) u,
        show diagT k (Fin n) s * u =
          (diagT k (Fin n) s * u * (diagT k (Fin n) s)⁻¹) * diagT k (Fin n) s by group,
        rep_mul π (diagT k (Fin n) s * u * (diagT k (Fin n) s)⁻¹),
        he.inv _ (hK.up s hs u hu)]
  · have h3 := he.lin _ (twKer π (unipB k (Fin n)) 1).mkQ (π (diagT k (Fin n) t) v) ?_
    · exact h3.trans rfl
    · intro g hg
      obtain ⟨u, hu, hgu⟩ := exists_unipotent_eq_of_mem_iwLev_of_fixed π K hK t ht v hv g hg
      rw [hgu, hN u hu]
end
