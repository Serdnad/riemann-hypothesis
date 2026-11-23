module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSemiMeasOfCovolOne
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle306
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiActionsMatchThroughLinkMap
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemidirectHaarMeasureFundamentalDomain
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel Matrix

namespace GlobalTheory.IwaPlace

variable {D : D7}

def hermAt (S : HSp D) (x y : Fin S.rank → AE D) : AE D := ∑ i, ∑ j, cA D (y i) * gA S i j * x j

def IsSDAt (S : HSp D) (v : Pl D) (Λ : AddSubgroup (Fin S.rank → AE D)) : Prop :=
  (∀ y ∈ Λ, ∀ i, y i ∈ idAt D (· = v)) ∧
    (∃ m : ℕ, 0 < m ∧ ∀ y : Fin S.rank → AE D, (∀ i, y i ∈ intAt D (· = v)) → (m : AE D) • y ∈ Λ) ∧
    ∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ ∀ x ∈ Λ, hermAt S y x ∈ intAt D (· = v))

theorem mem_congGrp_iff (V : HSp D) (I : Ideal (AE D)) (g : GA D V) :
    g ∈ congGrp V I ↔ ∀ i j, mt V g i j - (1 : Mx D V.rank V.rank) i j ∈ I := by
  unfold congGrp
  rw [MonoidHom.mem_ker]
  have e1 : ((1 : Mx D V.rank V.rank).map (Ideal.Quotient.mk I)) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have e2 : ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)).comp (matHom V) g).1 = (mt V g).map (Ideal.Quotient.mk I) := rfl
  constructor
  · intro h i j
    rw [← Ideal.Quotient.eq]
    have := congrArg (fun u : GL (Fin V.rank) (AE D ⧸ I) => u.1 i j) h
    simp only [e2, Units.val_one] at this
    rw [← e1] at this
    exact this
  · intro h
    ext i j
    rw [e2, Units.val_one, ← e1]
    exact Ideal.Quotient.eq.2 (h i j)

theorem mulVec_mem_idAt {P : Pl D → Prop} {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ idAt D P) (i : Fin m) : (M *ᵥ y) i ∈ idAt D P :=
  by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem wittCoreEmbedding_preserves_supportedUnitarySubgroup {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {P : Pl D → Prop} {γ : GA D S₀}
    (hγ : γ ∈ grpAt S₀ P) : d.emb0 γ ∈ grpAt S P := by
  have hγ' := (mem_congGrp_iff S₀ (idAt D P) γ).1 hγ
  refine (mem_congGrp_iff S (idAt D P) _).2 fun i j => ?_
  have e : mt S (d.emb0 γ) - 1 = d.j0 ⬝ (mt S₀ γ - 1) ⬝ d.p0 := by
    rw [d.unitaryMatrix_wittCoreEmbedding, ← d.sum_eq_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    abel
  rw [← Matrix.sub_apply, e, Matrix.mul_apply]
  refine Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ ?_
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (by rw [Matrix.sub_apply]; exact hγ' l k)

end GlobalTheory.IwaPlace

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open Filter Topology IsDedekindDomain NumberField
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.AdelicLimit

section Basis

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]



theorem repr_map {R R' : Type} [CommRing R] [CommRing R'] [Algebra F R] [Algebra F R'] (α : R →ₐ[F] R')
    (z : R ⊗[F] E) (k : Fin (Module.finrank F E)) :
    (Algebra.TensorProduct.basis R' (Module.finBasis F E)).repr (Algebra.TensorProduct.map α (AlgHom.id F E) z) k =
      α ((Algebra.TensorProduct.basis R (Module.finBasis F E)).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul]
    simp [Finsupp.smul_apply, Finsupp.mapRange_apply, map_mul, AlgHom.commutes]
  | add x y hx hy =>
    simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

end Basis

section Fin

variable {F : Type} [Field F] [NumberField F]

theorem tendsto_finAdele (f : Finset (HeightOneSpectrum (𝓞 F)) → FiniteAdeleRing (𝓞 F) F)
    (y g : FiniteAdeleRing (𝓞 F) F) (hin : ∀ T, ∀ v ∈ T, f T v = y v) (hout : ∀ T, ∀ v, v ∉ T → f T v = g v) :
    Tendsto f atTop (𝓝 y) := by
  classical
  let S : Set (HeightOneSpectrum (𝓞 F)) :=
    {v | y v ∈ v.adicCompletionIntegers F ∧ g v ∈ v.adicCompletionIntegers F}
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ Filter.principal S := by
    rw [Filter.le_principal_iff]; exact y.2.and g.2
  let P := RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) (Filter.principal S)
  let f' : Finset (HeightOneSpectrum (𝓞 F)) → P := fun T => ⟨fun v => f T v, by
    rw [Filter.eventually_principal]
    intro w hw
    show f T w ∈ (w.adicCompletionIntegers F : Set (w.adicCompletion F))
    by_cases h : w ∈ T
    · rw [hin T w h]; exact hw.1
    · rw [hout T w h]; exact hw.2⟩
  let y' : P := ⟨fun v => y v, by rw [Filter.eventually_principal]; exact fun w hw => hw.1⟩
  have hf : Tendsto f' atTop (𝓝 y') := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
    intro v
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ({v} : Finset _)] with T hT
    have : v ∈ T := hT (Finset.mem_singleton_self v)
    change y v = f T v
    rw [hin T v this]
  exact ((RestrictedProduct.continuous_inclusion hle).tendsto y').comp hf

end Fin

section Entry

variable {D : D7}


theorem repr_infPart (z : AE D) (k : Fin (Module.finrank D.host.F D.host.E)) :
    (Algebra.TensorProduct.basis (Ainf D.host.F) (Module.finBasis D.host.F D.host.E)).repr (infPart D z) k =
      fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr z k) := by
  change (Algebra.TensorProduct.basis (Ainf D.host.F) (Module.finBasis D.host.F D.host.E)).repr
    (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) z) k = _
  rw [repr_map]


theorem repr_compAt (w : Pl D) (z : AE D) (k : Fin (Module.finrank D.host.F D.host.E)) :
    (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).repr (compAt D w z) k =
      evalV D.host.F w (sndA D.host.F
        ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr z k)) := by
  change (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).repr
    (Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id D.host.F D.host.E)
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) z)) k = _
  rw [repr_map, repr_map]



theorem tendsto_entry (a : Finset (Pl D) → AE D) (b c : AE D) (hinf : ∀ T, infPart D (a T) = infPart D b)
    (hin : ∀ T, ∀ w ∈ T, compAt D w (a T) = compAt D w b)
    (hout : ∀ T w, w ∉ T → compAt D w (a T) = compAt D w c) : Tendsto a atTop (𝓝 b) := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  set Bs := Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E) with hBs
  have hc : ∀ k, Tendsto (fun T => Bs.repr (a T) k) atTop (𝓝 (Bs.repr b k)) := by
    intro k
    have h1 : ∀ T, (Bs.repr (a T) k).1 = (Bs.repr b k).1 := fun T => by
      have h := congrArg (fun z => (Algebra.TensorProduct.basis (Ainf D.host.F)
        (Module.finBasis D.host.F D.host.E)).repr z k) (hinf T)
      simp only [repr_infPart] at h
      exact h
    have h2 : Tendsto (fun T => (Bs.repr (a T) k).2) atTop (𝓝 (Bs.repr b k).2) := by
      refine tendsto_finAdele _ _ (Bs.repr c k).2 (fun T w hw => ?_) (fun T w hw => ?_)
      · have h := congrArg (fun z => (Algebra.TensorProduct.basis (Fv D.host.F w)
          (Module.finBasis D.host.F D.host.E)).repr z k) (hin T w hw)
        simp only [repr_compAt] at h
        exact h
      · have h := congrArg (fun z => (Algebra.TensorProduct.basis (Fv D.host.F w)
          (Module.finBasis D.host.F D.host.E)).repr z k) (hout T w hw)
        simp only [repr_compAt] at h
        exact h
    have h3 := (tendsto_const_nhds (x := (Bs.repr b k).1)).prodMk_nhds h2
    refine h3.congr fun T => ?_
    exact Prod.ext (h1 T).symm rfl
  have := tendsto_finsetSum (Finset.univ : Finset (Fin (Module.finrank D.host.F D.host.E)))
    (fun k _ => (hc k).smul_const (Bs k))
  simpa only [Bs.sum_repr] using this

theorem map_inv_entries {A R : Type} [CommRing A] [Ring R] {n : ℕ} (φ : A →+* R) (u v : GL (Fin n) A)
    (h : ∀ i j, φ ((u : Matrix (Fin n) (Fin n) A) i j) = φ ((v : Matrix (Fin n) (Fin n) A) i j)) :
    ∀ i j, φ (((u⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) i j) =
      φ (((v⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) i j) := by
  have hM : φ.mapMatrix (u : Matrix (Fin n) (Fin n) A) = φ.mapMatrix (v : Matrix (Fin n) (Fin n) A) :=
    Matrix.ext fun i j => h i j
  have e1 : φ.mapMatrix ((u⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) * φ.mapMatrix (u : Matrix (Fin n) (Fin n) A) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have e2 : φ.mapMatrix (v : Matrix (Fin n) (Fin n) A) * φ.mapMatrix ((v⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [← hM] at e2
  have e := left_inv_eq_right_inv e1 e2
  intro i j
  exact congrArg (fun M => M i j) e

end Entry



theorem tendsto_of_agree (D : D7) (S : HSp D) (κ : GA D S) (x : Finset (Pl D) → GA D S)
    (h1 : ∀ Fs i j, infPart D (Formalism.L2.Theta.mt S (x Fs) i j) = infPart D (Formalism.L2.Theta.mt S κ i j))
    (h2 : ∀ Fs, ∀ w ∈ Fs, ∀ i j, GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S (x Fs) i j) =
      GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S κ i j))
    (h3 : ∀ Fs w, w ∉ Fs → ∀ i j, GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S (x Fs) i j) =
      GlobalTheory.FinPl.compAt D w ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j)) :
    Filter.Tendsto x Filter.atTop (nhds κ) := by
  let u : Finset (Pl D) → GL (Fin S.rank) (AE D) := fun T => matHom S (x T)
  have hv : Tendsto (fun T => (u T).val) atTop
      (𝓝 (matHom S κ).val) :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j =>
      tendsto_entry (fun T => mt S (x T) i j) (mt S κ i j) ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j)
        (fun T => h1 T i j) (fun T w hw => h2 T w hw i j) (fun T w hw => h3 T w hw i j)
  have hi : Tendsto (fun T => ((u T)⁻¹).val) atTop
      (𝓝 ((matHom S κ)⁻¹).val) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    refine tendsto_entry _ _ ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j)
      (fun T => map_inv_entries (infPart D) (u T) (matHom S κ) (h1 T) i j)
      (fun T w hw => map_inv_entries (compAt D w) (u T) (matHom S κ) (h2 T w hw) i j)
      (fun T w hw => ?_)
    have h := map_inv_entries (compAt D w) (u T) 1 (fun i j => by rw [Units.val_one]; exact h3 T w hw i j) i j
    simpa using h
  have key : Tendsto u atTop (𝓝 (matHom S κ)) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    exact hv.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp hi)
  exact tendsto_subtype_rng.2 key

end GlobalTheory.AdelicLimit
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.JacMeas

open GlobalTheory.SemiHaar

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

def lv : UX D ρ →* GA D S := d.levi.comp (UX D ρ).subtype

theorem lv_mem (u : UX D ρ) : lv d u ∈ flagN d := d.levi_mem_NFlag u.2

theorem radX_le : radX d ≤ flagN d := inf_le_left

theorem lv_conj (n : GA D S) (hn : n ∈ radX d) (u : UX D ρ) : lv d u * n * (lv d u)⁻¹ ∈ radX d := by
  refine ⟨(flagN d).mul_mem ((flagN d).mul_mem (lv_mem d u) hn.1) ((flagN d).inv_mem (lv_mem d u)), ?_⟩
  change mt S (d.levi u.1 * n * (d.levi u.1)⁻¹) ⬝ d.jX = d.jX
  rw [← map_inv, mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.levi_jX, ← Matrix.mul_assoc (mt S n),
    mem_fixer.1 hn.2, ← Matrix.mul_assoc, d.levi_jX, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.mul_one]

theorem anisotropicEmbedding_conj_wittFlagUnipotentFixer (n : GA D S) (hn : n ∈ radX d) (h : GA D S₀) : d.emb0 h * n * (d.emb0 h)⁻¹ ∈ radX d :=
  ⟨(flag_jacobi_structure D S S₀ ρ d).2.2.2.2.1 n hn.1 h,
    (stabX d).mul_mem ((stabX d).mul_mem (wittSmallGroupEmbedding_mem_pointwiseStabilizerIsotropic d h) hn.2) ((stabX d).inv_mem (wittSmallGroupEmbedding_mem_pointwiseStabilizerIsotropic d h))⟩

theorem radX_sup_lv : radX d ⊔ (lv d).range = flagN d := by
  refine le_antisymm (sup_le (radX_le d) (by rintro _ ⟨u, rfl⟩; exact lv_mem d u)) fun n hn => ?_
  obtain ⟨u, hu, b, c, rfl⟩ := ((flag_jacobi_structure D S S₀ ρ d).1 n).1 hn
  exact mul_mem (Subgroup.mem_sup_right ⟨⟨u, hu⟩, rfl⟩)
    (Subgroup.mem_sup_left (mul_mem (nB_mem_radX d b) (nC_mem_radX d c)))

theorem wittFlagUnipotentFixer_sup_anisotropic_eq_stabilizer : radX d ⊔ d.emb0.range = stabX d := by
  refine le_antisymm (sup_le (radX_le_stabX d) (by rintro _ ⟨u, rfl⟩; exact wittSmallGroupEmbedding_mem_pointwiseStabilizerIsotropic d u)) fun g hg => ?_
  obtain ⟨n, hn, h, rfl⟩ := ((flag_jacobi_structure D S S₀ ρ d).2.2.1 g).1 hg
  exact mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨h, rfl⟩)

theorem blockX_mul_lv {n : GA D S} (hn : n ∈ radX d) (u : UX D ρ) : blockX d (n * lv d u) = u.1.1 := by
  change d.pX ⬝ (mt S (n * d.levi u.1) ⬝ d.jX) = _
  rw [mt_mul, Matrix.mul_assoc, d.levi_jX, ← Matrix.mul_assoc (mt S n), mem_fixer.1 hn.2, ← Matrix.mul_assoc, d.pX_jX,
    Matrix.one_mul]

theorem exists_rad_lv {n : GA D S} (hn : n ∈ flagN d) : ∃ n₀ ∈ radX d, ∃ u, n = n₀ * lv d u :=
  exists_mul_of_mem_sup_range (radX d) (lv d) (lv_conj d) (by rw [radX_sup_lv]; exact hn)

theorem continuous_blockX : Continuous (blockX d) :=
  continuous_const.matrix_mul ((continuous_mt S).matrix_mul continuous_const)

theorem isClosed_stabX : IsClosed (stabX d : Set (GA D S)) := by
  haveI := (lattice_Mx D S.rank ρ).2.2.2.1
  exact isClosed_eq ((continuous_mt S).matrix_mul continuous_const) continuous_const

theorem isClosed_flagN : IsClosed (flagN d : Set (GA D S)) := by
  haveI := (lattice_Mx D S.rank ρ).2.2.2.1
  haveI := (lattice_Mx D S₀.rank S₀.rank).2.2.2.1
  have e : (flagN d : Set (GA D S)) = (blockX d ⁻¹' GlobalTheory.UnitU.uniSet D ρ) ∩
      ({g | mt S g ⬝ d.jX = d.jX ⬝ blockX d g} ∩ {g | d.p0 ⬝ (mt S g ⬝ d.j0) = 1}) := by
    ext g
    constructor
    · intro hg
      refine ⟨?_, ?_, (GlobalTheory.JacProj.flag_le d hg).2⟩
      · obtain ⟨n, hn, u, rfl⟩ := exists_rad_lv d hg
        rw [Set.mem_preimage, blockX_mul_lv d hn]
        exact u.2
      · exact GlobalTheory.JacProj.keeps_jX d (GlobalTheory.JacProj.flag_le d hg).1
    · rintro ⟨h1, h2, h3⟩
      let u : UX D ρ := ⟨GlobalTheory.UnitU.toUnit _ h1, h1⟩
      have hs : (lv d u)⁻¹ * g ∈ stabX d := by
        change mt S ((lv d u)⁻¹ * g) ⬝ d.jX = d.jX
        have h4 : mt S g ⬝ d.jX = mt S (lv d u) ⬝ d.jX := (show _ = _ from h2).trans (d.levi_jX u.1).symm
        rw [mt_mul, Matrix.mul_assoc, h4, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
      obtain ⟨n, hn, h, he⟩ := ((flag_jacobi_structure D S S₀ ρ d).2.2.1 _).1 hs
      have hg : g = lv d u * n * d.emb0 h := by rw [mul_assoc, ← he, mul_inv_cancel_left]
      have hn' : lv d u * n ∈ flagN d := mul_mem (lv_mem d u) hn.1
      have h5 := GlobalTheory.JacProj.witt_anisotropic_block_flag_mul_embedded d hn' h
      rw [← hg, show d.p0 ⬝ (mt S g ⬝ d.j0) = 1 from h3] at h5
      have h6 : h = 1 := mt_injective S₀ (h5.symm.trans (mt_one S₀).symm)
      rw [hg, h6, map_one, mul_one]
      exact hn'
  rw [e]
  exact ((GlobalTheory.UnitU.isClosed_uniSet D ρ).preimage (continuous_blockX d)).inter
    ((isClosed_eq ((continuous_mt S).matrix_mul continuous_const) (continuous_const.matrix_mul (continuous_blockX d))).inter
      (isClosed_eq (continuous_const.matrix_mul ((continuous_mt S).matrix_mul continuous_const)) continuous_const))

theorem isClosed_radX : IsClosed (radX d : Set (GA D S)) := (isClosed_flagN d).inter (isClosed_stabX d)

theorem exists_proj_lv : ∃ p : flagN d → UX D ρ, Continuous p ∧
    ∀ (u : UX D ρ) (n : radX d) (hm : n.1 * lv d u ∈ flagN d), p ⟨n.1 * lv d u, hm⟩ = u := by
  choose n₀ hn₀ p hp using fun g : flagN d => exists_rad_lv d g.2
  have hb : ∀ g, (p g).1.1 = blockX d g.1 := fun g => by rw [hp g, blockX_mul_lv d (hn₀ g)]
  refine ⟨p, (GlobalTheory.UnitU.isClosedEmbedding_val D ρ).isInducing.continuous_iff.2 ?_, fun u n hm => ?_⟩
  · exact ((continuous_blockX d).comp continuous_subtype_val).congr fun g => (hb g).symm
  · exact Subtype.ext (Units.ext ((hb _).trans (blockX_mul_lv d n.2 u)))

theorem rat_lv (n : GA D S) (hn : n ∈ radX d) (u : UX D ρ) : n * lv d u ∈ GQ S ↔ n ∈ GQ S ∧ u ∈ UXQ D ρ := by
  have hb : ∀ g ∈ GQ S, blockX d g ∈ ratMx D ρ ρ := fun g hg =>
    ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff S g).1 hg) (rat_mem _))
  refine ⟨fun h => ?_, fun h => mul_mem h.1 (d.levi_mem_GQ h.2.1 h.2.2)⟩
  have h1 := hb _ h
  have h2 := hb _ (inv_mem h)
  rw [show (n * lv d u)⁻¹ = (lv d u⁻¹ * n⁻¹ * (lv d u⁻¹)⁻¹) * lv d u⁻¹ by simp,
    blockX_mul_lv d (lv_conj d _ (inv_mem hn) _)] at h2
  rw [blockX_mul_lv d hn] at h1
  refine ⟨?_, h1, h2⟩
  rw [show n = n * lv d u * (lv d u)⁻¹ by simp]
  exact mul_mem h (inv_mem (d.levi_mem_GQ h1 h2))

theorem jac_measure : ∀ (D : D7) (ρ : ℕ) (J : JacLev D ρ) (vU : VolU D ρ) (ν₀ : Measure (radX J.d)) (𝓝₀ : Set (radX J.d)), ν₀.IsHaarMeasure → IsFundamentalDomain ((GQ J.W).subgroupOf (radX J.d)) 𝓝₀ ν₀ → ν₀ 𝓝₀ = 1 → IsClosed ((radX J.d ⊔ J.d.emb0.range : Subgroup (GA D J.W)) : Set (GA D J.W)) ∧ (semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀).IsHaarMeasure ∧ (semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀).IsInvInvariant ∧ J.μR.IsInvInvariant ∧ ∀ F : GA D J.W → ENNReal, Measurable F → ∫⁻ r : jacGrp J.d, F r ∂J.μR = ∫⁻ u, ∫⁻ r : (radX J.d ⊔ J.d.emb0.range : Subgroup (GA D J.W)), F (r * J.d.levi u.1) ∂(semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀) ∂vU.ν := by
  intro D ρ J vU ν₀ 𝓝₀ hν₀ h𝓝₀ h𝓝₀1
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W
  obtain ⟨j1, j2, j3, j4, j5, -, j7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W₀
  obtain ⟨k1, k2, k3⟩ := GlobalTheory.UnitU.topology D ρ
  have k4 := (GlobalTheory.UnitU.rational D ρ).1
  have k5 : BorelSpace (UX D ρ) := ⟨rfl⟩
  obtain ⟨hU, 𝓤, h𝓤, h𝓤1⟩ := vU.unit
  haveI : SFinite vU.ν := by
    letI : LocallyCompactSpace (UX D ρ) := k1
    letI : SecondCountableTopology (UX D ρ) := k2
    letI : vU.ν.IsHaarMeasure := hU
    exact @MeasureTheory.instSFiniteOfSigmaFinite _ _ vU.ν (Measure.IsHaarMeasure.sigmaFinite vU.ν)
  obtain ⟨hN, h𝓝, h𝓝1⟩ := J.vN.unit
  obtain ⟨K, hK, hcov⟩ := J.cpt
  have hμ := J.v0.haar
  obtain ⟨p, hpc, hp⟩ := GlobalTheory.JacProj.exists_continuous_proj D J.W J.W₀ ρ J.d
  have hle : radX J.d ⊔ J.d.emb0.range ≤ flagN J.d ⊔ J.d.emb0.range := sup_le_sup_right (radX_le J.d) _
  have H0 := semiMeas_haar_inv (radX J.d) J.d.emb0 (isClosed_radX J.d) J.d.continuous_embed (anisotropicEmbedding_conj_wittFlagUnipotentFixer J.d)
    ⟨fun g => p (Subgroup.inclusion hle g), hpc.comp (continuous_inclusion hle), fun h n => hp h ⟨n.1, n.2.1⟩⟩
    (GQ J.W) (GQ J.W₀) (fun _ h => J.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints h) hK hcov J.v0.μ J.v0.fund ν₀ h𝓝₀
    (by rw [h𝓝₀1]; exact ENNReal.one_ne_top)
  have H1 := semiMeas_haar_inv (flagN J.d) J.d.emb0 (isClosed_flagN J.d) J.d.continuous_embed
    (flag_jacobi_structure D J.W J.W₀ ρ J.d).2.2.2.2.1 ⟨p, hpc, hp⟩
    (GQ J.W) (GQ J.W₀) (fun _ h => J.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints h) hK hcov J.v0.μ J.v0.fund J.vN.ν h𝓝
    (by rw [h𝓝1]; exact ENNReal.one_ne_top)
  refine ⟨by rw [wittFlagUnipotentFixer_sup_anisotropic_eq_stabilizer]; exact isClosed_stabX J.d, H0.1, H0.2, H1.2, fun F hF => ?_⟩
  have l1 : LocallyCompactSpace (radX J.d) := (isClosed_radX J.d).locallyCompactSpace
  have l2 : SecondCountableTopology (radX J.d) := TopologicalSpace.Subtype.secondCountableTopology _
  have l3 : LocallyCompactSpace (flagN J.d) := (isClosed_flagN J.d).locallyCompactSpace
  have l4 : SecondCountableTopology (flagN J.d) := TopologicalSpace.Subtype.secondCountableTopology _
  have hlv : Continuous (lv J.d) := J.d.continuous_levi.comp continuous_subtype_val
  have hs := J.d.continuous_embed
  have e1 : ∫⁻ r : jacGrp J.d, F r ∂J.μR = ∫⁻ h, ∫⁻ n, F (n.1 * J.d.emb0 h) ∂J.vN.ν ∂J.v0.μ :=
    lintegral_semiMeas (flagN J.d) J.d.emb0 hs J.v0.μ J.vN.ν F hF
  have e2 : ∀ h, ∫⁻ n, F (n.1 * J.d.emb0 h) ∂J.vN.ν = ∫⁻ u, ∫⁻ n, F (n.1 * lv J.d u * J.d.emb0 h) ∂ν₀ ∂vU.ν := fun h =>
    lintegral_of_covolOne (radX J.d) (lv J.d) (isClosed_radX J.d) hlv (lv_conj J.d) (flagN J.d) (radX_sup_lv J.d)
      (exists_proj_lv J.d) (GQ J.W) (UXQ D ρ) (rat_lv J.d) vU.ν h𝓤 h𝓤1 ν₀ h𝓝₀ h𝓝₀1 J.vN.ν h𝓝 h𝓝1
      (fun g => F (g * J.d.emb0 h)) (hF.comp (continuous_mul_const _).measurable)
  have e3 : ∀ u : UX D ρ, ∫⁻ r : (radX J.d ⊔ J.d.emb0.range : Subgroup (GA D J.W)), F (r * J.d.levi u.1)
      ∂(semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀) = ∫⁻ h, ∫⁻ n, F (n.1 * lv J.d u * J.d.emb0 h) ∂ν₀ ∂J.v0.μ := fun u => by
    rw [lintegral_semiMeas (radX J.d) J.d.emb0 hs J.v0.μ ν₀ (fun g => F (g * J.d.levi u.1))
      (hF.comp (continuous_mul_const _).measurable)]
    simp only [mul_assoc, J.d.wittHyperbolic_anisotropic_commute_levi]
    rfl
  have hm : Measurable fun q : (GA D J.W₀ × UX D ρ) × radX J.d => F (q.2.1 * lv J.d q.1.2 * J.d.emb0 q.1.1) :=
    hF.comp (Continuous.measurable (((continuous_subtype_val.comp continuous_snd).mul
      (hlv.comp (continuous_snd.comp continuous_fst))).mul (hs.comp (continuous_fst.comp continuous_fst))))
  rw [e1]
  simp only [e2, e3]
  exact lintegral_lintegral_swap (hm.lintegral_prod_right' (ν := ν₀)).aemeasurable

end GlobalTheory.JacMeas
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.unfoldingLevelsAndSteps_haarMeasures_exist : ∀ D : D7, (∀ V : HSp D, Nonempty (Vol V)) ∧ (∀ (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), Nonempty (VolN d)) ∧ (∀ m n, Nonempty (VolM D m n)) ∧ ∀ ρ, Nonempty (VolU D ρ) := by
  first | exact @GlobalTheory.Unf.VolExist.measures_exist | exact GlobalTheory.Unf.VolExist.measures_exist | (intros; apply GlobalTheory.Unf.VolExist.measures_exist <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.jacobiActions_match_through_linkMap : ∀ (D : D7) (ρ σ : ℕ) (B : BesLev D σ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ (l : Link B L' ζ') (W W₀ : HSp D) (d : HypDec W W₀ ρ), ∀ n ∈ flagN d, l.κ W₀ (ptS d L' (zEll L' ρ ζ') n) = ptT d B.L (yZero B.L ρ B.ζ) n ∧ cenT d B.L (yZero B.L ρ B.ζ) n = -cenS d L' (zEll L' ρ ζ') n := by
  first | exact @GlobalTheory.Unf.LinkPoint.link_point | exact GlobalTheory.Unf.LinkPoint.link_point | (intros; apply GlobalTheory.Unf.LinkPoint.link_point <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.semidirect_haar_measure_fundamental_domain : ∀ (D : D7) (S H : HSp D) (N : Subgroup (GA D S)) (s : GA D H →* GA D S), Continuous s → IsClosed (N : Set (GA D S)) → (∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N) → (∀ n ∈ N, ∀ n' ∈ N, ∀ h h', n * s h = n' * s h' → n = n' ∧ h = h') → (∀ n ∈ N, ∀ h, n * s h ∈ GQ S ↔ n ∈ GQ S ∧ h ∈ GQ H) → ∀ (vH : Vol H) (ν : Measure N) (𝓝 : Set N), ν.IsHaarMeasure → IsFundamentalDomain ((GQ S).subgroupOf N) 𝓝 ν → (semiMeas N s vH.μ ν).IsHaarMeasure → ∃ 𝓡 : Set (N ⊔ s.range : Subgroup (GA D S)), IsFundamentalDomain ((GQ S ⊓ (N ⊔ s.range)).subgroupOf (N ⊔ s.range)) 𝓡 (semiMeas N s vH.μ ν) ∧ ∀ f : GA D S → ℂ, Measurable f → (IntegrableOn (fun r : (N ⊔ s.range : Subgroup (GA D S)) => f r) 𝓡 (semiMeas N s vH.μ ν) ↔ AbsConv vH.μ vH.𝓕 ν 𝓝 fun h n => f (n.1 * s h)) ∧ (AbsConv vH.μ vH.𝓕 ν 𝓝 (fun h n => f (n.1 * s h)) → ∫ r in 𝓡, f (r : GA D S) ∂(semiMeas N s vH.μ ν) = ∫ h in vH.𝓕, ∫ n in 𝓝, f (n.1 * s h) ∂ν ∂vH.μ) := by
  first | exact @GlobalTheory.Unf.semiFd_iterated | exact GlobalTheory.Unf.semiFd_iterated | (intros; apply GlobalTheory.Unf.semiFd_iterated <;> assumption)
end
