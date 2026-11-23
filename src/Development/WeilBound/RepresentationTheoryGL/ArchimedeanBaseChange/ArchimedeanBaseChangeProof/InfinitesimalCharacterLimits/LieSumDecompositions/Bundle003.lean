module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle006
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle005
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksDefs

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs GlobalTheory.SmGL

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Curve

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

def ecurve {N : ℕ} (Z : Matrix (Fin N) (Fin N) (Cinf E)) (t : ℝ) : Matrix (Fin N) (Fin N) (Cinf E) :=
  NormedSpace.exp (t • Z)

theorem hasDerivAt_ecurve {N : ℕ} (Z : Matrix (Fin N) (Fin N) (Cinf E)) : HasDerivAt (ecurve Z) Z 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Z (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact h

theorem ecurve_zero {N : ℕ} (Z : Matrix (Fin N) (Fin N) (Cinf E)) : ecurve Z 0 = 1 := by
  simp [ecurve]

theorem ecurve_mem {N : ℕ} (Z : Matrix (Fin N) (Fin N) (Cinf E)) (hZ : Zᴴ = -Z) (t : ℝ) :
    ecurve Z t ∈ Matrix.unitaryGroup (Fin N) (Cinf E) := by
  have hc : (t • Z)ᴴ = -(t • Z) := by
    rw [conjTranspose_smul, hZ]; simp
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ecurve, ← Matrix.exp_conjTranspose, hc,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Z)).neg_right]
  simp

def toLclm (N : ℕ) : Matrix (Fin N) (Fin N) (Cinf E) →L[ℝ] Lie E N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => toL A, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

theorem hasDerivAt_toL_ecurve {N : ℕ} (Z : Matrix (Fin N) (Fin N) (Cinf E)) :
    HasDerivAt (fun t => (toL (ecurve Z t) : Lie E N)) (toL Z) 0 := by
  have h := ((toLclm (E := E) N).hasFDerivAt (x := ecurve Z 0)).comp_hasDerivAt (0 : ℝ) (hasDerivAt_ecurve Z)
  exact h

end Curve

def kcurve {N : ℕ} (Z : Matrix (Fin N) (Fin N) (Cinf E)) (hZ : Zᴴ = -Z) (t : ℝ) : Kinf E N :=
  ⟨ecurve Z t, ecurve_mem Z hZ t⟩

theorem lie_mem_orbSpan {N : ℕ} (φ : Sm E N) [FiniteDimensional ℂ (GlobalTheory.CuspRep.LocEx.orbSpan φ)]
    (Z : Matrix (Fin N) (Fin N) (Cinf E)) (hZ : Zᴴ = -Z) :
    lie E N (toL Z) φ ∈ GlobalTheory.CuspRep.LocEx.orbSpan φ := by
  set A : Submodule ℂ (GA E N → ℂ) := (GlobalTheory.CuspRep.LocEx.orbSpan φ).map (Sm E N).subtype with hA
  have : FiniteDimensional ℂ A := inferInstance
  obtain ⟨S, a, ha⟩ := SliceTensor.interp A
  let c : ℝ → GL (Fin N) (Cinf E) := fun t => Unitary.toUnits (kcurve Z hZ t)
  have h0 : c 0 = 1 := Units.ext (ecurve_zero Z)
  have hc : HasDerivAt (fun t => toL (c t).val) (toL Z) 0 := hasDerivAt_toL_ecurve Z
  have hmem : ∀ t, (cptRep E N (kcurve Z hZ t) φ).1 ∈ A := fun t =>
    ⟨_, Submodule.subset_span ⟨kcurve Z hZ t, rfl⟩, rfl⟩
  have hval : ∀ t g, (cptRep E N (kcurve Z hZ t) φ).1 g = φ.1 (g * infGL E N (c t)) := fun _ _ => rfl
  have key : ∀ g, lieD (toL Z) φ.1 g = ∑ κ : S, lieD (toL Z) φ.1 κ.1 * (a κ : GA E N → ℂ) g := by
    intro g
    have e : ∀ t, φ.1 (g * infGL E N (c t)) = ∑ κ : S, φ.1 (κ.1 * infGL E N (c t)) * (a κ : GA E N → ℂ) g := by
      intro t
      have := congrFun (ha _ (hmem t)) g
      rw [hval, Finset.sum_apply] at this
      rw [this]
      refine Finset.sum_congr rfl fun κ _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, hval]
    have d1 := hasDerivAt_curve φ g c (toL Z) h0 hc
    have d2 : HasDerivAt (fun t => ∑ κ : S, φ.1 (κ.1 * infGL E N (c t)) * (a κ : GA E N → ℂ) g)
        (∑ κ : S, lieD (toL Z) φ.1 κ.1 * (a κ : GA E N → ℂ) g) 0 :=
      HasDerivAt.fun_sum fun κ _ => (hasDerivAt_curve φ κ.1 c (toL Z) h0 hc).mul_const _
    rw [show (fun t => φ.1 (g * infGL E N (c t))) = fun t =>
      ∑ κ : S, φ.1 (κ.1 * infGL E N (c t)) * (a κ : GA E N → ℂ) g from funext e] at d1
    exact d1.unique d2
  have hL : (lie E N (toL Z) φ).1 ∈ A := by
    have e : (lie E N (toL Z) φ).1 = ∑ κ : S, lieD (toL Z) φ.1 κ.1 • (a κ : GA E N → ℂ) := by
      funext g
      rw [GlobalTheory.CuspRep.lie_apply, key g, Finset.sum_apply]
      rfl
    rw [e]
    exact A.sum_mem fun κ _ => A.smul_mem _ (a κ).2
  obtain ⟨y, hy, e⟩ := hL
  have : y = lie E N (toL Z) φ := Subtype.ext e
  rw [← this]
  exact hy

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration
end
end

section

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.KTypeSlices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def detKer (n : ℕ) : Subgroup (GL (Fin n) (Af E)) where
  carrier := {u | GlobalTheory.Mem.Chr.CharModel.logFin E (Matrix.GeneralLinearGroup.det u) = 0}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_mul, GlobalTheory.Mem.Chr.CharModel.logFin_mul] at *
    rw [ha, hb, add_zero]
  one_mem' := by
    simp only [Set.mem_setOf_eq, map_one, GlobalTheory.Mem.Chr.CharModel.logFin_one]
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq, map_inv] at *
    have h := GlobalTheory.Mem.Chr.CharModel.logFin_mul E (Matrix.GeneralLinearGroup.det a) (Matrix.GeneralLinearGroup.det a)⁻¹
    rw [mul_inv_cancel, GlobalTheory.Mem.Chr.CharModel.logFin_one, ha, zero_add] at h
    exact h.symm

theorem isOpen_detKer (n : ℕ) : IsOpen (detKer (E := E) n : Set (GL (Fin n) (Af E))) := by
  have hc : Continuous (fun u : GL (Fin n) (Af E) => Matrix.GeneralLinearGroup.det u) := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (Units.continuous_val).matrix_det
    · exact (Units.continuous_coe_inv).matrix_det
  have h := hc.continuousAt (x := 1)
  rw [ContinuousAt, map_one] at h
  exact Subgroup.isOpen_of_mem_nhds _ (h.eventually (GlobalTheory.Mem.Chr.CharModel.logFin_eventually E))

theorem t_logNorm_finId (x : (Af E)ˣ) :
    GlobalTheory.Mem.Chr.CharModel.logNorm E (finId E x) = - GlobalTheory.Mem.Chr.CharModel.logFin E x := by
  have h1 : GlobalTheory.Mem.Chr.CharModel.infPart E (finId E x) = 1 := Units.ext (by
    change (1 : InfiniteAdeleRing E) - 0 + 0 = 1
    simp)
  have h2 : GlobalTheory.Mem.Chr.CharModel.finPart E (finId E x) = x := Units.ext (by
    change (1 : Af E) - 1 + (x : Af E) = x
    simp)
  rw [GlobalTheory.Mem.Chr.CharModel.logNorm, h1, h2, GlobalTheory.Mem.Chr.CharModel.logInf_one, zero_sub]

theorem t_chi_fin {n : ℕ} (w : ℂ) {u : GL (Fin n) (Af E)} (hu : u ∈ detKer n) :
    ((chiDet n (Model.absC E w) (finGL E n u) : ℂˣ) : ℂ) = 1 := by
  rw [ExponentTwist.chiDet_absC_val, det_finGL, t_logNorm_finId]
  have h : GlobalTheory.Mem.Chr.CharModel.logFin E (Matrix.GeneralLinearGroup.det u) = 0 := hu
  rw [h, neg_zero]
  simp

theorem t_chi_inf {n : ℕ} (w : ℂ) (k : Kinf E n) :
    ((chiDet n (Model.absC E w) (infGL E n (Unitary.toUnits k)) : ℂˣ) : ℂ) = 1 := by
  rw [ExponentTwist.chiDet_absC_val, det_infGL, Model.logNorm_infId]
  have h : ∀ v, ‖(k : Matrix (Fin n) (Fin n) (Cinf E)).det v‖ = 1 := by
    intro v
    have hd := Matrix.det_of_mem_unitary k.2
    have e := congrFun (Unitary.mem_iff.1 hd).1 v
    change star ((k : Matrix (Fin n) (Fin n) (Cinf E)).det v) * (k : Matrix (Fin n) (Fin n) (Cinf E)).det v = 1 at e
    rw [Complex.star_def, Complex.conj_mul'] at e
    have e2 : ‖(k : Matrix (Fin n) (Fin n) (Cinf E)).det v‖ ^ 2 = 1 := by exact_mod_cast e
    have hn := norm_nonneg ((k : Matrix (Fin n) (Fin n) (Cinf E)).det v)
    nlinarith
  simp [h]

theorem t_typeB_mulChi {n : ℕ} {K' : Subgroup (GL (Fin n) (Af E))} {W' : Submodule ℂ (Kinf E n → ℂ)} {ψ : Sm E n}
    (hT : SpectralAccumulation.TypeB K' W' ψ) (hK' : K' ≤ detKer n) (w : ℂ) : SpectralAccumulation.TypeB K' W' (mulChi n (Model.absC E w) ψ) := by
  refine ⟨fun u hu g => ?_, fun g => ?_⟩
  · rw [mulChi_apply, mulChi_apply, map_mul, Units.val_mul, t_chi_fin w (hK' hu), mul_one, hT.1 u hu g]
  · have e : (fun k : Kinf E n => (mulChi n (Model.absC E w) ψ).1 (g * infGL E n (Unitary.toUnits k))) =
        ((chiDet n (Model.absC E w) g : ℂˣ) : ℂ) • fun k => ψ.1 (g * infGL E n (Unitary.toUnits k)) := by
      funext k
      rw [mulChi_apply, map_mul, Units.val_mul, t_chi_inf, mul_one, Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [e]
    exact W'.smul_mem _ (hT.2 g)

theorem untw {n : ℕ} {V : Submodule ℂ (Sm E n)} {z : ℂ} {ψ : Sm E n} (hψ : ψ ∈ tw V z) (h0 : ψ ≠ 0)
    {K' : Subgroup (GL (Fin n) (Af E))} {W' : Submodule ℂ (Kinf E n → ℂ)} (hT : SpectralAccumulation.TypeB K' W' ψ)
    (hK' : K' ≤ detKer n) : ∃ χ ∈ V, χ ≠ 0 ∧ SpectralAccumulation.TypeB K' W' χ := by
  obtain ⟨χ, hχ, rfl⟩ := hψ
  refine ⟨χ, hχ, fun h => h0 (by rw [h]; exact map_zero _), ?_⟩
  have e : χ = mulChi n (Model.absC E (-z)) (mulChi n (Model.absC E z) χ) := (ParabolicProjection.mulChi_absC_neg n z χ).symm
  rw [e]
  exact t_typeB_mulChi hT hK' (-z)

theorem memInd2_of_span {r s : ℕ} {V₁ : Submodule ℂ (Sm E r)} {V₂ : Submodule ℂ (Sm E s)} {φ : Sm E (r + s)}
    (h : φ ∈ Submodule.span ℂ {φ | MemInd2 V₁ V₂ φ}) : MemInd2 V₁ V₂ φ := by
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    refine ⟨fun x g => rfl, fun k g => ?_⟩
    have e : (fun m => (0 : Sm E (r + s)).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) *
      finGL E (r + s) g))) = 0 := rfl
    rw [e]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    refine ⟨fun u g => ?_, fun k g => ?_⟩
    · show x.1 (unip u * g) + y.1 (unip u * g) = x.1 g + y.1 g
      rw [hx.1 u g, hy.1 u g]
    · have e : (fun m => (x + y).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) =
          (fun m => x.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) +
          (fun m => y.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) := rfl
      rw [e]
      exact Submodule.add_mem _ (hx.2 k g) (hy.2 k g)
  | smul c x _ hx =>
    refine ⟨fun u g => ?_, fun k g => ?_⟩
    · show c * x.1 (unip u * g) = c * x.1 g
      rw [hx.1 u g]
    · have e : (fun m => (c • x).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) =
          c • (fun m => x.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) := rfl
      rw [e]
      exact Submodule.smul_mem _ c (hx.2 k g)

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.KTypeSlices

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockTwistCharacters

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


omit [IsCMField E] in
theorem pE_shift (a r : ℕ) (c w : ℂ) :
    pE E a r (c + w * r * (Module.finrank ℚ E : ℂ)) = pE E a r c + w.re * r := by
  have hd : (Module.finrank ℚ E : ℝ) ≠ 0 := by
    have : 0 < Module.finrank ℚ E := Module.finrank_pos
    exact_mod_cast this.ne'
  unfold pE
  have e : (c + w * r * (Module.finrank ℚ E : ℂ)).re = c.re + w.re * r * (Module.finrank ℚ E : ℝ) := by
    simp [Complex.add_re, Complex.mul_re]
  rw [e]
  field_simp
  ring

theorem nonPos_tw {a : ℕ} (V : Submodule ℂ (Sm E a)) (w : ℂ) (haut : ∀ φ ∈ V, IsAutForm φ)
    (hV : ∀ φ ∈ V, ∀ r, 0 < r → r < a → ∀ c ∈ Exp r φ.1, pE E a r c + w.re * r ≤ 0) :
    SpectralAccumulation.NonPos (tw V w) := by
  intro φ hφ r hr hra c hc
  obtain ⟨ψ, hψ, rfl⟩ := Submodule.mem_map.1 hφ
  have h0 := expTw_holds E a ψ w (haut ψ hψ) r hr hra c hc
  have h1 := hV ψ hψ r hr hra _ h0
  have e : c = (c - w * r * (Module.finrank ℚ E : ℂ)) + w * r * (Module.finrank ℚ E : ℂ) := by ring
  rw [e, pE_shift]
  exact h1

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockTwistCharacters

end
end

section

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAssembly

theorem factor {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (U : Submodule ℂ M)
    (T : M →ₗ[ℂ] N) (T' : M →ₗ[ℂ] N) (h : ∀ ψ ∈ U, T ψ = 0 → T' ψ = 0) :
    ∃ P : N →ₗ[ℂ] N, ∀ ψ ∈ U, P (T ψ) = T' ψ := by
  let f := T ∘ₗ U.subtype
  let g := T' ∘ₗ U.subtype
  have hle : LinearMap.ker f ≤ LinearMap.ker g := fun x hx => h x.1 x.2 hx
  let g₀ := (LinearMap.ker f).liftQ g hle
  let h₀ : LinearMap.range f →ₗ[ℂ] N := g₀ ∘ₗ f.quotKerEquivRange.symm.toLinearMap
  obtain ⟨P, hP⟩ := LinearMap.exists_extend h₀
  refine ⟨P, fun ψ hψ => ?_⟩
  have e1 : P (T ψ) = h₀ ⟨f ⟨ψ, hψ⟩, LinearMap.mem_range_self f _⟩ :=
    LinearMap.congr_fun hP (⟨f ⟨ψ, hψ⟩, LinearMap.mem_range_self f _⟩ : LinearMap.range f)
  rw [e1]
  change g₀ (f.quotKerEquivRange.symm ⟨f ⟨ψ, hψ⟩, _⟩) = _
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ}

theorem eq_of_levi {F₁ F₂ : Sm E (r + s)}
    (h₁ : ∀ (x : BlockIx (r + s) r → Ad E) g, F₁.1 (unip x * g) = F₁.1 g)
    (h₂ : ∀ (x : BlockIx (r + s) r → Ad E) g, F₂.1 (unip x * g) = F₂.1 g)
    (h : ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m : GA E r × GA E s),
      F₁.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) =
        F₂.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) : F₁ = F₂ := by
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨u, m, k, g, rfl⟩ := ParabolicProjection.exists_decomp x
  rw [mul_assoc, h₁, h₂]
  exact h k g m

theorem eq_zero_of_levi {F : Sm E (r + s)} (hF : ∀ (x : BlockIx (r + s) r → Ad E) g, F.1 (unip x * g) = F.1 g)
    (h : ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m : GA E r × GA E s),
      F.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) = 0) : F = 0 :=
  eq_of_levi hF (fun _ _ => rfl) h

theorem isStable_map {a : ℕ} {L : Submodule ℂ (Sm E a)} (hL : _root_.GlobalTheory.CuspRep.IsStable L) {z : Module.End ℂ (Sm E a)}
    (hz : ∀ o : Op E a, Commute z (act o)) : _root_.GlobalTheory.CuspRep.IsStable (L.map z) := by
  rintro o _ ⟨φ, hφ, rfl⟩
  exact ⟨act o φ, hL o φ hφ, by
    change z (act o φ) = act o (z φ)
    rw [← Module.End.mul_apply, (hz o).eq, Module.End.mul_apply]⟩

theorem finGen_map {a : ℕ} {L : Submodule ℂ (Sm E a)} {z : Module.End ℂ (Sm E a)}
    (hz : ∀ o : Op E a, Commute z (act o)) (S₁ : Finset (Sm E a)) (hS₁ : (↑S₁ : Set (Sm E a)) ⊆ L)
    (hgen : ∀ W : Submodule ℂ (Sm E a), _root_.GlobalTheory.CuspRep.IsStable W → (↑S₁ : Set (Sm E a)) ⊆ W → L ≤ W) : FinGen (L.map z) := by
  classical
  refine ⟨S₁.image z, fun x hx => ?_, fun W hW hSW => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    exact Submodule.mem_map_of_mem (hS₁ hy)
  · have hst : _root_.GlobalTheory.CuspRep.IsStable (W.comap z) := fun o φ hφ => by
      change z (act o φ) ∈ W
      rw [← Module.End.mul_apply, (hz o).eq, Module.End.mul_apply]
      exact hW o _ hφ
    have hle := hgen (W.comap z) hst fun y hy => hSW (Finset.mem_coe.2 (Finset.mem_image_of_mem z hy))
    rintro _ ⟨φ, hφ, rfl⟩
    exact hle hφ

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAssembly

end
end
