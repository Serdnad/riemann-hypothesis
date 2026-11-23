module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle686
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle758
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle685
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle724
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle403
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle690
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle082
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle735
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle659
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle759
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle658
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle655
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle706
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle559
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle761
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle587
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle564
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle705
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle736
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle563
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle760
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrisToODToOCr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle631
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

noncomputable section

namespace GlobalTheory.BKGal.HatVal

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K] {G : Type} [Group G] [TopologicalSpace G]

theorem TWincl_smul' {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R'] (f : R →ₐ[O] R')
    (T : LocLat G ℚ_[l] K O) (r : R) (z : TW R T) : TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul s x =>
    simp only [TWincl, smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply,
      smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

theorem TWincl_TWincl {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] [Algebra O R] [Algebra O R']
    [Algebra O R''] (f : R →ₐ[O] R') (g : R' →ₐ[O] R'') (T : LocLat G ℚ_[l] K O) (z : TW R T) :
    TWincl g T (TWincl f T z) = TWincl (g.comp f) T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.BKGal.HatVal


open GlobalTheory.BKGal.HatVal in
theorem GlobalTheory.BKGal.value_hat_mem_filZero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ (σ : D.MMl) (y : Vec K a ι) (hy : y ∈ ME D.toPhiMod), σ.1 - y ∈ D.Man → ∀ b₂, IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) b₂ → ∀ C : GlobalTheory.MemLoc.Core l, R.jB (toBcris t ϖ D.toPhiMod σ) - b₂ ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ hl2 ι _ _ η H D T R σ y hy hσy b₂ hb₂ C
  haveI : FiniteDimensional ℚ_[l] K := (inferInstance : TameDescentExponentData K l e a).finite
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K

  obtain ⟨ζ, ε, h0, -, hz1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : ε.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps ε := ⟨he, fun hh => hz1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  have hδl : ((frobeniusEquiv (Per.Fl l) l).symm ε) ^ l = ε := by
    rw [← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
  have hEps : IsEps ε := ⟨he, _, hδl, hE.2⟩
  set δ := (frobeniusEquiv (Per.Fl l) l).symm ε with hδ
  have hθν : (Per.θ l (muOf δ) : ℂ_[l]) ≠ 0 := by
    change (Per.θ l (Per.tm δ - 1) : ℂ_[l]) ≠ 0
    rw [map_sub, map_one, WittVector.fontaineTheta_teichmuller]
    intro h
    apply hE.2
    rw [← sub_eq_zero]
    exact Subtype.ext h

  have hνD : IsUnit (toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ η))) := by
    have h1 : IsUnit (GlobalTheory.MemLoc.aDp l (muOf δ ^ η)) := by
      rw [map_pow]
      exact ((GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (by
        rw [(GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]; exact hθν)).pow η
    have := h1.map (Algebra.TensorProduct.includeRight : Per.BdRp l →ₐ[ℤ_[l]] OD l O)
    rw [Algebra.TensorProduct.includeRight_apply] at this
    exact this

  have hED : IsUnit (dRO l O (toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e)))) := by
    have hxi : GlobalTheory.MemLoc.xi ε ∈ Ideal.span {ϖ.ev a (eis l a e)} := by
      rw [ϖ.span_ev_eis a, GlobalTheory.MemLoc.ker_theta_eq_span_xi hE]
      exact Ideal.subset_span rfl
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hxi
    have hu := GlobalTheory.MemLoc.TiedUnif.isUnit_xi hE
    rw [← hw, map_mul, map_mul] at hu
    have h1 := isUnit_of_mul_isUnit_right hu
    have := h1.map (Algebra.TensorProduct.includeRight : Per.BdR l →ₐ[ℤ_[l]] OdR l O)
    rw [Algebra.TensorProduct.includeRight_apply] at this
    exact this

  choose c hc z hz using GlobalTheory.T.coord_E_pow_basis_alt l a e O K t ϖ ι η H D T R ε δ hEps hδl

  obtain ⟨s, hs, hσv⟩ := GlobalTheory.T.eisensteinPow_smul_value_eq_sum_basis l a e O K t ϖ ι η H D T R σ c hc

  have hYA : ∀ j τ, E K l e ^ η * y τ j ∈ A O K := by
    intro j τ
    have h1 : y τ j ∈ invE l e (A O K) := mem_tot.1 hy τ j
    obtain ⟨n, hn⟩ := h1
    have h2 : (σ.1 - y) τ j ∈ Rpi O K l e := mem_tot.1 hσy τ j
    have h3 : E K l e ^ η * y τ j ∈ Rpi O K l e := by
      have : E K l e ^ η * y τ j = (s j τ : K⟦X⟧) - E K l e ^ η * (σ.1 - y) τ j := by
        rw [hs, Pi.sub_apply, Pi.sub_apply]; ring
      rw [this]
      exact sub_mem (invL_S_le_Rpi l e (s j τ).2) (mul_mem (pow_mem (E_mem l e _) η) h2)
    refine mem_A_of_E_pow_mul_mem l e n h3 ?_
    have hn' : E K l e ^ n * y τ j ∈ A O K := by rwa [coe_EIn] at hn
    rw [mul_left_comm]
    exact mul_mem (pow_mem (E_mem l e _) η) hn'
  set Y : ι → ZMod a → A O K := fun j τ => ⟨_, hYA j τ⟩ with hYdef

  have hbv := GlobalTheory.T.breuilKisin_value_mul_eisensteinPow_eq_sum l a e O K t ϖ ι η H D T R y hy b₂ hb₂ c hc Y (fun _ _ => rfl)
  have hAS : A O K ≤ invL l (S O K e) := le_trans (A_le_S l e) (le_away _ _)
  set ρ : ι → ZMod a → invL l (S O K e) := fun j τ => s j τ - ⟨_, hAS (hYA j τ)⟩ with hρdef
  have hρ : ∀ j τ, ∃ r ∈ Rpi O K l e, (ρ j τ : K⟦X⟧) = E K l e ^ η * r := fun j τ =>
    ⟨(σ.1 - y) τ j, mem_tot.1 hσy τ j, by
      rw [hρdef]
      simp only [Subalgebra.coe_sub, hs, Pi.sub_apply]
      ring⟩
  have hiBY : ∀ j, ϖ.iB t K (fun τ => ⟨_, hAS (hYA j τ)⟩) = toB l O (ϖ.iTot t K (Y j)) := fun j =>
    (PiSys.iB_of_mem t K ϖ (fun τ => ⟨_, A_le_S l e (hYA j τ)⟩)).trans
      (congrArg (toOB l O) (PiSys.iC_of_mem t K ϖ (Y j)))
  have key : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e)) ^ (H + η) •
      (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) = ∑ j, ϖ.iB t K (ρ j) • R.jB (fun i => toB l O (c j i)) := by
    rw [smul_sub, hσv, hbv, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sub_smul, ← hiBY j, ← map_sub]
    rfl

  apply GlobalTheory.T.mem_span_filtrationZero_of_integral_tensorLattice l O K T C
  set EAD := toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e)) with hEAD
  obtain ⟨v, hv⟩ := hνD.exists_left_inv
  have hcomp : (iotaO O C).comp (toB l O) = (dRO l O).comp (toOD l O) := AlgHom.ext (iotaO_toB C)
  have hPsiL : ∀ j, TWincl (iotaO O C) T (R.jB fun i => toB l O (c j i)) =
      TWincl (dRO l O) T ((v * EAD ^ H) • TWincl (toOD l O) T (z j)) := by
    intro j
    have h1 := congrArg (TWincl (iotaO O C) T) (hz j)
    rw [TWincl_smul', iotaO_toB, TWincl_TWincl, hcomp, ← TWincl_TWincl, TWincl_smul', map_pow] at h1
    calc TWincl (iotaO O C) T (R.jB fun i => toB l O (c j i))
        = dRO l O (v * toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ η))) •
            TWincl (iotaO O C) T (R.jB fun i => toB l O (c j i)) := by rw [hv, map_one, one_smul]
      _ = dRO l O v • TWincl (dRO l O) T (EAD ^ H • TWincl (toOD l O) T (z j)) := by
          rw [map_mul, mul_smul, h1]
      _ = _ := by rw [TWincl_smul', TWincl_smul', map_mul, mul_smul]
  choose z' hz' using fun j => GlobalTheory.T.image_deRham_eq_eisenstein_pow_mul_of_components l a e O K t ϖ C η (ρ j) (hρ j)
  have hE' : dRO l O EAD ^ (H + η) =
      iotaO O C ((toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e))) ^ (H + η)) := by
    rw [map_pow, iotaO_toB]
  have hmain : dRO l O EAD ^ (H + η) • TWincl (iotaO O C) T (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) =
      dRO l O EAD ^ (H + η) • TWincl (dRO l O) T (∑ j, (z' j * v) • TWincl (toOD l O) T (z j)) := by

    conv_lhs => rw [hE', ← TWincl_smul', key, map_sum]

    conv_rhs => rw [← map_pow, ← TWincl_smul', Finset.smul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TWincl_smul', hz' j, hPsiL j, ← TWincl_smul', smul_smul, smul_smul]
    congr 2
    ring
  exact ⟨_, ((hED.pow (H + η)).smul_left_cancel.1 hmain).symm⟩
end
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrisComparison

theorem toB_tmul' {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (o : O) (w : Ainf l) :
    toB l O (o ⊗ₜ w) = o ⊗ₜ acrisToBcris l (ainfToAcris l w) := rfl

theorem toB_frobOA {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (x : OA l O) :
    toB l O (frobOA l O x) = frobOB l O (toB l O x) := by
  simp only [toB, AlgHom.comp_apply, frobOB_toOB, frobOCr_toOCr]

theorem toB_galOA {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (g : GQ l) (x : OA l O) :
    toB l O (galOA O g x) = galOB O g (toB l O x) := by
  simp only [toB, AlgHom.comp_apply, galOB_toOB, galOCr_toOCr]

theorem map_smul_tw {O R N : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup N] [Module O N]
    (σ : R →ₐ[O] R) (h : N →ₗ[O] N) (r : R) (z : R ⊗[O] N) :
    TensorProduct.map σ.toLinearMap h (r • z) = σ r • TensorProduct.map σ.toLinearMap h z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul x y => simp only [TensorProduct.smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply, smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

theorem inclL_smul' {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι)
    (r : OA l O) (c : ι → OA l O) : inclL t ϖ P (r • c) = inclO l O r • inclL t ϖ P c := by
  rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
  exact congrArg _ (funext fun i => map_mul _ _ _)

theorem exists_Y : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (α : ℕ), (∀ m ∈ P.L, E K l e ^ α • m ∈ P.M) → ∃ Y : Matrix ι ι (OA l O), (∀ i j, ∃ f : ZMod a → A O K, (∀ τ, (f τ : K⟦X⟧) = E K l e ^ α * P.mx τ i j) ∧ Y i j = ϖ.iTot t K f) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P α hα
  have key : ∀ i j, ∃ f : ZMod a → A O K, (∀ τ, (f τ : K⟦X⟧) = E K l e ^ α * P.mx τ i j) := by
    intro i j
    have hv : (fun τ k => P.mx τ k j : Vec K a ι) ∈ P.L := mem_tot.2 fun τ => P.mem_extc.2
      ⟨Pi.single j 1, fun k => by
        by_cases hk : k = j
        · subst hk; simp only [Pi.single_eq_same]; exact one_mem _
        · rw [Pi.single_eq_of_ne hk]; exact zero_mem _, by
        ext1 k; simp [Matrix.mulVec_single]⟩
    have h := hα _ hv
    exact ⟨fun τ => ⟨E K l e ^ α * P.mx τ i j, mem_tot.1 h τ i⟩, fun τ => rfl⟩
  choose f hf using key
  exact ⟨fun i j => ϖ.iTot t K (f i j), fun i j => ⟨f i j, hf i j, rfl⟩⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T), (∃ jB, IsCrisCmp I jB) ∧ ∀ (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), IsCrisCmp I jB → (∀ (m m' : P.MMl), m'.1 = P.phi m.1 → jB (toBcris t ϖ P m') = TWmap (frobOB l O) T (jB (toBcris t ϖ P m))) ∧ (∀ w b b', IsCrisVal t ϖ P jB w b → IsCrisVal t ϖ P jB w b' → b = b') ∧ (∀ w b, IsCrisVal t ϖ P jB w b → IsCrisVal t ϖ P jB (phiW t ϖ P w) (TWmap (frobOB l O) T b)) ∧ (∀ x : ↥T.L.T, IsCrisVal t ϖ P jB (I.ofT x) ((1 : OB l O) ⊗ₜ[O] x)) ∧ (∀ g : Gl l, (∀ v ∈ LA t ϖ P, I.act (sQ l g) g v ∈ LA t ϖ P) → ∀ w b, IsCrisVal t ϖ P jB w b → IsCrisVal t ϖ P jB (I.act (sQ l g) g w) (actB (sQ l) T g b)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I
  obtain ⟨ε, hε⟩ := (GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).1
  obtain ⟨δ, hδ, -⟩ := hε.2
  obtain ⟨-, -, -, hμB, -, -, -⟩ := (GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).2 ε δ hε hδ
  obtain ⟨α, β, hα, hβ⟩ := P.exists_exponents
  obtain ⟨-, -, hK3, hK4⟩ := GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι P T I α β hα hβ ε δ hε hδ
  have hunit : ∀ n : ℕ, IsUnit (toB l O (1 ⊗ₜ (muOf ε ^ n))) := fun n => by
    rw [toB_tmul', map_pow, map_pow]
    exact (hμB.pow n).map (Algebra.TensorProduct.includeRight : Per.Bcris l →ₐ[ℤ_[l]] OB l O)
  obtain ⟨Y, hY⟩ := exists_Y l a e O K t ϖ ι P α hα
  have hEu := GlobalTheory.T.isUnit_toB_frobOA_eis l a e O ϖ
  have hYphi := GlobalTheory.T.eis_pow_smul_phiW_inclL_eq_inclL_mulVec l a e O K t ϖ ι P α Y hY
  have hSl := GlobalTheory.T.toBcris_phi_alt l a e O K t ϖ ι P α Y hY
  refine ⟨GlobalTheory.T.exists_bcris_comparison_kisinLattice l a e O K t ϖ ι P T I, fun jB hjB => ?_⟩
  have hμL : ∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O (1 ⊗ₜ (muOf ε ^ α)) • v) = TWincl (inclO l O) T z :=
    hK4
  have keyφ := GlobalTheory.T.cmp_semilinear_pair_alt l a e O K t ϖ ι P T I jB hjB _ (hunit α) hμL (frobOA l O) (frobOW l O) (frobOB l O)
    LinearMap.id (phiW t ϖ P) (frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ α) (Y.map (frobOA l O))
    (fun x => (frobOW_inclO x).symm) toB_frobOA (fun v => I.j_φ v) (phiW_smul t ϖ P)
    (fun c => by rw [map_pow]; exact hYphi c)
  refine ⟨fun m m' hmm => ?_, fun w b b' hb hb' => ?_, fun w b hb => ?_, fun x => ?_, fun g hg w b hb => ?_⟩
  · refine (hEu.pow α).smul_left_cancel.1 ?_
    rw [← LinearEquiv.map_smul, hSl m m' hmm, keyφ, map_pow]
    rfl
  · obtain ⟨m, c, hm, hw, hb⟩ := hb
    obtain ⟨m', c', hm', hw', hb'⟩ := hb'
    have h1 : m' • c = m • c' := inclL_injective t ϖ P (by
      rw [inclL_smul', inclL_smul', ← hw, ← hw', smul_smul, smul_smul, ← map_mul, ← map_mul, mul_comm])
    have h2 : ∀ (r : OA l O) (d : ι → OA l O), toB l O r • (fun i => toB l O (d i)) = fun i => toB l O ((r • d) i) :=
      fun r d => funext fun i => by simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    refine ((hm.mul hm').smul_left_cancel).1 ?_
    rw [mul_comm, mul_smul, hb, mul_comm, mul_smul, hb', ← LinearEquiv.map_smul, ← LinearEquiv.map_smul, h2, h2, h1]
  · obtain ⟨m, c, hm, hw, hb⟩ := hb
    refine ⟨frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ α * frobOA l O m, Y.map (frobOA l O) *ᵥ fun i => frobOA l O (c i), ?_, ?_, ?_⟩
    · rw [map_mul, map_pow, toB_frobOA m]
      exact (hEu.pow α).mul (hm.map _)
    · rw [map_mul, map_pow, mul_smul, ← frobOW_inclO m, ← phiW_smul, hw]
      exact hYphi c
    · have h3 := keyφ (fun i => toB l O (c i))
      rw [map_mul, mul_smul, toB_frobOA m]
      change _ • frobOB l O (toB l O m) • TensorProduct.map (frobOB l O).toLinearMap LinearMap.id b = _
      rw [← map_smul_tw, hb, ← h3]
      congr 1
      ext i
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul, toB_frobOA]
  · obtain ⟨c, hc⟩ := hK3 x
    refine ⟨1 ⊗ₜ (muOf ε ^ β), c, hunit β, hc.symm, ?_⟩
    have h4 := hjB c ((1 ⊗ₜ (muOf ε ^ β)) ⊗ₜ x) (by
      rw [hc, LinearEquiv.map_smul, I.j_ofT, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rfl)
    rw [h4, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl
  · obtain ⟨m, c, hm, hw, hb⟩ := hb
    obtain ⟨Γ, hΓ⟩ := (I.exists_isLMat_iff (sQ l g) g).2 hg
    have key := GlobalTheory.T.cmp_semilinear_pair_alt l a e O K t ϖ ι P T I jB hjB _ (hunit α) hμL (galOA O (sQ l g)) (galOW O (sQ l g))
      (galOB O (sQ l g)) (T.actT g) (I.act (sQ l g) g) 1 Γ (fun x => (galOW_inclO _ x).symm) (toB_galOA _)
      (fun v => I.j_act _ _ v) (I.act_smul _ _) (fun c => by rw [map_one, one_smul]; exact hΓ c)
    refine ⟨galOA O (sQ l g) m, Γ *ᵥ fun i => galOA O (sQ l g) (c i), ?_, ?_, ?_⟩
    · rw [toB_galOA]
      exact hm.map _
    · rw [← galOW_inclO, ← I.act_smul, hw]
      exact hΓ c
    · have h3 := key (fun i => toB l O (c i))
      rw [map_one, one_smul] at h3
      rw [toB_galOA]
      change _ • TensorProduct.map (galOB O (sQ l g)).toLinearMap (T.actT g) b = _
      rw [← map_smul_tw, hb, ← h3]
      congr 1
      ext i
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul, toB_galOA]

end GlobalTheory.CrisComparison
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem GlobalTheory.BSP.eq_of_hasSum_toDisc_of_J_adic : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ι : Type),
    TopBasis bk.ev bk.J ι → ∀ (w : ι → Ainf l) (z t : Ainf l), HasSum (fun i => bk.iA (w i)) (bk.iA t) →
    (∀ n : ℕ, ∃ F : Finset ι, ∀ G : Finset ι, F ⊆ G → z - ∑ i ∈ G, w i ∈ (bk.J ^ n).map bk.ev) → z = t := by
  intro l hl K bk ι tb w z t hsum hJ
  classical
  have hρ : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
    have hl1 : (1 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast hl.out.one_lt
    have he : (0 : ℝ) < 1 / (bk.Ep.natDegree : ℝ) := one_div_pos.2 (Nat.cast_pos.2 bk.deg_pos)
    exact ⟨NNReal.rpow_pos (zero_lt_one.trans hl1), NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (neg_neg_of_pos he)⟩
  have hinj : Function.Injective (toDisc l (bk.ev X) bk.ρ₀) :=
    (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk (Ainf l) bk.ev ι tb).1
  have hiA : bk.iA = toDisc l (bk.ev X) bk.ρ₀ := rfl
  apply hinj
  rw [← hiA]
  have key : ∀ ε : ℝ, 0 < ε → ‖bk.iA z - bk.iA t‖ ≤ 2 * ε := by
    intro ε hε
    obtain ⟨n, hn⟩ := GlobalTheory.BSP.norm_toDisc_J_pow_small l K bk (Ainf l) bk.ev bk.ρ₀ hρ.1 hρ.2 ε hε
    obtain ⟨F, hF⟩ := hJ n
    have hev : ∀ᶠ G in Filter.atTop, ‖∑ i ∈ G, bk.iA (w i) - bk.iA t‖ < ε := by
      have := (hsum : Filter.Tendsto _ _ _)
      have h2 := Metric.tendsto_nhds.1 this ε hε
      filter_upwards [h2] with G hG
      simpa [dist_eq_norm] using hG
    obtain ⟨G₀, hG₀⟩ := Filter.eventually_atTop.1 hev
    set G := F ∪ G₀
    have h1 : ‖bk.iA (z - ∑ i ∈ G, w i)‖ ≤ ε := hn _ (hF G Finset.subset_union_left)
    have h2 : ‖∑ i ∈ G, bk.iA (w i) - bk.iA t‖ < ε := hG₀ G Finset.subset_union_right
    have hsplit : bk.iA z - bk.iA t = bk.iA (z - ∑ i ∈ G, w i) + (∑ i ∈ G, bk.iA (w i) - bk.iA t) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum]; abel
    rw [hsplit]
    calc _ ≤ ‖bk.iA (z - ∑ i ∈ G, w i)‖ + ‖∑ i ∈ G, bk.iA (w i) - bk.iA t‖ := norm_add_le _ _
      _ ≤ 2 * ε := by linarith
  have h0 : ‖bk.iA z - bk.iA t‖ = 0 := by
    refine le_antisymm ?_ (norm_nonneg _)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := key (ε / 2) (by positivity)
    linarith
  exact sub_eq_zero.1 (norm_eq_zero.1 h0)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_root_radii (l : ℕ) (hl : 2 ≤ l) (ρ₀ : ℝ≥0) (h0 : 0 < ρ₀) (h1 : ρ₀ < 1) :
    ∃ r : ℕ → ℝ≥0, r 0 = ρ₀ ∧ (∀ n, r (n + 1) ^ l = r n) ∧ (∀ n, ρ₀ ≤ r n) ∧ (∀ n, r n < 1) ∧
      ∀ ρ₁ : ℝ≥0, ρ₁ < 1 → ∃ n, ρ₁ ≤ r n := by
  have hl0 : l ≠ 0 := by omega
  let r : ℕ → ℝ≥0 := fun n => ρ₀ ^ (((l ^ n : ℕ) : ℝ)⁻¹)
  have hp : ∀ n, r n ^ (l ^ n) = ρ₀ := fun n => NNReal.rpow_inv_natCast_pow _ (pow_ne_zero _ hl0)
  have hlt : ∀ n, r n < 1 := fun n => by
    by_contra h
    have := one_le_pow₀ (not_lt.1 h) (n := l ^ n)
    rw [hp] at this
    exact absurd h1 (not_lt.2 this)
  refine ⟨r, by simpa using hp 0, fun n => ?_, fun n => ?_, hlt, fun ρ₁ h => ?_⟩
  · refine (pow_left_inj₀ zero_le zero_le (pow_ne_zero n hl0)).1 ?_
    rw [← pow_mul, ← pow_succ', hp, hp]
  · rw [← hp n]
    exact pow_le_of_le_one zero_le (hlt n).le (pow_ne_zero _ hl0)
  · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one h0 h
    refine ⟨n, le_of_lt (lt_of_pow_lt_pow_left₀ (l ^ n) zero_le ?_)⟩
    rw [hp]
    exact (pow_le_pow_of_le_one zero_le h.le (Nat.lt_pow_self (by omega)).le).trans_lt hn

theorem norm_l_pow_mul_disc (l : ℕ) [Fact l.Prime] {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (k : ℕ)
    (y : Disc l u ρ) : ‖((l : ℕ) : Disc l u ρ) ^ k * y‖ = ‖y‖ / (l : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A u ρ).2.1, ih, div_div, pow_succ]

theorem exists_bounded_of_phi_equation : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ (φ : A →+* A), φ (s X) = s X ^ l → ∀ (Φ : Disc l (s X) bk.ρ₀ →+* Disc l (s X) bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) φ Φ → ∀ (κ : Type) (c : κ → κ → A), (∀ i (n : ℕ), {j | c i j ∉ (bk.J ^ n).map s}.Finite) → ∀ (h : ℕ) (V : κ → Disc l (s X) bk.ρ₀), Filter.Tendsto V Filter.cofinite (nhds 0) → (∀ j, HasSum (fun i => Φ (V i) * toDisc l (s X) bk.ρ₀ (c i j)) (toDisc l (s X) bk.ρ₀ (s bk.E) ^ h * V j)) → ∃ (k : ℕ) (v : κ → A), (∀ j, toDisc l (s X) bk.ρ₀ (v j) = (l : Disc l (s X) bk.ρ₀) ^ k * V j) ∧ ∀ n : ℕ, {j | v j ∉ (bk.J ^ n).map s}.Finite := by
  intro l hl K bk A _ s ι tb φ hφ Φ hΦ κ c hc h V hV hs
  obtain ⟨-, -, ⟨h0, h1, -⟩, -⟩ := GlobalTheory.T.breuilKisin_flat_radius_ideal_facts l K bk
  have hl2 := hl.out.two_le
  obtain ⟨r, r0, rs, rle, rlt, rlim⟩ := exists_root_radii l hl2 bk.ρ₀ h0 h1
  have rpos : ∀ n, 0 < r n := fun n => h0.trans_le (rle n)
  have hR : ∀ n, ∃ R : Disc l (s X) (r n) →+* Disc l (s X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R := fun n =>
    GlobalTheory.T.exists_closedDiscExtension_of_pow_dvd l A A (RingHom.id A) (s X) (s X) (r n) bk.ρ₀ 1 h0 (by simp) (by simpa using rle n)
  choose R hR using hR
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ j, ‖V j‖ ≤ C := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto_cofinite hV)
    exact ⟨max C 0, le_max_right _ _, fun j => (hC _ ⟨j, rfl⟩).trans (le_max_left _ _)⟩
  set m := bk.Ep.natDegree * h with hm
  have h0' : (0 : ℝ) < bk.ρ₀ := h0
  have key : ∀ n, ∃ U : κ → Disc l (s X) (r n), Filter.Tendsto U Filter.cofinite (nhds 0) ∧
      (∀ j, R n (U j) = V j) ∧ ∀ j, ‖U j‖ ≤ C * ((r n : ℝ) / bk.ρ₀) ^ m := by
    intro n
    induction n with
    | zero =>
      have gen : ∀ (ρ : ℝ≥0) (R₀ : Disc l (s X) ρ →+* Disc l (s X) bk.ρ₀), ρ = bk.ρ₀ →
          IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R₀ → ∃ U : κ → Disc l (s X) ρ, Filter.Tendsto U Filter.cofinite (nhds 0) ∧
          (∀ j, R₀ (U j) = V j) ∧ ∀ j, ‖U j‖ ≤ C * ((ρ : ℝ) / bk.ρ₀) ^ m := by
        rintro ρ R₀ rfl hR₀
        refine ⟨V, hV, fun j => ?_, fun j => ?_⟩
        · rw [hR₀.unique (isDiscMap_id l (s X) bk.ρ₀)]; rfl
        · rw [div_self h0'.ne', one_pow, mul_one]; exact hC j
      exact gen _ _ r0 (hR 0)
    | succ n ih =>
      obtain ⟨U, hU, hRU, hn⟩ := ih
      obtain ⟨U', hU', hRU', hn'⟩ := GlobalTheory.T.exists_phiContraction_disc_step l K bk A s ι tb φ hφ Φ hΦ κ c hc h V hs (r n) (r (n + 1))
        (rle n) (rlt n) (rs n) (R n) (R (n + 1)) (hR n) (hR (n + 1)) U _ (by positivity) hU hRU hn
      refine ⟨U', hU', hRU', fun j => ?_⟩
      have hp : (0 : ℝ) < r (n + 1) := rpos _
      have hle : (r n : ℝ) ≤ r (n + 1) * r (n + 1) := by
        have : r n ≤ r (n + 1) ^ 2 := by
          rw [← rs n]; exact pow_le_pow_of_le_one zero_le (rlt _).le hl2
        rw [← sq]; exact_mod_cast this
      refine le_of_mul_le_mul_left ((hn' j).trans ?_) (pow_pos hp m)
      rw [mul_left_comm, ← mul_pow, ← mul_div_assoc]
      gcongr
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (C * (1 / (bk.ρ₀ : ℝ)) ^ m)
    (show (1 : ℝ) < l by exact_mod_cast hl.out.one_lt)
  have hlk : (0 : ℝ) < (l : ℝ) ^ k := pow_pos (Nat.cast_pos.2 hl.out.pos) k
  have hv : ∀ j, ∃ a, toDisc l (s X) bk.ρ₀ a = (l : Disc l (s X) bk.ρ₀) ^ k * V j := fun j =>
    GlobalTheory.T.exists_base_eq_of_closedDisc_extends_norm_le_one l K bk A s ι tb bk.ρ₀ h0 h1 _ fun ρ₁ hρ₁ => by
      obtain ⟨n, hn⟩ := rlim ρ₁ hρ₁
      obtain ⟨U, -, hRU, hU⟩ := key n
      refine ⟨r n, R n, (l : Disc l (s X) (r n)) ^ k * U j, hn, rle n, rlt n, hR n, ?_, ?_⟩
      · rw [map_mul, map_pow, map_natCast, hRU]
      · rw [norm_l_pow_mul_disc, div_le_one hlk]
        refine (hU j).trans (le_trans ?_ hk.le)
        have : (r n : ℝ) ≤ 1 := (rlt n).le
        gcongr
  choose v hv using hv
  refine ⟨k, v, hv, fun n => ?_⟩
  obtain ⟨ε, hε, hJ⟩ := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk A s ι tb bk.ρ₀ h0 h1).2.1 n
  have ht : Filter.Tendsto (fun j => (l : Disc l (s X) bk.ρ₀) ^ k * V j) Filter.cofinite (nhds 0) := by
    simpa using hV.const_mul ((l : Disc l (s X) bk.ρ₀) ^ k)
  have he := Filter.eventually_cofinite.1 (ht.eventually (Metric.closedBall_mem_nhds 0 hε))
  refine he.subset fun j hj hj' => hj (hJ _ ?_)
  rw [hv]
  simpa using hj'

end GlobalTheory.BSP
end
