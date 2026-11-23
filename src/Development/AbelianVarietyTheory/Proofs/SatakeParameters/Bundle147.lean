module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle051
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle139
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle134
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelPurity
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle004
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle141
public import Formalism.LocalToGlobal.AlgebraicTheory.Bundle001
public import Formalism.LocalToGlobal.Columns.Bundle023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle142
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle140
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
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.KernelLattices.Bundle001

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.galois_logTeichmullerRatio_eq_add_kummer : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (Co : Core l), Co.ζ = P.ζQ → ∀ ϖ : Per.Fl l,
  (∀ m : ℕ, (rootT ϖ m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (lRoot l m)) → ϖ.untilt = ((l : ℕ) : Per.OC l) →
  ∀ u : Per.BdRp l, IsLogP (beta ϖ) u → ∀ g : GQ l,
    Per.σDp g u = u + Co.j (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l (kummer P g)) * Co.t) := by
  first | exact @GlobalTheory.Pst.StLat.gal_log | exact GlobalTheory.Pst.StLat.gal_log | (intros; apply GlobalTheory.Pst.StLat.gal_log <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.log_period_congruence_bdr : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), Per.kerP l = Ideal.span {beta ϖ} →
  (∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n}) → ∀ u : Per.BdRp l, IsLogP (beta ϖ) u →
  ∀ m : ℕ, 1 ≤ m → ∃ s ∈ Sg ϖ, ∃ e : Per.BdRp l, (e = 1 ∨ e = -1) ∧
    betaD ϖ ^ (2 * l ^ m) ∣ ((l : ℕ) : Per.BdRp l) * (((l : ℕ) : Per.BdRp l) ^ (m - 1) * u - s) - e * betaD ϖ ^ (l ^ m) := by
  first | exact @GlobalTheory.Pst.StLat.log_trunc_pow | exact GlobalTheory.Pst.StLat.log_trunc_pow | (intros; apply GlobalTheory.Pst.StLat.log_trunc_pow <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHecke.Cosets

open IsLocalRing

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] {p : O}

theorem map_res_eq_zero_iff (hp : Irreducible p) {m n : ℕ} (X : Matrix (Fin m) (Fin n) O) :
    X.map (residue O) = 0 ↔ ∃ C : Matrix (Fin m) (Fin n) O, X = p • C := by
  have hm : maximalIdeal O = Ideal.span {p} := hp.maximalIdeal_eq
  constructor
  · intro h
    have : ∀ i j, ∃ c, X i j = p * c := by
      intro i j
      have h1 : residue O (X i j) = 0 := congrFun (congrFun h i) j
      rw [residue_eq_zero_iff, hm, Ideal.mem_span_singleton] at h1
      exact h1
    choose C hC using this
    exact ⟨Matrix.of C, Matrix.ext hC⟩
  · rintro ⟨C, rfl⟩
    ext i j
    have : residue O (p * C i j) = 0 := by
      rw [residue_eq_zero_iff, hm, Ideal.mem_span_singleton]
      exact dvd_mul_right _ _
    exact this

theorem map_inj {m n : ℕ} {X Y : Matrix (Fin m) (Fin n) O}
    (h : X.map (algebraMap O K) = Y.map (algebraMap O K)) : X = Y := by
  ext i j
  exact IsFractionRing.injective O K (congrFun (congrFun h i) j)

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
theorem map_smul' {m n : ℕ} (c : O) (X : Matrix (Fin m) (Fin n) O) :
    (c • X).map (algebraMap O K) = algebraMap O K c • X.map (algebraMap O K) := by
  ext i j
  simp

theorem intM_inv_smul_iff (hp : Irreducible p) {m n : ℕ} (X : Matrix (Fin m) (Fin n) O) :
    IntM O ((algebraMap O K p)⁻¹ • X.map (algebraMap O K)) ↔ X.map (residue O) = 0 := by
  have h0 : algebraMap O K p ≠ 0 := by
    intro h
    exact hp.ne_zero (IsFractionRing.injective O K (by rw [h, map_zero]))
  rw [map_res_eq_zero_iff hp, intM_iff]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, map_inj (K := K) ?_⟩
    rw [map_smul', hC, smul_smul, mul_inv_cancel₀ h0, one_smul]
  · rintro ⟨C, rfl⟩
    refine ⟨C, ?_⟩
    rw [map_smul', smul_smul, inv_mul_cancel₀ h0, one_smul]

theorem exists_of_range_le (hp : Irreducible p) {n : ℕ} {A A' : Matrix (Fin n) (Fin n) O}
    (h : LinearMap.range (A'.map (residue O)).mulVecLin ≤ LinearMap.range (A.map (residue O)).mulVecLin) :
    ∃ B C : Matrix (Fin n) (Fin n) O, A' = A * B + p • C := by
  have h1 : ∀ j, ∃ b : Fin n → O, (A.map (residue O)) *ᵥ (fun i => residue O (b i)) =
      (A'.map (residue O)) *ᵥ Pi.single j 1 := by
    intro j
    obtain ⟨y, hy⟩ := h ⟨Pi.single j 1, rfl⟩
    choose b hb using fun i => residue_surjective (R := O) (y i)
    refine ⟨b, ?_⟩
    have : (fun i => residue O (b i)) = y := funext hb
    rw [this]
    exact hy
  choose b hb using h1
  obtain ⟨C, hC⟩ := (map_res_eq_zero_iff hp (A' - A * Matrix.of fun i j => b j i)).1 (by
    ext i j
    have := congrFun (hb j) i
    rw [Matrix.mulVec_single_one] at this
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.col_apply] at this
    simp [Matrix.mul_apply, ← this])
  exact ⟨_, C, by rw [← hC]; abel⟩

theorem range_le_of_mul {n : ℕ} {A A' : Matrix (Fin n) (Fin n) O} {a a' : GL (Fin n) K}
    (hA : A.map (algebraMap O K) = a.1) (hA' : A'.map (algebraMap O K) = a'.1) (h : IntM O (a⁻¹ * a').1) :
    LinearMap.range (A'.map (residue O)).mulVecLin ≤ LinearMap.range (A.map (residue O)).mulVecLin := by
  obtain ⟨B, hB⟩ := intM_iff.1 h
  have : A' = A * B := by
    refine map_inj (K := K) ?_
    rw [Matrix.map_mul, hA, hA', hB, ← Units.val_mul, mul_inv_cancel_left]
  rw [this, Matrix.map_mul, Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

theorem intM_of_range_le (hp : Irreducible p) {n : ℕ} {A A' : Matrix (Fin n) (Fin n) O} {a a' : GL (Fin n) K}
    (hA : A.map (algebraMap O K) = a.1) (hA' : A'.map (algebraMap O K) = a'.1)
    (ha : IntM O (algebraMap O K p • (a⁻¹).1))
    (h : LinearMap.range (A'.map (residue O)).mulVecLin ≤ LinearMap.range (A.map (residue O)).mulVecLin) :
    IntM O (a⁻¹ * a').1 := by
  obtain ⟨B, C, hBC⟩ := exists_of_range_le hp h
  have : (a⁻¹ * a').1 = B.map (algebraMap O K) + (algebraMap O K p • (a⁻¹).1) * C.map (algebraMap O K) := by
    rw [Units.val_mul, ← hA', hBC, Matrix.map_add _ (map_add _), Matrix.map_mul, map_smul', hA, Matrix.mul_add,
      ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  rw [this]
  exact (intM_iff.2 ⟨B, rfl⟩).add (ha.mul (intM_iff.2 ⟨C, rfl⟩))

theorem GInt.exists_det {n : ℕ} {k : GL (Fin n) K} (hk : GInt O k) : ∃ u : Oˣ, k.1.det = algebraMap O K u := by
  obtain ⟨A, hA⟩ := intM_iff.1 hk.1
  obtain ⟨B, hB⟩ := intM_iff.1 hk.2
  have : A * B = 1 := by
    refine map_inj (K := K) ?_
    rw [Matrix.map_mul, hA, hB, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hu : IsUnit A.det := Matrix.isUnit_det_of_right_inverse this
  refine ⟨hu.unit, ?_⟩
  rw [← hA, IsUnit.unit_spec, RingHom.map_det]
  rfl

theorem hk_mul {n j : ℕ} {α k₁ k₂ : GL (Fin n) K} (hα : Hk O p j α) (h₁ : GInt O k₁) (h₂ : GInt O k₂) :
    Hk O p j (k₁ * α * k₂) := by
  refine ⟨(h₁.1.mul hα.1).mul h₂.1, ?_, ?_⟩
  · have := (h₂.2.mul hα.2.1).mul h₁.2
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
    rwa [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc] at this
  · obtain ⟨u, hu⟩ := hα.2.2
    obtain ⟨u₁, hu₁⟩ := GInt.exists_det h₁
    obtain ⟨u₂, hu₂⟩ := GInt.exists_det h₂
    refine ⟨u₁ * u * u₂, ?_⟩
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hu, hu₁, hu₂, ← map_mul, ← map_mul]
    congr 1
    push_cast
    ring

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
theorem gInt_map {n : ℕ} (g : GL (Fin n) O) : GInt O (Matrix.GeneralLinearGroup.map (algebraMap O K) g) :=
  ⟨intM_iff.2 ⟨g.1, rfl⟩, by rw [← map_inv]; exact intM_iff.2 ⟨(g⁻¹).1, rfl⟩⟩

theorem cond_iff (hp : Irreducible p) {m n : ℕ} (z : Matrix (Fin m) (Fin n) O) {A : Matrix (Fin n) (Fin n) O}
    {a : Matrix (Fin n) (Fin n) K} (hA : A.map (algebraMap O K) = a) :
    IntM O (((algebraMap O K p)⁻¹ • z.map (algebraMap O K)) * a) ↔
      LinearMap.range (A.map (residue O)).mulVecLin ≤ LinearMap.ker (z.map (residue O)).mulVecLin := by
  rw [← hA, Matrix.smul_mul, ← Matrix.map_mul, intM_inv_smul_iff hp, LinearMap.range_le_ker_iff,
    ← Matrix.mulVecLin_mul, Matrix.map_mul]
  constructor
  · intro h
    rw [h, Matrix.mulVecLin_zero]
  · intro h
    apply Matrix.toLin'.injective
    rw [map_zero]
    exact h

theorem card_cosets : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (p : O), Irreducible p → ∀ (m n j : ℕ) (ι : Type) (α : GL (Fin n) K) (R : Finset ι) (ρ : ι → GL (Fin n) K) (z : Matrix (Fin m) (Fin n) O), j ≤ n → Hk O p j α → Reps O α R ρ → Nat.card {γ : ι // γ ∈ R ∧ IntM O (((algebraMap O K p)⁻¹ • z.map (algebraMap O K)) * (ρ γ).1)} = Nat.card {W : Submodule (IsLocalRing.ResidueField O) (Fin n → IsLocalRing.ResidueField O) // Module.finrank (IsLocalRing.ResidueField O) W + j = n ∧ W ≤ LinearMap.ker (z.map (IsLocalRing.residue O)).mulVecLin} := by
  intro O K _ _ _ _ _ _ p hp m n j ι α R ρ z hj hα hR
  have hH : ∀ γ ∈ R, Hk O p j (ρ γ) := by
    intro γ hγ
    obtain ⟨k₁, k₂, h₁, h₂, h⟩ := hR.1 γ hγ
    rw [h]
    exact hk_mul hα h₁ h₂
  choose A hA using fun γ (hγ : γ ∈ R) => intM_iff.1 (hH γ hγ).1
  refine Nat.card_eq_of_bijective (fun γ => ⟨LinearMap.range ((A γ.1 γ.2.1).map (residue O)).mulVecLin,
    GlobalTheory.SplitHecke.finrank_range_reduction O K p hp n j _ _ hj (hH _ γ.2.1) (hA _ γ.2.1), (cond_iff hp z (hA _ γ.2.1)).1 γ.2.2⟩) ⟨?_, ?_⟩
  · rintro ⟨γ, hγ, hγ1⟩ ⟨γ', hγ', hγ2⟩ h
    have h' : LinearMap.range ((A γ hγ).map (residue O)).mulVecLin =
        LinearMap.range ((A γ' hγ').map (residue O)).mulVecLin := congrArg Subtype.val h
    have hG : GInt O ((ρ γ)⁻¹ * ρ γ') := by
      refine ⟨intM_of_range_le hp (hA γ hγ) (hA γ' hγ') (hH γ hγ).2.1 h'.ge, ?_⟩
      rw [_root_.mul_inv_rev, inv_inv]
      exact intM_of_range_le hp (hA γ' hγ') (hA γ hγ) (hH γ' hγ').2.1 h'.le
    obtain ⟨k₁, k₂, h₁, h₂, he⟩ := hR.1 γ' hγ'
    have hu := hR.2 k₁ k₂ h₁ h₂
    rw [← he] at hu
    exact Subtype.ext (hu.unique ⟨hγ, hG⟩ ⟨hγ', by rw [inv_mul_cancel]; exact gInt_one⟩)
  · rintro ⟨W, hW, hWz⟩
    obtain ⟨A₀, hA₀⟩ := intM_iff.1 hα.1
    have h0 := GlobalTheory.SplitHecke.finrank_range_reduction O K p hp n j _ _ hj hα hA₀
    obtain ⟨g, hg⟩ := GlobalTheory.SplitHecke.exists_gl_map_residue_eq O n (LinearMap.range (A₀.map (residue O)).mulVecLin) W (by omega)
    obtain ⟨γ, ⟨hγ, hG⟩, -⟩ := hR.2 _ 1 (gInt_map g) gInt_one
    rw [mul_one] at hG
    have hgA : (g.1 * A₀).map (algebraMap O K) =
        (Matrix.GeneralLinearGroup.map (algebraMap O K) g * α).1 := by
      rw [Matrix.map_mul, hA₀]
      rfl
    have hr : LinearMap.range ((A γ hγ).map (residue O)).mulVecLin = W := by
      rw [← hg, ← LinearMap.range_comp, ← Matrix.mulVecLin_mul, ← Matrix.map_mul]
      refine le_antisymm (range_le_of_mul hgA (hA γ hγ) ?_) (range_le_of_mul (hA γ hγ) hgA hG.1)
      have := hG.2
      rwa [_root_.mul_inv_rev, inv_inv] at this
    exact ⟨⟨γ, hγ, (cond_iff hp z (hA γ hγ)).2 (hr ▸ hWz)⟩, Subtype.ext hr⟩

end GlobalTheory.SplitHecke.Cosets
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ProdReorder
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ProdReorder
section SlopeTestRemainingChoices
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem multiProd_single_equiv {dτ : Fin 1 → ℕ} (τ : ∀ a, Irr k (dτ a)) (e : (Σ a, Fin (dτ a)) ≃ Fin (dτ 0)) :
    Nonempty ((multiProd e fun a => (τ a).π).Equiv (τ 0).π) := by
  have A := multiProd_head (k := k) (fun a => (τ a).π) e (by simp : dτ 0 + 0 = dτ 0)
          (Equiv.equivOfIsEmpty (Σ a : Fin 0, Fin (dτ a.succ)) (Fin 0))
  have B := ind₂_unit_right (k := k) (by simp : dτ 0 + 0 = dτ 0) (τ 0).π (τ 0).smooth (fun a : Fin 0 => (τ a.succ).π) (Equiv.equivOfIsEmpty (Σ a : Fin 0, Fin (dτ a.succ)) (Fin 0))
  exact A.elim fun a => B.elim fun b => ⟨a.trans b⟩

theorem commutes_multiProd_single {p : ℕ} (x : Irr k p) {dτ : Fin 1 → ℕ} (τ : ∀ a, Irr k (dτ a)) (hc : Commutes x (τ 0)) (N : ℕ) (e : (Σ a, Fin (dτ a)) ≃ Fin (dτ 0)) (h₁ : p + dτ 0 = N) (h₂ : dτ 0 + p = N) : Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (multiProd e fun a => (τ a).π))).Equiv (ind₂ (stdSum h₂) (extTensor (multiProd e fun a => (τ a).π) x.π))) := by
  have M := multiProd_single_equiv τ e
  have s1 : Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (multiProd e fun a => (τ a).π))).Equiv (ind₂ (stdSum h₁) (extTensor x.π (τ 0).π))) := ind₂_congr h₁ (eqv_refl _) M
  have s2 : Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (τ 0).π)).Equiv (ind₂ (stdSum h₂) (extTensor (τ 0).π x.π))) := hc N h₁ h₂
  have s3 : Nonempty ((ind₂ (stdSum h₂) (extTensor (τ 0).π x.π)).Equiv (ind₂ (stdSum h₂) (extTensor (multiProd e fun a => (τ a).π) x.π))) := ind₂_congr h₂ (eqv_symm M) (eqv_refl _)
  exact s1.elim fun a => s2.elim fun b => s3.elim fun c => ⟨(a.trans b).trans c⟩

theorem commutes_ind₂_of_head {p d T' T N : ℕ} (x : Irr k p) (y : Irr k d) {W : Type} [AddCommGroup W] [Module ℂ W]
    (R : Representation ℂ (GL (Fin T') k) W) (sR : IsSmooth R) {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (P : Representation ℂ (GL (Fin T) k) Y) (h : d + T' = T) (H : Nonempty (P.Equiv (ind₂ (stdSum h) (extTensor y.π R))))
    (hc : Commutes x y)
    (IH : ∀ M (g₁ : p + T' = M) (g₂ : T' + p = M),
      Nonempty ((ind₂ (stdSum g₁) (extTensor x.π R)).Equiv (ind₂ (stdSum g₂) (extTensor R x.π))))
    (h₁ : p + T = N) (h₂ : T + p = N) :
    Nonempty ((ind₂ (stdSum h₁) (extTensor x.π P)).Equiv (ind₂ (stdSum h₂) (extTensor P x.π))) := by
  have hA2 : (p + d) + T' = N := by omega
  have hB1 : d + p = p + d := Nat.add_comm _ _
  have h₄ : d + (p + T') = N := by omega
  have hD : T' + p = p + T' := Nat.add_comm _ _
  have s1 : Nonempty ((ind₂ (stdSum h₁) (extTensor x.π P)).Equiv
      (ind₂ (stdSum h₁) (extTensor x.π (ind₂ (stdSum h) (extTensor y.π R))))) :=
    ind₂_congr h₁ (eqv_refl x.π) H
  have s2 : Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (ind₂ (stdSum h) (extTensor y.π R)))).Equiv
      (ind₂ (stdSum hA2) (extTensor (ind₂ (stdSum (rfl : p + d = p + d)) (extTensor x.π y.π)) R))) :=
    (ind₂_assoc' (k := k) rfl hA2 h h₁ x.π y.π R x.smooth y.smooth sR).elim fun a => ⟨a.symm⟩
  have s3 : Nonempty ((ind₂ (stdSum hA2) (extTensor (ind₂ (stdSum (rfl : p + d = p + d)) (extTensor x.π y.π)) R)).Equiv
      (ind₂ (stdSum hA2) (extTensor (ind₂ (stdSum hB1) (extTensor y.π x.π)) R))) :=
    ind₂_congr hA2 (hc (p + d) rfl hB1) (eqv_refl R)
  have s4 : Nonempty ((ind₂ (stdSum hA2) (extTensor (ind₂ (stdSum hB1) (extTensor y.π x.π)) R)).Equiv
      (ind₂ (stdSum h₄) (extTensor y.π (ind₂ (stdSum (rfl : p + T' = p + T')) (extTensor x.π R))))) :=
    ind₂_assoc' (k := k) hB1 hA2 rfl h₄ y.π x.π R y.smooth x.smooth sR
  have s5 : Nonempty ((ind₂ (stdSum h₄) (extTensor y.π (ind₂ (stdSum (rfl : p + T' = p + T')) (extTensor x.π R)))).Equiv
      (ind₂ (stdSum h₄) (extTensor y.π (ind₂ (stdSum hD) (extTensor R x.π))))) :=
    ind₂_congr h₄ (eqv_refl y.π) (IH _ rfl hD)
  have s6 : Nonempty ((ind₂ (stdSum h₄) (extTensor y.π (ind₂ (stdSum hD) (extTensor R x.π)))).Equiv
      (ind₂ (stdSum h₂) (extTensor (ind₂ (stdSum h) (extTensor y.π R)) x.π))) :=
    (ind₂_assoc' (k := k) h h₂ hD h₄ y.π R x.π y.smooth sR x.smooth).elim fun a => ⟨a.symm⟩
  have s7 : Nonempty ((ind₂ (stdSum h₂) (extTensor (ind₂ (stdSum h) (extTensor y.π R)) x.π)).Equiv
      (ind₂ (stdSum h₂) (extTensor P x.π))) :=
    ind₂_congr h₂ (H.elim fun a => ⟨a.symm⟩) (eqv_refl x.π)
  exact s1.elim fun a1 => s2.elim fun a2 => s3.elim fun a3 => s4.elim fun a4 => s5.elim fun a5 =>
    s6.elim fun a6 => s7.elim fun a7 => ⟨a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans a7)))))⟩

end SlopeTestRemainingChoices

section Succ
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem commutes_multiProd_succ {p s : ℕ} (x : Irr k p)
    (ih : ∀ (dτ : Fin s → ℕ) (τ : ∀ a, Irr k (dτ a)), (∀ a, Commutes x (τ a)) → ∀ (T N : ℕ) (e : (Σ a, Fin (dτ a)) ≃ Fin T) (h₁ : p + T = N) (h₂ : T + p = N), Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (multiProd e fun a => (τ a).π))).Equiv (ind₂ (stdSum h₂) (extTensor (multiProd e fun a => (τ a).π) x.π))))
    (dτ : Fin (s + 1) → ℕ) (τ : ∀ a, Irr k (dτ a)) (hc : ∀ a, Commutes x (τ a)) (T N : ℕ) (e : (Σ a, Fin (dτ a)) ≃ Fin T) (h₁ : p + T = N) (h₂ : T + p = N) :
    Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (multiProd e fun a => (τ a).π))).Equiv (ind₂ (stdSum h₂) (extTensor (multiProd e fun a => (τ a).π) x.π))) := by
  have key : ∀ (S : ℕ) (e' : (Σ a : Fin s, Fin (dτ a.succ)) ≃ Fin S) (h : dτ 0 + S = T),
      Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (multiProd e fun a => (τ a).π))).Equiv (ind₂ (stdSum h₂) (extTensor (multiProd e fun a => (τ a).π) x.π))) := by
    intro S e' h
    have H := multiProd_head (k := k) (fun a => (τ a).π) e h e'
    have sR : IsSmooth (multiProd e' fun a : Fin s => (τ a.succ).π) :=
      GlobalTheory.SmGL.isSmooth_parInd e' (piTensor fun a : Fin s => (τ a.succ).π)
    exact commutes_ind₂_of_head x (τ 0) _ sR _ h H (hc 0)
      (fun M g₁ g₂ => ih (fun a => dτ a.succ) (fun a => τ a.succ) (fun a => hc a.succ) _ M e' g₁ g₂) h₁ h₂
  have h : dτ 0 + ∑ a : Fin s, dτ a.succ = T := by
    have := Fintype.card_congr e
    simp only [Fintype.card_sigma, Fintype.card_fin] at this
    rw [← this]
    exact (Fin.sum_univ_succ _).symm
  exact key _ (finSigmaFinEquiv (n := fun a : Fin s => dτ a.succ)) h
end Succ

theorem commutes_multiProd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p u : ℕ) (x : Irr k p) (dτ : Fin (u + 1) → ℕ) (τ : ∀ a, Irr k (dτ a)), (∀ a, Commutes x (τ a)) → ∀ (T N : ℕ) (e : (Σ a, Fin (dτ a)) ≃ Fin T) (h₁ : p + T = N) (h₂ : T + p = N), Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (multiProd e fun a => (τ a).π))).Equiv (ind₂ (stdSum h₂) (extTensor (multiProd e fun a => (τ a).π) x.π))) := by
  intro k _ _ _ _ p u x
  induction u with
  | zero =>
    intro dτ τ hc T N e h₁ h₂
    have hT : T = dτ 0 := by
      have := Fintype.card_congr e
      simpa [Fintype.card_sigma] using this.symm
    subst hT
    exact commutes_multiProd_single x τ (hc 0) N e h₁ h₂
  | succ u ih =>
    exact commutes_multiProd_succ x ih

end GlobalTheory.ProdReorder
end

section

namespace GlobalTheory

theorem regularAlgebraicPurity_of_clozel (hP : GlobalTheory.Published.ClozelPurity) (hC : GlobalTheory.Published.ClozelCohomological) :
    GlobalTheory.Published.RegularAlgebraicPurity := by
  intro E _ _ _ a ha π hr
  exact ⟨hP E a ha π fun τ => (hr τ).2, hC E a ha π hr⟩

end GlobalTheory
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

theorem _root_.GlobalTheory.T.padic_norm_le_one_host_base_module_at_d : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p = D.host.d → ∀ (φ : D.host.E →+* ℂ_[p]) (a : D.host.E), a ∈ D.host.AA0 → ‖φ a‖ ≤ 1 := by
  first | exact @GlobalTheory.IntegralAtPlace.norm_le_one | exact GlobalTheory.IntegralAtPlace.norm_le_one | (intros; apply GlobalTheory.IntegralAtPlace.norm_le_one <;> assumption)
end

section


theorem _root_.GlobalTheory.T.localNormalisation_intertwiner_prime_index : Formalism.L2.AlgTh.LocNormInter := by
  first | exact @GlobalTheory.locNormInter | exact GlobalTheory.locNormInter | (intros; apply GlobalTheory.locNormInter <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2

namespace GlobalTheory

theorem levGTop_rPsymF_eq_twLt : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m), X.Ok → Pr.Ok → Ch.Ok →
    levGTop Ch (rPsymF Ch) = twLt Ch R.m := by
  intro X Pr R Ch _ _ _
  funext w
  rw [levGTop_PsymF]
  show _ = colLevSym Ch R.m w
  unfold colLevSym
  rw [if_neg (by have := R.two_le_m; omega), dite_eq_right (by omega), dite_eq_right (by omega)]
  rfl

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

theorem _root_.GlobalTheory.T.principal_congruence_le_twisted_k1 : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} (r c : ℕ), 0 < c → prinCong N P c ≤ twK1H P N r c := by
  first | exact @GlobalTheory.PrincipalCongruenceLevelK1.principal_congruence_le_level_k1 | exact GlobalTheory.PrincipalCongruenceLevelK1.principal_congruence_le_level_k1 | (intros; apply GlobalTheory.PrincipalCongruenceLevelK1.principal_congruence_le_level_k1 <;> assumption)
end

section


theorem _root_.GlobalTheory.T.mem_range_witt_algClosure_of_bounded_ringHom : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (W : Type) [CommRing W], 0 < n → (∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) → IsAdicComplete (Ideal.span {(p : W)}) W → ∀ φ : W →+* ℂ_[p], (∀ x, ‖φ x‖ ≤ 1) → ∀ x, φ x ∈ Set.range (Formalism.L2.G.Pend.wToC p) := by
  first | exact @GlobalTheory.mem_range_wToC_of_pow_congr | exact GlobalTheory.mem_range_wToC_of_pow_congr | (intros; apply GlobalTheory.mem_range_wToC_of_pow_congr <;> assumption)
end

section


theorem _root_.GlobalTheory.T.ringHom_witt_algClosure_eq_of_congr_mod_prime : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (W : Type) [CommRing W], 0 < n → (∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) → ∀ f g : W →+* Formalism.L2.G.Pend.WW p, (∀ x, (p : Formalism.L2.G.Pend.WW p) ∣ f x - g x) → f = g := by
  first | exact @GlobalTheory.ringHom_wittKbar_eq_of_modp | exact GlobalTheory.ringHom_wittKbar_eq_of_modp | (intros; apply GlobalTheory.ringHom_wittKbar_eq_of_modp <;> assumption)
end

section


theorem _root_.GlobalTheory.T.coboundary_integral_law_respects_simeq : Formalism.L2.KerInert.BeCob.CobSimeq := by
  first | exact @GlobalTheory.CobSimeqProof.cobSimeq | exact GlobalTheory.CobSimeqProof.cobSimeq | (intros; apply GlobalTheory.CobSimeqProof.cobSimeq <;> assumption)
end
