module

public import Formalism.SharpRestriction.LevelLetterCocycles.DownSlotProposition
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle012
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle014
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfPhi
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle009
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle018
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfEqv
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfNat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {T : LocLat G Qp LL O}

theorem framepf_smulLA_eq (π' : LetA O n) (c : ZMod n) (a : LetA O n) (z : W.EE ⊗[O] LcQ W T π' c) :
    smulLA W T π' c a z = algebraMap (LetA O n) W.EE a • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e ℓ => rw [framepf_smulLA_tmul, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]

variable (Bs : FramepfBas W T) (π' : LetA O n) (c : ZMod n)
    (hπ0 : ∀ j, PowerSeries.constantCoeff (π' j) = 0)
    (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hR2 : ∀ a : LetA O n, a ∈ W.AΔ → ∃! f : ZMod n → PowerSeries O,
      ∀ j, a j = PowerSeries.subst (π' j) (f j))
    (γ0 : ∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π'))

include hπ0 hΔπ γ0 in
theorem framepf_φA_ι_mem (g : PowerSeries O) : W.φA (framepf_ι π' (c - 1) g) ∈ W.AΔ := by
  intro δ hδ
  rw [← LocWach.φA_γA, framepf_ι_Δ π' hπ0 hΔπ γ0 _ g δ hδ]

theorem framepf_φD_vec (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (k : Fin Bs.r) :
    W.φD T (framepf_vec Bs π' (c - 1) H k) =
      ∑ m, W.φA (framepf_ι π' (c - 1) (H m k)) • W.φD T (Bs.b m) := by
  unfold framepf_vec

  rw [map_sum]
  exact Finset.sum_congr rfl fun m _ => framepf_φD_smul _ _

def framepf_ebar (j : Fin Bs.r) : LcQ W T π' c :=
  (framepf_Lbas Bs π' c hπ0 hΔπ hR2 γ0 hu).symm (Pi.single j 1)

theorem framepf_hh_ebar (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (j : Fin Bs.r) :
    framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H (framepf_ebar Bs π' c hπ0 hΔπ hR2 γ0 hu j) =
      framepf_vec Bs π' (c - 1) H j := by
  unfold framepf_hh framepf_ebar
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    Fintype.linearCombination_apply_single, one_smul]

def framepf_Ψβ (βφ : Module.Basis (Fin Bs.r) W.EE (W.DD T)) (F : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) :
    W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c :=
  βφ.constr W.EE fun k => ∑ j, algebraMap (LetA O n) W.EE (W.φA (framepf_ι π' (c - 1) (F j k))) ⊗ₜ
    framepf_ebar Bs π' c hπ0 hΔπ hR2 γ0 hu j

variable (βφ : Module.Basis (Fin Bs.r) W.EE (W.DD T)) (hβφ : ∀ k, βφ k = W.φD T (Bs.b k))

include hβφ in
theorem framepf_Ψβ_sum (F : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (a : Fin Bs.r → LetA O n) :
    framepf_Ψβ Bs π' c hπ0 hΔπ hR2 γ0 hu βφ F (∑ k, a k • W.φD T (Bs.b k)) =
      ∑ j, algebraMap (LetA O n) W.EE (∑ k, a k * W.φA (framepf_ι π' (c - 1) (F j k))) ⊗ₜ
        framepf_ebar Bs π' c hπ0 hΔπ hR2 γ0 hu j := by
  have e1 : ∀ k, framepf_Ψβ Bs π' c hπ0 hΔπ hR2 γ0 hu βφ F (a k • W.φD T (Bs.b k)) =
      ∑ j, algebraMap (LetA O n) W.EE (a k * W.φA (framepf_ι π' (c - 1) (F j k))) ⊗ₜ
        framepf_ebar Bs π' c hπ0 hΔπ hR2 γ0 hu j := by
    intro k
    rw [← algebraMap_smul W.EE (a k), LinearMap.map_smul, ← hβφ k]
    unfold framepf_Ψβ
    rw [Module.Basis.constr_basis, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul, ← map_mul]

  rw [map_sum, Finset.sum_congr rfl fun k _ => e1 k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_

  rw [← TensorProduct.sum_tmul, ← map_sum]


include hπ0 hΔπ γ0 hβφ in
theorem framepf_Ψβ_Pc (hT : IsCrys PD T.ρ) (F : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O))
    (p : W.DD T) (hp : p ∈ PcS W T c) :
    ∃ t, framepf_Ψβ Bs π' c hπ0 hΔπ hR2 γ0 hu βφ F p = toLA W T π' c ⊤ t := by
  obtain ⟨a, haΔ, hac, hap⟩ := framepf_Pc_coord Bs hT c p hp
  have hmem : ∀ j, ∑ k, a k * W.φA (framepf_ι π' (c - 1) (F j k)) ∈ W.AΔ := fun j =>
    Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ (haΔ k) (framepf_φA_ι_mem π' c hπ0 hΔπ γ0 _)
  refine ⟨∑ j, (⟨_, hmem j⟩ : ↥W.AΔ) ⊗ₜ (⟨framepf_ebar Bs π' c hπ0 hΔπ hR2 γ0 hu j, trivial⟩ :
    ↥(⊤ : Submodule O (LcQ W T π' c))), ?_⟩

  rw [hap, framepf_Ψβ_sum Bs π' c hπ0 hΔπ hR2 γ0 hu βφ hβφ, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [framepf_toLA_tmul]
  congr 2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, hac k]

variable (Eπ : LetA O n) (hEu : IsUnit (algebraMap (LetA O n) W.EE Eπ))
    (hEΔ : ∀ δ ∈ W.DelF, W.γA δ Eπ = Eπ) (h' M : ℕ)


include hπ0 hΔπ γ0 hβφ hEΔ in
theorem framepf_Ψβ_Lam (hT : IsCrys PD T.ρ) (F : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O))
    (y : W.DD T) (hy : y ∈ LamPS W T Eπ h' c) :
    framepf_Ψβ Bs π' c hπ0 hΔπ hR2 γ0 hu βφ F y ∈ LamLA W T π' Eπ h' c ⊤ := by
  rw [mem_LamPS] at hy
  obtain ⟨h1, hΔ, hl⟩ := hy
  have hP : Eπ ^ h' • y ∈ PcS W T c := by
    unfold PcS
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨(Submodule.restrictScalars_mem _ _ _).2 h1, ?_⟩, ?_⟩
    · rw [mem_DelS]
      intro δ hδ
      rw [gradNPf_γD_smul, map_pow, hEΔ δ hδ, hΔ δ hδ]
    · rw [mem_letS, smul_smul, mul_comm, ← smul_smul, hl]
  obtain ⟨t, ht⟩ := framepf_Ψβ_Pc Bs π' c hπ0 hΔπ hR2 γ0 hu βφ hβφ hT F _ hP
  refine Submodule.mem_comap.2 ⟨t, ?_⟩
  rw [← ht, framepf_smulLA_eq, ← LinearMap.map_smul, algebraMap_smul]


include hπ0 hΔπ γ0 hβφ in
theorem framepf_Ψβ_J (hT : IsCrys PD T.ρ) (F : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O))
    (y : W.DD T) (hy : y ∈ JP W T π' Eπ h' M c) :
    framepf_Ψβ Bs π' c hπ0 hΔπ hR2 γ0 hu βφ F y ∈ JLA W T π' Eπ h' M c := by
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hy
  obtain ⟨t, ht⟩ := framepf_Ψβ_Pc Bs π' c hπ0 hΔπ hR2 γ0 hu βφ hβφ hT F p hp
  refine Submodule.mem_map.2 ⟨_, ⟨t, rfl⟩, ?_⟩
  rw [framepf_smulLA_eq, ← ht, ← LinearMap.map_smul, algebraMap_smul]
  rfl

include hπ0 in
theorem framepf_ι_X_pow_mul (k : ℕ) (g : PowerSeries O) :
    framepf_ι π' (c - 1) (PowerSeries.X ^ k * g) = π' ^ k * framepf_ι π' (c - 1) g := by
  induction k with
  | zero => rw [pow_zero, one_mul, pow_zero, one_mul]
  | succ k ih =>
    rw [pow_succ', mul_assoc, framepf_ι_mul π' (c - 1) (hπ0 _), ih, framepf_ι_X π' (c - 1) (hπ0 _),
      pow_succ']
    have := framepf_letE_ι π' (c - 1) hπ0 g
    calc letE (c - 1) * π' * (π' ^ k * framepf_ι π' (c - 1) g)
        = π' * π' ^ k * (letE (c - 1) * framepf_ι π' (c - 1) g) := by ring
      _ = π' * π' ^ k * framepf_ι π' (c - 1) g := by rw [this]


include hπ0 in
theorem framepf_φA_ι_entry (M : ℕ) (lam : O) (K : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O))
    (j k : Fin Bs.r) :
    W.φA (framepf_ι π' (c - 1) ((PowerSeries.C lam • (1 : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) +
      (PowerSeries.X : PowerSeries O) ^ M • K) j k)) =
      (if j = k then algebraMap O (LetA O n) lam * letE c else 0) +
        W.φA π' ^ M * W.φA (framepf_ι π' (c - 1) (K j k)) := by
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
    framepf_ι_add π' (c - 1) (hπ0 _), map_add, framepf_ι_X_pow_mul π' c hπ0, map_mul, map_pow]
  congr 1
  by_cases h : j = k
  · subst h
    rw [Matrix.one_apply_eq, mul_one, framepf_ι_C π' (c - 1) (hπ0 _), map_mul,
      Formalism.MainNotions.LiftingTheory.wmap_φA_letE, AlgHom.commutes, if_pos rfl, mul_comm]
  · rw [Matrix.one_apply_ne h, mul_zero, framepf_ι_zero π' (c - 1) hπ0, map_zero, if_neg h]

include hπ0 in
theorem framepf_φA_ι_matmul (F H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (j k : Fin Bs.r) :
    ∑ m, W.φA (framepf_ι π' (c - 1) (F j m)) * W.φA (framepf_ι π' (c - 1) (H m k)) =
      W.φA (framepf_ι π' (c - 1) ((F * H) j k)) := by

  rw [Matrix.mul_apply, framepf_ι_sum π' (c - 1) hπ0, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [framepf_ι_mul π' (c - 1) (hπ0 _), map_mul]

end Local

end Formalism.MainNotions.N.Ln34

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' M σ : ℕ) (c : ZMod n)

structure FramepfData (T : LocLat G Qp LL O) (hh : LcQ W T π' c →ₗ[O] W.DD T)
    (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T) (Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c) : Prop where
  hγ : ∀ ℓ, W.γD T W.gam (hh ℓ) - hh ℓ ∈ PiNS W T π' M
  hmod : ∀ z hz, hh (mkL W T π' c z hz) - ((PD.p : ℕ) : O) ^ σ • z ∈ PiNS W T π' 1
  hΨ : ∀ e ℓ, Ψ (e ⊗ₜ ℓ) = e • W.φD T (hh ℓ)
  ΨJ : ∀ x ∈ JLA W T π' Eπ h' M c, Ψ x ∈ JP W T π' Eπ h' M c
  ΦJ : ∀ y ∈ JP W T π' Eπ h' M c, Φ y ∈ JLA W T π' Eπ h' M c
  βα : ∀ x ∈ LamLA W T π' Eπ h' c ⊤, Φ (Ψ x) - ((PD.p : ℕ) : O) ^ (2 * σ) • x ∈ JLA W T π' Eπ h' M c
  αβ : ∀ y ∈ LamPS W T Eπ h' c, Ψ (Φ y) - ((PD.p : ℕ) : O) ^ (2 * σ) • y ∈ JP W T π' Eπ h' M c
  sat : ∀ x ∈ LamLA W T π' Eπ h' c ⊤, ((PD.p : ℕ) : O) ^ (2 * σ) • x ∈ JLA W T π' Eπ h' M c →
    x ∈ JLA W T π' Eπ h' M c
  inj : ∀ x ∈ PiNS W T π' 1, W.γD T W.gam x - x ∈ PiNS W T π' M → x ∈ PiNS W T π' M
  loc : ∀ τ ζ, Pt c ζ τ → ∀ x y, Ψ x - y ∈ JP W T π' Eπ h' M c →
    ∀ (m : ℕ) (a : Fin m → ↥W.AΔ) (z : Fin m → W.DD T), IsRepL W T π' Eπ h' c x a z →
    ∀ (k : ℕ) (hk : W.Q ^ k • (Eπ ^ h' • y) ∈ W.N T) (i : ℤ), i < k + 4 * h' →
      W.levN T c ζ ⟨_, hk⟩ i =
        (PD.p ^ σ) • serMul (W.lev c ζ (W.Q ^ k)) (expS W T c ζ (fun j => (a j : LetA O n)) z) i

theorem quotientMk_eq_iff_sub_mem {T : LocLat G Qp LL O} {y y' : W.DD T} (hy : y ∈ LamPS W T Eπ h' c)
    (hy' : y' ∈ LamPS W T Eπ h' c) :
    mkP W T π' Eπ h' M c y hy = mkP W T π' Eπ h' M c y' hy' ↔ y - y' ∈ JP W T π' Eπ h' M c :=
  Submodule.Quotient.eq _

theorem framepf_mkLA_eq {T : LocLat G Qp LL O} {x x' : LA W T π' c} (hx : x ∈ LamLA W T π' Eπ h' c ⊤)
    (hx' : x' ∈ LamLA W T π' Eπ h' c ⊤) :
    mkLA W T π' Eπ h' M c x hx = mkLA W T π' Eπ h' M c x' hx' ↔ x - x' ∈ JLA W T π' Eπ h' M c :=
  Submodule.Quotient.eq _



theorem framepf_frameA (hK : W.gamK = W.gam) (hu : IsUnit (algebraMap (LetA O n) W.EE π'))
    (huE : IsUnit (algebraMap (LetA O n) W.EE Eπ)) (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (u : LetA O n) (huΔ : u ∈ W.AΔ) (hφ : W.φA π' ^ M = π' ^ M * Eπ ^ (4 * h') * u)
    {f t t' : LetA O n} (hfΔ : f ∈ W.AΔ) (hf : W.γA W.gamK π' = π' * f)
    (htΔ : t ∈ W.AΔ) (ht : W.γA W.gamK Eπ = Eπ * t)
    (ht'Δ : t' ∈ W.AΔ) (ht' : Eπ = W.γA W.gamK Eπ * t')
    (hex : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∃ (hh : LcQ W T π' c →ₗ[O] W.DD T)
      (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T) (Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c),
      (∀ x ∈ LamLA W T π' Eπ h' c ⊤, Ψ x ∈ LamPS W T Eπ h' c) ∧
      (∀ y ∈ LamPS W T Eπ h' c, Φ y ∈ LamLA W T π' Eπ h' c ⊤) ∧
      FramepfData W Pt π' Eπ h' M σ c T hh Ψ Φ) :
    FrameA W Pt π' Eπ h' M σ c := by
  have hex' : ∀ T : LocLat G Qp LL O, ∃ (hh : LcQ W T π' c →ₗ[O] W.DD T)
      (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T) (Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c),
      (∀ x ∈ LamLA W T π' Eπ h' c ⊤, Ψ x ∈ LamPS W T Eπ h' c) ∧
      (∀ y ∈ LamPS W T Eπ h' c, Φ y ∈ LamLA W T π' Eπ h' c ⊤) ∧
      (IsCrys PD T.ρ → FramepfData W Pt π' Eπ h' M σ c T hh Ψ Φ) := by
    intro T
    by_cases hT : IsCrys PD T.ρ
    · obtain ⟨hh, Ψ, Φ, h1, h2, h3⟩ := hex T hT
      exact ⟨hh, Ψ, Φ, h1, h2, fun _ => h3⟩
    · exact ⟨0, 0, 0, fun _ _ => Submodule.zero_mem _, fun _ _ => Submodule.zero_mem _,
        fun h => absurd h hT⟩
  choose hh Ψ Φ hΨL hΦL hD using hex'
  let α : FrA W π' Eπ h' M c := fun T => (Submodule.mkQ _).comp (LinearMap.codRestrict (LamPS W T Eπ h' c)
    (((Ψ T).restrictScalars O).comp (LamLA W T π' Eπ h' c ⊤).subtype) fun x => hΨL T x x.2)
  let β : FrB W π' Eπ h' M c := fun T => (Submodule.mkQ _).comp
    (LinearMap.codRestrict (LamLA W T π' Eπ h' c ⊤)
      (((Φ T).restrictScalars O).comp (LamPS W T Eπ h' c).subtype) fun y => hΦL T y y.2)
  have hα : ∀ T x hx y hy, α T ⟨x, hx⟩ = mkP W T π' Eπ h' M c y hy ↔
      Ψ T x - y ∈ JP W T π' Eπ h' M c := fun T x hx y hy =>
    quotientMk_eq_iff_sub_mem W π' Eπ h' M c (hΨL T x hx) hy
  have hβ : ∀ T y hy x hx, β T ⟨y, hy⟩ = mkLA W T π' Eπ h' M c x hx ↔
      Φ T y - x ∈ JLA W T π' Eπ h' M c := fun T y hy x hx =>
    framepf_mkLA_eq W π' Eπ h' M c (hΦL T y hy) hx
  refine ⟨α, β, fun T hT _ => ?_, fun T₁ T₂ F hT₁ hT₂ _ _ => ?_⟩
  · have D := hD T hT
    have hΨγ := framepf_Ψα_γ π' Eπ h' M c ht'Δ ht' hu huE hΔπ u huΔ hφ (hh T)
      (by rw [hK]; exact D.hγ) (Ψ T) D.hΨ
    refine ⟨fun x hx hJ => ?_, fun y hy hJ => ?_, fun x hx y hy h => ?_, fun y hy x hx h => ?_,
      fun a ha x hx y hy h hax hay => ?_, fun a ha y hy x hx h hay hax => ?_,
      fun x hx y hy h hgx hgy => ?_, fun y hy x hx h hgy hgx => ?_,
      fun τ ζ hpt x hx y hy h => D.loc τ ζ hpt x y ((hα T x hx y hy).1 h)⟩
    · exact (hα T x hx 0 (Submodule.zero_mem _)).2 (by rw [sub_zero]; exact D.ΨJ x hJ)
    · exact (hβ T y hy 0 (Submodule.zero_mem _)).2 (by rw [sub_zero]; exact D.ΦJ y hJ)
    · rw [hβ]
      have h1 := Submodule.sub_mem _ (D.βα x hx) (D.ΦJ _ ((hα T x hx y hy).1 h))
      rw [map_sub, sub_sub_sub_cancel_left] at h1
      exact h1
    · rw [hα]
      have h1 := Submodule.sub_mem _ (D.αβ y hy) (D.ΨJ _ ((hβ T y hy x hx).1 h))
      rw [map_sub, sub_sub_sub_cancel_left] at h1
      exact h1
    · rw [hα, framepf_Ψ_smulLA, ← smul_sub]
      exact framepf_JP_smul π' Eπ h' M c ha ((hα T x hx y hy).1 h)
    · rw [hβ, ← algebraMap_smul W.EE a y, map_smul, ← framepf_smulLA_alg, ← map_sub]
      exact framepf_JLA_smul π' Eπ h' M c ha ((hβ T y hy x hx).1 h)
    · rw [hα]
      have h1 := Submodule.sub_mem _
        (framepf_γ_JP π' Eπ h' M c hfΔ hf htΔ ht ((hα T x hx y hy).1 h)) (hΨγ x hx)
      rw [map_sub, sub_sub_sub_cancel_left] at h1
      exact h1
    · rw [hβ]
      have h1 := Submodule.add_mem _
        (framepf_Ψβ_γ π' Eπ h' M c hfΔ hf htΔ ht ht'Δ ht' (Ψ T) (Φ T) _ hΨγ (hΦL T) D.ΦJ D.αβ D.βα
          D.sat y hy hgy)
        (framepf_γ_JLA π' Eπ h' M c hfΔ hf htΔ ht ((hβ T y hy x hx).1 h))
      rw [map_sub, sub_add_sub_cancel] at h1
      exact h1
  · have D₁ := hD T₁ hT₁
    have D₂ := hD T₂ hT₂
    have hFN := W.map_N F hT₁ hT₂
    have hnat := framepf_Ψα_nat F hFN π' Eπ h' M c hu huE hΔπ u huΔ hφ (hh T₁) (hh T₂)
      (framepf_hh_nat F hFN π' c M _ D₂.inj (hh T₁) (hh T₂) D₁.hγ D₂.hγ D₁.hmod D₂.hmod)
      (Ψ T₁) D₁.hΨ (Ψ T₂) D₂.hΨ
    refine ⟨fun x₁ hx₁ x₂ hx₂ y₁ hy₁ hy₂ hov h => ?_, fun y₁ hy₁ hy₂ x₁ hx₁ x₂ hx₂ hov h => ?_⟩
    · rw [hα]
      exact framepf_α_nat F hFN π' Eπ h' M c (Ψ T₁) (Ψ T₂) hnat x₁ hx₁ x₂ y₁ hov
        ((hα T₁ x₁ hx₁ y₁ hy₁).1 h)
    · rw [hβ]
      exact framepf_β_nat F hFN π' Eπ h' M c (Ψ T₁) (Ψ T₂) hnat (Φ T₁) (Φ T₂) _ (hΦL T₁) (hΦL T₂)
        D₂.ΦJ D₁.αβ D₂.βα D₂.sat y₁ hy₁ hy₂ x₁ x₂ hov ((hβ T₁ y₁ hy₁ x₁ hx₁).1 h)

end Local

end Formalism.MainNotions.N.Ln34

end
end
