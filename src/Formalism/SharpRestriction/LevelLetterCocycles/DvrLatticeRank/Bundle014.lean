module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle012
public import Formalism.SharpRestriction.LevelLetterCocycles.DownSlotProposition
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfDict
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfNat
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle009
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle018
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
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

theorem framepf_βα_core (Bs : FramepfBas W T) (π' Eπ : LetA O n) (h' M : ℕ)
    (c : ZMod n) (huE : IsUnit (algebraMap (LetA O n) W.EE Eπ))
    (eb : Module.Basis (Fin Bs.r) O (LcQ W T π' c)) (P R S : Fin Bs.r → Fin Bs.r → LetA O n)
    (hS : ∀ m k, S m k ∈ W.AΔ) (lam : O) (hPR : ∀ j k, ∑ m, P j m * R m k =
      (if j = k then algebraMap O (LetA O n) lam * letE c else 0) + π' ^ M * Eπ ^ (4 * h') * S j k)
    (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T) (Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c)
    (hΨ : ∀ e j, Ψ (e ⊗ₜ eb j) = e • ∑ m, R m j • W.φD T (Bs.b m))
    (hΦ : ∀ a : Fin Bs.r → LetA O n, Φ (∑ k, a k • W.φD T (Bs.b k)) =
      ∑ j, algebraMap (LetA O n) W.EE (∑ k, a k * P j k) ⊗ₜ eb j)
    (x : LA W T π' c) (hx : x ∈ LamLA W T π' Eπ h' c ⊤) :
    Φ (Ψ x) - lam • x ∈ JLA W T π' Eπ h' M c := by
  choose a haΔ ha using (framepf_mem_toLA π' c eb _).1 hx
  have hee : (letE c : LetA O n) * letE c = letE c := Formalism.MainNotions.LiftingTheory.wmap_letE_idem c
  have hx' : algebraMap (LetA O n) W.EE (Eπ ^ h') • x =
      ∑ k, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a k) ⊗ₜ[O] eb k := by
    rw [← framepf_smulLA_alg, ← (Algebra.TensorProduct.basis W.EE eb).sum_repr (smulLA W T π' c _ x)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ha, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hm : ∀ j, ∑ k, a k * S j k ∈ W.AΔ := fun j =>
    Subalgebra.sum_mem _ fun k _ => W.AΔ.mul_mem (haΔ k) (hS j k)
  refine ⟨∑ j, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * ∑ k, a k * S j k) ⊗ₜ[O] eb j,
    ⟨∑ j, (⟨_, hm j⟩ : ↥W.AΔ) ⊗ₜ ⟨eb j, trivial⟩, by rw [map_sum]; rfl⟩, ?_⟩
  obtain ⟨Λ, hΛ⟩ : IsUnit (algebraMap (LetA O n) W.EE (Eπ ^ h')) := by rw [map_pow]; exact huE.pow _
  have hcan : ∀ z z' : LA W T π' c, algebraMap (LetA O n) W.EE (Eπ ^ h') • z =
      algebraMap (LetA O n) W.EE (Eπ ^ h') • z' → z = z' := by
    intro z z' h
    have := congrArg (fun w => ((Λ⁻¹ : W.EEˣ) : W.EE) • w) h
    simpa only [← hΛ, smul_smul, Units.inv_mul, one_smul] using this
  apply hcan
  have h1 : Ψ (algebraMap (LetA O n) W.EE (Eπ ^ h') • x) =
      ∑ m, (∑ k, (letE c : LetA O n) * a k * R m k) • W.φD T (Bs.b m) := by

    rw [hx', map_sum]
    simp only [hΨ, algebraMap_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_smul.symm
  have h3 : ∀ j, ∑ m, (∑ k, (letE c : LetA O n) * a k * R m k) * P j m =
      algebraMap O (LetA O n) lam * ((letE c : LetA O n) * a j) +
        Eπ ^ h' * (π' ^ M * Eπ ^ (3 * h') * ((letE c : LetA O n) * ∑ k, a k * S j k)) := by
    intro j
    have : ∑ m, (∑ k, (letE c : LetA O n) * a k * R m k) * P j m =
        ∑ k, (letE c : LetA O n) * a k * ∑ m, P j m * R m k := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    simp only [hPR, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum]
    congr 1
    · linear_combination (algebraMap O (LetA O n) lam * a j) * hee
    · exact Finset.sum_congr rfl fun k _ => by ring
  rw [smul_sub, ← map_smul Φ, ← map_smul Ψ, h1, hΦ, smul_comm _ lam x, hx', framepf_smulLA_alg,
    Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h3, ← algebraMap_smul W.EE lam, IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
  simp only [TensorProduct.smul_tmul', smul_eq_mul]
  rw [← TensorProduct.sub_tmul, ← map_mul, ← map_mul, ← map_mul, ← map_sub, add_sub_cancel_left]

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
    {W : LocWach PD LL O v n} {T : LocLat G Qp LL O}
    (Bs : FramepfBas W T) (π' : LetA O n) (c : ZMod n)
    (hπ0 : ∀ j, PowerSeries.constantCoeff (π' j) = 0)
    (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hR2 : ∀ a : LetA O n, a ∈ W.AΔ → ∃! f : ZMod n → PowerSeries O,
      ∀ j, a j = PowerSeries.subst (π' j) (f j))
    (γ0 : ∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π'))

include hπ0 hΔπ γ0 in
theorem framepf_hhx_ι_Δ (i : ZMod n) (g : PowerSeries O) (δ : W.Gam) (hδ : δ ∈ W.DelF) :
    W.γA δ (framepf_ι π' i g) = framepf_ι π' i g := by
  have h := framepf_ι_letγ π' i (hπ0 i) (W.γ₀ δ) (γ0 δ hδ) PowerSeries.X (by simp)
    (by rw [PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' (hπ0 i))];
        exact congrFun (hΔπ δ hδ) i) g
  rw [PowerSeries.X_subst] at h
  exact h

include hπ0 hΔπ γ0 in
theorem framepf_hhx_vec_mem (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (k : Fin Bs.r) :
    framepf_vec Bs π' (c - 1) H k ∈ NcS W T (c - 1) := by
  unfold framepf_vec
  refine Submodule.sum_mem _ fun m _ => ?_
  rw [mem_NcS]
  obtain ⟨hN, hΔ⟩ := Bs.mem m
  refine ⟨(W.N T).smul_mem _ hN, fun δ hδ => ?_, ?_⟩
  · rw [gradNPf_γD_smul, framepf_hhx_ι_Δ π' hπ0 hΔπ γ0 _ _ δ hδ, hΔ δ hδ]
  · rw [smul_smul, framepf_letE_ι π' (c - 1) hπ0]

theorem framepf_hhx_mem (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (ℓ : LcQ W T π' c) :
    framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ ∈ NcS W T (c - 1) := by
  unfold framepf_hh
  rw [LinearMap.comp_apply, Fintype.linearCombination_apply]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (framepf_hhx_vec_mem Bs π' c hπ0 hΔπ γ0 H k)

include hπ0 in
theorem framepf_hhx_vec_pow (i : ZMod n) (Hm : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (M : ℕ)
    (k : Fin Bs.r) :
    framepf_vec Bs π' i ((PowerSeries.X : PowerSeries O) ^ M • Hm) k =
      π' ^ M • framepf_vec Bs π' i Hm k := by
  induction M with
  | zero => rw [pow_zero, pow_zero, one_smul, one_smul]
  | succ M ih => rw [pow_succ', mul_smul, framepf_vec_X_smul Bs π' i hπ0, ih, smul_smul, ← pow_succ']

theorem framepf_hhx_apply (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (ℓ : LcQ W T π' c) :
    framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ =
      ∑ k, framepf_Lbas Bs π' c hπ0 hΔπ hR2 γ0 hu ℓ k • framepf_vec Bs π' (c - 1) H k := by
  unfold framepf_hh
  rw [LinearMap.comp_apply, Fintype.linearCombination_apply]
  rfl

theorem framepf_hhx_γ (Gs : PowerSeries O) (hGs0 : PowerSeries.constantCoeff Gs = 0)
    (hGs : W.γ₀ W.gam (π' (c - 1)) = PowerSeries.subst (π' (c - 1)) Gs)
    (Γ : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O))
    (hΓ : ∀ m, W.γD T W.gam ((letE (c - 1) : LetA O n) • Bs.b m) = framepf_vec Bs π' (c - 1) Γ m)
    (H Km : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (M : ℕ)
    (hH : Γ * H.map (PowerSeries.subst Gs) - H = (PowerSeries.X : PowerSeries O) ^ M • Km)
    (ℓ : LcQ W T π' c) :
    W.γD T W.gam (framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ) - framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ ∈
      PiNS W T π' M := by
  have e : W.γD T W.gam (framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ) -
      framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ = π' ^ M • framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu Km ℓ := by

    rw [framepf_hhx_apply, framepf_hhx_apply, map_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, framepf_γ_vec Bs π' (c - 1) hπ0 Gs hGs0 hGs Γ hΓ, sub_eq_iff_eq_add.1 hH,
      framepf_vec_add Bs π' (c - 1) hπ0, framepf_hhx_vec_pow Bs π' hπ0, smul_add, add_sub_cancel_right,
      smul_comm]
  have hm := (mem_NcS W T (c - 1) _).1 (framepf_hhx_mem Bs π' c hπ0 hΔπ hR2 γ0 hu Km ℓ)
  rw [e, mem_PiNS]
  refine ⟨⟨_, hm.1, rfl⟩, fun δ hδ => ?_⟩
  rw [gradNPf_γD_smul, map_pow, hΔπ δ hδ, hm.2.1 δ hδ]

theorem framepf_hhx_mod (lσ : O) (H Km : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O))
    (hH : H = PowerSeries.C lσ • (1 : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) +
      (PowerSeries.X : PowerSeries O) • Km)
    (z : W.DD T) (hz : z ∈ NcS W T (c - 1)) :
    framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H (mkL W T π' c z hz) - lσ • z ∈ PiNS W T π' 1 := by
  set ℓ := mkL W T π' c z hz with hℓ
  have hv : ∀ k, framepf_coordL Bs π' c hπ0 hΔπ hR2 γ0
      ⟨_, framepf_hhx_vec_mem Bs π' c hπ0 hΔπ γ0 H k⟩ = lσ • Pi.single k 1 := by
    intro k
    have e := framepf_gco_eq Bs π' c hπ0 hΔπ hR2 γ0 ⟨_, framepf_hhx_vec_mem Bs π' c hπ0 hΔπ γ0 H k⟩
      (fun m => H m k) rfl
    funext m
    rw [framepf_coordL_apply, e, hH]
    by_cases hmk : m = k
    · subst hmk; simp
    · simp [Matrix.one_apply_ne hmk, Pi.single_eq_of_ne hmk]
  have hsum : (⟨_, framepf_hhx_mem Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ⟩ : ↥(NcS W T (c - 1))) =
      ∑ k, framepf_Lbas Bs π' c hπ0 hΔπ hR2 γ0 hu ℓ k •
        (⟨_, framepf_hhx_vec_mem Bs π' c hπ0 hΔπ γ0 H k⟩ : ↥(NcS W T (c - 1))) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact framepf_hhx_apply Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ
  have key := (framepf_coordL_ker Bs π' c hπ0 hΔπ hR2 γ0 hu
    (⟨_, framepf_hhx_mem Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ⟩ - lσ • ⟨z, hz⟩)).1 (by

      rw [map_sub, map_smul, hsum, map_sum, ← framepf_Lbas_mk Bs π' c hπ0 hΔπ hR2 γ0 hu ⟨z, hz⟩]
      simp only [map_smul, hv]
      have : Submodule.Quotient.mk (⟨z, hz⟩ : ↥(NcS W T (c - 1))) = ℓ := rfl
      rw [this, sub_eq_zero]
      funext m
      simp [Finset.sum_apply, Pi.single_apply, mul_comm])
  exact key

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
    {W : LocWach PD LL O v n} {T : LocLat G Qp LL O}

theorem framepf_φD_smul (a : LetA O n) (x : W.DD T) : W.φD T (a • x) = W.φA a • W.φD T x := by
  have := W.φD_smul T (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.φE_ext, algebraMap_smul] at this
  exact this

theorem framepf_smulLA_tmul (π' : LetA O n) (c : ZMod n) (a : LetA O n) (e : W.EE)
    (ℓ : LcQ W T π' c) : smulLA W T π' c a (e ⊗ₜ ℓ) = (algebraMap (LetA O n) W.EE a * e) ⊗ₜ ℓ := rfl

theorem framepf_toLA_tmul (π' : LetA O n) (c : ZMod n) (S : Submodule O (LcQ W T π' c)) (a : ↥W.AΔ)
    (s : ↥S) : toLA W T π' c S (a ⊗ₜ s) =
      algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a) ⊗ₜ (s : LcQ W T π' c) := rfl

variable (Bs : FramepfBas W T) (π' : LetA O n) (c : ZMod n)
    (hπ0 : ∀ j, PowerSeries.constantCoeff (π' j) = 0)
    (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hR2 : ∀ a : LetA O n, a ∈ W.AΔ → ∃! f : ZMod n → PowerSeries O,
      ∀ j, a j = PowerSeries.subst (π' j) (f j))
    (γ0 : ∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π'))

include hπ0 hΔπ γ0 in
theorem framepf_ι_Δ (i : ZMod n) (g : PowerSeries O) (δ : W.Gam) (hδ : δ ∈ W.DelF) :
    W.γA δ (framepf_ι π' i g) = framepf_ι π' i g := by
  have h := framepf_ι_letγ π' i (hπ0 i) (W.γ₀ δ) (γ0 δ hδ) PowerSeries.X (by simp)
    (by rw [PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' (hπ0 i))];
        exact congrFun (hΔπ δ hδ) i) g
  rw [PowerSeries.X_subst] at h
  exact h

include hπ0 hΔπ γ0 in
theorem framepf_vec_mem (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (k : Fin Bs.r) :
    framepf_vec Bs π' (c - 1) H k ∈ NcS W T (c - 1) := by
  unfold framepf_vec
  refine Submodule.sum_mem _ fun m _ => ?_
  rw [mem_NcS]
  obtain ⟨hN, hΔ⟩ := Bs.mem m
  refine ⟨(W.N T).smul_mem _ hN, fun δ hδ => ?_, ?_⟩
  · rw [gradNPf_γD_smul, framepf_ι_Δ π' hπ0 hΔπ γ0 _ _ δ hδ, hΔ δ hδ]
  · rw [smul_smul, framepf_letE_ι π' (c - 1) hπ0]

include hπ0 hΔπ γ0 in
theorem framepf_hh_mem (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (ℓ : LcQ W T π' c) :
    framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ ∈ NcS W T (c - 1) := by
  unfold framepf_hh
  rw [LinearMap.comp_apply, Fintype.linearCombination_apply]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (framepf_vec_mem Bs π' c hπ0 hΔπ γ0 H k)

def framepf_Ψα (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) :
    W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T :=
  LinearMap.liftBaseChange W.EE ((W.φD T).comp (framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H))

theorem framepf_Ψα_tmul (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (e : W.EE) (ℓ : LcQ W T π' c) :
    framepf_Ψα Bs π' c hπ0 hΔπ hR2 γ0 hu H (e ⊗ₜ ℓ) =
      e • W.φD T (framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ) := by
  unfold framepf_Ψα
  rw [LinearMap.liftBaseChange_tmul, LinearMap.comp_apply]

theorem framepf_Ψα_smulLA (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (a : LetA O n)
    (x : W.EE ⊗[O] LcQ W T π' c) :
    framepf_Ψα Bs π' c hπ0 hΔπ hR2 γ0 hu H (smulLA W T π' c a x) =
      a • framepf_Ψα Bs π' c hπ0 hΔπ hR2 γ0 hu H x := by
  induction x using TensorProduct.inductionOn with
  | tmul e ℓ =>
    rw [framepf_smulLA_tmul, framepf_Ψα_tmul, framepf_Ψα_tmul, mul_smul, algebraMap_smul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add]


include hπ0 hΔπ γ0 in
theorem framepf_Ψα_toLA (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O))
    (t : ↥W.AΔ ⊗[O] ↥(⊤ : Submodule O (LcQ W T π' c))) :
    framepf_Ψα Bs π' c hπ0 hΔπ hR2 γ0 hu H (toLA W T π' c ⊤ t) ∈ PcS W T c := by
  induction t using TensorProduct.inductionOn with
  | tmul a s =>
    rw [framepf_toLA_tmul, framepf_Ψα_tmul, algebraMap_smul]
    have hh := framepf_hh_mem Bs π' c hπ0 hΔπ hR2 γ0 hu H (s : LcQ W T π' c)
    rw [mem_NcS] at hh
    obtain ⟨hN, hΔ, hl⟩ := hh
    unfold PcS
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · rw [Submodule.restrictScalars_mem]
      apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨_, ?_, rfl⟩
      rw [← hl]
      exact ⟨_, hN, rfl⟩
    · rw [mem_DelS]
      intro δ hδ
      rw [gradNPf_γD_smul, map_mul, ← W.φγ_comm, hΔ δ hδ, a.2 δ hδ, Formalism.MainNotions.LiftingTheory.wmap_γA_letE]
    · rw [mem_letS, smul_smul, ← mul_assoc]
      unfold letE
      rw [← Pi.single_mul, mul_one]
  | add x y hx hy =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ hx hy

variable (Eπ : LetA O n) (hEu : IsUnit (algebraMap (LetA O n) W.EE Eπ))
    (hEΔ : ∀ δ ∈ W.DelF, W.γA δ Eπ = Eπ) (h' M : ℕ)


include hEu hEΔ in
theorem framepf_Lam_cancel {y : W.DD T} (hΔ : ∀ δ ∈ W.DelF, W.γD T δ (Eπ ^ h' • y) = Eπ ^ h' • y)
    (hl : (letE c : LetA O n) • (Eπ ^ h' • y) = Eπ ^ h' • y) :
    (∀ δ ∈ W.DelF, W.γD T δ y = y) ∧ (letE c : LetA O n) • y = y := by
  have hu' : IsUnit (algebraMap (LetA O n) W.EE (Eπ ^ h')) := by rw [map_pow]; exact hEu.pow _
  refine ⟨fun δ hδ => ?_, ?_⟩
  · rw [← sub_eq_zero]
    apply gradNPf_tf W T _ hu'
    have h1 := hΔ δ hδ
    rw [gradNPf_γD_smul, map_pow, hEΔ δ hδ] at h1
    rw [smul_sub, h1, sub_self]
  · rw [← sub_eq_zero]
    apply gradNPf_tf W T _ hu'
    rw [smul_sub, smul_smul, mul_comm, ← smul_smul, hl, sub_self]


include hπ0 hΔπ γ0 hEu hEΔ in
theorem framepf_Ψα_Lam (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (x : W.EE ⊗[O] LcQ W T π' c)
    (hx : x ∈ LamLA W T π' Eπ h' c ⊤) :
    framepf_Ψα Bs π' c hπ0 hΔπ hR2 γ0 hu H x ∈ LamPS W T Eπ h' c := by
  obtain ⟨t, ht⟩ := Submodule.mem_comap.1 hx
  have hP := framepf_Ψα_toLA Bs π' c hπ0 hΔπ hR2 γ0 hu H t
  rw [ht, framepf_Ψα_smulLA] at hP
  unfold PcS at hP
  obtain ⟨hP12, hP3⟩ := Submodule.mem_inf.1 hP
  obtain ⟨hP1, hP2⟩ := Submodule.mem_inf.1 hP12
  rw [mem_DelS] at hP2
  rw [mem_letS] at hP3
  rw [Submodule.restrictScalars_mem] at hP1
  obtain ⟨hΔ, hl⟩ := framepf_Lam_cancel c Eπ hEu hEΔ h' hP2 hP3
  rw [mem_LamPS]
  exact ⟨hP1, hΔ, hl⟩


include hπ0 hΔπ γ0 in
theorem framepf_Ψα_J (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (x : W.EE ⊗[O] LcQ W T π' c)
    (hx : x ∈ JLA W T π' Eπ h' M c) :
    framepf_Ψα Bs π' c hπ0 hΔπ hR2 γ0 hu H x ∈ JP W T π' Eπ h' M c := by
  obtain ⟨z, ⟨t, rfl⟩, rfl⟩ := Submodule.mem_map.1 hx
  rw [framepf_Ψα_smulLA]
  exact Submodule.mem_map.2 ⟨_, framepf_Ψα_toLA Bs π' c hπ0 hΔπ hR2 γ0 hu H t, rfl⟩


end Local

end Formalism.MainNotions.N.Ln34

end
end
