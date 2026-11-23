module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle153
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle496
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle259
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle260
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle261
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle239
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle497
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle484
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenKerFinIdele
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Prism GlobalTheory.PrismS

noncomputable section

namespace GlobalTheory.PrismSplit

theorem isUnit_sub_of_pow_eq_one {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {m : ℕ}
    (hm0 : 0 < m) (hm : IsUnit (m : O)) {a b : O} (ha : a ^ m = 1) (hb : b ^ m = 1) (h : a ≠ b) :
    IsUnit (a - b) := by
  by_contra hn
  have h1 := (Commute.all a b).geom_sum₂_mul m
  rw [ha, hb, sub_self] at h1
  have h2 := (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr h)
  have h3 : IsLocalRing.residue O a = IsLocalRing.residue O b := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hn
  have h4 := congrArg (IsLocalRing.residue O) h2

  simp only [map_sum, map_mul, map_pow, h3, map_zero] at h4
  rw [geom_sum₂_self] at h4
  have hbu : IsUnit b := IsUnit.of_pow_eq_one hb hm0.ne'
  have h5 : IsUnit ((m : IsLocalRing.ResidueField O) * IsLocalRing.residue O b ^ (m - 1)) := by
    refine IsUnit.mul ?_ ((hbu.map _).pow _)
    simpa using hm.map (IsLocalRing.residue O)
  exact h5.ne_zero h4

theorem existsUnique_of_separated {R W O ι : Type} [CommRing R] [Nontrivial R] [CommRing W]
    [CommRing O] [Algebra R W] [Algebra R O] [Fintype ι] [Module.Free R W] [Module.Finite R W]
    (hr : Module.finrank R W = Fintype.card ι) (φ : ι → (W →ₐ[R] O))
    (hs : ∀ i j, i ≠ j → ∃ w, IsUnit (φ i w - φ j w)) {d : ℕ} (o : Module.Basis (Fin d) R O)
    (y : ι → O) : ∃! c : Fin d → W, ∀ k, y k = ∑ i, o i * φ k (c i) := by
  classical
  let F : (Fin d → W) →ₗ[R] (ι → O) :=
    { toFun := fun c k => ∑ i, o i * φ k (c i)
      map_add' := fun c c' => by
        funext k; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r c => by
        funext k; simp [Finset.smul_sum] }
  let Φ : O ⊗[R] W →ₐ[O] (ι → O) :=
    Algebra.TensorProduct.lift (Algebra.ofId O (ι → O)) (AlgHom.pi φ)
      (fun _ _ => Commute.all _ _)
  have hΦ : ∀ (a : O) (w : W) (k : ι), Φ (a ⊗ₜ w) k = a * φ k w := by
    intro a w k
    simp [Φ]
  have h1 : ∀ t, Φ t ∈ LinearMap.range F := by
    intro t
    induction t with
    | add s t hs ht => rw [map_add]; exact add_mem hs ht
    | tmul a w =>
      refine ⟨fun i => o.repr a i • w, ?_⟩
      funext k
      rw [hΦ]
      conv_rhs => rw [← o.sum_repr a]
      rw [Finset.sum_mul]
      simp [F]
  have h2 : ∀ i, Pi.single i (1 : O) ∈ Φ.range := by
    intro i
    choose w hw using hs i
    have : (Pi.single i (1 : O) : ι → O) = ∏ j : {j // i ≠ j}, (((hw j.1 j.2).unit⁻¹ : Oˣ) : O) •
        (Φ (1 ⊗ₜ w j.1 j.2) - algebraMap O (ι → O) (φ j.1 (w j.1 j.2))) := by
      funext k
      rw [Finset.prod_apply]
      by_cases hk : i = k
      · subst hk
        rw [Pi.single_eq_same, eq_comm]
        refine Finset.prod_eq_one fun j _ => ?_
        simp [hΦ]
      · rw [Pi.single_eq_of_ne (Ne.symm hk), eq_comm]
        refine Finset.prod_eq_zero (Finset.mem_univ ⟨k, hk⟩) ?_
        simp [hΦ]
    rw [this]
    refine Subalgebra.prod_mem _ fun j _ => Subalgebra.smul_mem _ (sub_mem (AlgHom.mem_range_self Φ _) ?_) _
    exact Subalgebra.algebraMap_mem _ _
  have h3 : Function.Surjective F := by
    intro y
    have : y ∈ Φ.range := by
      rw [← Finset.univ_sum_single y]
      refine sum_mem fun i _ => ?_
      have : (Pi.single i (y i) : ι → O) = y i • (Pi.single i (1 : O) : ι → O) := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      rw [this]
      exact Subalgebra.smul_mem _ (h2 i) _
    obtain ⟨t, rfl⟩ := this
    exact h1 t
  have : Module.Free R O := Module.Free.of_basis o
  have : Module.Finite R O := Module.Finite.of_basis o
  have e : (Fin d → W) ≃ₗ[R] (ι → O) := LinearEquiv.ofFinrankEq _ _ (by
    simp [Module.finrank_pi_fintype, hr, Module.finrank_eq_card_basis o, mul_comm])
  have h4 : Function.Injective F :=
    OrzechProperty.injective_of_surjective_of_injective e.toLinearMap F e.injective h3
  obtain ⟨c, hc⟩ := h3 y
  refine ⟨c, fun k => (congrFun hc k).symm, fun c' hc' => h4 ?_⟩
  rw [hc]
  exact funext fun k => (hc' k).symm

theorem exists_root_ne {l : ℕ} [Fact l.Prime] {K LL : FinExt l}
    {e e' : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1} (h : e ≠ e') :
    ∃ (ω : ↥(K0 K)) (m : ℕ), 0 < m ∧ ¬ l ∣ m ∧ ω ^ m = 1 ∧ e ω ≠ e' ω := by
  by_contra hn
  push Not at hn
  apply h
  ext1 x
  obtain ⟨a, ha⟩ := NormedField.exists_lt_norm ℚ_[l] ‖(x : Om l)‖
  have ha0 : 0 < ‖a‖ := (norm_nonneg _).trans_lt ha
  have ha1 : a ≠ 0 := norm_pos_iff.mp ha0
  obtain ⟨n, z, ω, hω, hx⟩ := GlobalTheory.UnramSpan.exists_sum_rootsOfUnity l K
    (algebraMap ℚ_[l] (Om l) a⁻¹ * x) (algebraMap ℚ_[l] ↥(K0 K) a⁻¹ * x).2 (by
      rw [← Algebra.smul_def, norm_smul, norm_inv, inv_mul_le_iff₀ ha0, mul_one]
      exact ha.le)
  have hx' : algebraMap ℚ_[l] ↥(K0 K) a⁻¹ * x =
      ∑ i, algebraMap ℚ_[l] ↥(K0 K) (z i : ℚ_[l]) * (⟨ω i, (hω i).1⟩ : ↥(K0 K)) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact hx
  have : e (algebraMap ℚ_[l] ↥(K0 K) a⁻¹ * x) = e' (algebraMap ℚ_[l] ↥(K0 K) a⁻¹ * x) := by

    rw [hx', map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨m, hm, hl, h1⟩ := (hω i).2
    rw [map_mul, map_mul, e.commutes, e'.commutes, hn _ m hm hl (Subtype.ext (by simpa using h1))]
  rw [map_mul, map_mul, e.commutes, e'.commutes] at this
  exact mul_left_cancel₀ ((_root_.map_ne_zero _).mpr (inv_ne_zero ha1)) this

theorem isUnit_natCast {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] {m : ℕ}
    (hl : ¬ l ∣ m) : IsUnit (m : O) := by
  have hu : IsUnit (m : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => hl ?_)
    have := (PadicInt.norm_int_lt_one_iff_dvd (p := l) (m : ℤ)).mp (by simpa using h)
    exact_mod_cast this
  simpa using hu.map (algebraMap ℤ_[l] O)

theorem exists_isUnit_sub {l : ℕ} [Fact l.Prime] {K LL : FinExt l}
    {e e' : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1} (h : e ≠ e') : ∃ w, IsUnit (embW e w - embW e' w) := by
  obtain ⟨_, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  obtain ⟨ω, m, hm, hl, h1, hne⟩ := exists_root_ne h
  have hi : IsIntegral ℤ_[l] ω := IsIntegral.of_pow hm (by rw [h1]; exact isIntegral_one)
  have hp : ∀ f : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1, embW f ⟨ω, hi⟩ ^ m = 1 := by
    intro f
    apply Subtype.ext
    change f ω ^ m = 1
    rw [← map_pow, h1, map_one]
  exact ⟨⟨ω, hi⟩, isUnit_sub_of_pow_eq_one hm (isUnit_natCast _ hl) (hp e) (hp e')
    fun h => hne (congrArg Subtype.val h)⟩

theorem existsUnique_coords : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (emb : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)), Function.Injective emb → ∀ (d : ℕ) (o : Module.Basis (Fin d) ℤ_[l] ↥(OL LL)) (y : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL)), ∃! c : Fin d → WK K, ∀ k, y k = ∑ i, o i * embW (emb k) (c i) := by
  intro l _ K LL emb hemb d o y
  have hfd : FiniteDimensional ℚ_[l] ↥(K0 K) := (unr K).2
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨_, -, -, -, hfree, hfin, -⟩ := GlobalTheory.Per.integers_completeDVR l (unr K)
  have : Module.IsTorsionFree ℤ_[l] ↥(K0 K) := by
    rw [Module.isTorsionFree_iff_faithfulSMul, faithfulSMul_iff_algebraMap_injective,
      IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥(K0 K)]
    exact (algebraMap ℚ_[l] ↥(K0 K)).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  refine existsUnique_of_separated ?_ (fun k => embW (emb k)) ?_ o y
  · rw [ZMod.card]
    exact IsIntegralClosure.rank ℤ_[l] ℚ_[l] ↥(K0 K) (integralClosure ℤ_[l] ↥(K0 K))
  · exact fun i j hij => exists_isUnit_sub (hemb.ne hij)

end GlobalTheory.PrismSplit
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DeRhamSymbolBasis

open GlobalTheory.DeRhamSymbol

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (J : ThetaL P AI)

theorem theta_zero : J.θ 0 = 0 := by
  have h := J.θ_add 0 (zero_mem _) 0 (zero_mem _)
  rw [add_zero] at h
  simpa using h

theorem theta_sum {ι : Type} (s : Finset ι) (f : ι → P.R.BdR)
    (hf : ∀ i, f i ∈ (P.PD (botExt l)).Fil 0) : J.θ (∑ i ∈ s, f i) = ∑ i ∈ s, J.θ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using theta_zero J
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      J.θ_add _ (hf a) _ (Submodule.sum_mem _ fun i _ => hf i), ih]

theorem om_mul_mem (c : Om l) {x : P.R.BdR} (hx : x ∈ (P.PD (botExt l)).Fil 0) :
    algebraMap (Om l) P.R.BdR c * x ∈ (P.PD (botExt l)).Fil 0 := by
  simpa using (P.PD (botExt l)).Fil_mul _ _ _ _ (om_mem c) hx

theorem theta_comb {n : ℕ} (c : Fin n → Om l) (f : Fin n → P.R.BdR)
    (hf : ∀ i, f i ∈ (P.PD (botExt l)).Fil 0) :
    J.θ (∑ i, algebraMap (Om l) P.R.BdR (c i) * f i) = ∑ i, (c i : PadicComplex l) * J.θ (f i) := by
  rw [theta_sum J _ _ fun i => om_mul_mem (c i) (hf i)]
  exact Finset.sum_congr rfl fun i _ => by rw [J.θ_mul _ (om_mem _) _ (hf i), J.θ_Om]

omit J in
theorem shift_act (a : ℤ) (g : GQ l) (x : P.R.BdR) :
    ((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * P.actQdR g x =
      algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) *
        P.actQdR g (((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * x) := by
  rw [map_mul, DeRhamSymbol.act_zpow, ← mul_assoc, ← mul_assoc,
    ← map_mul, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one,
    map_one, one_mul]

omit J in
theorem exists_adapted {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {d : ℕ} (b : Module.Basis (Fin d) Qp V)
    (hL : FiniteDimensional Qp LL) (hV : FiniteDimensional LL V) (hDR : IsDR PD ρ) :
    ∃ (x : Fin d → Fin d → BdR) (u : Fin d → ℤ), (∀ k, (∀ g : G, (Matrix.of fun i j =>
      algebraMap Qp BdR (b.repr (ρ g (b j)) i)).mulVec (fun i => PD.actdR g (x k i)) = x k) ∧
      ∀ i, x k i ∈ PD.Fil (u k)) ∧ ∀ (a : ℤ) (c : Fin d → K), (∀ k, u k ≠ a → c k = 0) →
      (∀ i, ∑ k, algebraMap K BdR (c k) * x k i ∈ PD.Fil (a + 1)) → ∀ k, c k = 0 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨Fin.elim0, Fin.elim0, fun k => k.elim0, fun _ _ _ _ k => k.elim0⟩
  haveI : Nontrivial V := ⟨⟨b ⟨0, hd⟩, 0, b.ne_zero _⟩⟩
  haveI := PD.finK
  have hfin : Module.Finite LL ↥(DdR PD ρ) := by
    apply Module.finite_of_finrank_pos
    rw [hDR]
    exact Nat.mul_pos Module.finrank_pos Module.finrank_pos
  obtain ⟨Φ, -, hΦ⟩ := GlobalTheory.exists_coord_tensor_dR PD ρ b
  obtain ⟨D, hD, hDf, hDr⟩ := GlobalTheory.deRham_invariants_coord_finrank PD ρ b hL hfin hDR Φ hΦ
  obtain ⟨x, u, hx, hind⟩ := GlobalTheory.exists_family_adapted_filtration K (Fin d → BdR) D
    (fun a => Submodule.pi Set.univ fun _ => PD.Fil a) d hDf hDr
    (fun a z hz i hi => PD.Fil_anti a (hz i hi))
    (fun z => by
      have anti : Antitone PD.Fil := antitone_int_of_succ_le PD.Fil_anti
      choose f hf using fun i => PD.Fil_exh (z i)
      obtain ⟨m, hm⟩ := (Set.finite_range f).bddBelow
      exact ⟨m, fun i _ => anti (hm ⟨i, rfl⟩) (hf i)⟩)
    (fun z hz => funext fun i => PD.Fil_sep _ fun a => hz a i trivial)
  refine ⟨x, u, fun k => ⟨(hD _).1 (hx k).1, fun i => (hx k).2 i trivial⟩, fun a c hc hs => ?_⟩
  refine hind a c hc fun i _ => ?_
  have := hs i
  simp only [← Algebra.smul_def] at this
  simpa only [Finset.sum_apply, Pi.smul_apply, SetLike.mem_coe] using this

omit J in
theorem sum_mem_DdR {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {d : ℕ} (b : Module.Basis (Fin d) Qp V) (x : Fin d → BdR)
    (hx : ∀ g : G, (Matrix.of fun i j =>
      algebraMap Qp BdR (b.repr (ρ g (b j)) i)).mulVec (fun i => PD.actdR g (x i)) = x) :
    ∑ i, b i ⊗ₜ[Qp] x i ∈ DdR PD ρ := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero]
  intro g
  have hact : ∀ (v : V) (y : BdR),
      actVdR PD ρ g (v ⊗ₜ y) = ρ g v ⊗ₜ PD.actdR g y := by
    intro v y
    unfold actVdR
    rw [TensorProduct.AlgebraTensorModule.map_tmul]
    rfl
  obtain ⟨Φ, h, -⟩ := GlobalTheory.exists_tensor_coord_of_basis (M := BdR) b
  apply Φ.injective
  funext i

  rw [map_sum, map_sum, map_sum, Finset.sum_apply, Finset.sum_apply]
  simp only [hact, h, Module.Basis.repr_self]
  have h1 := congrFun (hx g) i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, ← Algebra.smul_def] at h1
  rw [h1, Finset.sum_eq_single i]
  · simp
  · intro j _ hij
    simp [Finsupp.single_apply, hij]
  · simp


omit J in
theorem exists_symbol_basis : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (θ : ThetaL P AI) (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsDR (P.PD K) T.ρ → ∀ (d : ℕ) (b : Module.Basis (Fin d) ℚ_[l] T.V) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)), (∀ (g : ↥(GK K)) (i j : Fin d), M (g : GQ l) i j = algebraMap ℚ_[l] (PadicComplex l) (b.repr (T.ρ g (b j)) i)) → ∀ t : (P.R.BdR)ˣ, (t : P.R.BdR) = P.ιB P.tB → ∃ (u : Fin d → ℤ) (y : Fin d → Fin d → P.R.BdR), (∀ k i, y k i ∈ (P.PD K).Fil 0) ∧ (∀ k, ∑ i, b i ⊗ₜ[ℚ_[l]] (y k i * ((t ^ u k : (P.R.BdR)ˣ) : P.R.BdR)) ∈ DdR (P.PD K) T.ρ) ∧ LinearIndependent (PadicComplex l) (fun k i => θ.θ (y k i)) ∧ ∀ σ ∈ GK K, ∀ k, twAct AI.actC P.χQ (u k) M σ (fun i => θ.θ (y k i)) = fun i => θ.θ (y k i) := by
  intro l _ P AI J K LL T hDR d b M hM t ht
  obtain rfl : t = tU P := Units.ext ht
  obtain ⟨x, u, hx, hind⟩ := exists_adapted (P.PD K) T.ρ b LL.2 T.fdim hDR
  have key : ∀ k i, ((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k i ∈ (P.PD (botExt l)).Fil 0 :=
    fun k i => (shift_iff J (u k) 0 _).2 (by
      rw [add_zero]; exact (mem_iff K _ _).1 ((hx k).2 i))
  have heq : ∀ σ ∈ GK K, ∀ k, twAct AI.actC P.χQ (u k) M σ
      (fun i => J.θ (((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k i)) =
      fun i => J.θ (((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k i) := by
    intro σ hσ k
    funext i
    generalize hN : (fun i j => b.repr (T.ρ ⟨σ, hσ⟩ (b j)) i : Fin d → Fin d → ℚ_[l]) = N
    have hN' : ∀ i j, b.repr (T.ρ ⟨σ, hσ⟩ (b j)) i = N i j := fun i j => congrFun (congrFun hN i) j
    have h1 := congrFun ((hx k).1 ⟨σ, hσ⟩) i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, P.PD_actdR, hN'] at h1
    have h2 : ((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k i =
        ∑ j, algebraMap (Om l) P.R.BdR (algebraMap ℚ_[l] (Om l)
          (((P.χQ σ ^ u k : ℚ_[l]ˣ) : ℚ_[l]) * N i j)) *
          P.actQdR σ (((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k j) := by
      conv_lhs => rw [← h1]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_left_comm, shift_act, ← IsScalarTower.algebraMap_apply,
        map_mul (algebraMap ℚ_[l] P.R.BdR), mul_left_comm, mul_assoc]
    conv_rhs => rw [h2, theta_comb J _ _ fun j => act_mem σ (key k j)]
    simp only [twAct, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [J.θ_act σ _ (key k j), hM ⟨σ, hσ⟩ i j, hN', ← mul_assoc, chiC, ← map_mul]
    rfl
  refine ⟨u, fun k i => ((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k i,
    fun k i => (mem_iff K _ _).2 (key k i), fun k => ?_, ?_, heq⟩
  · have : ∀ i, ((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k i *
        ((tU P ^ u k : P.R.BdRˣ) : P.R.BdR) = x k i := fun i => by
      rw [mul_right_comm, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one,
        one_mul]
    simp only [this]
    exact sum_mem_DdR (P.PD K) T.ρ b _ (hx k).1
  · refine GlobalTheory.SerreTateIndep.linearIndependent_of_weightwise l AI.actC P.χQ (GK K) K.1
      (tate_invariants_twist l AI.actC P.χQ ⟨AI.actC_ext, AI.actC_norm⟩ P.χQ_cyc K) d d M _ u heq ?_
    intro a c hc hs
    refine hind a c hc fun i => ?_
    have h1 := congrFun hs i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
    rw [← theta_comb J (fun k => ((c k : ↥K.1) : Om l)) _ (fun k => key k i),
      J.θ_ker _ (Submodule.sum_mem _ fun k _ => om_mul_mem _ (key k i))] at h1
    rw [mem_iff K, ← shift_iff J, Finset.mul_sum]
    convert h1 using 2 with k
    by_cases hk : u k = a
    · rw [hk, mul_left_comm]
      rfl
    · simp [hc k hk]

end GlobalTheory.DeRhamSymbolBasis
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory

namespace GlobalTheory.CellDec

theorem isCompact_unip_entries_mem :
    ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (C : Set (Ad E)), IsCompact C →
    IsCompact {g : GA E n | g ∈ GlobalTheory.CellDec.NA E n ∧ ∀ i j : Fin n, i < j → (g : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ C} := by
  intro E _ _ n C hC
  classical
  let S : Fin n → Fin n → Set (Ad E) := fun i j => if j < i then {0} else if i = j then {1} else C
  let P : Set (Matrix (Fin n) (Fin n) (Ad E)) := Set.univ.pi fun i => Set.univ.pi (S i)
  have hP : IsCompact P := by
    refine isCompact_univ_pi fun i => isCompact_univ_pi fun j => ?_
    simp only [S]
    split_ifs
    · exact isCompact_singleton
    · exact isCompact_singleton
    · exact hC
  have memP : ∀ M : Matrix (Fin n) (Fin n) (Ad E), M ∈ P ↔
      (∀ i j, j < i → M i j = 0) ∧ (∀ i, M i i = 1) ∧ ∀ i j, i < j → M i j ∈ C := by
    intro M
    change (∀ i ∈ Set.univ, ∀ j ∈ Set.univ, M i j ∈ S i j) ↔ _
    simp only [S]
    constructor
    · intro h
      refine ⟨fun i j hji => ?_, fun i => ?_, fun i j hij => ?_⟩
      · have := h i trivial j trivial; rw [if_pos hji] at this; exact this
      · have := h i trivial i trivial; rw [if_neg (lt_irrefl i), if_pos rfl] at this; exact this
      · have := h i trivial j trivial; rw [if_neg (not_lt.2 hij.le), if_neg hij.ne] at this; exact this
    · rintro ⟨h0, h1, hc⟩ i - j -
      split_ifs with hji hij
      · exact h0 i j hji
      · subst hij; exact h1 i
      · exact hc i j (lt_of_le_of_ne (not_lt.1 hji) hij)
  have hdet : ∀ M ∈ P, M.det = 1 := by
    intro M hM
    obtain ⟨h0, h1, -⟩ := (memP M).1 hM
    rw [Matrix.det_of_isUpperTriangular (fun i j hji => h0 i j hji)]
    simp [h1]
  rw [Units.isEmbedding_embedProduct.isCompact_iff]
  have key : (Units.embedProduct (Matrix (Fin n) (Fin n) (Ad E))) ''
      {g : GA E n | g ∈ GlobalTheory.CellDec.NA E n ∧ ∀ i j : Fin n, i < j → (g : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ C} =
      (fun M => (M, MulOpposite.op M.adjugate)) '' P := by
    ext x
    constructor
    · rintro ⟨g, ⟨hN, hc⟩, rfl⟩
      obtain ⟨h0, h1⟩ := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hN
      have hgP : (g : Matrix (Fin n) (Fin n) (Ad E)) ∈ P := (memP _).2 ⟨h0, h1, hc⟩
      refine ⟨g, hgP, ?_⟩
      have hadj : (g : Matrix (Fin n) (Fin n) (Ad E)).adjugate = ((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) := by
        calc (g : Matrix (Fin n) (Fin n) (Ad E)).adjugate
            = (((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) * g) * (g : Matrix (Fin n) (Fin n) (Ad E)).adjugate := by
              rw [Units.inv_mul, Matrix.one_mul]
          _ = ((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) * ((g : Matrix (Fin n) (Fin n) (Ad E)) * (g : Matrix (Fin n) (Fin n) (Ad E)).adjugate) := by
              rw [Matrix.mul_assoc]
          _ = ((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) := by
              rw [Matrix.mul_adjugate, hdet _ hgP, one_smul, Matrix.mul_one]
      simp only [Units.embedProduct_apply, hadj]
    · rintro ⟨M, hM, rfl⟩
      have hd := hdet M hM
      let g : GA E n := ⟨M, M.adjugate, by rw [Matrix.mul_adjugate, hd, one_smul],
        by rw [Matrix.adjugate_mul, hd, one_smul]⟩
      obtain ⟨h0, h1, hc⟩ := (memP M).1 hM
      refine ⟨g, ⟨(GlobalTheory.SmGL.mem_unipB (Ad E)).2 ⟨h0, h1⟩, hc⟩, ?_⟩
      rfl
  rw [key]
  exact hP.image (continuous_id.prodMk (MulOpposite.continuous_op.comp continuous_id.matrix_adjugate))

end GlobalTheory.CellDec
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.TiedDual

theorem tied_isCrys_dual : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → (∀ (K : FinExt l) (b : P.R.B), b ≠ 0 → (∀ g ∈ GK K, ∃ x : ℚ_[l], P.actQ g b = x • b) → IsUnit b) → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → IsCrys (P.PD K) ρ.dual := by
  intro l _ P AI T hreg K LL V _ _ _ _ _ ρ hρ
  have := LL.2
  have : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T K
  have e : ∀ (g : ↥(GK K)) z, (P.PD K).actB g z = P.actQ g z := fun g z => P.PD_actB K g z
  have hf : GlobalTheory.RegularRing.FracInv (P.PD K) := by
    intro x y hx h
    refine GlobalTheory.Per.FracInv.tied_frac_invariant l P AI T K y x hx fun g hg => ?_
    have h1 := h ⟨g, hg⟩
    rw [e, e] at h1
    rw [mul_comm, h1, mul_comm]
  have hu : GlobalTheory.RegularRing.LineUnit (P.PD K) := by
    intro b hb h
    refine hreg K b hb fun g hg => ?_
    obtain ⟨x, hx⟩ := h ⟨g, hg⟩
    exact ⟨x, by rw [← e ⟨g, hg⟩, hx, Algebra.smul_def]⟩
  exact GlobalTheory.RegularRing.dualCrys (P.PD K) ↥LL.1 hf hu V ρ hρ

end GlobalTheory.Per.TiedDual
end
