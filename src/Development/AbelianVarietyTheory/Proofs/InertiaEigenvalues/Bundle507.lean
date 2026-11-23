module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterPairingHarishChandraCuspidalMackey
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle316
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle480
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle450
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle473
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle481
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockCharactersCrystallineOfRules
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle494
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle500
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle159
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle484
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle499
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle292
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

noncomputable section

namespace GlobalTheory.GLq.DetRoot

open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem ip_list_sum_left {G : Type} [Group G] [Fintype G] (L : List (G → ℂ)) (B : G → ℂ) :
    ip L.sum B = (L.map fun ρ => ip ρ B).sum := by
  induction L with
  | nil => simp [ip]
  | cons ρ L ih =>
    rw [List.sum_cons, List.map_cons, List.sum_cons, ← ih]
    unfold ip
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem list_nat_sum {G : Type} [Group G] [Fintype G] (L : List (G → ℂ)) (hL : ∀ ρ ∈ L, IsIrr ρ) (B : G → ℂ)
    (hB : IsChar B) : ∃ N : ℕ, (L.map fun ρ => ip ρ B).sum = N ∧ ∀ ρ ∈ L, ip ρ B ≠ 0 → N ≠ 0 := by
  induction L with
  | nil => exact ⟨0, by simp, by simp⟩
  | cons ρ L ih =>
    obtain ⟨N, hN, hN0⟩ := ih (fun σ hσ => hL σ (List.mem_cons_of_mem _ hσ))
    obtain ⟨k, hk⟩ := GlobalTheory.GLq.LabelMul.ip_nat (hL ρ List.mem_cons_self) hB
    refine ⟨k + N, by simp [hN, hk], ?_⟩
    intro σ hσ h0
    rcases List.mem_cons.1 hσ with rfl | hσ
    · rw [hk] at h0
      have : k ≠ 0 := by exact_mod_cast h0
      omega
    · have := hN0 σ hσ h0
      omega

theorem ip_ne_zero_of_common {G : Type} [Group G] [Fintype G] {ψ A B : G → ℂ} (hψ : IsIrr ψ) (hA : IsChar A)
    (hB : IsChar B) (hψA : ip ψ A ≠ 0) (hψB : ip ψ B ≠ 0) : ip A B ≠ 0 := by
  obtain ⟨L, hL, rfl⟩ := (GlobalTheory.T.character_decomposition_and_classFunction_expansion G A).1 hA
  rw [GlobalTheory.GLq.LabelMul.ip_sum_eq_count hψ L hL] at hψA
  have hm : ψ ∈ L := List.count_pos_iff.1 (Nat.pos_of_ne_zero (by exact_mod_cast hψA))
  obtain ⟨N, hN, hN0⟩ := list_nat_sum L hL B hB
  rw [ip_list_sum_left, hN]
  exact_mod_cast hN0 ψ hm hψB

theorem ip_add_ne_zero {G : Type} [Group G] [Fintype G] {ψ X Y : G → ℂ} (hψ : IsIrr ψ) (hX : IsChar X)
    (hY : IsChar Y) (h : ip ψ X ≠ 0) : ip ψ (X + Y) ≠ 0 := by
  rw [GlobalTheory.GLq.LabelMul.ip_add_right]
  obtain ⟨k, hk⟩ := GlobalTheory.GLq.LabelMul.ip_nat hψ hX
  obtain ⟨l, hl⟩ := GlobalTheory.GLq.LabelMul.ip_nat hψ hY
  rw [hk] at h
  have hk0 : k ≠ 0 := by exact_mod_cast h
  rw [hk, hl]
  exact_mod_cast (show k + l ≠ 0 by omega)

theorem isChar_hcL_cusp (K : List (Pc g)) (hK : ∀ p ∈ K, IsCusp p.2) (m : ℕ) (hm : degL K = m) :
    IsChar (hcL K m) :=
  (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g K K m hm.symm (fun p hp => GlobalTheory.GLq.IpCuspProd.isChar_of_isCusp (hK p hp))).1

theorem ip_hc_left (m : ℕ) (ψ : Gn g (m + 1) → ℂ) (hψ : IsIrr ψ) (σ : Gn g m → ℂ) (hσ : IsIrr σ)
    (β : Gn g 1 → ℂ) (hβ : IsChar β) (K : List (Pc g)) (hK : ∀ p ∈ K, IsCusp p.2) (hd : degL K = m)
    (hσK : ip σ (hcL K m) ≠ 0) (h : ip ψ (hc m 1 σ β (m + 1)) ≠ 0) : ip ψ (hc m 1 (hcL K m) β (m + 1)) ≠ 0 := by
  obtain ⟨R, hR, he⟩ := GlobalTheory.GLq.LabelMul.exists_add_of_ip_ne_zero hσ (isChar_hcL_cusp K hK m hd) hσK
  rw [he, GlobalTheory.GLq.LabelMul.hc_add_left]
  have hc := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g m 1 (m + 1) rfl).1
  exact ip_add_ne_zero hψ (hc σ β (GlobalTheory.GLq.LabelMul.isChar_of_isIrr hσ) hβ) (hc R β hR hβ) h

theorem ip_hc_right (m : ℕ) (ψ : Gn g (m + 1) → ℂ) (hψ : IsIrr ψ) (σ : Gn g m → ℂ) (hσ : IsIrr σ)
    (β : Gn g 1 → ℂ) (hβ : IsChar β) (K : List (Pc g)) (hK : ∀ p ∈ K, IsCusp p.2) (hd : degL K = m)
    (hσK : ip σ (hcL K m) ≠ 0) (h : ip ψ (hc 1 m β σ (m + 1)) ≠ 0) : ip ψ (hc 1 m β (hcL K m) (m + 1)) ≠ 0 := by
  obtain ⟨R, hR, he⟩ := GlobalTheory.GLq.LabelMul.exists_add_of_ip_ne_zero hσ (isChar_hcL_cusp K hK m hd) hσK
  rw [he, GlobalTheory.GLq.LabelMul.hc_add_right]
  have hc := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g 1 m (m + 1) (by omega)).1
  exact ip_add_ne_zero hψ (hc β σ hβ (GlobalTheory.GLq.LabelMul.isChar_of_isIrr hσ)) (hc β R hβ hR) h

theorem eq_of_isCuspOf_det (L : LabelDatum g) (θ : (ZMod g)ˣ →* ℂˣ) (c : ZMod g) (h : GlobalTheory.GLp.IsCharLab L θ c)
    (P : (ZMod g)[X])
    (hP : IsCuspOf L P (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ))) : P = X - C c := by
  obtain ⟨⟨hm, -, h0, hdeg⟩, -, hf⟩ := hP
  have hPe : P = X - C (-P.coeff 0) := by
    rw [map_neg, sub_neg_eq_add]; exact hm.eq_X_add_C hdeg
  have hc'0 : -P.coeff 0 ≠ 0 := neg_ne_zero.2 h0
  obtain ⟨u, hu⟩ := GlobalTheory.GLq.LabelDet.gen_one_mem L
  let y : Gn g 1 := Units.map (Matrix.scalar (Fin 1) : ZMod g →+* Mt g 1).toMonoidHom u
  have hy00 : (y : Mt g 1) 0 0 = u := by simp [y]
  have hcp : (y : Mt g 1).charpoly = X - C ((y : Mt g 1) 0 0) := by
    simp [Matrix.charpoly, Matrix.det_fin_one]
  have hx : algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (-P.coeff 0) ∈ Formalism.CyclotomicNorms.rootsBar P := by
    rw [hPe]; simp [Formalism.CyclotomicNorms.rootsBar]
  have hz : L.gen 1 ∈ Formalism.CyclotomicNorms.rootsBar (y : Mt g 1).charpoly := by
    rw [hcp, hy00, ← hu]; simp [Formalism.CyclotomicNorms.rootsBar]
  have hirr : Irreducible (y : Mt g 1).charpoly := by rw [hcp]; exact irreducible_X_sub_C _
  have key := hf _ hx y hirr _ hz
  have hxp : (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (-P.coeff 0)) ^ (g ^ 1 - 1) = 1 := by
    rw [← map_pow, pow_one, ZMod.pow_card_sub_one_eq_one hc'0, map_one]
  have hth := GlobalTheory.GLq.LabelDet.theta_gen_pow L hxp 1
  rw [pow_one, pow_one] at hth
  have hdet : Matrix.GeneralLinearGroup.det y = u := by ext; simp [y, Matrix.det_fin_one]
  simp only [hdet, Nat.sub_self, pow_zero, one_mul, Finset.sum_range_one, pow_one, hth] at key
  rw [h.2 u hu] at key
  have := L.teich_inj _ _ ((_root_.map_ne_zero _).2 h.1) ((_root_.map_ne_zero _).2 hc'0) key
  rw [hPe, (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective this]

end GlobalTheory.GLq.DetRoot

namespace GlobalTheory.GLq.DetRoot

open scoped Classical

theorem root_of_hc_det : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (n : ℕ) (ψ : Gn g (n + 1) → ℂ) (f : (ZMod g)[X]),
    IsIrr ψ → HasLabel L ψ f → ∀ (σ : Gn g n → ℂ), IsIrr σ → ∀ (θ : (ZMod g)ˣ →* ℂˣ) (c : ZMod g),
    GlobalTheory.GLp.IsCharLab L θ c →
    (ip ψ (hc n 1 σ (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (n + 1)) ≠ 0 → f.IsRoot c) ∧
    (ip ψ (hc 1 n (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) σ (n + 1)) ≠ 0 → f.IsRoot c) := by
  intro g _ L n ψ f hψ hL σ hσ θ c hlab
  obtain ⟨Q, hQ, hQd, rfl, hQi⟩ := hL
  obtain ⟨K, hK, hKd, hKi⟩ := GlobalTheory.GLq.SuppCusp.exists_cusp_list g n σ hσ
  subst hKd
  have hβI : IsIrr (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) :=
    GlobalTheory.GLq.LabelDet.isIrr_hom (θ.comp Matrix.GeneralLinearGroup.det)
  have hβC := GlobalTheory.GLq.LabelMul.isChar_of_isIrr hβI
  have hβcusp : IsCusp (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) :=
    ⟨one_pos, hβI, fun a h1 h2 => by omega⟩
  have hQc : ∀ p ∈ Q.map Prod.snd, IsCusp p.2 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact (hQ q hq).2.1
  have hA := isChar_hcL_cusp _ hQc _ hQd

  have fin : ∀ K' : List (Pc g), (Q.map Prod.snd).Perm K' →
      (⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g) ∈ K' →
      ((Q.map Prod.fst).prod).IsRoot c := by
    intro K' hp hm
    obtain ⟨⟨P, s⟩, hq, hs⟩ := List.mem_map.1 (hp.mem_iff.2 hm)
    dsimp only at hs
    subst hs
    have hP := eq_of_isCuspOf_det L θ c hlab P (hQ _ hq)
    have hdvd : P ∣ (Q.map Prod.fst).prod := List.dvd_prod (List.mem_map.2 ⟨_, hq, rfl⟩)
    exact Polynomial.IsRoot.dvd (by rw [hP]; exact root_X_sub_C.2 rfl) hdvd
  have hbc : ∀ p ∈ [(⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g)], IsCusp p.2 := by
    intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    exact hβcusp
  have hKc := fun p hp => GlobalTheory.GLq.IpCuspProd.isChar_of_isCusp (hK p hp)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h2 := ip_hc_left _ ψ hψ σ hσ _ hβC K hK rfl hKi h
    have e2 : hc (degL K) 1 (hcL K (degL K))
        (hcL [(⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g)] 1) (degL K + 1) =
        hcL (K ++ [(⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g)]) (degL K + 1) :=
      (GlobalTheory.GLq.LabelMul.hcL_append K _ hKc (fun p hp => GlobalTheory.GLq.IpCuspProd.isChar_of_isCusp (hbc p hp))
        (degL K + 1) (by simp [degL])).symm
    rw [GlobalTheory.GLq.IpCuspProd.hcL_single 1 _ (GlobalTheory.GLq.IpCuspProd.isClass_of_isChar hβC)] at e2
    rw [e2] at h2
    have hKd' : degL (K ++ [(⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g)]) =
        degL K + 1 := by simp [degL]
    have hB := isChar_hcL_cusp _ (fun p hp => by
      rcases List.mem_append.1 hp with hp | hp
      · exact hK p hp
      · exact hbc p hp) _ hKd'
    have hAB := ip_ne_zero_of_common hψ hA hB hQi h2
    refine fin (K ++ [(⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g)]) ?_
      (List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl)))
    by_contra hn
    exact hAB ((GlobalTheory.GLq.IpCuspProd.ip_hcL_cusp g _ _ _ hQd hKd' hQc (fun p hp => by
      rcases List.mem_append.1 hp with hp | hp
      · exact hK p hp
      · exact hbc p hp)).1 hn)
  · have h2 := ip_hc_right _ ψ hψ σ hσ _ hβC K hK rfl hKi h
    have e2 : hc 1 (degL K) (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (hcL K (degL K))
        (degL K + 1) =
        hcL ((⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g) :: K) (degL K + 1) :=
      (hcL_cons (⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g) K (degL K + 1)).symm
    rw [e2] at h2
    have hKd' : degL ((⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g) :: K) =
        degL K + 1 := by simp [degL]; omega
    have hKc' : ∀ p ∈ (⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g) :: K,
        IsCusp p.2 := by
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hβcusp
      · exact hK p hp
    have hB := isChar_hcL_cusp _ hKc' _ hKd'
    have hAB := ip_ne_zero_of_common hψ hA hB hQi h2
    refine fin ((⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g) :: K) ?_
      List.mem_cons_self
    by_contra hn
    exact hAB ((GlobalTheory.GLq.IpCuspProd.ip_hcL_cusp g _ _ _ hQd hKd' hQc hKc').1 hn)

end GlobalTheory.GLq.DetRoot
end
end

section

noncomputable section

namespace GlobalTheory.SplitCrys

open Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.BlockCrys

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {n : ℕ}

theorem finrank_coordInv_of_split (A : G → Matrix (Fin n) (Fin n) Qp) (W : Matrix (Fin n) (Fin n) B)
    (hu : IsUnit W.det) (hW : ∀ g, (A g).map (algebraMap Qp B) * W.map (PD.actB g) = W) :
    finrank K₀ (coordInv PD A) = n := by
  haveI : Nontrivial B := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply PD.not_mem_filtration_two
    rw [Subsingleton.elim PD.t 0, map_zero]
    exact zero_mem _
  have hact : ∀ g (y : Fin n → B),
      coordAct PD A g (W.mulVec y) = W.mulVec fun i => PD.actB g (y i) := by
    intro g y
    have h1 : (fun i => PD.actB g (W.mulVec y i)) =
        (W.map (PD.actB g)).mulVec fun i => PD.actB g (y i) := by
      funext i

      simp [Matrix.mulVec, dotProduct, map_sum]
    change ((A g).map (algebraMap Qp B)).mulVec _ = _
    rw [h1, Matrix.mulVec_mulVec, hW]
  have hinj : Function.Injective W.mulVec :=
    Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det W).2 hu)
  let f : (Fin n → K₀) →ₗ[K₀] (Fin n → B) :=
    (W.mulVecLin.restrictScalars K₀).comp ((Algebra.linearMap K₀ B).compLeft (Fin n))
  have hf : ∀ c, f c = W.mulVec fun i => algebraMap K₀ B (c i) := fun c => rfl
  have hfi : Function.Injective f := by
    intro c d h
    rw [hf, hf] at h
    funext i
    exact (algebraMap K₀ B).injective (congrFun (hinj h) i)
  have hr : LinearMap.range f = coordInv PD A := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩ g
      rw [hf, hact]
      simp only [AlgEquiv.commutes]
    · intro hx
      have hxy : W.mulVec (W⁻¹.mulVec x) = x := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
      have hc : ∀ i, ∃ c : K₀, algebraMap K₀ B c = W⁻¹.mulVec x i := fun i =>
        PD.invB _ fun g => by
          have h2 := hact g (W⁻¹.mulVec x)
          rw [hxy, hx g] at h2
          exact congrFun (hinj (h2.symm.trans hxy.symm)) i
      choose c hc using hc
      refine ⟨c, ?_⟩
      rw [hf, funext hc, hxy]
  rw [← hr, LinearMap.finrank_range_of_inj hfi, Module.finrank_fin_fun]

theorem isCrys_of_split {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V]
    [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {n : ℕ} (e : Basis (Fin n) Qp V)
    [FiniteDimensional Qp LL] (W : Matrix (Fin n) (Fin n) B) (hu : IsUnit W.det)
    (hW : ∀ g, (Matrix.of fun i j => algebraMap Qp B (e.repr (ρ g (e j)) i)) * W.map (PD.actB g) = W) :
    IsCrys PD ρ := by
  let A : G → Matrix (Fin n) (Fin n) Qp := fun g => Matrix.of fun i j => e.repr (ρ g (e j)) i
  have h1 := finrank_coordInv PD ρ e A fun g i j => rfl
  have h2 := finrank_coordInv_of_split PD A W hu hW
  have hL : 0 < finrank Qp LL := Module.finrank_pos
  have hV : finrank Qp LL * finrank LL V = n := by
    rw [Module.finrank_mul_finrank Qp LL V, finrank_eq_card_basis e, Fintype.card_fin]
  rw [h2, ← hV, mul_left_comm] at h1
  exact Nat.eq_of_mul_eq_mul_left hL h1

end GlobalTheory.SplitCrys
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar



noncomputable section

namespace GlobalTheory.TwoStepModel

variable {D : D7} {m n : ℕ}

def tensorHalf (a' b : AE D) (Ψ : Mx D m n → ℂ) : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ) where
  toFun Φ x := Φ (a' • x) * Ψ (b • x) * (if IsHalf (a' + b) x then 1 else 0)
  map_add' Φ Φ' := by funext x; simp only [Pi.add_apply]; ring
  map_smul' c Φ := by funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem tensorHalf_apply (a' b : AE D) (Ψ Φ : Mx D m n → ℂ) (x : Mx D m n) :
    tensorHalf a' b Ψ Φ x = Φ (a' • x) * Ψ (b • x) * (if IsHalf (a' + b) x then 1 else 0) := rfl

open GlobalTheory.ExportSeries.RestrictHalfModel

theorem tensorHalf_halfInd (a' b : AE D) (Λ : AddSubgroup (Mx D m n)) (Ψ : Mx D m n → ℂ) :
    tensorHalf a' b Ψ ((1 : ℂ) • halfInd a' Λ) = restrictHalf b a' Λ Ψ := by
  funext x
  simp only [tensorHalf_apply, restrictHalf_apply, one_smul, add_comm b a']
  ring

theorem isSBHalf_tensorHalf {a' b : AE D} (ha' : a' * a' = a') (hb : b * b = b) {Λ : AddSubgroup (Mx D m n)}
    (hΛ : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ) {Φ Ψ : Mx D m n → ℂ} (hΦ : IsSBHalf a' Λ Φ)
    (hΨ : IsSBHalf b Λ Ψ) : IsSBHalf (a' + b) Λ (tensorHalf a' b Ψ Φ) := by
  obtain ⟨-, k, hk, hinv, hlat⟩ := hΦ
  obtain ⟨-, k', hk', hinv', hlat'⟩ := hΨ
  refine ⟨fun t ht => ?_, k * k', Nat.mul_pos hk hk', fun u hu hhu t => ?_, fun t ht => ?_⟩
  · rw [tensorHalf_apply] at ht
    by_contra h
    exact ht (by rw [if_neg h, mul_zero])
  · rw [isHalf_iff'] at hhu
    simp only [tensorHalf_apply]
    have e1 : a' • (t + (k * k') • u) = a' • t + k • (a' • (k' • u)) := by
      rw [smul_add, mul_comm k k', mul_smul, smul_comm k' k u, smul_comm a' k]
    have e2 : b • (t + (k * k') • u) = b • t + k' • (b • (k • u)) := by
      rw [smul_add, mul_smul, smul_comm k k' u, smul_comm b k']
    have e3 : (a' + b) • ((k * k') • u) = (k * k') • u := by rw [smul_comm, hhu]
    rw [e1, hinv _ (hΛ a' ha' _ (Λ.nsmul_mem hu k')) (isHalf_smul ha' _), e2,
      hinv' _ (hΛ b hb _ (Λ.nsmul_mem hu k)) (isHalf_smul hb _), isHalf_add_iff e3]
  · rw [tensorHalf_apply] at ht
    have h1 : Φ (a' • t) ≠ 0 := fun h => ht (by rw [h, zero_mul, zero_mul])
    have h2 : Ψ (b • t) ≠ 0 := fun h => ht (by rw [h, mul_zero, zero_mul])
    have h3 : IsHalf (a' + b) t := by
      by_contra h
      exact ht (by rw [if_neg h, mul_zero])
    rw [isHalf_iff', add_smul] at h3
    rw [← h3, smul_add, mul_smul, mul_comm k k', mul_smul k']
    exact Λ.add_mem (by rw [smul_comm k k']; exact Λ.nsmul_mem (hlat _ h1) k') (by rw [smul_comm k' k]; exact Λ.nsmul_mem (hlat' _ h2) k)

theorem isPlaceModel_comp_tensorHalf {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)}
    {f₀ : WO S T → ℂ} {a' b : AE D} {T₀ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} (ha' : a' * a' = a') (hb : b * b = b)
    (hab : a' * b = 0) (hΛ : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ) {Ψ : WO S T → ℂ} (hΨ : IsSBHalf b Λ Ψ)
    (hT : IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a' + b) Λ 1 f₀ T₀) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) a' Λ 1 (T₀ (restrictHalf b a' Λ Ψ)) (T₀ ∘ₗ tensorHalf a' b Ψ) := by
  have hsb : ∀ Φ, IsSBHalf a' Λ Φ → IsSBHalf (a' + b) Λ (tensorHalf a' b Ψ Φ) :=
    fun Φ hΦ => isSBHalf_tensorHalf ha' hb hΛ hΦ hΨ
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · obtain ⟨hbx, hax⟩ := smul_of_half hab hx
    have hxa : IsHalf (a' + b) x := (isHalf_iff' _ _).2 hax
    have e : tensorHalf a' b Ψ (fun t => Φ (t + x)) = fun t => tensorHalf a' b Ψ Φ (t + x) := by
      funext z
      simp only [tensorHalf_apply]
      rw [smul_add, (isHalf_iff' _ _).1 hx, smul_add b, hbx, add_zero, isHalf_add_iff hax]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e]
    exact hT.trans _ (hsb Φ hΦ) x hxa
  · have hy' : IsHalf (cA D (a' + b)) y := by
      rw [isHalf_iff'] at hy ⊢
      rw [map_add (f := _), add_smul, hy, ← hy, smul_smul, ← map_mul, mul_comm, hab, map_zero, zero_smul, add_zero]
    have e : tensorHalf a' b Ψ (fun t => ψ (symplO S T t y) * Φ t) =
        fun t => ψ (symplO S T t y) * tensorHalf a' b Ψ Φ t := by
      funext z
      simp only [tensorHalf_apply]
      rw [GlobalTheory.SplitScalar.symplO_smul, (isHalf_iff' _ _).1 hy]
      ring
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e]
    exact hT.modul _ (hsb Φ hΦ) y hy'
  · rw [LinearMap.comp_apply, tensorHalf_halfInd]

end GlobalTheory.TwoStepModel

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.TiedSpan

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem exists_sum_of_isCrys [IsDomain B] (hf : GlobalTheory.RegularRing.FracInv PD)
    (hu : GlobalTheory.RegularRing.LineUnit PD) [FiniteDimensional Qp LL] [FiniteDimensional LL V]
    (ρ : Representation LL G V) (h : IsCrys PD ρ) (y : V ⊗[Qp] B) :
    ∃ (m : ℕ) (b : Fin m → B) (d : Fin m → V ⊗[Qp] B), (∀ i, d i ∈ Dcris PD ρ) ∧
      y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp (b i)) (d i) := by
  have hs := (GlobalTheory.RegularRing.isCrys_iff_span PD hf hu ρ).1 h
  have hy : (TensorProduct.comm Qp B V).symm y ∈
      Submodule.span B (GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.DcrisK₀ PD ρ : Set (B ⊗[Qp] V)) := hs ▸ Submodule.mem_top
  obtain ⟨m, b, e, he⟩ := Submodule.mem_span_set'.1 hy
  refine ⟨m, b, fun i => TensorProduct.comm Qp B V (e i : B ⊗[Qp] V), fun i => (e i).2, ?_⟩
  have h2 := congrArg (TensorProduct.comm Qp B V) he

  rw [LinearEquiv.apply_symm_apply, map_sum] at h2
  rw [← h2]
  exact Finset.sum_congr rfl fun i _ => GlobalTheory.Per.TiedIndep.comm_smul (LL := LL) _ _

end Generic

theorem tied_crisSpan : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → (∀ (K : FinExt l) (b : P.R.B), b ≠ 0 → (∀ g ∈ GK K, ∃ x : ℚ_[l], P.actQ g b = x • b) → IsUnit b) → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → ∀ y : V ⊗[ℚ_[l]] P.R.B, ∃ (m : ℕ) (b : Fin m → P.R.B) (d : Fin m → V ⊗[ℚ_[l]] P.R.B), (∀ i, d i ∈ Dcris (P.PD K) ρ) ∧ y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[↥LL.1] V) (LinearMap.mulLeft ℚ_[l] (b i)) (d i) := by
  intro l _ P AI T hreg K LL V _ _ _ _ _ ρ h y
  have : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T K
  have := LL.2
  have e : ∀ (g : ↥(GK K)) z, (P.PD K).actB g z = P.actQ g z := fun g z => P.PD_actB K g z
  refine exists_sum_of_isCrys (P.PD K) ?_ ?_ ρ h y
  · intro x y hx h
    refine GlobalTheory.Per.FracInv.tied_frac_invariant l P AI T K y x hx fun g hg => ?_
    have h1 := h ⟨g, hg⟩
    rw [e, e] at h1
    rw [mul_comm, h1, mul_comm]
  · intro b hb h
    refine hreg K b hb fun g hg => ?_
    obtain ⟨x, hx⟩ := h ⟨g, hg⟩
    rw [e] at hx
    exact ⟨x, by rw [Algebra.smul_def]; exact hx⟩

end GlobalTheory.Per.TiedSpan
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

theorem _root_.GlobalTheory.T.bcris_regular_surjections_of_fontaine_theorem : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → (∀ (K : FinExt l) (b : P.R.B), b ≠ 0 → (∀ g ∈ GK K, ∃ x : ℚ_[l], P.actQ g b = x • b) → IsUnit b) ∧ (∀ u : P.R.B, ∃ x, x - P.φB x = u) ∧ ∀ (K : FinExt l) (w : P.R.BdR), ∃ x : P.R.B, P.φB x = x ∧ P.ιB x - w ∈ (P.PD K).Fil 0 := by
  first | exact @GlobalTheory.MemLoc.TiedRegular.regular_onto | exact GlobalTheory.MemLoc.TiedRegular.regular_onto | (intros; apply GlobalTheory.MemLoc.TiedRegular.regular_onto <;> assumption)
end
