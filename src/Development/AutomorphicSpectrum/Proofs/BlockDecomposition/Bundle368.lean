module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle482
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle145
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle084
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle110
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle111
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle350
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle120
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle173
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle302
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle351
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle315
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle316
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle354
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle349
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle317
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle353
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentCongruenceFactorization
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle120
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactCosetSet
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle335

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.CompactAvg

theorem exists_perm_of_reps {G : Type} [Group G] (J H : Subgroup G) {r : ℕ} (x : Fin r → G)
    (hx : ∀ i, x i ∈ J) (hu : ∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ H) {j : G} (hj : j ∈ J) :
    ∃ σ : Equiv.Perm (Fin r), ∀ i, (x (σ i))⁻¹ * (j * x i) ∈ H := by
  have h : ∀ i, ∃ k, (x k)⁻¹ * (j * x i) ∈ H := fun i => (hu _ (J.mul_mem hj (hx i))).exists
  choose f hf using h
  have hinj : Function.Injective f := by
    intro a b hab
    have ha := hf a
    have hb := hf b
    rw [← hab] at hb
    have hm : (x a)⁻¹ * x b ∈ H := by
      have h2 := H.mul_mem (H.inv_mem ha) hb
      have e : ((x (f a))⁻¹ * (j * x a))⁻¹ * ((x (f a))⁻¹ * (j * x b)) = (x a)⁻¹ * x b := by group
      rwa [e] at h2
    have h1 : (x b)⁻¹ * x b ∈ H := by simp [H.one_mem]
    exact (hu (x b) (hx b)).unique hm h1
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), hf⟩

theorem exists_average : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G), IsCompact (J : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∃ E : V →ₗ[ℂ] V, (∀ v, E v ∈ fixed π J) ∧ (∀ v ∈ fixed π J, E v = v) ∧ (∀ l : Module.Dual ℂ V, (∀ x ∈ J, l ∘ₗ π x = l) → l ∘ₗ E = l) ∧ (∀ x ∈ J, E ∘ₗ π x = E) ∧ ∀ (u : V) (H : Subgroup G), H ≤ J → (∀ h ∈ H, π h u = u) → ∀ (r : ℕ) (x : Fin r → G), 0 < r → (∀ i, x i ∈ J) → (∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ H) → E u = ((r : ℂ)⁻¹) • ∑ i, π (x i) u := by
  intro G _ _ _ J hJ V _ _ π hπ
  have hsub : ∀ v, v - GlobalTheory.LocGL.idem hπ hJ v ∈ twKer π J 1 := fun v => by
    rw [← GlobalTheory.LocGL.idem_eq_zero_iff hπ hJ, map_sub,
      GlobalTheory.LocGL.idem_of_mem hπ hJ (GlobalTheory.LocGL.idem_mem hπ hJ v), sub_self]
  refine ⟨GlobalTheory.LocGL.idem hπ hJ, GlobalTheory.LocGL.idem_mem hπ hJ, fun v hv => GlobalTheory.LocGL.idem_of_mem hπ hJ hv,
    ?_, ?_, ?_⟩
  · intro l hl
    have hk : twKer π J 1 ≤ LinearMap.ker l := by
      refine Submodule.span_le.2 ?_
      rintro w ⟨n, v, rfl⟩
      have h1 : l (π (n : G) v) = l v := LinearMap.congr_fun (hl n n.2) v
      simp [h1]
    refine LinearMap.ext fun v => ?_
    have h2 := hk (hsub v)
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h2
    exact h2.symm
  · intro x hx
    exact LinearMap.ext fun v => GlobalTheory.LocGL.idem_apply_mem hπ hJ hx v
  · intro u H _ hu r x hr hxJ hex
    have hrc : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hr.ne'
    have hfix : ((r : ℂ)⁻¹ • ∑ i, π (x i) u) ∈ fixed π J := GlobalTheory.Parabolic.mem_fixed.2 fun j hj => by
      obtain ⟨σ, hσ⟩ := exists_perm_of_reps J H x hxJ hex hj

      rw [map_smul, map_sum]
      congr 1
      refine Fintype.sum_equiv σ _ _ fun i => ?_
      have e : j * x i = x (σ i) * ((x (σ i))⁻¹ * (j * x i)) := by group
      rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hu _ (hσ i)]
    have h3 : GlobalTheory.LocGL.idem hπ hJ ((r : ℂ)⁻¹ • ∑ i, π (x i) u) = GlobalTheory.LocGL.idem hπ hJ u := by

      rw [map_smul, map_sum, Finset.sum_congr rfl fun i _ => GlobalTheory.LocGL.idem_apply_mem hπ hJ (hxJ i) u,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ hrc, one_smul]
    rw [← h3, GlobalTheory.LocGL.idem_of_mem hπ hJ hfix]

end GlobalTheory.CompanionTheory.CompactAvg
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

theorem _root_.GlobalTheory.T.induced_product_drop_zero_factors : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r r' N : ℕ} (y : Fin r → IrrGL (k := k)) (hd : ∑ a, (y a).1 = N) (o : Fin r' → Fin r), StrictMono o → (∀ j, (y j).1 ≠ 0 → j ∈ Set.range o) → ∀ (hd' : ∑ a, (y (o a)).1 = N), Nonempty ((prodIrr y hd).Equiv (prodIrr (fun a => y (o a)) hd')) := by
  first | exact @GlobalTheory.CompanionTheory.FineProd.ProdDrop.prodIrr_drop | exact GlobalTheory.CompanionTheory.FineProd.ProdDrop.prodIrr_drop | (intros; apply GlobalTheory.CompanionTheory.FineProd.ProdDrop.prodIrr_drop <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace GlobalTheory.CompanionTheory.ProdStage

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


open GlobalTheory.ProdFlatten in
unseal GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two in
theorem equiv_of_iso_two {p q c r t N : ℕ} (x : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) (w : Fin c → IrrGL (k := k))
    (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t)
    (hz : ∑ a, (w a).1 = N) (e : r + t = N) (H : Iso (two e (pr x hx) (pr y hy)) (pr w hz)) :
    Nonempty ((ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy))).Equiv (prodIrr w hz)) := H


open GlobalTheory.ProdFlatten in
unseal GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.one in
theorem equiv_of_iso {q c N : ℕ} (y : Fin q → IrrGL (k := k)) (w : Fin c → IrrGL (k := k))
    (hy : ∑ a, (y a).1 = N) (hz : ∑ a, (w a).1 = N) (H : Iso (pr y hy) (pr w hz)) :
    Nonempty ((prodIrr y hy).Equiv (prodIrr w hz)) := H

theorem ind₂_prodIrr_empty {c q N : ℕ} (x : Fin 0 → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) (w : Fin c → IrrGL (k := k))
    (hw : List.ofFn w = List.ofFn y) (hx : ∑ a, (x a).1 = 0) (hy : ∑ a, (y a).1 = N)
    (hz : ∑ a, (w a).1 = N) (e : 0 + N = N) :
    Nonempty ((ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy))).Equiv (prodIrr w hz)) := by
  have A : Nonempty ((ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy))).Equiv (prodIrr y hy)) :=
    GlobalTheory.ProdReorder.ind₂_unit_left k N 0 e _ (prodIrr y hy) (isSmooth_prodIrr y hy)
      (fun a => (x a).1) (fun a => (x a).2.rep.V) (fun a => (x a).rep) (stdBlocks (fun a => (x a).1) hx)
  have B : Nonempty ((prodIrr y hy).Equiv (prodIrr w hz)) :=
    equiv_of_iso y w hy hz (GlobalTheory.ProdFlatten.pr_congr hw.symm hy hz)
  exact A.elim fun a => B.elim fun b => ⟨a.trans b⟩

theorem ind₂_prodIrr_equiv_zero {q c r t N : ℕ} (x : Fin 0 → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) (w : Fin c → IrrGL (k := k))
    (hw : List.ofFn w = List.ofFn y) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t)
    (hz : ∑ a, (w a).1 = N) (e : r + t = N) :
    Nonempty ((ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy))).Equiv (prodIrr w hz)) := by
  have hr : r = 0 := by simpa using hx.symm
  subst hr
  have ht : t = N := by omega
  subst ht
  exact ind₂_prodIrr_empty x y w hw hx hy hz e

theorem ind₂_prodIrr_equiv_pos {p q c r t N : ℕ} (hp : p ≠ 0) (x : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k))
    (w : Fin c → IrrGL (k := k)) (hw : List.ofFn w = List.ofFn x ++ List.ofFn y) (hx : ∑ a, (x a).1 = r)
    (hy : ∑ a, (y a).1 = t) (hz : ∑ a, (w a).1 = N) (e : r + t = N) :
    Nonempty ((ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy))).Equiv (prodIrr w hz)) :=
  equiv_of_iso_two x y w hx hy hz e
    (GlobalTheory.ProdFlatten.iso_symm (GlobalTheory.ProdFlatten.pr_append x y w hw (Or.inl hp) hx hy hz e))

theorem ind₂_prodIrr_equiv {p q c r t N : ℕ} (x : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) (w : Fin c → IrrGL (k := k))
    (hw : List.ofFn w = List.ofFn x ++ List.ofFn y) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t)
    (hz : ∑ a, (w a).1 = N) (e : r + t = N) :
    Nonempty ((ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy))).Equiv (prodIrr w hz)) := by
  cases p with
  | zero => exact ind₂_prodIrr_equiv_zero x y w (by simpa using hw) hx hy hz e
  | succ n => exact ind₂_prodIrr_equiv_pos (Nat.succ_ne_zero n) x y w hw hx hy hz e

theorem prod₂_prodIrr_append : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p q r t : ℕ) (x : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k))
    (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t) (h : ∑ a, (Fin.append x y a).1 = r + t),
    Nonempty ((prod₂ (prodIrr x hx) (prodIrr y hy)).Equiv (prodIrr (Fin.append x y) h)) :=
  fun _ _ _ _ _ _ _ _ _ x y hx hy h =>
    ind₂_prodIrr_equiv x y (Fin.append x y) (List.ofFn_fin_append x y) hx hy h rfl

end GlobalTheory.CompanionTheory.ProdStage
end
end

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.SumU

variable {E : Type} [Field E] [NumberField E] {m : ℕ}

theorem fibre_bound (c : Matrix (Fin m) (Fin m) E) (b : (Fin m → E) ⧸ lam c) :
    Finite {U : (Fin m → E) ⧸ intVec E m //
        (Submodule.Quotient.mk (Quotient.out U) : (Fin m → E) ⧸ lam c) = b} ∧
      Nat.card {U : (Fin m → E) ⧸ intVec E m //
        (Submodule.Quotient.mk (Quotient.out U) : (Fin m → E) ⧸ lam c) = b} ≤ delta c := by
  obtain ⟨hne, hidx⟩ := GlobalTheory.T.delta_eq_lattice_index E m c
  set H := (intVec E m).toAddSubgroup with hH
  set Kg := (lam c).toAddSubgroup with hK
  have hidx' : delta c = (H.addSubgroupOf Kg).index := hidx
  have hcard : Nat.card (Kg ⧸ H.addSubgroupOf Kg) = delta c := by
    rw [hidx']; rfl
  haveI : Finite (Kg ⧸ H.addSubgroupOf Kg) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hne)
  have hw : (Submodule.Quotient.mk (Quotient.out b) : (Fin m → E) ⧸ lam c) = b :=
    Quotient.out_eq' b
  have hmem : ∀ a : {U : (Fin m → E) ⧸ intVec E m //
      (Submodule.Quotient.mk (Quotient.out U) : (Fin m → E) ⧸ lam c) = b},
      Quotient.out a.1 - Quotient.out b ∈ Kg := by
    intro a
    have : (Submodule.Quotient.mk (Quotient.out a.1) : (Fin m → E) ⧸ lam c) =
        Submodule.Quotient.mk (Quotient.out b) := a.2.trans hw.symm
    exact (Submodule.Quotient.eq _).1 this
  let φ : {U : (Fin m → E) ⧸ intVec E m //
      (Submodule.Quotient.mk (Quotient.out U) : (Fin m → E) ⧸ lam c) = b} →
      Kg ⧸ H.addSubgroupOf Kg := fun a => QuotientAddGroup.mk ⟨_, hmem a⟩
  have hφ : Function.Injective φ := by
    intro a a' h
    have h1 := QuotientAddGroup.eq.1 h
    have h2 : -(Quotient.out a.1 - Quotient.out b) + (Quotient.out a'.1 - Quotient.out b) ∈ H :=
      AddSubgroup.mem_addSubgroupOf.1 h1
    have h3 : Quotient.out a.1 - Quotient.out a'.1 ∈ intVec E m := by
      have h4 := neg_mem h2
      have h5 : -(-(Quotient.out a.1 - Quotient.out b) + (Quotient.out a'.1 - Quotient.out b)) =
          Quotient.out a.1 - Quotient.out a'.1 := by abel
      rw [h5] at h4
      exact h4
    apply Subtype.ext
    have h6 : (Submodule.Quotient.mk (Quotient.out a.1) : (Fin m → E) ⧸ intVec E m) =
        Submodule.Quotient.mk (Quotient.out a'.1) := (Submodule.Quotient.eq _).2 h3
    have e1 : (Submodule.Quotient.mk (Quotient.out a.1) : (Fin m → E) ⧸ intVec E m) = a.1 :=
      Quotient.out_eq' _
    have e2 : (Submodule.Quotient.mk (Quotient.out a'.1) : (Fin m → E) ⧸ intVec E m) = a'.1 :=
      Quotient.out_eq' _
    rw [← e1, ← e2, h6]
  refine ⟨Finite.of_injective φ hφ, ?_⟩
  rw [← hcard]
  exact Nat.card_le_card_of_injective φ hφ

theorem sum_tor : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (c : Matrix (Fin m) (Fin m) E) (r : ℝ), 1 < r → Summable (fun U : (Fin m → E) ⧸ intVec E m => (Ideal.absNorm (tor c (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r))) ∧ ∑' U : (Fin m → E) ⧸ intVec E m, (Ideal.absNorm (tor c (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r)) ≤ delta c * zetaR E r := by
  intro E _ _ m c r hr
  obtain ⟨hs, hle⟩ := GlobalTheory.T.torsion_norm_zeta_bound E m (lam c) (GlobalTheory.T.lam_is_lattice E m c) r hr
  have hg : ∀ x : (Fin m → E) ⧸ lam c,
      0 ≤ (Ideal.absNorm (Ideal.torsionOf (𝓞 E) ((Fin m → E) ⧸ lam c) x) : ℝ) ^
        (-((m : ℝ) + r)) := fun x => Real.rpow_nonneg (Nat.cast_nonneg _) _
  obtain ⟨h1, h2⟩ := GlobalTheory.T.tsum_comp_bounded_fibres_le ((Fin m → E) ⧸ intVec E m) ((Fin m → E) ⧸ lam c)
    (fun U => Submodule.Quotient.mk (Quotient.out U)) (delta c) (fibre_bound c)
    (fun x => (Ideal.absNorm (Ideal.torsionOf (𝓞 E) ((Fin m → E) ⧸ lam c) x) : ℝ) ^
      (-((m : ℝ) + r))) hg hs
  refine ⟨h1, h2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.SumU
end

section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

theorem _root_.GlobalTheory.T.local_graded_class_representative : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (t : Fin d → Γ(X, W)) (s : ℕ) (E : Frame (sP (KS q s {W})) d)
    (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s t E ε → ∀ (σ : ∀ T, E.D ⟶ T) (m : ℕ) (r : ℤ), r = m → m + 1 ≤ s →
    (∀ c : HQ (KS q s {W}) r (r + 1) m, ∃ y : Idx m d → Γ(X, W),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (fun u => ∑ I : Idx m d, E.form σ I.1 (ε (y I)) u) c) ∧
    ∀ y : Idx m d → Γ(X, W),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (fun u => ∑ I : Idx m d, E.form σ I.1 (ε (y I)) u) 0 → y = 0 := by
  first | exact @GlobalTheory.CompanionTheory.ConeLocal.loc_coef | exact GlobalTheory.CompanionTheory.ConeLocal.loc_coef | (intros; apply GlobalTheory.CompanionTheory.ConeLocal.loc_coef <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mirabolic_double_coset_dichotomy : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), ψ ≠ 1 → ∀ (m j : ℕ) (g : Mir k (m + (j + 1))),
    (∃ h ∈ MirabolicParabolic k m (j + 1), ∃ x : Mir k (m + j), g = h * embedding₂ k (m + j) x) ∨
    ∃ u : MirUin k (m + (j + 1)), ∃ hx : g * (u : Mir k (m + (j + 1))) * g⁻¹ ∈ MirabolicParabolic k m (j + 1),
      gpProj k m (j + 1) ⟨_, hx⟩ = 1 ∧ mirChar k ψ (m + j) u ≠ 1 := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.Dich.dichotomy | exact GlobalTheory.CompanionTheory.LeibPhi.Dich.dichotomy | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.Dich.dichotomy <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.BZNuPair

theorem _root_.GlobalTheory.T.whittaker_subquotient_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (Y : Type) [AddCommGroup Y] [Module ℂ Y]
    (J : Representation ℂ (Levi k fun a => Fin (d a)) Y) (T T' : Subrepresentation J) (X : Fin 2 → Type)
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)),
    T' ≤ T → (subQuot T T').Equiv (piTensor ρ) →
    ⨆ f : (ρ 0).IntertwiningMap (subQuot (whitImg ψ d J T) (whitImg ψ d J T')), LinearMap.range f.toLinearMap = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.BZNuPair.WhitCover.main | exact GlobalTheory.CompanionTheory.BZNuPair.WhitCover.main | (intros; apply GlobalTheory.CompanionTheory.BZNuPair.WhitCover.main <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.parabolic_unipotent_levi_decomp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (h : HPG k i t), ∃ (x : Fin i → k) (q : Qp k i t), (h : Mir k (i + t)) = uM k (i + t) (topV k i t x) * levi k (i + t) (q : GL (Fin (i + t)) k) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.HpgMem.main | exact GlobalTheory.CompanionTheory.BZPsiPG.HpgMem.main | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.HpgMem.main <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.smooth_tensor_fixed_parabolic_near_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ z : V ⊗[ℂ] W, ∃ U ∈ nhds (1 : Mir k (i + t)), ∀ h : HPG k i t, (h : Mir k (i + t)) ∈ U → hRep τ σ h z = z := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.Stab.hRep_fix | exact GlobalTheory.CompanionTheory.BZPsiPG.Stab.hRep_fix | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.Stab.hRep_fix <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

theorem exists_hpg_mid_levi (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) (p : Mir k (i + t)) :
    ∃ h ∈ HPG k i t, ∃ κ ∈ GlobalTheory.SplitWeil.KO k (Fin (i + t)), ∃ v : Fin t → k,
      p = h * (uM k (i + t) (midV k i t v) * levi k (i + t) κ) := by
  obtain ⟨y, hy⟩ := GlobalTheory.CompanionTheory.BZPsiPG.exists_uM_of_mem k (i + t)
    (GlobalTheory.CompanionTheory.BZMirAdj.mem_of_mirProj_eq_one k (i + t)
      (p * (GlobalTheory.BZMir.levi k (i + t) (GlobalTheory.BZMir.mirabolicProjection k (i + t) p))⁻¹)
      (by rw [map_mul, map_inv, GlobalTheory.CompanionTheory.BZMirAdj.mirProj_levi, mul_inv_cancel]))
  have hp : p = GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) y *
      GlobalTheory.BZMir.levi k (i + t) (GlobalTheory.BZMir.mirabolicProjection k (i + t) p) := by
    rw [← hy, inv_mul_cancel_right]
  obtain ⟨q, κ, hκ, hgq⟩ := GlobalTheory.T.iwasawa_decomp_parabolic_maximal_compact k i t (GlobalTheory.BZMir.mirabolicProjection k (i + t) p)
  obtain ⟨x, v, hxv⟩ := GlobalTheory.CompanionTheory.BZPsiPG.exists_top_mid k i t
    ((((q : GL (Fin (i + t)) k)⁻¹ : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k) *ᵥ y)
  obtain ⟨hq, -⟩ := GlobalTheory.T.levi_block_mem_parabolic k i t q
  obtain ⟨hx, -⟩ := GlobalTheory.T.unipotent_top_mem_parabolic k i t x
  refine ⟨GlobalTheory.BZMir.levi k (i + t) q * GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x),
    mul_mem hq hx, κ, hκ, v, ?_⟩
  have key : GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) y * GlobalTheory.BZMir.levi k (i + t) q =
      GlobalTheory.BZMir.levi k (i + t) q * GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t)
        ((((q : GL (Fin (i + t)) k)⁻¹ : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k) *ᵥ y) := by
    rw [GlobalTheory.CompanionTheory.BZPsiPG.levi_mul_uM, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mulVec]
  rw [hp, hgq, map_mul, ← mul_assoc (GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) y), key, hxv,
    GlobalTheory.CompanionTheory.BZPsiPG.uM_add]
  simp only [mul_assoc]

theorem eq_zero_of_fibV_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (a : cIndSpace (HPG k i t) (hRep τ σ)),
    (∀ κ ∈ GlobalTheory.SplitWeil.KO k (Fin (i + t)), fibV a κ = 0) → a = 0 := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ a ha
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext p
  obtain ⟨h, hh, κ, hκ, v, rfl⟩ := GlobalTheory.CompanionTheory.BZPsiPG.FibKer.exists_hpg_mid_levi k i t p
  have hfe : a.1.1.1 (h * (GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.midV k i t v) *
      GlobalTheory.BZMir.levi k (i + t) κ)) =
      GlobalTheory.CompanionTheory.BZPsiPG.hRep τ σ ⟨h, hh⟩ (a.1.1.1 (GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t)
        (GlobalTheory.CompanionTheory.BZPsiPG.midV k i t v) * GlobalTheory.BZMir.levi k (i + t) κ)) :=
    a.1.1.2 ⟨h, hh⟩ _
  have hz : a.1.1.1 (GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.midV k i t v) *
      GlobalTheory.BZMir.levi k (i + t) κ) = 0 := congrFun (ha κ hκ) v
  show a.1.1.1 _ = (0 : V ⊗[ℂ] W)
  rw [hfe, hz, map_zero]

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unipotent_congruence_factorization : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1) (hs1 : ValuativeRel.valuation k (s : k) < 1)
    (d : Fin (t + 1) → k) (m : Mir k ((i + 1) + t)) (h : Mir k ((i + 1) + t + 1)) (hh : h ∈ HPG k (i + 1) (t + 1))
    (κ : Mir k ((i + 1) + t + 1)) (hκ : κ ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs ((i + 1) + t + 1))
    (e : dEmb k i t d * sEmb k ((i + 1) + t) m = h * κ),
  ∃ a ∈ MirabolicParabolic k (i + 1) t, ∃ x ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs ((i + 1) + t), m = a * x := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Onto.Key1.mem_mirabolicParabolic_mul_cong | exact GlobalTheory.CompanionTheory.BZPhiPG.Onto.Key1.mem_mirabolicParabolic_mul_cong | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Onto.Key1.mem_mirabolicParabolic_mul_cong <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.weyl_not_mem_closed_cell :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
      [IsNonarchimedeanLocalField k] (i t : ℕ),
      GlobalTheory.CompanionTheory.BZPhiPG.wEl (k := k) i t ∉ Cl (k := k) i t ∧
        dEmb (k := k) i t 0 = 1 := by
  intro k _ _ _ _ i t
  constructor
  · intro hmem
    simp only [GlobalTheory.CompanionTheory.BZPhiPG.Cl, Set.mem_ofPred_eq] at hmem
    let c : Fin ((i + 1) + t + 1) := ⟨i, by omega⟩
    have hc : (Fin.castLE (by omega) (Fin.last i) : Fin ((i + 1) + t + 2)) =
        Fin.castSucc c := Fin.ext rfl
    have hzero := hmem (Fin.last i)
    rw [hc, GlobalTheory.CompanionTheory.BZPhiPG.wEl, ← map_inv] at hzero
    change GlobalTheory.BZMir.glEmbMat k ((i + 1) + t + 1)
        (((wGL (k := k) i t)⁻¹ : GL (Fin ((i + 1) + t + 1)) k) :
          Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k)
        (Fin.castSucc (Fin.last ((i + 1) + t))) (Fin.castSucc c) = 0 at hzero
    simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_castSucc] at hzero
    change Equiv.Perm.permMatrix k (piPerm i t) (Fin.last ((i + 1) + t)) c = 0 at hzero
    have hperm : piPerm i t (Fin.last ((i + 1) + t)) = c :=
      Fin.ext (piPerm_last_val i t)
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hperm] at hzero
  · have h : Fin.append (0 : Fin (i + 1) → k) (0 : Fin (t + 1) → k) = 0 := by
      funext j
      refine Fin.addCases (fun a => ?_) (fun b => ?_) j
      · rw [Fin.append_left]; rfl
      · rw [Fin.append_right]; rfl
    apply Subtype.ext
    change GlobalTheory.BZMir.unip k ((i + 1) + (t + 1))
      (Multiplicative.ofAdd (Fin.append (0 : Fin (i + 1) → k) (0 : Fin (t + 1) → k))) = 1
    rw [h, ofAdd_zero, map_one]
end
