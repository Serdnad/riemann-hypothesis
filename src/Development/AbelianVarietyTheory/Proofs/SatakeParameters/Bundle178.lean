module

public import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle170
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle018
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.InertKernelTheory.Bundle008
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
import Formalism.LocalToGlobal.InertKernelTheory.Bundle009
import Formalism.LocalToGlobal.InertKernelTheory.Bundle003
import Formalism.LocalToGlobal.KernelLattices.Bundle001
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.LtCNeZero
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle017
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle002
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.IsComplRatCompl
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle001
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle001

@[expose] public section

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct
open Formalism.L2.Th1.H Formalism.L2.KerInert.RepComb

noncomputable section

namespace GlobalTheory.CommonReps

def RepsIn {G : Type} [AddCommGroup G] (X Y : AddSubgroup G) (S : Finset G) : Prop :=
  (∀ x ∈ S, x ∈ Y) ∧ (∀ x ∈ S, ∀ y ∈ S, x - y ∈ X → x = y) ∧ ∀ y ∈ Y, ∃ x ∈ S, y - x ∈ X

theorem isReps_map {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℂ V] [DecidableEq V] (f : G →+ V)
    (hf : Function.Injective f) {X Y : AddSubgroup G} {S : Finset G} (h : RepsIn X Y S) :
    IsReps (X.map f) (Y.map f) (S.image f) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
    exact ⟨x, h1 x hx, rfl⟩
  · intro v hv w hw hvw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨m, hm, hme⟩ := hvw
    rw [← map_sub] at hme
    rw [h2 x hx y hy (hf hme ▸ hm)]
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hyx⟩ := h3 y hy
    exact ⟨f x, Finset.mem_image_of_mem f hx, ⟨y - x, hyx, map_sub f y x⟩⟩

theorem repsIn_preimage {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℂ V] (f : G →+ V)
    (hf : Function.Injective f) {X Y : AddSubgroup G} {T : Finset V} (h : IsReps (X.map f) (Y.map f) T) :
    RepsIn X Y (T.preimage f hf.injOn) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := h1 (f x) (Finset.mem_preimage.1 hx)
    exact hf hyx ▸ hy
  · intro x hx y hy hxy
    exact hf (h2 _ (Finset.mem_preimage.1 hx) _ (Finset.mem_preimage.1 hy) ⟨x - y, hxy, map_sub f x y⟩)
  · intro y hy
    obtain ⟨v, hv, hyv⟩ := h3 (f y) ⟨y, hy, rfl⟩
    obtain ⟨x, -, rfl⟩ := h1 v hv
    refine ⟨x, Finset.mem_preimage.2 hv, ?_⟩
    obtain ⟨m, hm, hme⟩ := hyv
    rw [← map_sub] at hme
    exact hf hme ▸ hm

theorem repsIn_move {R G : Type} [CommRing R] [AddCommGroup G] [Module R G] [DecidableEq G]
    (X Y X₀ Y₀ : Submodule R G) (g c k : R) (hg : g = 1 + c * k)
    (hY : ∀ y ∈ Y, g • y ∈ Y₀) (hY₀ : ∀ y ∈ Y₀, g • y ∈ Y) (hX : ∀ x ∈ X, g • x ∈ X₀) (hX₀ : ∀ x ∈ X₀, g • x ∈ X)
    (hcY : ∀ y ∈ Y, c • y ∈ X) (hcY₀ : ∀ y ∈ Y₀, c • y ∈ X₀) {S₀ : Finset G}
    (hS : RepsIn X₀.toAddSubgroup Y₀.toAddSubgroup S₀) :
    RepsIn X.toAddSubgroup Y.toAddSubgroup (S₀.image (g • ·)) := by
  obtain ⟨h1, h2, h3⟩ := hS
  have hgg : ∀ z : G, z = g • g • z - (2 * k + c * k * k) • (c • z) := by
    intro z
    rw [smul_smul, smul_smul, ← sub_smul, hg]
    have : (1 + c * k) * (1 + c * k) - (2 * k + c * k * k) * c = 1 := by ring
    rw [this, one_smul]
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
    exact hY₀ x (h1 x hx)
  · intro v hv w hw hvw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hw
    have hxy : x - y ∈ Y₀ := Y₀.sub_mem (h1 x hx) (h1 y hy)
    have e1 : g • g • (x - y) ∈ X₀ := by
      rw [smul_sub g x y]; exact hX _ hvw
    have e2 : x - y ∈ X₀ := by
      rw [hgg (x - y)]
      exact X₀.sub_mem e1 (X₀.smul_mem _ (hcY₀ _ hxy))
    rw [h2 x hx y hy e2]
  · intro y hy
    obtain ⟨x, hx, hyx⟩ := h3 (g • y) (hY y hy)
    refine ⟨g • x, Finset.mem_image_of_mem _ hx, ?_⟩
    have e : y - g • x = g • (g • y - x) - (2 * k + c * k * k) • (c • y) := by
      conv_lhs => rw [hgg y]
      rw [smul_sub]; abel
    rw [e]
    exact X.sub_mem (hX₀ _ hyx) (X.smul_mem _ (hcY y hy))

theorem common_reps_of {R G V κ : Type} [CommRing R] [AddCommGroup G] [Module R G] [AddCommGroup V] [Module ℂ V]
    (f : G →+ V) (hf : Function.Injective f) (g c k : R) (hg : g = 1 + c * k)
    (X Y : κ → Submodule R G) (X₀ Y₀ : Submodule R G)
    (hY : ∀ i, ∀ y ∈ Y i, g • y ∈ Y₀) (hY₀ : ∀ i, ∀ y ∈ Y₀, g • y ∈ Y i) (hX : ∀ i, ∀ x ∈ X i, g • x ∈ X₀)
    (hX₀ : ∀ i, ∀ x ∈ X₀, g • x ∈ X i) (hcY : ∀ i, ∀ y ∈ Y i, c • y ∈ X i) (hcY₀ : ∀ y ∈ Y₀, c • y ∈ X₀)
    (hidx : relIdx (X₀.toAddSubgroup.map f) (Y₀.toAddSubgroup.map f) ≠ 0) :
    ∃ S : Finset V, ∀ i, IsReps ((X i).toAddSubgroup.map f) ((Y i).toAddSubgroup.map f) S := by
  classical
  have h0 := repsIn_preimage f hf (Formalism.L2.Ker.repsOf_spec _ _ hidx)
  exact ⟨(((Formalism.L2.Ker.repsOf _ _).preimage f hf.injOn).image (g • ·)).image f, fun i =>
    isReps_map f hf (repsIn_move (X i) (Y i) X₀ Y₀ g c k hg (hY i) (hY₀ i) (hX i) (hX₀ i) (hcY i) hcY₀ h0)⟩

section Tw

variable {E : Type} [Field E] [NumberField E] [StarRing E] {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W]
  [IsScalarTower (𝓞 E) E W]

theorem smul_mem_twO_of (M M₀ : Submodule (𝓞 E) W) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ) (g : 𝓞 E)
    (hg : ∀ x ∈ M, g • x ∈ M₀) {x : W} (hx : x ∈ Formalism.L2.Ker.twist₂ M c e) : g • x ∈ Formalism.L2.Ker.twist₂ M₀ c e := by
  rw [Formalism.L2.Ker.mem_twO] at hx ⊢
  intro Q
  obtain ⟨s, hs, hsx⟩ := hx Q
  refine ⟨s, hs, ?_⟩
  rw [smul_comm _ g, smul_comm s g]
  exact hg _ hsx

theorem natsmul_mem_twO (L : Submodule (𝓞 E) W) (c : ℕ) (e e' : HeightOneSpectrum (𝓞 E) → ℤ) (he : ∀ Q, e' Q ≤ e Q + 1)
    {x : W} (hx : x ∈ Formalism.L2.Ker.twist₂ L c e) : (c : 𝓞 E) • x ∈ Formalism.L2.Ker.twist₂ L c e' := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rw [Nat.cast_zero, zero_smul]; exact Submodule.zero_mem _
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  rw [Formalism.L2.Ker.mem_twO] at hx ⊢
  intro Q
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = e Q + 1 - e' Q := ⟨(e Q + 1 - e' Q).toNat, Int.toNat_of_nonneg (by linarith [he Q])⟩
  have key : ((c : E) ^ e' Q)⁻¹ • ((c : 𝓞 E) • x) = ((c : 𝓞 E) ^ n) • (((c : E) ^ e Q)⁻¹ • x) := by
    rw [← IsScalarTower.algebraMap_smul E ((c : 𝓞 E) ^ n), ← IsScalarTower.algebraMap_smul E (c : 𝓞 E) x, smul_smul, smul_smul]
    congr 1
    simp only [map_pow, map_natCast]
    rw [← zpow_neg, ← zpow_neg, ← zpow_natCast, hn, ← zpow_add_one₀ hcE, ← zpow_add₀ hcE]
    congr 1; ring
  rw [key]
  exact Submodule.smul_mem _ _ (hx Q)

theorem mem_twO_zero (M : Submodule (𝓞 E) W) (c : ℕ) (x : W) : x ∈ Formalism.L2.Ker.twist₂ M c (fun _ => 0) ↔ x ∈ M := by
  rw [Formalism.L2.Ker.mem_twO]
  simp only [zpow_zero, inv_one, one_smul]
  exact ⟨fun h => Formalism.L2.Ker.mem_of_forall_locP M h, fun h Q => Formalism.L2.Ker.le_locP' M Q h⟩

end Tw

end GlobalTheory.CommonReps

namespace GlobalTheory.CommonReps

theorem common_reps_halves : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι κ : Type) [Fintype ι] [Nonempty ι] [Fintype κ] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (AA0 : Submodule (𝓞 E) E) (SS : Finset (HeightOneSpectrum (𝓞 E))) (cl : ℕ) (N₀ : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N₀' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (N : κ → Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : κ → Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (g : 𝓞 E), δ ≠ 0 → (∃ k : 𝓞 E, g = 1 + (cl : 𝓞 E) * k) → (∀ i, (∀ x ∈ perO AA0 (N i) (N' i), g • x ∈ perO AA0 N₀ N₀') ∧ ∀ x ∈ perO AA0 N₀ N₀', g • x ∈ perO AA0 (N i) (N' i)) → relIdx (LamC emb δ AA0 N₀ N₀') (AC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → relIdx (BC emb δ AA0 SS N₀ N₀' cl) (LamC emb δ AA0 N₀ N₀' ⊓ AC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → relIdx (LamC emb δ AA0 N₀ N₀') (BC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → ∃ SX SA SB : Finset (VV ι a b), ∀ i, IsReps (LamC emb δ AA0 (N i) (N' i)) (AC emb δ AA0 SS (N i) (N' i) cl) SX ∧ IsReps (BC emb δ AA0 SS (N i) (N' i) cl) (LamC emb δ AA0 (N i) (N' i) ⊓ AC emb δ AA0 SS (N i) (N' i) cl) SA ∧ IsReps (LamC emb δ AA0 (N i) (N' i)) (BC emb δ AA0 SS (N i) (N' i) cl) SB := by
  intro E _ _ _ ι κ _ _ _ a b emb δ AA0 SS cl N₀ N₀' N N' g hδ hk hmv h1 h2 h3
  obtain ⟨k, hk⟩ := hk
  set f : Formalism.L2.Col.HomE E a b →+ VV ι a b := embH emb δ with hfdef
  have hf : Function.Injective f := embH_inj emb hδ
  have hinf : ∀ M A : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b),
      M.toAddSubgroup.map f ⊓ A.toAddSubgroup.map f = (M ⊓ A).toAddSubgroup.map f := fun M A =>
    (AddSubgroup.map_inf_eq M.toAddSubgroup A.toAddSubgroup f hf).symm
  have hexpS : ∀ Q, expS SS Q ≤ 1 ∧ -1 ≤ expS SS Q := fun Q => by
    rcases Formalism.L2.Ker.expS_cases SS Q with h | h | h <;> rw [h] <;> norm_num

  have hcA : ∀ M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b), ∀ y ∈ halfAO SS M cl, (cl : 𝓞 E) • y ∈ M := fun M y hy =>
    (mem_twO_zero M cl _).1 (natsmul_mem_twO M cl _ _ (fun Q => by linarith [(hexpS Q).1]) hy)
  have hcB : ∀ M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b), ∀ y ∈ halfBO SS M cl, (cl : 𝓞 E) • y ∈ M := fun M y hy =>
    (mem_twO_zero M cl _).1 (natsmul_mem_twO M cl _ _ (fun Q => by linarith [(hexpS Q).2]) hy)
  have hcM : ∀ M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b), ∀ y ∈ M, (cl : 𝓞 E) • y ∈ halfBO SS M cl := fun M y hy =>
    natsmul_mem_twO M cl (fun _ => 0) _ (fun Q => by linarith [(hexpS Q).1]) ((mem_twO_zero M cl y).2 hy)
  have hA : ∀ M M' : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b), (∀ x ∈ M, g • x ∈ M') → ∀ y ∈ halfAO SS M cl, g • y ∈ halfAO SS M' cl :=
    fun M M' h y hy => smul_mem_twO_of M M' cl _ g h hy
  have hB : ∀ M M' : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b), (∀ x ∈ M, g • x ∈ M') → ∀ y ∈ halfBO SS M cl, g • y ∈ halfBO SS M' cl :=
    fun M M' h y hy => smul_mem_twO_of M M' cl _ g h hy
  obtain ⟨SX, hSX⟩ := common_reps_of f hf g (cl : 𝓞 E) k hk (fun i => perO AA0 (N i) (N' i))
    (fun i => halfAO SS (perO AA0 (N i) (N' i)) cl) (perO AA0 N₀ N₀') (halfAO SS (perO AA0 N₀ N₀') cl)
    (fun i => hA _ _ (hmv i).1) (fun i => hA _ _ (hmv i).2) (fun i => (hmv i).1) (fun i => (hmv i).2)
    (fun i => hcA _) (hcA _) h1
  have h2' := h2
  simp only [LamC, AC, BC, laV] at h2'
  rw [hinf] at h2'
  obtain ⟨SA, hSA⟩ := common_reps_of f hf g (cl : 𝓞 E) k hk (fun i => halfBO SS (perO AA0 (N i) (N' i)) cl)
    (fun i => perO AA0 (N i) (N' i) ⊓ halfAO SS (perO AA0 (N i) (N' i)) cl) (halfBO SS (perO AA0 N₀ N₀') cl)
    (perO AA0 N₀ N₀' ⊓ halfAO SS (perO AA0 N₀ N₀') cl)
    (fun i y hy => ⟨(hmv i).1 _ hy.1, hA _ _ (hmv i).1 _ hy.2⟩) (fun i y hy => ⟨(hmv i).2 _ hy.1, hA _ _ (hmv i).2 _ hy.2⟩)
    (fun i => hB _ _ (hmv i).1) (fun i => hB _ _ (hmv i).2)
    (fun i y hy => hcM _ y hy.1) (fun y hy => hcM _ y hy.1) h2'
  obtain ⟨SB, hSB⟩ := common_reps_of f hf g (cl : 𝓞 E) k hk (fun i => perO AA0 (N i) (N' i))
    (fun i => halfBO SS (perO AA0 (N i) (N' i)) cl) (perO AA0 N₀ N₀') (halfBO SS (perO AA0 N₀ N₀') cl)
    (fun i => hB _ _ (hmv i).1) (fun i => hB _ _ (hmv i).2) (fun i => (hmv i).1) (fun i => (hmv i).2)
    (fun i => hcB _) (hcB _) h3
  refine ⟨SX, SA, SB, fun i => ⟨hSX i, ?_, hSB i⟩⟩
  have e : LamC emb δ AA0 (N i) (N' i) ⊓ AC emb δ AA0 SS (N i) (N' i) cl =
      (perO AA0 (N i) (N' i) ⊓ halfAO SS (perO AA0 (N i) (N' i)) cl).toAddSubgroup.map f := hinf _ _
  rw [e]
  exact hSA i

end GlobalTheory.CommonReps
end
end

section

namespace GlobalTheory.KerJ.CharVal

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta NumberField

theorem lamC_mem' {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {x : ℂ} (h : x ∈ Qbar) :
    lamC lam x = lam ⟨x, h⟩ := by
  unfold lamC; rw [dite_eq_left h]

theorem embT_mem (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : embT D τ x ∈ Qbar := by
  have hx : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have : IsAlgebraic ℚ ((embT D τ).toRatAlgHom x) := hx.algHom _
  exact (mem_algebraicClosure_iff).2 this

theorem chi_pow (D : D7) (t : D.Dt) (h : ℕ) (z : letI := D.host.cmStar; unitary D.host.E)
    (hp : PowRat D t h z) :
    ((D.chiD t : ℂˣ) : ℂ) ^ h = ∏ τ, (embT D τ (z : D.host.E))⁻¹ := by
  obtain ⟨-, k, hk, e⟩ := hp
  have h1 : D.chiD t ^ h = D.chiD (D.e1Dt z) := by
    rw [← map_pow, e, map_mul, D.chiD_UO k hk, mul_one]
  rw [← Units.val_pow_eq_pow_val, h1]
  exact D.rest_detCharacter_on_unitary_eq z

theorem chi_mem (D : D7) (t : D.Dt) (h : ℕ) (z : letI := D.host.cmStar; unitary D.host.E)
    (hp : PowRat D t h z) : ((D.chiD t : ℂˣ) : ℂ) ∈ Qbar := by
  have h0 : ((D.chiD t : ℂˣ) : ℂ) ^ h ∈ Qbar := by
    rw [chi_pow D t h z hp]
    exact prod_mem fun τ _ => inv_mem (embT_mem D τ _)
  exact (mem_algebraicClosure_iff).2 (((mem_algebraicClosure_iff).1 h0).of_pow hp.1)

theorem chiVal_holds (D : D7) : chiVal D := by
  intro p _ lam t h z hp
  refine ⟨chi_pow D t h z hp, ?_⟩
  have hm := chi_mem D t h z hp
  have e : (⟨((D.chiD t : ℂˣ) : ℂ), hm⟩ : Qbar) ^ h = ∏ τ, (⟨embT D τ (z : D.host.E), embT_mem D τ _⟩ : Qbar)⁻¹ := by
    apply Subtype.ext
    push_cast
    exact chi_pow D t h z hp
  rw [lamC_mem' lam hm, ← norm_pow, ← map_pow, e, map_prod, norm_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_inv₀, norm_inv, lamC_mem' lam (embT_mem D τ _)]

theorem key_norm {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {ι : Type*} [Fintype ι] (y κ : Qbar) (w : ι → Qbar)
    (s : ι → ℤ) (h n : ℕ) (hn : 0 < n) (e : y ^ h = (∏ τ, w τ ^ s τ) * κ) (hκ : κ ^ n = 1) :
    ‖lam y‖ ^ h = ∏ τ, ‖lam (w τ)‖ ^ s τ := by
  have h1 : ‖lam κ‖ = 1 := by
    have : ‖lam κ‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, hκ, map_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
  rw [← norm_pow, ← map_pow, e, map_mul, norm_mul, h1, mul_one, map_prod, norm_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_zpow₀, norm_zpow]

theorem val_of (D : D7) (ρ : D.Dt →* ℂˣ) (s : D.what₂.Tau → ℤ) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    (t : D.Dt) (h : ℕ) (z : letI := D.host.cmStar; unitary D.host.E) (hp : PowRat D t h z)
    (ha : ((ρ t : ℂˣ) : ℂ) ∈ Qbar) (hU : ∀ k ∈ D.UO, ∃ n : ℕ, 0 < n ∧ ρ k ^ n = 1)
    (hz : ((ρ (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, (embT D τ (z : D.host.E)) ^ (s τ)) :
    ‖lamC lam ((ρ t : ℂˣ) : ℂ)‖ ^ h = ∏ τ, ‖lamC lam (embT D τ (z : D.host.E))‖ ^ (s τ) := by
  obtain ⟨-, k, hk, e⟩ := hp
  obtain ⟨n, hn, h1⟩ := hU k hk
  have h1' : ((ρ k : ℂˣ) : ℂ) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, h1]; rfl
  have hkm : ((ρ k : ℂˣ) : ℂ) ∈ Qbar :=
    (mem_algebraicClosure_iff).2 (((mem_algebraicClosure_iff).1 (h1' ▸ one_mem Qbar)).of_pow hn)
  have e2 : ((ρ t : ℂˣ) : ℂ) ^ h = (∏ τ, (embT D τ (z : D.host.E)) ^ (s τ)) * ((ρ k : ℂˣ) : ℂ) := by
    rw [← hz, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← map_pow, e, map_mul]
  have := key_norm lam (⟨_, ha⟩ : Qbar) ⟨_, hkm⟩ (fun τ => ⟨embT D τ (z : D.host.E), embT_mem D τ _⟩) s h n hn
    (by
      apply (algebraMap Qbar ℂ).injective
      simp only [map_pow, map_mul, map_prod, map_zpow₀]
      exact e2)
    (by
      apply (algebraMap Qbar ℂ).injective
      simp only [map_pow, map_one]
      exact h1')
  rw [lamC_mem' lam ha, this]
  exact Finset.prod_congr rfl fun τ _ => by rw [lamC_mem' lam (embT_mem D τ _)]

theorem rhoVal_holds (D : D7) {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (mt : ℕ → D.Dt →* ℂˣ)
    (hR : rhoThreeOf D C mt) : rhoValOf D C mt := by
  intro p _ lam t h z hp i hi
  obtain ⟨a, b, c⟩ := hR i hi
  obtain ⟨⟨a1, -⟩, ⟨a2, -⟩⟩ := a t h z hp
  exact ⟨val_of D _ _ lam t h z hp a1 (fun k hk => by obtain ⟨n, hn, x, -⟩ := b k hk; exact ⟨n, hn, x⟩) (c z).1,
    val_of D _ _ lam t h z hp a2 (fun k hk => by obtain ⟨n, hn, -, x⟩ := b k hk; exact ⟨n, hn, x⟩) (c z).2⟩

theorem isUltra (p : ℕ) [Fact p.Prime] : IsUltrametricDist ℂ_[p] :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (PadicComplex.isNonarchimedean p)

theorem norm_le_one_of_int {K : Type} [NormedField K] [IsUltrametricDist K] (x : K)
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := K)).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := K))).mem_of_integral h1
  have h3 : NormedField.valuation x ≤ 1 := h2
  rw [NormedField.valuation_apply] at h3
  exact_mod_cast h3

section Nu

variable {E : Type} [Field E] [NumberField E] {K : Type} [NormedField K] [IsUltrametricDist K] (ψ : E →+* K)

theorem psi_int (a : 𝓞 E) : ‖ψ (a : E)‖ ≤ 1 :=
  norm_le_one_of_int _ ((RingOfIntegers.isIntegral_coe a).map (ψ : E →+* K).toIntAlgHom)

theorem pow_bound (𝔞 : Submodule (𝓞 E) E) (B : ℝ) (hB : ∀ x ∈ 𝔞, ‖ψ x‖ ≤ B) (hB0 : 0 ≤ B) :
    ∀ (n : ℕ), ∀ y ∈ 𝔞 ^ n, ‖ψ y‖ ≤ B ^ n := by
  intro n
  induction n with
  | zero =>
    intro y hy
    rw [pow_zero] at hy
    obtain ⟨a, rfl⟩ := Submodule.mem_one.mp hy
    rw [pow_zero]
    exact psi_int ψ a
  | succ n ih =>
    intro y hy
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy (fun m hm k hk => ?_) (fun x y hx hy => ?_)
    · rw [map_mul, norm_mul, pow_succ]
      exact mul_le_mul (ih m hm) (hB k hk) (norm_nonneg _) (pow_nonneg hB0 n)
    · rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)

theorem nu_pow (𝔞 : Submodule (𝓞 E) E) (h : ℕ) (h0 : h ≠ 0) (z : E)
    (e : 𝔞 ^ h = Submodule.span (𝓞 E) {z}) :
    sSup ((fun x : E => ‖ψ x‖) '' (𝔞 : Set E)) ^ h = ‖ψ z‖ := by
  set S := (fun x : E => ‖ψ x‖) '' (𝔞 : Set E) with hS
  have hne : S.Nonempty := ⟨_, 0, 𝔞.zero_mem, rfl⟩
  have hpow : ∀ x ∈ 𝔞, ‖ψ x‖ ^ h ≤ ‖ψ z‖ := by
    intro x hx
    have : x ^ h ∈ Submodule.span (𝓞 E) {z} := e ▸ Submodule.pow_mem_pow 𝔞 hx h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 this
    rw [← norm_pow, ← map_pow, ← ha, Algebra.smul_def, map_mul, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (psi_int ψ a)
  set b : ℝ := ‖ψ z‖ ^ ((h : ℝ)⁻¹) with hb
  have hb0 : 0 ≤ b := Real.rpow_nonneg (norm_nonneg _) _
  have hbh : b ^ h = ‖ψ z‖ := Real.rpow_inv_natCast_pow (norm_nonneg _) h0
  have hle : ∀ x ∈ 𝔞, ‖ψ x‖ ≤ b := fun x hx =>
    (pow_le_pow_iff_left₀ (norm_nonneg _) hb0 h0).1 (hbh ▸ hpow x hx)
  have hbd : BddAbove S := ⟨b, by rintro _ ⟨x, hx, rfl⟩; exact hle x hx⟩
  have hs0 : 0 ≤ sSup S := Real.sSup_nonneg (by rintro _ ⟨x, -, rfl⟩; exact norm_nonneg _)
  apply le_antisymm
  · rw [← hbh]
    exact pow_le_pow_left₀ hs0 (csSup_le hne (by rintro _ ⟨x, hx, rfl⟩; exact hle x hx)) h
  · have hz : z ∈ 𝔞 ^ h := e ▸ Submodule.mem_span_singleton_self z
    exact pow_bound ψ 𝔞 (sSup S) (fun x hx => le_csSup hbd ⟨x, hx, rfl⟩) hs0 h z hz

end Nu

noncomputable def psiT (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) : D.host.E →+* ℂ_[p] :=
  lam.comp ((embT D τ).codRestrict Qbar (embT_mem D τ))

theorem lamC_embT (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) (x : D.host.E) :
    lamC lam (embT D τ x) = psiT D lam τ x := lamC_mem' lam (embT_mem D τ x)

theorem nrmId_pow (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) (𝔞 : IdE D) (h : ℕ) (h0 : h ≠ 0)
    (z : D.host.E) (e : 𝔞 ^ h = Submodule.span (𝓞 D.host.E) {z}) :
    nrmId D lam τ 𝔞 ^ h = ‖lamC lam (embT D τ z)‖ := by
  unfold nrmId
  simp only [lamC_embT]
  haveI := isUltra p
  exact nu_pow (psiT D lam τ) 𝔞 h h0 z e

theorem nrmId_nonneg (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) (𝔞 : IdE D) :
    0 ≤ nrmId D lam τ 𝔞 :=
  Real.sSup_nonneg (by rintro _ ⟨x, -, rfl⟩; exact norm_nonneg _)

theorem root_eq {ι : Type*} [Fintype ι] (a : ℝ) (ha : 0 ≤ a) (ν f : ι → ℝ) (hν : ∀ τ, 0 ≤ ν τ) (s : ι → ℤ) (h : ℕ) (h0 : h ≠ 0)
    (hf : ∀ τ, ν τ ^ h = f τ) (e : a ^ h = ∏ τ, f τ ^ s τ) : a = ∏ τ, ν τ ^ s τ := by
  refine (pow_left_inj₀ ha (Finset.prod_nonneg fun τ _ => zpow_nonneg (hν τ) _) h0).1 ?_
  rw [e, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← hf τ, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem brRho_holds (D : D7) {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u))
    (mt : ℕ → D.Dt →* ℂˣ) (hR : rhoThreeOf D C mt) : brRhoOf D C mt := by
  intro idl hpin p _ lam t
  obtain ⟨k, z, hp⟩ := powRatAll_of D idl hpin (GlobalTheory.KernelScalarUnit.normOne_pow D) t
  obtain ⟨-, -, hmul, hz, -⟩ := hpin
  have h0 : k ≠ 0 := Nat.pos_iff_ne_zero.1 hp.1
  have hid : idl (QuotientGroup.mk t) ^ k = Submodule.span (𝓞 D.host.E) {(z : D.host.E)} := by
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    obtain ⟨-, c, hc, e⟩ := hp
    rw [← idl_pow hmul, ← hz z]
    congr 1
    rw [← QuotientGroup.mk_pow, e]
    exact QuotientGroup.mk_mul_of_mem _ hc
  have hf : ∀ τ, nrmId D lam τ (idl (QuotientGroup.mk t)) ^ k = ‖lamC lam (embT D τ (z : D.host.E))‖ :=
    fun τ => nrmId_pow D lam τ _ k h0 _ hid
  have hν : ∀ τ, 0 ≤ nrmId D lam τ (idl (QuotientGroup.mk t)) := fun τ => nrmId_nonneg D lam τ _
  refine ⟨?_, fun i hi => ?_⟩
  · have e := (chiVal_holds D p lam t k z hp).2
    have := root_eq _ (norm_nonneg _) _ _ hν (fun _ => (-1 : ℤ)) k h0 hf (by simpa only [zpow_neg_one] using e)
    simpa only [zpow_neg_one] using this
  · obtain ⟨x, y⟩ := rhoVal_holds D C mt hR p lam t k z hp i hi
    exact ⟨root_eq _ (norm_nonneg _) _ _ hν _ k h0 hf x, root_eq _ (norm_nonneg _) _ _ hν _ k h0 hf y⟩

end GlobalTheory.KerJ.CharVal
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem isUnit_natCast_of_coprime_local {R : Type*} [CommRing R] [IsLocalRing R] {p s : ℕ} (hp : ¬ IsUnit (p : R))
    (hs : Nat.Coprime s p) : IsUnit (s : R) := by
  have hc : IsCoprime (s : R) (p : R) := Nat.Coprime.cast hs
  obtain ⟨a, b, hab⟩ := hc
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := a * (s : R)) (b := b * (p : R)) (by rw [hab]; exact isUnit_one) with h | h
  · exact isUnit_of_mul_isUnit_right h
  · exact absurd (isUnit_of_mul_isUnit_right h) hp

theorem natCast_isUnit_localRing : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (v : X.Pl) (s : ℕ), Nat.Coprime s p → IsUnit (s : X.G.P.W v) :=
  fun X v _ hs => isUnit_natCast_of_coprime_local (X.G.P.setting v).p_unif.not_isUnit hs

end GlobalTheory.TwV
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

theorem _root_.GlobalTheory.T.exists_natCast_coprime_mem_heightOneSpectrum : ∀ {E : Type} [Field E] [NumberField E] (p : ℕ), p.Prime → ∀ (P : HeightOneSpectrum (𝓞 E)), ((p : ℕ) : 𝓞 E) ∉ P.asIdeal → ∃ ℓ : ℕ, 0 < ℓ ∧ ((ℓ : ℕ) : 𝓞 E) ∈ P.asIdeal ∧ Nat.Coprime ℓ p := by
  first | exact @GlobalTheory.natCast_mem_heightOneSpectrum_coprime | exact GlobalTheory.natCast_mem_heightOneSpectrum_coprime | (intros; apply GlobalTheory.natCast_mem_heightOneSpectrum_coprime <;> assumption)
end
