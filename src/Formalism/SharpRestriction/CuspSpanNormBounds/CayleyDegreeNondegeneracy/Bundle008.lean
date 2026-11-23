module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ForPrimeFlagLattice
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.InnerMemOneOfMemDualOrthLattice
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.MemSupIsotropicOfDualPairing
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle006
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GluingMassOfGluingFacts
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle007
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.LatticeClassesOfLiftTransitivity
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsND
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsRpowPow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cyc

variable {D : D7} {V : Type} [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
  [IsScalarTower (𝓞 D.host.E) D.host.E V] (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E)
  (M : Submodule (𝓞 D.host.E) V) (T : ℕ) (w₁ : V) (hw₁ : w₁ ∈ Formalism.HermitianLatticesTheory.dual h M)
  (hgen : ∀ w ∈ Formalism.HermitianLatticesTheory.dual h M, ∃ a : 𝓞 D.host.E, w + a • w₁ ∈ M)
  (hann : ∀ a : 𝓞 D.host.E, a • w₁ ∈ M ↔ ((T : ℕ) : 𝓞 D.host.E) ∣ a)


include hw₁ hgen in
theorem discriminant_one_generator : DiscGen h M 1 := by
  refine ⟨{Submodule.Quotient.mk ⟨w₁, hw₁⟩}, by simp, ?_⟩
  rw [eq_top_iff, Finset.coe_singleton]
  intro q _
  obtain ⟨⟨w, hw⟩, rfl⟩ := Submodule.mkQ_surjective _ q
  obtain ⟨a, ha⟩ := hgen w hw
  refine Submodule.mem_span_singleton.2 ⟨-a, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap]
  show (-a) • w₁ - w ∈ M
  have e : (-a) • w₁ - w = -(w + a • w₁) := by rw [neg_smul]; abel
  rw [e]
  exact M.neg_mem ha


include hw₁ hgen hann in
theorem corank_one_mod_prime_over (p : Ideal (𝓞 D.host.F)) (hp : p.IsMaximal) (hTp : ((T : ℕ) : 𝓞 D.host.F) ∈ p) :
    eP h M p = 1 := by
  set P : Ideal (𝓞 D.host.E) := pE D.host.F D.host.E p with hP
  set Md := Formalism.HermitianLatticesTheory.dual h M with hMd
  set K : Submodule (𝓞 D.host.E) Md := (M ⊔ P • Md).comap Md.subtype with hK
  have hTP : ((T : ℕ) : 𝓞 D.host.E) ∈ P := by
    have := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) hTp
    rw [map_natCast] at this
    exact this
  have hstep : ∀ n ∈ P • Md, ∃ b ∈ P, n - b • w₁ ∈ M := by
    intro n hn
    refine Submodule.smul_induction_on hn ?_ ?_
    · intro r hr w hw
      obtain ⟨c, hc⟩ := hgen w hw
      refine ⟨-(r * c), P.neg_mem (P.mul_mem_right _ hr), ?_⟩
      have e : r • w - (-(r * c)) • w₁ = r • (w + c • w₁) := by
        rw [neg_smul, sub_neg_eq_add, smul_add, mul_smul]
      rw [e]
      exact M.smul_mem _ hc
    · rintro x y ⟨b, hb, hx⟩ ⟨b', hb', hy⟩
      refine ⟨b + b', P.add_mem hb hb', ?_⟩
      have e : x + y - (b + b') • w₁ = (x - b • w₁) + (y - b' • w₁) := by rw [add_smul]; abel
      rw [e]
      exact M.add_mem hx hy
  set φ : 𝓞 D.host.E →ₗ[𝓞 D.host.E] (Md ⧸ K) :=
    LinearMap.toSpanSingleton (𝓞 D.host.E) (Md ⧸ K) (Submodule.Quotient.mk ⟨w₁, hw₁⟩) with hφ
  have hφa : ∀ a, φ a = Submodule.Quotient.mk (a • (⟨w₁, hw₁⟩ : Md)) := fun a => by
    rw [hφ, LinearMap.toSpanSingleton_apply, Submodule.Quotient.mk_smul]
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨⟨w, hw⟩, rfl⟩ := Submodule.mkQ_surjective _ q
    obtain ⟨a, ha⟩ := hgen w hw
    refine ⟨-a, ?_⟩
    rw [hφa, Submodule.mkQ_apply, Submodule.Quotient.eq, hK, Submodule.mem_comap]
    show (-a) • w₁ - w ∈ M ⊔ P • Md
    have e : (-a) • w₁ - w = -(w + a • w₁) := by rw [neg_smul]; abel
    rw [e]
    exact Submodule.mem_sup_left (M.neg_mem ha)
  have hker : LinearMap.ker φ = P := by
    ext a
    rw [LinearMap.mem_ker, hφa, Submodule.Quotient.mk_eq_zero, hK, Submodule.mem_comap]
    show a • w₁ ∈ M ⊔ P • Md ↔ a ∈ P
    constructor
    · intro ha
      obtain ⟨m, hm, n, hn, e⟩ := Submodule.mem_sup.1 ha
      obtain ⟨b, hb, hnb⟩ := hstep n hn
      have h1 : (a - b) • w₁ ∈ M := by
        have : (a - b) • w₁ = m + (n - b • w₁) := by rw [sub_smul, ← e]; abel
        rw [this]
        exact M.add_mem hm hnb
      obtain ⟨o, ho⟩ := (hann _).1 h1
      have : a = ((T : ℕ) : 𝓞 D.host.E) * o + b := by rw [← ho]; ring
      rw [this]
      exact P.add_mem (P.mul_mem_right _ hTP) hb
    · intro ha
      exact Submodule.mem_sup_right (Submodule.smul_mem_smul ha hw₁)
  have hcard : Nat.card (Md ⧸ K) = Ideal.absNorm p ^ 2 := by
    rw [← Nat.card_congr (φ.quotKerEquivOfSurjective hsurj).toEquiv,
      Nat.card_congr (Submodule.quotEquivOfEq _ _ hker).toEquiv, ← Formalism.MainNotions.BridgeLemma.absNorm_pE]
    exact (Ideal.absNorm_eq_natCard P).symm
  have hq := Formalism.MainNotions.BridgeLemma.absNorm_ge_two p hp
  show Nat.log (Ideal.absNorm p ^ 2) (Nat.card (Md ⧸ K)) = 1
  rw [hcard]
  have := Nat.log_pow (b := Ideal.absNorm p ^ 2) (by nlinarith) 1
  rwa [pow_one] at this

end Cyc

theorem orthLattice_structure_of_det (D : D7) (u : D.what₂.Word)
    (hdet : ForPrimeFlagLattice D u fun F0 Λ =>
      latDetH (D.sp.X 0).hT (L0X D Λ (lf D F0)) = ((Tu D u ^ D.R.f : ℕ) : ℝ)) : BaseLatticeStructure D u := by
  intro hTp h3 hsp F0 he hz Λ hrow
  obtain ⟨hΛ, hu, hlift, hconv⟩ := hrow.2.1
  obtain ⟨w₁, hw₁, hgen, hann⟩ := dual_orthLattice_quotient_cyclic F0 he hz Λ hΛ hu hlift.1 hconv.2 hTp.ne_zero
  exact ⟨orthLattice_isLattice F0 he hz Λ hΛ hu, orthLattice_isIntegral_of_unimodular Λ (lf D F0) hu, hdet hTp h3 hsp F0 he hz Λ hrow,
    discriminant_one_generator _ _ w₁ hw₁ hgen, fun p hp hTpp => corank_one_mod_prime_over _ _ (Tu D u) w₁ hw₁ hgen hann p hp hTpp⟩

end Formalism.MainNotions.BridgeLemma₂

end
end

section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence.LatticeLiftIndependence

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Aut

variable (D : D7) (u : D.what₂.Word) (hT : Tu D u ≠ 0) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (he : F0.e = D.sp.hypE) (hz : F0.z = D.zmOf u)

theorem mem_perpS_iff_mem_orth (y : (VS D).V) : y ∈ perpS (VS D) F0.X ↔ y ∈ orth (hS D) F0.X := by
  rw [Formalism.MainNotions.mem_orth_iff]
  rfl

theorem flag_stabilizer_map_isotropic (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ stabF D F0) :
    F0.X.map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.X := by
  have := hσ.2.1 D.R.rS
  rwa [partial_isotropic_top] at this

theorem flag_stabilizer_mem_isotropic (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ stabF D F0) (x : (VS D).V) (hx : x ∈ F0.X) :
    σ x ∈ F0.X := by
  rw [← flag_stabilizer_map_isotropic D u F0 σ hσ]
  exact ⟨x, hx, rfl⟩

theorem flag_stabilizer_mem_perp (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ stabF D F0) (y : (VS D).V)
    (hy : y ∈ perpS (VS D) F0.X) : σ y ∈ perpS (VS D) F0.X := by
  intro x hx
  rw [← flag_stabilizer_map_isotropic D u F0 σ hσ] at hx
  obtain ⟨x', hx', rfl⟩ := hx
  change (VS D).hT (σ x') (σ y) = 0
  rw [hσ.1 x' y]
  exact hy x' hx'

include he in
theorem embedding_add_smul_z_mem_perp (w : (D.sp.X 0).V) (c : D.host.E) : D.sp.iXY 0 w + c • F0.z ∈ perpS (VS D) F0.X := by
  intro x hx
  have h1 : (VS D).hT x (D.sp.iXY 0 w) = 0 :=
    Formalism.MainNotions.hT_swap_zero ((Formalism.MainNotions.mem_orth_iff _ _).1 (isotropic_le_orth_range D u F0 he hx) _ ⟨w, rfl⟩)
  have h2 : (VS D).hT x F0.z = 0 := Formalism.MainNotions.hT_zero_of_mem_X F0 F0.z_orth x hx
  rw [map_add (f := _), map_smul, h1, h2, smul_zero, add_zero]

def quotientClass (w : (D.sp.X 0).V) (c : D.host.E) : WbQ D F0 :=
  Submodule.Quotient.mk ⟨D.sp.iXY 0 w + c • F0.z, embedding_add_smul_z_mem_perp D u F0 he w c⟩

include hT hz in
theorem quotientClass_surjective (q : WbQ D F0) : ∃ w c, q = quotientClass D u F0 he w c := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨w, c, h⟩ := exists_decomp_orth_isotropic D u hT F0 he hz x.1 ((mem_perpS_iff_mem_orth D u F0 _).1 x.2)
  refine ⟨w, c, ?_⟩
  unfold quotientClass
  rw [Submodule.Quotient.eq]
  exact h

include hT hz in
theorem quotientClass_injective_left {w w' : (D.sp.X 0).V} {c c' : D.host.E} (h : quotientClass D u F0 he w c = quotientClass D u F0 he w' c') :
    w = w' := by
  unfold quotientClass at h
  rw [Submodule.Quotient.eq] at h
  have h' : D.sp.iXY 0 w + c • F0.z - (D.sp.iXY 0 w' + c' • F0.z) ∈ F0.X := h
  have hT' : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hT
  have hzW : ∀ v, (VS D).hT F0.z (D.sp.iXY 0 v) = 0 := fun v => by rw [hz]; exact z_orth_embedding D u v
  have h0 : (VS D).hT F0.z (D.sp.iXY 0 w + c • F0.z - (D.sp.iXY 0 w' + c' • F0.z)) = 0 :=
    Formalism.MainNotions.hT_swap_zero (Formalism.MainNotions.hT_zero_of_mem_X F0 F0.z_orth _ h')
  have hc : c = c' := by
    simp only [map_sub, map_add (f := _), map_smul, hzW, F0.z_norm, smul_eq_mul, zero_add] at h0
    have : (c - c') * ((Tu D u : ℕ) : D.host.E) = 0 := by linear_combination -h0
    rcases mul_eq_zero.1 this with h1 | h1
    · exact sub_eq_zero.1 h1
    · exact absurd h1 hT'
  subst hc
  have h2 : D.sp.iXY 0 (w - w') ∈ Wsp D ⊓ Xsp (lf D F0) := by
    refine ⟨⟨_, rfl⟩, ?_⟩
    have e : D.sp.iXY 0 (w - w') = D.sp.iXY 0 w + c • F0.z - (D.sp.iXY 0 w' + c • F0.z) := by
      rw [map_sub]; abel
    rw [e]
    exact h'
  rw [(Formalism.MainNotions.WHyp_Wsp D u hT (lf D F0) he hz).2.1, Submodule.mem_bot] at h2
  exact sub_eq_zero.1 (embedding_W_injective D (by rw [h2, map_zero]))

def ActsAsExtendByOne (φ : WbQ D F0 → WbQ D F0) (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) : Prop :=
  ∀ w c, φ (quotientClass D u F0 he w c) = quotientClass D u F0 he (γ w) c

theorem actsAsExtendByOne_of_induced (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ stabF D F0)
    (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) (hind : ∀ w, σ (D.sp.iXY 0 w) - D.sp.iXY 0 (γ w) ∈ F0.X)
    (φ : WbQ D F0 → WbQ D F0)
    (hφ : ∀ (x : perpS (VS D) F0.X) (hx : σ x.1 ∈ perpS (VS D) F0.X),
      φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨σ x.1, hx⟩) : ActsAsExtendByOne D u F0 he φ γ := by
  intro w c
  unfold quotientClass
  rw [hφ _ (flag_stabilizer_mem_perp D u F0 σ hσ _ (embedding_add_smul_z_mem_perp D u F0 he w c)), Submodule.Quotient.eq]
  change σ (D.sp.iXY 0 w + c • F0.z) - (D.sp.iXY 0 (γ w) + c • F0.z) ∈ F0.X
  have e : σ (D.sp.iXY 0 w + c • F0.z) - (D.sp.iXY 0 (γ w) + c • F0.z) = σ (D.sp.iXY 0 w) - D.sp.iXY 0 (γ w) := by
    rw [map_add (f := _), map_smul, hσ.2.2]
    abel
  rw [e]
  exact hind w

theorem gmap_latticeWithZ_of_induced (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ stabF D F0)
    (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) (hind : ∀ w, σ (D.sp.iXY 0 w) - D.sp.iXY 0 (γ w) ∈ F0.X)
    (Λ : LatV D) : gmap (extendByOne D γ) (latticeWithZ D F0 Λ) = latticeWithZ D F0 (gmap σ Λ) := by
  have hX := flag_stabilizer_map_isotropic D u F0 σ hσ
  have hLs := Lsub_gmap_of_isometry F0 σ hσ.1 hX Λ
  ext ⟨w, c⟩
  have e : (extendByOne D γ).symm (w, c) = (γ.symm w, c) := rfl
  rw [isomAct_mem_gmap, e, mem_latticeWithZ_iff, mem_latticeWithZ_iff, hLs, isomAct_mem_gmap]
  have hd : σ.symm (D.sp.iXY 0 w + c • F0.z) - (D.sp.iXY 0 (γ.symm w) + c • F0.z) ∈ F0.X := by
    have h1 := hind (γ.symm w)
    rw [LinearEquiv.apply_symm_apply] at h1
    have h2 : σ.symm (σ (D.sp.iXY 0 (γ.symm w)) - D.sp.iXY 0 w) ∈ F0.X := by
      rw [← Submodule.mem_map_equiv, hX]
      exact h1
    have hzs : σ.symm F0.z = F0.z := by
      rw [LinearEquiv.symm_apply_eq]
      exact hσ.2.2.symm
    have e3 : σ.symm (D.sp.iXY 0 w + c • F0.z) - (D.sp.iXY 0 (γ.symm w) + c • F0.z) =
        -(σ.symm (σ (D.sp.iXY 0 (γ.symm w)) - D.sp.iXY 0 w)) := by
      rw [map_add (f := _), map_smul, hzs, map_sub, LinearEquiv.symm_apply_apply]
      abel
    rw [e3]
    exact F0.X.neg_mem h2
  have hd' := isotropic_le_Lsub F0 Λ hd
  constructor
  · intro ha
    have := (Lsub Λ (lf D F0)).add_mem ha hd'
    simpa using this
  · intro hb
    have := (Lsub Λ (lf D F0)).sub_mem hb hd'
    simpa using this

end Aut

end Formalism.MainNotions.BridgeLemma₂

end
end

section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rows_exp_nd {m f s r c mx cf C : ℝ} (hm : m = 2 * r + 2) (hr : 0 ≤ r) (hf : 1 ≤ f) (hs : 0 ≤ s) (hc : 0 ≤ c)
    (hmx : 0 ≤ mx) (hcf : cf ≤ m) (hC : 4 + (c ^ 2 + 2 * mx) * (6 * c + 2) ≤ C ^ 2) :
    1 + 12 * f * (r + 1) ^ 2 + (c ^ 2 * m ^ 3 * f + 4 * (mx * m ^ 2 * f * (r + 1))) *
        (2 * (c * (s + m) * m + c * cf) + 2 * (c * r ^ 2) + 6 * (r + 1) ^ 2) ≤
      C * m ^ 2 * f * (C * (s + m) * m ^ 2) := by
  have hm2 : 2 ≤ m := by linarith
  set Mx : ℝ := (s + m) * m with hMx
  have hMx1 : m ^ 2 ≤ Mx := by rw [hMx]; nlinarith
  have hMx2 : m ≤ Mx := by nlinarith
  have hMx0 : 0 ≤ Mx := by nlinarith
  have hr1 : r + 1 = m / 2 := by linarith
  have hrm : r ^ 2 ≤ Mx := by nlinarith
  have e1 : c ^ 2 * m ^ 3 * f + 4 * (mx * m ^ 2 * f * (r + 1)) = (c ^ 2 + 2 * mx) * (m ^ 3 * f) := by rw [hr1]; ring
  have b1 : c * cf ≤ c * Mx := mul_le_mul_of_nonneg_left (hcf.trans hMx2) hc
  have b2 : c * r ^ 2 ≤ c * Mx := mul_le_mul_of_nonneg_left hrm hc
  have b3 : 6 * (r + 1) ^ 2 ≤ 2 * Mx := by rw [hr1]; nlinarith
  have br : 2 * (c * (s + m) * m + c * cf) + 2 * (c * r ^ 2) + 6 * (r + 1) ^ 2 ≤ (6 * c + 2) * Mx := by
    have : c * (s + m) * m = c * Mx := by rw [hMx]; ring
    rw [this]; nlinarith
  have hK0 : 0 ≤ m ^ 3 * f := by positivity
  have hp0 : 0 ≤ (c ^ 2 + 2 * mx) * (m ^ 3 * f) := by positivity
  have t1 : (c ^ 2 + 2 * mx) * (m ^ 3 * f) * (2 * (c * (s + m) * m + c * cf) + 2 * (c * r ^ 2) + 6 * (r + 1) ^ 2) ≤
      (c ^ 2 + 2 * mx) * (m ^ 3 * f) * ((6 * c + 2) * Mx) := mul_le_mul_of_nonneg_left br hp0
  have hKM : 0 ≤ m ^ 3 * f * Mx := by positivity
  have t2 : 1 + 12 * f * (r + 1) ^ 2 ≤ 4 * (m ^ 3 * f * Mx) := by
    rw [hr1]
    have a1 : f * m ^ 2 ≤ m ^ 3 * f * Mx := by
      have : (1 : ℝ) ≤ m * Mx := by nlinarith
      calc f * m ^ 2 = f * m ^ 2 * 1 := by ring
        _ ≤ f * m ^ 2 * (m * Mx) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = m ^ 3 * f * Mx := by ring
    have a2 : (1 : ℝ) ≤ f * m ^ 2 := by nlinarith
    nlinarith
  have t3 : (4 + (c ^ 2 + 2 * mx) * (6 * c + 2)) * (m ^ 3 * f * Mx) ≤ C ^ 2 * (m ^ 3 * f * Mx) :=
    mul_le_mul_of_nonneg_right hC hKM
  rw [e1]
  calc 1 + 12 * f * (r + 1) ^ 2 + (c ^ 2 + 2 * mx) * (m ^ 3 * f) *
        (2 * (c * (s + m) * m + c * cf) + 2 * (c * r ^ 2) + 6 * (r + 1) ^ 2)
      ≤ 4 * (m ^ 3 * f * Mx) + (c ^ 2 + 2 * mx) * (m ^ 3 * f) * ((6 * c + 2) * Mx) := add_le_add t2 t1
    _ = (4 + (c ^ 2 + 2 * mx) * (6 * c + 2)) * (m ^ 3 * f * Mx) := by ring
    _ ≤ C ^ 2 * (m ^ 3 * f * Mx) := t3
    _ = C * m ^ 2 * f * (C * (s + m) * m ^ 2) := by rw [hMx]; ring

section Rec

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

theorem rows_m_cast (D : D7) : (D.R.m : ℝ) = 2 * (D.R.rS : ℝ) + 2 := by
  have := d_m_eq D; exact_mod_cast this

theorem rows_cF_le {C' Cl Cg cb Cu cT CT C0 A : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A) :
    cF D.R.f ≤ D.R.m := by
  obtain ⟨_, _, _, _, h5, _⟩ := hH.1.1
  have h5' : Real.log (D.R.f : ℝ) ≤ Real.sqrt (D.R.rS : ℝ) := h5
  have hr : (1 : ℝ) ≤ D.R.rS := by exact_mod_cast hH.2.1.1
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast rows_f_pos D
  have hsq : Real.sqrt (D.R.rS : ℝ) ≤ D.R.rS := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hl2 := Real.log_two_gt_d9
  have hl0 : 0 ≤ Real.log (D.R.f : ℝ) := Real.log_nonneg hf
  have e : cF D.R.f = 2 + Real.log (D.R.f : ℝ) / Real.log 2 := by
    unfold cF lg2f Real.logb
    rw [Real.log_mul (by norm_num) (by linarith)]
    field_simp
    ring
  have h2 : Real.log (D.R.f : ℝ) / Real.log 2 ≤ 2 * Real.log (D.R.f : ℝ) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  rw [e, rows_m_cast]
  linarith

theorem rows_one_le_NT (D : D7) (w : D.what₂.Word) : 1 ≤ NT D w := by
  unfold NT
  exact one_le_pow₀ (by exact_mod_cast (D.mem w).A.T_prime.pos)

theorem rows_XiP_le (D : D7) (large₂ : SizeData₂ D) (w : D.what₂.Word) {c Ch C : ℝ} (hc : 0 ≤ c) (hcC : c ≤ C)
    (hC : 2 * pairCountExponentShift D c Ch ≤ C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m)) (s : ℕ) :
    XiS D w (rows_P D large₂ c Ch ^ 2) c s ≤ XiB D large₂ w C s := by
  have hb := d_two_le_b D large₂
  have hb0 : 0 < large₂.sc.b := by linarith
  have hP1 := rows_P_one_le D large₂ c Ch
  have hN := rows_one_le_NT D w
  have hPH : rows_P D large₂ c Ch ^ 2 ≤ Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.m : ℝ)) := by
    unfold rows_P Hb
    rw [rows_rpow_pow hb0, ← Real.rpow_mul hb0.le]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
  unfold XiB XiS Xi
  split_ifs
  · exact le_rfl
  · have h1 : (1 : ℝ) ≤ rows_P D large₂ c Ch ^ 2 * NT D w := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hP1) hN
    have h2 : rows_P D large₂ c Ch ^ 2 * NT D w ≤ Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.m : ℝ)) * NT D w :=
      mul_le_mul_of_nonneg_right hPH (by linarith)
    have h3 : (rows_P D large₂ c Ch ^ 2 * NT D w) ^ (c * (D.R.k : ℝ)) ≤
        (Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.m : ℝ)) * NT D w) ^ (C * (D.R.k : ℝ)) :=
      calc (rows_P D large₂ c Ch ^ 2 * NT D w) ^ (c * (D.R.k : ℝ))
          ≤ (Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.m : ℝ)) * NT D w) ^ (c * (D.R.k : ℝ)) :=
            Real.rpow_le_rpow (by linarith) h2 (by positivity)
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (h1.trans h2) (by gcongr)
    have h4 : (c * (D.R.k : ℝ)) ^ (D.R.k * D.R.f) ≤ (C * (D.R.k : ℝ)) ^ (D.R.k * D.R.f) :=
      pow_le_pow_left₀ (by positivity) (by gcongr) _
    exact mul_le_mul h4 h3 (Real.rpow_nonneg (by linarith) _) (by
      have : 0 ≤ C := hc.trans hcC
      positivity)
  · exact le_rfl

theorem rows_ndB_le {C' Cl Cg cb Cu cT CT C0 A c Ch δ C : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hc : 0 ≤ c) (hcC : c ≤ C) (hC1 : 1 ≤ C) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1)
    (hC : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C ^ 2) (s : ℕ) :
    rows_ndB D large₂ u u' c Ch δ s ≤
      LatticeSumBounds.ndRow C D.R.k D.R.m D.R.f s large₂.sc.b (gg D) D.host.v (GamS D large₂) (XiB D large₂ u C) * rDD D u' := by
  have hg2 := two_le_gg_of_count_hypotheses hH.1
  have hv1 : 1 ≤ D.host.v := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h19, _⟩ := hH.1.1
    exact h19
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast rows_f_pos D
  have hGam0 : 0 < GamS D large₂ := by unfold GamS; exact Real.exp_pos _
  have hP1 := rows_P_one_le D large₂ c Ch
  have hmx : 0 ≤ max (Ch - c) 0 := le_max_right _ _
  have hexp := rows_exp_nd (m := D.R.m) (f := D.R.f) (s := s) (r := D.R.rS) (c := c) (mx := max (Ch - c) 0)
    (cf := cF D.R.f) (C := C) (rows_m_cast D) (by positivity) hf (by positivity) hc hmx (rows_cF_le hH) hC
  have hpe2 : 2 * pairCountExponentShift D c Ch ≤ C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m) := by
    have e1 : pairCountExponentShift D c Ch = (c ^ 2 + 2 * max (Ch - c) 0) * ((D.R.m : ℝ) ^ 3 * D.R.f) := by
      unfold pairCountExponentShift
      have : (D.R.rS : ℝ) + 1 = (D.R.m : ℝ) / 2 := by rw [rows_m_cast]; ring
      rw [this]; ring
    have h0 : 0 ≤ (D.R.m : ℝ) ^ 3 * D.R.f := by positivity
    have h1 : 2 * (c ^ 2 + 2 * max (Ch - c) 0) ≤ C ^ 2 := by
      have : 0 ≤ (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c) := by positivity
      nlinarith
    rw [e1]
    calc 2 * ((c ^ 2 + 2 * max (Ch - c) 0) * ((D.R.m : ℝ) ^ 3 * D.R.f))
        = (2 * (c ^ 2 + 2 * max (Ch - c) 0)) * ((D.R.m : ℝ) ^ 3 * D.R.f) := by ring
      _ ≤ C ^ 2 * ((D.R.m : ℝ) ^ 3 * D.R.f) := mul_le_mul_of_nonneg_right h1 h0
      _ = _ := by ring
  have := rows_num_nd (k := D.R.k) (m := D.R.m) (f := D.R.f) (s := s) (r := D.R.rS) (b := large₂.sc.b) (g := gg D)
    (v := D.host.v) (Γ := GamS D large₂) (c := c) (C := C) (pe := pairCountExponentShift D c Ch) (E1 := pairCountExponent D c s)
    (cr := c * (D.R.rS : ℝ) ^ 2) (δ := δ) (rD := rDD D u') (XiP := XiS D u (rows_P D large₂ c Ch ^ 2) c s)
    (Xi := XiB D large₂ u C) (d_two_le_b D large₂) (by linarith) (by linarith) hGam0.le hc hcC hC1 hδ0 hδ
    (rows_rDD_nonneg D u') (rows_XiS_nonneg D u (by positivity) hc s) (rows_XiP_le D large₂ u hc hcC hpe2 s)
    (by unfold pairCountExponentShift pairCountExponent; exact hexp)
  unfold rows_ndB rows_R rows_Phi
  exact this

theorem rows_RowBound_mono {Q : D.s.Pair u u' → Prop} {B B' : ℝ} (h : RowBound X Y Q B) (hB : B ≤ B')
    (hdim : 0 ≤ dimPi (hc := D.hcW) u) : RowBound X Y Q B' := fun S hS =>
  (h S hS).trans (mul_le_mul_of_nonneg_left hB (mul_nonneg (rows_massRows_nonneg Y) hdim))

theorem rows_RowsND_record {C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm C : ℝ} {q : ℕ}
    (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) (hδ : δ ≤ 1) (hcC : c ≤ C) (hC1 : 1 ≤ C)
    (hC : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C ^ 2)
    (hq2 : 4 * (c * D.R.k) + 4 * pairCountExponent D c D.R.k + 4 * (c * (D.R.rS : ℝ) ^ 2) + C2 * (D.R.m : ℝ) ^ 2 / 2 +
      12 * ((D.R.rS : ℝ) + 1) ^ 2 ≤ (q : ℝ) / ((D.R.rS : ℝ) + 1)) : RowsND X Y C := by
  intro s hs hsk
  refine rows_RowBound_mono Y (rows_ND_record Y h s hs hsk ?_) (rows_ndB_le h.hH h.hc hcC hC1 h.hδ hδ hC s) h.hdim.le
  have : pairCountExponent D c s ≤ pairCountExponent D c D.R.k := by
    unfold pairCountExponent
    have hsk' : (s : ℝ) ≤ D.R.k := by exact_mod_cast hsk
    have := h.hc
    gcongr
  linarith

end Rec

end Formalism.MainNotions.BridgeLemma₂

end
end
