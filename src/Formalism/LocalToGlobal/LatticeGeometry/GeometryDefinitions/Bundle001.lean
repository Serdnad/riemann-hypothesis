module

public import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.PClassD
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle006
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle012
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SatakeDualWeyl.Statement

@[expose] public section

section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P

namespace Formalism.L2.Geo.Def.PC

section LG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] 𝔸
local notation "𝒮" => tensInt (F := F) 𝔸 (intOE E) (intAd F)

theorem lg (Λ : Submodule (𝓞 E) (n → E)) (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤)
    (y : n → 𝒜) (hy : ∀ v : HeightOneSpectrum (𝓞 F), (fun i => prV (E := E) v (y i)) ∈ latV v Λ) :
    y ∈ latA (F := F) Λ := by
  classical
  obtain ⟨c₁, hc₁, h₁⟩ := adelstabL_lower (F := F) Λ hspan
  choose d0 hd0 hd0m using fun i => levelaf_denom (F := F) (E := E) (y i)
  have hE : ∀ v, (fun i => afsplitEps E v * y i) ∈ latA (F := F) Λ := by
    intro v
    have := ie_lat v Λ _ (hy v)
    simpa only [afsplit_decomp] using this
  have h3 : ∀ i, levelafC E (∏ j, d0 j) * y i ∈ 𝒮 := by
    intro i
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_comm (d0 i), levelafC_mul, mul_assoc]
    exact mul_mem (levelafC_mem _) (hd0m i)
  have h4 := h₁ _ h3
  obtain ⟨T, u, hu, h1⟩ := unit_away (c₁ * ∏ j, d0 j)
    (mul_ne_zero hc₁ (Finset.prod_ne_zero_iff.2 fun j _ => hd0 j))
  have hu' : (1 : E) ⊗ₜ[F] u ∈ 𝒮 := Subring.subset_closure (Or.inr ⟨⟨u, hu⟩, rfl⟩)
  have hone : (1 : 𝒜) = ((1 : E) ⊗ₜ[F] u) * levelafC E (c₁ * ∏ j, d0 j) + ∑ v ∈ T, afsplitEps E v := by
    rw [Algebra.TensorProduct.one_def]
    conv_lhs => rw [h1]
    rw [TensorProduct.tmul_add, TensorProduct.tmul_sum]
    congr 1
    rw [levelafC, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm u]
  have hy' : y = (⟨_, hu'⟩ : 𝒮) • (fun i => levelafC E c₁ * (levelafC E (∏ j, d0 j) * y i)) +
      ∑ v ∈ T, (fun i => afsplitEps E v * y i) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, Subring.smul_def, smul_eq_mul]
    conv_lhs => rw [← one_mul (y i), hone]
    rw [levelafC_mul, add_mul, Finset.sum_mul]
    ring
  rw [hy']
  exact add_mem (Submodule.smul_mem _ _ h4) (sum_mem fun v _ => hE v)

omit [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in
theorem mem_stab_of {A R : Type} [CommRing A] [CommRing R] [Algebra R A] (Λ : Submodule R (n → A)) (g : GL n A)
    (h1 : ∀ x ∈ Λ, (g : Matrix n n A) *ᵥ x ∈ Λ)
    (h2 : ∀ x ∈ Λ, ((g⁻¹ : GL n A) : Matrix n n A) *ᵥ x ∈ Λ) : g ∈ stabGL Λ := by
  unfold stabGL
  refine fun x => ⟨h1 x, fun hx => ?_⟩
  have h3 := h2 _ hx
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h3

theorem pr_mulVec (v : HeightOneSpectrum (𝓞 F)) (x : GL n 𝒜) (y : n → 𝒜) :
    (fun i => prV (E := E) v (((x : Matrix n n 𝒜) *ᵥ y) i)) =
      ((bc (prV (E := E) v) x : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ
        (fun i => prV (E := E) v (y i)) := by
  unfold prV bc
  funext i
  rw [Units.coe_map]
  exact RingHom.map_mulVec _ _ _ i

private theorem prV_inclE' (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    prV (E := E) v (inclE (F := F) 𝔸 e) = inclE (F := F) (v.adicCompletion F) e := by
  simp [prV, inclE, Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.map_tmul]

private theorem stabGL_latA_pr_of_mem (Λ : Submodule (𝓞 E) (n → E)) (x : GL n 𝒜)
    (hx : x ∈ stabGL (latA (F := F) Λ)) (v : HeightOneSpectrum (𝓞 F)) (z : n → E ⊗[F] v.adicCompletion F)
    (hz : z ∈ latV v Λ) :
    ((bc (prV (E := E) v) x : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ z ∈
      latV v Λ := by
  have hx' : ∀ y : n → 𝒜, y ∈ latA (F := F) Λ ↔ (x : Matrix n n 𝒜) *ᵥ y ∈ latA (F := F) Λ := hx
  unfold latV latS at hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    have hmem : (fun i => inclE (F := F) 𝔸 (l i)) ∈ latA (F := F) Λ :=
      Submodule.subset_span ⟨l, hl, rfl⟩
    have h2 := pr_lat (F := F) v Λ _ ((hx' _).1 hmem)
    rw [pr_mulVec] at h2
    have e : (fun i => prV (E := E) v (inclE (F := F) 𝔸 (l i))) =
        (fun i => inclE (F := F) (v.adicCompletion F) (l i)) := funext fun i => prV_inclE' v (l i)
    rw [e] at h2
    exact h2
  | zero => simp
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
  | smul s a _ ha =>
    have e : ((bc (prV (E := E) v) x : GL n (E ⊗[F] v.adicCompletion F)) :
          Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ (s • a) =
        s • (((bc (prV (E := E) v) x : GL n (E ⊗[F] v.adicCompletion F)) :
          Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ a) := by
      funext i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Subring.smul_def, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e]
    exact Submodule.smul_mem _ s ha

theorem stab_pr (Λ : Submodule (𝓞 E) (n → E)) (x : GL n 𝒜) (hx : x ∈ stabGL (latA (F := F) Λ))
    (v : HeightOneSpectrum (𝓞 F)) : bc (prV (E := E) v) x ∈ stabGL (latV v Λ) := by
  have hxi : x⁻¹ ∈ stabGL (latA (F := F) Λ) := inv_mem hx
  have key : ∀ z : n → E ⊗[F] v.adicCompletion F, z ∈ latV v Λ ↔
      ((bc (prV (E := E) v) x : GL n (E ⊗[F] v.adicCompletion F)) :
        Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ z ∈ latV v Λ := by
    intro z
    refine ⟨stabGL_latA_pr_of_mem Λ x hx v z, fun hz => ?_⟩
    have h := stabGL_latA_pr_of_mem Λ x⁻¹ hxi v _ hz
    rwa [map_inv, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec] at h
  exact key

theorem stab_of_loc (Λ : Submodule (𝓞 E) (n → E)) (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤)
    (x : GL n 𝒜) (hx : ∀ v : HeightOneSpectrum (𝓞 F), bc (prV (E := E) v) x ∈ stabGL (latV v Λ)) :
    x ∈ stabGL (latA (F := F) Λ) := by
  have fwd : ∀ g : GL n 𝒜, (∀ v : HeightOneSpectrum (𝓞 F), bc (prV (E := E) v) g ∈ stabGL (latV v Λ)) →
      ∀ y ∈ latA (F := F) Λ, (g : Matrix n n 𝒜) *ᵥ y ∈ latA (F := F) Λ := by
    intro g hg y hy
    refine lg (F := F) Λ hspan _ fun v => ?_
    rw [pr_mulVec]
    have hgv : ∀ z : n → E ⊗[F] v.adicCompletion F, z ∈ latV v Λ ↔
        ((bc (prV (E := E) v) g : GL n (E ⊗[F] v.adicCompletion F)) :
          Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ z ∈ latV v Λ := hg v
    exact (hgv _).1 (pr_lat (F := F) v Λ y hy)
  refine mem_stab_of (latA (F := F) Λ) x (fwd x hx) (fwd x⁻¹ fun v => ?_)
  rw [map_inv]
  exact inv_mem (hx v)

end LG

end Formalism.L2.Geo.Def.PC
end
end

section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P

namespace Formalism.L2.Geo.Def.PN

section LG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] 𝔸
local notation "𝒮" => tensInt (F := F) 𝔸 (intOE E) (intAd F)

theorem latS_mul_mem {R : Type} [CommRing R] [Algebra F R] (S : Subring (E ⊗[F] R))
    (Λ : Submodule (𝓞 E) (n → E)) {c : E ⊗[F] R} (hc : c ∈ S) {w : n → E ⊗[F] R}
    (hw : w ∈ latS (F := F) R S Λ) : (fun i => c * w i) ∈ latS (F := F) R S Λ :=
  Submodule.smul_mem _ (⟨c, hc⟩ : S) hw

theorem prV_latS (Λ : Submodule (𝓞 E) (n → E)) (v : HeightOneSpectrum (𝓞 F)) {u : n → 𝒜}
    (hu : u ∈ latS (F := F) 𝔸 𝒮 Λ) :
    (fun i => prV (E := E) v (u i)) ∈ latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, hx, rfl⟩ := hu
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero =>
    have : (fun i => prV (E := E) v ((0 : n → 𝒜) i)) = 0 := by ext i; simp
    rw [this]; exact zero_mem _
  | add a b _ _ ha hb =>
    have : (fun i => prV (E := E) v ((a + b) i)) =
        (fun i => prV (E := E) v (a i)) + (fun i => prV (E := E) v (b i)) := by
      ext i; simp
    rw [this]; exact add_mem ha hb
  | smul s a _ ha =>
    have : (fun i => prV (E := E) v ((s • a) i)) =
        (fun i => prV (E := E) v (s : 𝒜) * prV (E := E) v (a i)) := by
      ext i; rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul]
    rw [this]; exact latS_mul_mem _ Λ (afsplit_prV_int v _ s.2) ha

theorem IE_latS (Λ : Submodule (𝓞 E) (n → E)) (v : HeightOneSpectrum (𝓞 F))
    {h : n → E ⊗[F] v.adicCompletion F}
    (hh : h ∈ latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ) :
    (fun i => afsplitIE v (h i)) ∈ latS (F := F) 𝔸 𝒮 Λ := by
  induction hh using Submodule.span_induction with
  | mem h hh =>
    obtain ⟨x, hx, rfl⟩ := hh
    have : (fun i => afsplitIE v (inclE (F := F) (v.adicCompletion F) (x i))) =
        (fun i => afsplitEps E v * inclE (F := F) 𝔸 (x i)) := by
      ext i
      rw [← afsplit_decomp, afsplit_prV_inclE]
    rw [this]
    exact latS_mul_mem _ Λ (afsplit_eps_int v) (Submodule.subset_span ⟨x, hx, rfl⟩)
  | zero =>
    have : (fun i => afsplitIE v ((0 : n → E ⊗[F] v.adicCompletion F) i)) = 0 := by ext i; simp
    rw [this]; exact zero_mem _
  | add a b _ _ ha hb =>
    have : (fun i => afsplitIE v ((a + b) i)) =
        (fun i => afsplitIE v (a i)) + (fun i => afsplitIE v (b i)) := by
      ext i; simp
    rw [this]; exact add_mem ha hb
  | smul s a _ ha =>
    have : (fun i => afsplitIE v ((s • a) i)) =
        (fun i => afsplitIE v (s : E ⊗[F] v.adicCompletion F) * afsplitIE v (a i)) := by
      ext i; rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul]
    rw [this]; exact latS_mul_mem _ Λ (afsplit_IE_int v _ s.2) ha

theorem latS_of_prod (Λ : Submodule (𝓞 E) (n → E)) (T : Finset (HeightOneSpectrum (𝓞 F))) :
    ∀ w : n → 𝒜, (∀ v ∈ T, (fun i => prV (E := E) v (w i)) ∈ latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ) →
    (fun i => (∏ v ∈ T, (1 - afsplitEps E v)) * w i) ∈ latS (F := F) 𝔸 𝒮 Λ →
    w ∈ latS (F := F) 𝔸 𝒮 Λ := by
  classical
  induction T using Finset.induction_on with
  | empty => intro w _ h; simpa using h
  | insert v T hv ih =>
    intro w hloc h
    have h1 : (fun i => (1 - afsplitEps E v) * w i) ∈ latS (F := F) 𝔸 𝒮 Λ := by
      apply ih
      · intro u hu
        have huv : u ≠ v := fun e => hv (e ▸ hu)
        have : (fun i => prV (E := E) u ((1 - afsplitEps E v) * w i)) =
            (fun i => prV (E := E) u (w i)) := by
          ext i
          rw [map_mul, map_sub, map_one, afsplit_prV_eps_ne v u huv, sub_zero, one_mul]
        rw [this]
        exact hloc u (Finset.mem_insert_of_mem hu)
      · have : (fun i => (∏ v ∈ T, (1 - afsplitEps E v)) * ((1 - afsplitEps E v) * w i)) =
            (fun i => (∏ v ∈ insert v T, (1 - afsplitEps E v)) * w i) := by
          ext i
          rw [Finset.prod_insert hv]; ring
        rw [this]; exact h
    have h2 := IE_latS Λ v (hloc v (Finset.mem_insert_self v T))
    have : w = (fun i => afsplitIE v (prV (E := E) v (w i))) + (fun i => (1 - afsplitEps E v) * w i) := by
      ext i
      rw [Pi.add_apply, afsplit_decomp]; ring
    rw [this]; exact add_mem h2 h1

theorem prod_eps_eq (d : 𝓞 F) (hd : d ≠ 0) :
    ∃ a ∈ intAd F, (∏ v ∈ (levelaf_finite_places d hd).toFinset, (1 - afsplitEps E v)) =
      ((1 : E) ⊗ₜ[F] a) * levelafC E d := by
  classical
  set T := (levelaf_finite_places d hd).toFinset with hT
  have hdF : algebraMap (𝓞 F) F d ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
  refine ⟨algebraMap F 𝔸 (algebraMap (𝓞 F) F d)⁻¹ * ∏ v ∈ T, (1 - afsplitI v 1), ?_, ?_⟩
  · intro u
    have e : (algebraMap F 𝔸 (algebraMap (𝓞 F) F d)⁻¹ * ∏ v ∈ T, (1 - afsplitI v 1)) u =
        algebraMap F (u.adicCompletion F) (algebraMap (𝓞 F) F d)⁻¹ *
          ∏ v ∈ T, (1 - (afsplitI v (1 : v.adicCompletion F)) u) := by
      have := map_prod (evalV F u) (fun v => (1 - afsplitI v (1 : v.adicCompletion F))) T
      rw [afsplit_mul_apply]
      congr 1
    rw [e]
    by_cases hu : u ∈ T
    · rw [Finset.prod_eq_zero hu (by rw [afsplitI_self, sub_self]), mul_zero]
      exact zero_mem _
    · rw [Finset.prod_eq_one (fun v hv => by
        rw [afsplitI_ne v u (fun e => hu (e ▸ hv)), sub_zero]), mul_one]
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀]
      have h1 : ¬ Valued.v (algebraMap (𝓞 F) (u.adicCompletion F) d) < 1 := by
        simpa [hT] using hu
      have h2 : Valued.v (algebraMap (𝓞 F) (u.adicCompletion F) d) ≤ 1 := levelaf_int_mem_v u d
      have h3 : Valued.v (algebraMap (𝓞 F) (u.adicCompletion F) d) = 1 := le_antisymm h2 (not_lt.1 h1)
      rw [IsScalarTower.algebraMap_apply (𝓞 F) F (u.adicCompletion F)] at h3
      rw [h3, inv_one]
  · have e1 : ∀ v : HeightOneSpectrum (𝓞 F), (1 - afsplitEps E v) =
        (Algebra.TensorProduct.includeRight : 𝔸 →ₐ[F] 𝒜) (1 - afsplitI v 1) := by
      intro v
      rw [map_sub, map_one]
      rfl
    rw [Finset.prod_congr rfl (fun v _ => e1 v), ← map_prod, levelafC,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.includeRight_apply]
    congr 1
    rw [mul_right_comm, IsScalarTower.algebraMap_apply (𝓞 F) F 𝔸, ← map_mul, inv_mul_cancel₀ hdF, map_one,
      one_mul]

theorem latS_of_loc (Λ : Submodule (𝓞 E) (n → E)) (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤)
    (w : n → 𝒜) (hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      (fun i => prV (E := E) v (w i)) ∈ latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ) :
    w ∈ latS (F := F) 𝔸 𝒮 Λ := by
  classical
  choose d0 hd0 hd0m using fun i => levelaf_denom (F := F) (E := E) (w i)
  obtain ⟨c, hc, hcm⟩ := adelstabL_lower (F := F) Λ hspan
  have h1 : ∀ i, levelafC E (∏ j, d0 j) * w i ∈ 𝒮 := by
    intro i
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_comm (d0 i), levelafC_mul, mul_assoc]
    exact mul_mem (levelafC_mem _) (hd0m i)
  have h2 := hcm _ h1
  have hd : c * ∏ j, d0 j ≠ 0 := mul_ne_zero hc (Finset.prod_ne_zero_iff.2 fun j _ => hd0 j)
  obtain ⟨a, ha, hae⟩ := prod_eps_eq (E := E) _ hd
  refine latS_of_prod Λ (levelaf_finite_places _ hd).toFinset w (fun v _ => hloc v) ?_
  rw [hae]
  have ha' : (1 : E) ⊗ₜ[F] a ∈ 𝒮 := Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
  have := latS_mul_mem _ Λ ha' h2
  convert this using 2
  rw [levelafC_mul]; ring

end LG

end Formalism.L2.Geo.Def.PN
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct

namespace Formalism.L2.Geo.Def

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

section Frames

variable {K : Type} [Field K] [NumberField K] [StarRing K]


open Classical in
def frameOf {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  if h : ∃ Y : Matrix ι ι ℂ, IsUnit Y.det ∧ (Y⁻¹).conjTranspose * Y⁻¹ = M then h.choose else 1


end Frames

end Formalism.L2.Geo.Def
end
end
