module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle056
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle005
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice

namespace GlobalTheory.Proof.TwistSupportPeriodicLevels

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_KO_of_latOf_eq {Y : Type} [Fintype Y] [DecidableEq Y] {g : GL Y k} (h : latOf g = latOf 1) :
    g ∈ KO k Y := by
  have h1 := latOf_le_iff.mp h.le
  have h2 := latOf_le_iff.mp h.ge
  simp only [inv_one, one_mul, mul_one] at h1 h2
  exact mem_KO.mpr ⟨h1, h2⟩

variable {r s s' : Type} [Fintype r] [DecidableEq r]

theorem intM_of_parPhi_ne_zero (δ : kˣ →* ℂˣ) {x : Matrix (r ⊕ s) (r ⊕ s') k} (hx : parPhi δ x ≠ 0) : IntM x := by
  obtain ⟨⟨g, hg, e⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff δ).mp hx
  rw [← Matrix.fromBlocks_toBlocks x, intM_fromBlocks]
  refine ⟨?_, h12, h21.intM, h22⟩
  rw [← e]
  exact intM_of_mem_KO hg

private theorem parPhi_add_eq_of_maxM {δ : kˣ →* ℂˣ} (hδ : IsTame δ) {x y : Matrix (r ⊕ s) (r ⊕ s') k}
    (hy : MaxM y) (hx : parPhi δ x ≠ 0) : parPhi δ (x + y) = parPhi δ x := by

  obtain ⟨⟨g, hg, e⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff δ).mp hx
  have hyb : MaxM (Matrix.fromBlocks y.toBlocks₁₁ y.toBlocks₁₂ y.toBlocks₂₁ y.toBlocks₂₂) := by
    rwa [Matrix.fromBlocks_toBlocks]
  obtain ⟨hy11, hy12, hy21, hy22⟩ := maxM_fromBlocks.mp hyb
  have a11 : (x + y).toBlocks₁₁ = x.toBlocks₁₁ + y.toBlocks₁₁ := Matrix.ext fun _ _ => rfl
  have a12 : (x + y).toBlocks₁₂ = x.toBlocks₁₂ + y.toBlocks₁₂ := Matrix.ext fun _ _ => rfl
  have a21 : (x + y).toBlocks₂₁ = x.toBlocks₂₁ + y.toBlocks₂₁ := Matrix.ext fun _ _ => rfl
  have a22 : (x + y).toBlocks₂₂ = x.toBlocks₂₂ + y.toBlocks₂₂ := Matrix.ext fun _ _ => rfl
  have hM : MaxM ((x + y).toBlocks₁₁ - g.val) := by
    rw [a11, ← e]
    simpa using hy11
  obtain ⟨u, hu, hgu⟩ := exists_mul_KOne hg hM
  have k21 : MaxM (x + y).toBlocks₂₁ := by rw [a21]; exact h21.add hy21
  have k12 : IntM (x + y).toBlocks₁₂ := by rw [a12]; exact h12.add hy12.intM
  have k22 : IntM (x + y).toBlocks₂₂ := by rw [a22]; exact h22.add hy22.intM
  rw [parPhi_of_mem δ (mul_mem hg (KOne_le_KO hu)) hgu k21 k12 k22, parPhi_of_mem δ hg e h21 h12 h22]
  simp only [map_mul, tame_det_of_mem_KOne hδ hu, mul_one]


open Classical in
theorem parPhi_add {δ : kˣ →* ℂˣ} (hδ : IsTame δ) (x : Matrix (r ⊕ s) (r ⊕ s') k) {y : Matrix (r ⊕ s) (r ⊕ s') k}
    (hy : MaxM y) : parPhi δ (x + y) = parPhi δ x := by
  by_cases hx : parPhi δ x = 0
  · by_contra hne
    have hxy : parPhi δ (x + y) ≠ 0 := fun h0 => hne (h0.trans hx.symm)
    have back := parPhi_add_eq_of_maxM hδ hy.neg hxy
    rw [add_neg_cancel_right] at back
    exact hxy (back.symm.trans hx)
  · exact parPhi_add_eq_of_maxM hδ hy hx

variable {ι ι' Y Y' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']

theorem intM_of_coords {F : LatFrame k ι Y} {F' : LatFrame k ι' Y'} (hF : F.bas ∈ KO k Y) (hF' : F'.bas ∈ KO k Y')
    {x : Matrix Y Y' k} (h : IntM (F.coords F' x)) : IntM x := by
  have hM : IntM ((F.bas⁻¹).val * x * F'.bas.val) := fun a b => by
    have := h (F.ord.symm a) (F'.ord.symm b)
    simp only [LatFrame.coords, Matrix.submatrix_apply, Equiv.apply_symm_apply] at this
    exact this
  have hx : F.bas.val * ((F.bas⁻¹).val * x * F'.bas.val) * (F'.bas⁻¹).val = x := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      Units.mul_inv, Matrix.mul_one]
  rw [← hx]
  exact ((intM_of_mem_KO hF).mul hM).mul (mem_KO.mp hF').2

theorem maxM_coords {F : LatFrame k ι Y} {F' : LatFrame k ι' Y'} (hF : F.bas ∈ KO k Y) (hF' : F'.bas ∈ KO k Y')
    {y : Matrix Y Y' k} (h : MaxM y) : MaxM (F.coords F' y) := by
  have hM : MaxM ((F.bas⁻¹).val * y * F'.bas.val) :=
    ((mem_KO.mp hF).2.mul_maxM h).mul_intM (intM_of_mem_KO hF')
  show MaxM (((F.bas⁻¹).val * y * F'.bas.val).submatrix F.ord F'.ord)
  exact fun i j => hM (F.ord i) (F'.ord j)

theorem coords_add (F : LatFrame k ι Y) (F' : LatFrame k ι' Y') (x y : Matrix Y Y' k) :
    F.coords F' (x + y) = F.coords F' x + F.coords F' y := by
  unfold LatFrame.coords
  rw [Matrix.mul_add, Matrix.add_mul]
  ext i j
  simp

theorem stabLat_le_KO {g : GL Y k} (hg : g ∈ KO k Y) : stabLat g ≤ KO k Y := by
  intro a ha
  have hc := mem_stabLat.mp ha
  have e : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem hg hc) (inv_mem hg)

private theorem transport_parPhi_add_eq_of_maxM [Fintype s] [DecidableEq s] [Fintype s'] [DecidableEq s'] {δ : kˣ →* ℂˣ}
    (hδ : IsTame δ) {F : LatFrame k (r ⊕ s) Y} {F' : LatFrame k (r ⊕ s') Y'} (hF : F.bas ∈ KO k Y)
    (hF' : F'.bas ∈ KO k Y') (x : Matrix Y Y' k) {y : Matrix Y Y' k} (hy : MaxM y) :
    F.transport F' (parPhi δ) (x + y) = F.transport F' (parPhi δ) x := by
  show parPhi δ (F.coords F' (x + y)) = parPhi δ (F.coords F' x)
  rw [coords_add]
  exact parPhi_add hδ _ (maxM_coords hF hF' hy)

end

theorem ofTwist_support_periodic_levels : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s : ℕ) (r t Z : Type) [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] [Fintype Z] [DecidableEq Z] (X : ℕ → Type) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (μ₀ : ℕ → kˣ →* ℂˣ) (F : ∀ j c, j + c = s + 1 → LatFrame k (Ix r t j) (X j ⊕ Fin c)) (Ftop : LatFrame k (Ix r t (s + 2)) Z), (∀ j c h, latOf (F j c h).bas = latOf 1) → (∀ j c h x, (Chain.ofTwist δ hδ μ₀ F Ftop).Phi j c h x ≠ 0 → IntM x) ∧ (∀ j c h x y, MaxM y → (Chain.ofTwist δ hδ μ₀ F Ftop).Phi j c h (x + y) = (Chain.ofTwist δ hδ μ₀ F Ftop).Phi j c h x) ∧ ∀ j c h, ((Chain.ofTwist δ hδ μ₀ F Ftop).lev j c h).J ≤ KO k (X j ⊕ Fin c) := by
  intro k _ _ _ _ s r t Z _ _ _ _ _ _ X _ _ δ hδ μ₀ F Ftop hF
  have hK : ∀ j c h, (F j c h).bas ∈ KO k (X j ⊕ Fin c) := fun j c h => mem_KO_of_latOf_eq (hF j c h)
  refine ⟨fun j c h x hx => ?_, fun j c h x y hy => ?_, fun j c h => ?_⟩
  · exact intM_of_coords (hK (j + 1) c (by omega)) (hK j (c + 1) (by omega)) (intM_of_parPhi_ne_zero δ hx)
  · exact transport_parPhi_add_eq_of_maxM hδ (hK (j + 1) c (by omega)) (hK j (c + 1) (by omega)) x hy
  · exact ((TypeDatum.map_conj (parahoric r (Fin j × t) δ hδ) (F j c h)).2.2).trans (stabLat_le_KO (hK j c h))

end GlobalTheory.Proof.TwistSupportPeriodicLevels
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound

namespace GlobalTheory.SatakeBound.Rep

section Abstract

variable {G X V : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]

theorem norm_le_card {ι : Type} {π : Representation ℂ G V} (hπ : IsUnitarisable π) {v : V} (hv : v ≠ 0)
    (S : Finset ι) (g : ι → G) (l : ℂ) (h : ∑ c ∈ S, π (g c) v = l • v) : ‖l‖ ≤ S.card := by
  obtain ⟨B, b1, b2, b3⟩ := hπ
  letI : InnerProductSpace.Core ℂ V := UnitInd.core B b1 b2
  letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore _
  have hn : ∀ x : G, ‖π x v‖ = ‖v‖ := fun x => by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) v]
    exact congrArg (fun z : ℂ => √(RCLike.re z)) (b3 x v v)
  have h1 : ‖l‖ * ‖v‖ ≤ S.card * ‖v‖ := by
    rw [← norm_smul, ← h]
    refine (norm_sum_le _ _).trans ?_
    simp [hn]
  exact le_of_mul_le_mul_right h1 (norm_pos_iff.2 hv)

theorem sum_fixed (ρ : Representation ℂ G X) (K : Subgroup G) {w : X} (hw : ∀ x ∈ K, ρ x w = w)
    (S : Finset (G ⧸ K)) (hS : ∀ x ∈ K, ∀ c ∈ S, x • c ∈ S) (x : G) (hx : x ∈ K) :
    ρ x (∑ c ∈ S, ρ c.out w) = ∑ c ∈ S, ρ c.out w := by

  rw [map_sum]
  refine Finset.sum_nbij' (fun c => x • c) (fun c => x⁻¹ • c) (hS x hx) (hS _ (inv_mem hx))
    (fun c _ => by simp) (fun c _ => by simp) fun c _ => ?_
  have h1 : x • c = ((x * c.out : G) : G ⧸ K) := by
    conv_lhs => rw [← QuotientGroup.out_eq' c]
    rfl
  obtain ⟨y, hy⟩ := QuotientGroup.mk_out_eq_mul K (x * c.out)
  rw [h1, hy, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hw y y.2]

theorem exists_vector [TopologicalSpace G] [IsTopologicalGroup G] {ρ : Representation ℂ G X}
    {π : Representation ℂ G V} (hρ : IsSmooth ρ) (hπ : IsUnitarisable π) {K : Subgroup G}
    (hK : IsCompact (K : Set G)) (f : ρ.IntertwiningMap π) (hf : Function.Surjective f)
    (hs : fixed π K ≠ ⊥) (E : X →ₗ[ℂ] ℂ) (hE : ∀ u : X, (∀ x ∈ K, ρ x u = u) → E u = 0 → u = 0) :
    ∃ w : X, (∀ x ∈ K, ρ x w = w) ∧ E w = 1 ∧ ∀ S : Finset (G ⧸ K), (∀ x ∈ K, ∀ c ∈ S, x • c ∈ S) →
      ‖∑ c ∈ S, E (ρ c.out w)‖ ≤ S.card := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hs
  obtain ⟨u, rfl⟩ := hf v
  obtain ⟨w, hw, hfw⟩ := IwahoriOnto.exists_fixed_map_eq hρ hK f.toLinearMap u fun h hh => by
    show f (ρ h u) = f u
    rw [f.isIntertwining]
    simpa using hv ⟨h, hh⟩
  have hw' : ∀ x ∈ K, ρ x w = w := fun x hx => by simpa using hw ⟨x, hx⟩
  have hfw0 : f w ≠ 0 := fun h => hv0 (hfw.symm.trans h)
  have hEw : E w ≠ 0 := fun h => hfw0 (by rw [hE w hw' h, map_zero])
  obtain ⟨z, hz, hEz, hfz⟩ : ∃ z : X, (∀ x ∈ K, ρ x z = z) ∧ E z = 1 ∧ f z ≠ 0 :=
    ⟨(E w)⁻¹ • w, fun x hx => by rw [map_smul, hw' x hx], by simp [hEw], by
      rw [map_smul]; exact smul_ne_zero (inv_ne_zero hEw) hfw0⟩
  refine ⟨z, hz, hEz, fun S hS => norm_le_card hπ hfz S (fun c => c.out) _ ?_⟩
  have h1 := hE (∑ c ∈ S, ρ c.out z - (∑ c ∈ S, E (ρ c.out z)) • z)
    (fun x hx => by rw [map_sub, sum_fixed ρ K hz S hS x hx, map_smul, hz x hx])
    (by rw [map_sub, map_sum, map_smul, hEz, smul_eq_mul, mul_one, sub_self])
  have h2 := congrArg f (sub_eq_zero.1 h1)

  rw [map_sum, map_smul] at h2
  rw [← h2]
  exact Finset.sum_congr rfl fun c _ => (f.isIntertwining _ _ _ _).symm

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem law (α : Fin n → ℂˣ)
    (f : IndSp (points (Fin n)) ((ofChar (torusChar fun i => unrChar k (α i))).comp
      (leviTorus k (Fin n)).symm.toMonoidHom))
    (b : GL (Fin n) k) (hb : b ∈ borel k (Fin n)) (t : Fin n → kˣ)
    (ht : ∀ i, (b : Matrix (Fin n) (Fin n) k) i i = t i) (g : GL (Fin n) k) :
    f.1.1 (b * g) = (∏ i : Fin n, ((α i : ℂ) * (((resCard k : ℝ) ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ))
      ^ ord k (t i)) * f.1.1 g := by
  refine (parInd_law _ _ f ⟨b, hb⟩ g).trans ?_
  show _ • ofChar _ _ (f.1.1 g) = _
  rw [ofChar_apply, torusChar_apply, deltaHalf_apply, smul_eq_mul, ← mul_assoc,
    Units.coe_prod, Units.coe_prod, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have e : Matrix.GeneralLinearGroup.det (leviProj _ (points (Fin n)) ⟨b, hb⟩ i) = t i := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique]
    exact ht i
  show _ * ((unrChar k (α i)
    (Matrix.GeneralLinearGroup.det (leviProj _ (points (Fin n)) ⟨b, hb⟩ i)) : ℂˣ) : ℂ) = _
  have e2 : ((modExp (fun _ : Fin n => Unit) i : ℂ) / 2) =
      ((-(((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ) := by
    rw [modExp_fin _ (fun _ => by simp)]
    push_cast
    ring
  have hq : (0 : ℝ) ≤ resCard k := Nat.cast_nonneg _
  rw [e, e2, val_absPow_ofReal, unrChar_apply, Units.val_zpow_eq_zpow_val, mul_zpow, mul_comm,
    GlobalTheory.LGrp.nabs_eq_zpow, ← Complex.ofReal_zpow, ← Real.rpow_intCast, ← Real.rpow_intCast,
    ← Real.rpow_mul hq, ← Real.rpow_mul hq]
  congr 3
  push_cast
  ring

theorem exists_sph : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (α : Fin n → ℂˣ), IsUnitarisable π → HasSatake π α → ∃ φ : GL (Fin n) k → ℂ, IsBorelSph k (fun i : Fin n => (α i : ℂ) * (((resCard k : ℝ) ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ)) φ ∧ HasBoundedSums k φ := by
  intro k _ _ _ _ n V _ _ π α hu ⟨_, hs, S, f, hf⟩
  have hsm : IsSmooth S.toRepresentation :=
    IsSubquotient.isSmooth ⟨S, .id _, Function.surjective_id⟩ (isSmooth_parInd _ _)
  let E : S.toSubmodule →ₗ[ℂ] ℂ := ⟨⟨fun u => u.1.1.1 1, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  have hr : ∀ u : S.toSubmodule, (∀ x ∈ KO k (Fin n), S.toRepresentation x u = u) →
      ∀ g, ∀ x ∈ KO k (Fin n), u.1.1.1 (g * x) = u.1.1.1 g := fun u h g x hx =>
    congrArg (fun z : S.toSubmodule => z.1.1.1 g) (h x hx)
  obtain ⟨w, hw, hw1, hb⟩ := exists_vector hsm hu SplitFlip.isCompact_KO f hf hs E fun u h h0 => by
    refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun g => ?_)))
    obtain ⟨b, hb, x, hx, rfl⟩ := iwasawa_blockTriangular k (Fin n) Fin.val g
    have h1 := parInd_law _ _ u.1 ⟨b, (mem_borel _).2 hb⟩ 1
    have h2 : u.1.1.1 1 = 0 := h0
    rw [h2, map_zero, smul_zero, mul_one] at h1
    exact (hr u h b x hx).trans h1
  refine ⟨w.1.1.1, ⟨hr w hw, fun b hb t ht => ?_⟩, fun T hT => ?_⟩
  · have h1 := law α w.1 b hb t ht 1
    have h2 : w.1.1.1 1 = 1 := hw1
    rwa [h2, mul_one, mul_one] at h1
  · refine le_of_eq_of_le ?_ (hb T hT)
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    show _ = w.1.1.1 (1 * c.out)
    rw [one_mul]

end GlobalTheory.SatakeBound.Rep
end
end

section

noncomputable section

open scoped TensorProduct
open GlobalTheory.PRep GlobalTheory.JHMult

namespace GlobalTheory.SmGL

namespace AdditiveExpand

variable {G : Type} [Group G] [TopologicalSpace G]


open Classical in
theorem jhMult_rep_rep (c d : IrrCl G) : jhMult c.rep.ρ d.rep.ρ = if c = d then 1 else 0 := by
  split_ifs with h
  · subst h; exact jhMult_self c.rep.irr
  · by_contra h0
    obtain ⟨φ⟩ := (jhMult_ne_zero_iff.1 h0).nonempty_equiv c.rep.irr d.rep.irr
    exact h (c.cl_rep.symm.trans ((IrrRep.cl_eq_iff.2 ⟨φ.symm⟩).trans d.cl_rep))

variable (φ : SmRep G → ℕ∞) (h0 : ∀ B : SmRep G, Subsingleton B.V → φ B = 0)
  (hadd : ∀ (B B₁ B₂ : SmRep G) (ι : B₁.ρ.IntertwiningMap B.ρ) (p : B.ρ.IntertwiningMap B₂.ρ),
    Function.Injective ι → Function.Surjective p → (∀ u, p (ι u) = 0) →
      (∀ v, p v = 0 → ∃ u, ι u = v) → φ B = φ B₁ + φ B₂)

variable [IsTopologicalGroup G]

def sub (B : SmRep G) (S : Subrepresentation B.ρ) : SmRep G :=
  ⟨S.toSubmodule, S.toRepresentation,
    IsSubquotient.isSmooth ⟨S, .id _, Function.surjective_id⟩ B.smooth⟩

def quo (B : SmRep G) (S T : Subrepresentation B.ρ) : SmRep G :=
  ⟨_, subQuot S T, IsSubquotient.isSmooth
    ⟨S, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.Quotient.mk_surjective _⟩ B.smooth⟩

include h0 hadd

theorem congr_equiv {B B' : SmRep G} (e : B.ρ.Equiv B'.ρ) : φ B = φ B' := by
  have hs : Subsingleton (sub B ⊥).V := inferInstanceAs (Subsingleton (⊥ : Submodule ℂ B.V))
  have := hadd B (sub B ⊥) B' ⟨Submodule.subtype _, fun _ => rfl⟩ e.toIntertwiningMap
    Subtype.val_injective e.surjective
    (fun u => by rw [Subsingleton.elim u 0, map_zero, map_zero])
    (fun v hv => ⟨0, by
      rw [map_zero]
      exact (e.injective (hv.trans (map_zero e).symm)).symm⟩)
  rw [this, h0 _ hs, zero_add]

theorem one_coord₂ (B : SmRep G) (h : HasFiniteLength B.ρ) (T : Finset (IrrCl G))
    (hT : ∀ c ∉ T, jhMult c.rep.ρ B.ρ = 0) :
    φ B = ∑ c ∈ T, jhMult c.rep.ρ B.ρ * φ (SmRep.ofIrr c.rep) := by
  classical
  have ψ := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := B.ρ)
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 h
  have : WellFoundedGT (Subrepresentation B.ρ) := ψ.toOrderEmbedding.wellFoundedGT
  have : WellFoundedLT (Subrepresentation B.ρ) := ψ.toOrderEmbedding.wellFoundedLT
  have key : ∀ S : Subrepresentation B.ρ, (∀ c ∉ T, jhMult c.rep.ρ S.toRepresentation = 0) →
      φ (sub B S) = ∑ c ∈ T, jhMult c.rep.ρ S.toRepresentation * φ (SmRep.ofIrr c.rep) := by
    intro S
    induction S using WellFoundedLT.induction with
    | ind S ih =>
    intro hS'
    rcases eq_or_ne S ⊥ with rfl | hS
    · have hs : Subsingleton (⊥ : Subrepresentation B.ρ).toSubmodule :=
        inferInstanceAs (Subsingleton (⊥ : Submodule ℂ B.V))
      rw [h0 _ hs]
      exact (Finset.sum_eq_zero fun c _ => by
        rw [jhMult_of_subsingleton c.rep.irr, zero_mul]).symm
    obtain ⟨R, -, hR⟩ := exists_le_covBy_of_lt (bot_lt_iff_ne_bot.2 hS)
    let σ : IrrRep G := ⟨_, subQuot S R, (quo B S R).smooth, isIrreducible_subQuot hR⟩
    obtain ⟨e⟩ := σ.nonempty_equiv_rep
    have hm : ∀ c : IrrCl G, jhMult c.rep.ρ S.toRepresentation =
        jhMult c.rep.ρ R.toRepresentation + if c = σ.cl then 1 else 0 := fun c => by
      rw [jhMult_of_le c.rep.irr hR.le, ← jhMult_rep_rep, jhMult_congr_right _ e]
    have hp : ∀ v : S.toSubmodule, (Submodule.Quotient.mk v : (quo B S R).V) = 0 ↔
        v.1 ∈ R.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
    have h1 := hadd (sub B S) (sub B R) (quo B S R) ⟨Submodule.inclusion hR.le, fun _ => rfl⟩
      ⟨Submodule.mkQ _, fun _ => rfl⟩ (Submodule.inclusion_injective hR.le)
      (Submodule.Quotient.mk_surjective _) (fun u => (hp _).2 u.2)
      fun v hv => ⟨⟨v.1, (hp v).1 hv⟩, rfl⟩
    have h2 : φ (quo B S R) = φ (SmRep.ofIrr σ.cl.rep) :=
      (congr_equiv φ h0 hadd (B := SmRep.ofIrr σ.cl.rep) (B' := quo B S R) e).symm
    have h3 : σ.cl ∈ T := by
      by_contra hn
      have := hS' _ hn
      rw [hm] at this
      simp at this
    rw [h1, h2, ih R hR.lt fun c hc => (add_eq_zero.1 ((hm c).symm.trans (hS' c hc))).1]
    simp only [hm, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', if_pos h3]
  have h4 := key ⊤ (by simpa only [jhMult_congr_right _ (topEquiv B.ρ)] using hT)
  rw [← congr_equiv φ h0 hadd (B := sub B ⊤) (B' := B) (topEquiv B.ρ), h4]
  simp only [jhMult_congr_right _ (topEquiv B.ρ)]

end AdditiveExpand


open AdditiveExpand in
theorem additive_family_expand : ∀ (α : Type) [Fintype α] [DecidableEq α] (Γ : α → Type) [∀ i, Group (Γ i)] [∀ i, TopologicalSpace (Γ i)] [∀ i, IsTopologicalGroup (Γ i)] (Φ : (∀ i, GlobalTheory.SmGL.SmRep (Γ i)) → ℕ∞), (∀ (A : ∀ i, GlobalTheory.SmGL.SmRep (Γ i)) (i : α), Subsingleton (A i).V → Φ A = 0) → (∀ (A : ∀ i, GlobalTheory.SmGL.SmRep (Γ i)) (i : α) (B B₁ B₂ : GlobalTheory.SmGL.SmRep (Γ i)) (ι : B₁.ρ.IntertwiningMap B.ρ) (p : B.ρ.IntertwiningMap B₂.ρ), Function.Injective ι → Function.Surjective p → (∀ u, p (ι u) = 0) → (∀ v, p v = 0 → ∃ u, ι u = v) → Φ (Function.update A i B) = Φ (Function.update A i B₁) + Φ (Function.update A i B₂)) → ∀ (A : ∀ i, GlobalTheory.SmGL.SmRep (Γ i)), (∀ i, GlobalTheory.SmGL.HasFiniteLength (A i).ρ) → ∀ T : Finset (∀ i, GlobalTheory.SmGL.IrrCl (Γ i)), (∀ t ∉ T, ∃ i, GlobalTheory.SmGL.jhMult (t i).rep.ρ (A i).ρ = 0) → Φ A = ∑ t ∈ T, (∏ i, GlobalTheory.SmGL.jhMult (t i).rep.ρ (A i).ρ) * Φ (fun i => GlobalTheory.SmGL.SmRep.ofIrr (t i).rep) := by
  intro α _ _ Γ _ _ _ Φ h0 hadd
  classical
  have key : ∀ s : Finset α, ∀ A : ∀ i, SmRep (Γ i),
      (∀ i ∉ s, ∃ c : IrrCl (Γ i), A i = SmRep.ofIrr c.rep) → (∀ i, HasFiniteLength (A i).ρ) →
      ∀ T : Finset (∀ i, IrrCl (Γ i)), (∀ t ∉ T, ∃ i, jhMult (t i).rep.ρ (A i).ρ = 0) →
      Φ A = ∑ t ∈ T, (∏ i, jhMult (t i).rep.ρ (A i).ρ) * Φ (fun i => SmRep.ofIrr (t i).rep) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro A hA _ T hT
      choose c hc using fun i => hA i (Finset.notMem_empty i)
      obtain rfl : A = fun i => SmRep.ofIrr (c i).rep := funext hc
      have hm : ∀ t : ∀ i, IrrCl (Γ i),
          (∏ i, jhMult (t i).rep.ρ (SmRep.ofIrr (c i).rep).ρ) = if t = c then 1 else 0 := fun t => by
        have : ∀ i, jhMult (t i).rep.ρ (SmRep.ofIrr (c i).rep).ρ = if t i = c i then 1 else 0 :=
          fun i => jhMult_rep_rep _ _
        simp only [this, Finset.prod_ite_zero, Finset.prod_const_one, Finset.mem_univ,
          forall_const, funext_iff]
      have h3 : c ∈ T := by
        by_contra hn
        obtain ⟨i, hi⟩ := hT c hn
        exact one_ne_zero ((jhMult_self (c i).rep.irr).symm.trans hi)
      simp only [hm, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', if_pos h3]
    | insert i s his ih =>
      intro A hA hl T hT
      let μ : ∀ j, IrrCl (Γ j) → SmRep (Γ j) → ℕ∞ := fun j c B => jhMult c.rep.ρ B.ρ
      have hC := finite_constituents (hl i)
      have h1 := one_coord₂ (fun B => Φ (Function.update A i B))
        (fun B hB => h0 _ i (by rw [Function.update_self]; exact hB)) (hadd A i) (A i) (hl i)
        hC.toFinset (fun c hc => by simpa using hc)
      simp only [Function.update_eq_self] at h1
      have h2 : ∀ c ∈ hC.toFinset, Φ (Function.update A i (SmRep.ofIrr c.rep)) =
          ∑ t ∈ T, ((if t i = c then 1 else 0) * ∏ j ∈ Finset.univ.erase i, μ j (t j) (A j)) *
            Φ (fun i => SmRep.ofIrr (t i).rep) := by
        intro c hc
        rw [ih (Function.update A i (SmRep.ofIrr c.rep)) ?_ ?_ T ?_]
        · refine Finset.sum_congr rfl fun t _ => ?_
          congr 1
          change ∏ j, μ j (t j) (Function.update A i (SmRep.ofIrr c.rep) j) = _
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self]
          congr 1
          · exact jhMult_rep_rep _ _
          · exact Finset.prod_congr rfl fun j hj => by
              rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
        · intro j hj
          rcases eq_or_ne j i with rfl | hji
          · exact ⟨c, Function.update_self ..⟩
          · rw [Function.update_of_ne hji]
            exact hA j (by simp [hji, hj])
        · intro j
          rcases eq_or_ne j i with rfl | hji
          · rw [Function.update_self]; exact c.rep.hasFiniteLength
          · rw [Function.update_of_ne hji]; exact hl j
        · intro t ht
          obtain ⟨j, hj⟩ := hT t ht
          refine ⟨j, ?_⟩
          change μ j (t j) (Function.update A i (SmRep.ofIrr c.rep) j) = 0
          rcases eq_or_ne j i with rfl | hji
          · rw [Function.update_self]
            refine (jhMult_rep_rep _ _).trans (if_neg ?_)
            rintro rfl
            exact (hC.mem_toFinset.1 hc) hj
          · rw [Function.update_of_ne hji]; exact hj
      rw [h1, Finset.sum_congr rfl fun c hc => by rw [h2 c hc, Finset.mul_sum], Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      change _ = (∏ j, μ j (t j) (A j)) * _
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq]
      split_ifs with h
      · exact (mul_assoc _ _ _).symm
      · have : μ i (t i) (A i) = 0 := by simpa using h
        rw [this, zero_mul, zero_mul]
  exact fun A hl T hT => key Finset.univ A (fun i hi => absurd (Finset.mem_univ i) hi) hl T hT

end GlobalTheory.SmGL
end
end
