module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LeAdicClosure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle006
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.finrank_structMapY_range :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → Module.rank k (F.strY k) ≤ C₀ := by
  intro l _ k _ _ F C₀ hF
  obtain ⟨-, -, hΨst, -, -⟩ := UpperTheory.V.Fr.star hF
  choose gv hgv using hF.f3
  set ρ := chRep (F.Ψ⁻¹.comp F.del.ker.subtype) with hρ
  have hρapp : ∀ (g : F.G0) (w : k), ρ g w = ((F.Ψ (g : F.Γ) : k))⁻¹ * w := by
    intro g w
    simp [hρ, chRep]
  have hne : ∀ γ : F.Γ, ((F.Ψ γ : k)) ≠ 0 := fun γ => Units.ne_zero _
  have hl : ∀ v s, ((F.loc0 v s : F.G0) : F.Γ) = F.loc v s := fun _ _ => rfl
  have ha : ∀ v, ((F.Ψ (F.loc v (gv v)) : k)) ≠ 1 := by
    intro v h
    apply hgv v
    rw [Units.val_eq_one.mp h, one_pow]
  have hΨlc : IsLocallyConstant (fun g : F.G0 => F.Ψ (g : F.Γ)) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro g
    refine ⟨(fun h : F.G0 => g⁻¹ * h) ⁻¹' ((↑) ⁻¹' (F.Ψ.ker : Set F.Γ)), ?_, ?_, ?_⟩
    · exact (hF.Ψ_open.preimage continuous_subtype_val).preimage (continuous_const.mul continuous_id)
    · simp
    · intro h hh
      simp only [Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker, Subgroup.coe_mul,
        Subgroup.coe_inv, map_mul, map_inv] at hh
      exact (inv_mul_eq_one.mp hh).symm
  let xf : (F.G0 → k) → F.G0 → k := fun y g => ((F.Ψ (g : F.Γ) : k))⁻¹ * y g
  let af : (F.G0 → k) → F.V × Bool → k := fun y p =>
    if p.2 then (1 - ((F.Ψ (F.loc p.1 (gv p.1)) : k))⁻¹)⁻¹ * y (F.star (F.loc0 p.1 (gv p.1)))
    else -((((F.Ψ (F.loc p.1 (gv p.1)) : k)) - 1)⁻¹ * y (F.loc0 p.1 (gv p.1)))
  have hmem : ∀ y ∈ F.strY k, (xf y, af y) ∈ Z1C F.loc2 ρ (fun _ => ⊥) := by
    intro y hy
    obtain ⟨hlc, hcoc, hg0, hα, hβ⟩ := hy
    refine ⟨?_, ?_, ?_⟩
    · exact hΨlc.comp₂ hlc (fun u w => ((u : k))⁻¹ * w)
    · intro s t
      rw [hρapp]
      simp only [xf]
      rw [hcoc s t, Subgroup.coe_mul, map_mul, Units.val_mul, smul_eq_mul]
      have := hne s
      have := hne t
      field_simp
    · rintro ⟨v, b⟩ s
      rw [Submodule.mem_bot, hρapp]
      dsimp only
      have h1 : ((F.Ψ (F.loc v (gv v)) : k)) - 1 ≠ 0 := sub_ne_zero.mpr (ha v)
      have h2 : 1 - ((F.Ψ (F.loc v (gv v)) : k))⁻¹ ≠ 0 := by
        rw [sub_ne_zero]
        intro h
        exact ha v (inv_eq_one.mp h.symm)
      have := hne (F.loc v (gv v))
      have := hne (F.loc v s)
      cases b
      · obtain ⟨α, hα'⟩ := hα v
        have key : af y (v, false) = -α := by
          simp only [af, Bool.false_eq_true, if_false]
          rw [hα' (gv v), smul_eq_mul]
          field_simp
        rw [key]
        simp only [xf, Frame.loc2, Bool.false_eq_true, if_false]
        rw [hl, hα' s, smul_eq_mul]
        field_simp
        ring
      · obtain ⟨β, hβ'⟩ := hβ v
        have key : af y (v, true) = β := by
          simp only [af, if_true]
          rw [hβ' (gv v), smul_eq_mul, Units.val_inv_eq_inv_val]
          field_simp
        have hc : F.star (F.loc0 v s⁻¹) = F.conj (F.loc0 v s) := by
          show F.conj ((F.loc0 v s⁻¹)⁻¹) = _
          rw [map_inv (F.loc0 v) s, inv_inv]
        have hcv : F.Ψ ((F.conj (F.loc0 v s) : F.G0) : F.Γ) = F.Ψ (F.loc v s) := by
          rw [← hc, hΨst, hl, map_inv, map_inv, inv_inv]
        rw [key]
        simp only [xf, Frame.loc2, if_true, MonoidHom.comp_apply]
        rw [hcv, ← hc, hβ' s⁻¹]
        simp only [map_inv, inv_inv, Units.val_inv_eq_inv_val, smul_eq_mul]
        field_simp
        ring
  let φ : F.strY k →ₗ[k] Z1C F.loc2 ρ (fun _ => ⊥) :=
    { toFun := fun y => ⟨(xf y.1, af y.1), hmem y.1 y.2⟩
      map_add' := by
        intro y z
        apply Subtype.ext
        refine Prod.ext (funext fun g => ?_) (funext fun p => ?_)
        · simp [xf, mul_add]
        · simp only [af, Submodule.coe_add, Prod.snd_add, Pi.add_apply]
          split_ifs <;> ring
      map_smul' := by
        intro a y
        apply Subtype.ext
        refine Prod.ext (funext fun g => ?_) (funext fun p => ?_)
        · simp [xf]
          ring
        · simp only [af, SetLike.val_smul, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          split_ifs <;> ring }
  have hinj : Function.Injective
      ((Submodule.mkQ (Submodule.comap (Z1C F.loc2 ρ (fun _ => ⊥)).subtype (continuousCoboundaries1 ρ (fun _ => ⊥)))).comp φ) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap] at hy
    obtain ⟨X, hX, -⟩ := hy
    obtain ⟨-, -, hg0, -, -⟩ := y.2
    have hy' : ∀ g, (y : F.G0 → k) g = X - ((F.Ψ (g : F.Γ) : k)) * X := by
      intro g
      have h := hX g
      rw [hρapp] at h
      have := hne g
      change ((F.Ψ (g : F.Γ) : k))⁻¹ * (y : F.G0 → k) g = _ at h
      field_simp at h
      linear_combination h
    have hd : ((F.Ψ (F.g0 : F.Γ) : k)) - ((F.Ψ (F.g0 : F.Γ) : k))⁻¹ ≠ 0 := by
      intro h
      apply hF.baseSubgroup_spec
      have hu := hne F.g0
      rw [sub_eq_zero] at h
      rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, pow_two]
      calc ((F.Ψ (F.g0 : F.Γ) : k)) * (F.Ψ (F.g0 : F.Γ) : k)
          = (F.Ψ (F.g0 : F.Γ) : k) * ((F.Ψ (F.g0 : F.Γ) : k))⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ hu
    have hX0 : X = 0 := by
      have h := hg0
      rw [hy', hy', hΨst, Units.val_inv_eq_inv_val] at h
      have h' : (((F.Ψ (F.g0 : F.Γ) : k)) - ((F.Ψ (F.g0 : F.Γ) : k))⁻¹) * X = 0 := by
        linear_combination -h
      exact (mul_eq_zero.mp h').resolve_left hd
    apply Subtype.ext
    funext g
    rw [hy', hX0]
    simp
  exact (LinearMap.rank_le_of_injective _ hinj).trans hF.b1
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.finrank_structMapS_range :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → Module.rank k (F.strS k) ≤ C₀ := by
  intro l _ k _ _ F C₀ hF
  have h2 : (2 : k) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : k) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff k l] at h'
    exact hF.l_odd ((Nat.prime_dvd_prime_iff_eq (Fact.out : l.Prime) Nat.prime_two).mp h')
  set χ := F.Ψ⁻¹ ^ 2 * F.delK k with hχ
  have hc : ((χ F.c : kˣ) : k) = -1 := by
    simp [hχ, Frame.delK, hF.del_c, hF.Ψ_c]
  let Z := Z1C F.loc (chRep χ) fun _ => (⊥ : Submodule k k)
  let f : Z →ₗ[k] (F.G0 → k) :=
    { toFun := fun x g => (x.1.1 g + ((χ g : k) * x.1.1 F.c - x.1.1 F.c) * 2⁻¹) * (F.Ψ g : k)
      map_add' := by
        intro x y
        funext g
        simp
        ring
      map_smul' := by
        intro r x
        funext g
        simp
        ring }
  have hker : Submodule.comap Z.subtype (continuousCoboundaries1 (chRep χ) fun _ => (⊥ : Submodule k k)) ≤ LinearMap.ker f := by
    rintro ⟨x, hx⟩ hb
    rw [Submodule.mem_comap] at hb
    obtain ⟨X, hX, -⟩ := hb
    rw [LinearMap.mem_ker]
    funext g
    have e1 := hX (g : F.Γ)
    have e2 := hX F.c
    simp only [Submodule.subtype_apply, chRep_apply, hc] at e1 e2
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
    rw [e1, e2]
    field_simp
    ring
  let L := Submodule.liftQ _ f hker
  have hle : F.strS k ≤ LinearMap.range L := by
    intro a ha
    obtain ⟨x, hx, hx0, hax⟩ := frame_extension_of_locallyConstant hF a ha
    refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
    rw [Submodule.liftQ_apply]
    funext g
    simp [f, hx0, hax]
  calc Module.rank k (F.strS k) ≤ Module.rank k (LinearMap.range L) := Submodule.rank_mono hle
    _ ≤ Module.rank k (H1C F.loc (chRep χ) fun _ => (⊥ : Submodule k k)) := rank_range_le L
    _ ≤ C₀ := hF.b1p
end

section

noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.Fr

namespace Frame

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] (F : Frame l k) (Q : Type) [CommRing Q] [Algebra k Q]

structure Low (y a : F.G0 → Q) : Prop where
  lcy : IsLocallyConstant y
  lca : IsLocallyConstant a
  muly : ∀ g h : F.G0, y (g * h) = (F.Ψ h : k) • y g + y h
  mula : ∀ g h : F.G0, a (g * h) = (F.Ψ h : k) • a g + y (F.star g) * y h + (((F.Ψ g)⁻¹ : kˣ) : k) • a h
  pol : ∀ g, a (F.star g) = a g
  nor : y F.g0 = y (F.star F.g0)
  loc : ∀ v, ∃ α β γ : Q, ∀ s, y (F.loc0 v s) = ((F.Ψ (F.loc v s) : k) - 1) • α ∧
    y (F.star (F.loc0 v s)) = (1 - (((F.Ψ (F.loc v s))⁻¹ : kˣ) : k)) • β ∧
    a (F.loc0 v s) = ((F.Ψ (F.loc v s) : k) - (((F.Ψ (F.loc v s))⁻¹ : kˣ) : k)) • γ -
      (1 - (((F.Ψ (F.loc v s))⁻¹ : kˣ) : k)) • (α * β)

variable {F Q} {Q' : Type} [CommRing Q'] [Algebra k Q'] {y a : F.G0 → Q}

theorem Low.map (h : F.Low Q y a) (φ : Q →ₐ[k] Q') : F.Low Q' (fun g => φ (y g)) (fun g => φ (a g)) := by
  refine
    { lcy := h.lcy.comp φ
      lca := h.lca.comp φ
      muly g g' := by simp only [h.muly, map_add (f := _), map_smul]
      mula g g' := by simp only [h.mula, map_add (f := _), map_smul, map_mul]
      pol g := by simp only [h.pol]
      nor := congrArg φ h.nor
      loc := ?_ }
  intro v
  obtain ⟨α, β, γ, H⟩ := h.loc v
  refine ⟨φ α, φ β, φ γ, fun s => ?_⟩
  obtain ⟨h1, h2, h3⟩ := H s
  exact ⟨by rw [h1, map_smul], by rw [h2, map_smul], by rw [h3, map_sub, map_smul, map_smul, map_mul]⟩

theorem Low.comb (h : F.Low Q y a) (t : Q) {b : F.G0 → Q} (hb : b ∈ F.strS Q) :
    F.Low Q (fun g => t * y g) (fun g => t ^ 2 * a g + b g) := by
  refine
    { lcy := h.lcy.comp (t * ·)
      lca := (h.lca.comp (t ^ 2 * ·)).add hb.1
      muly g g' := by simp only [h.muly, Algebra.smul_def]; ring
      mula g g' := by simp only [h.mula, hb.2.1 g g', Algebra.smul_def]; ring
      pol g := by simp only [h.pol, hb.2.2.1 g]
      nor := congrArg (t * ·) h.nor
      loc := ?_ }
  intro v
  obtain ⟨α, β, γ, H⟩ := h.loc v
  obtain ⟨δ, H'⟩ := hb.2.2.2 v
  refine ⟨t * α, t * β, t ^ 2 * γ + δ, fun s => ?_⟩
  obtain ⟨h1, h2, h3⟩ := H s
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]; simp only [Algebra.smul_def]; ring
  · rw [h2]; simp only [Algebra.smul_def]; ring
  · rw [h3, H' s]; simp only [Algebra.smul_def]; ring

theorem Low.zero : F.Low Q 0 0 :=
  ⟨IsLocallyConstant.const 0, IsLocallyConstant.const 0, by simp, by simp, fun _ => rfl, rfl,
    fun _ => ⟨0, 0, 0, by simp⟩⟩

theorem Low.strS (h : F.Low Q 0 a) : a ∈ F.strS Q := by
  refine ⟨h.lca, fun g g' => by simpa using h.mula g g', h.pol, fun v => ?_⟩
  obtain ⟨α, β, γ, H⟩ := h.loc v
  refine ⟨γ, fun s => ?_⟩
  obtain ⟨-, h2, h3⟩ := H s
  rw [h3, mul_comm α, ← smul_mul_assoc, ← h2]
  simp

theorem strS_mul (t : Q) (ha : a ∈ F.strS Q) : (fun g => t * a g) ∈ F.strS Q :=
  strS_map (LinearMap.mulLeft k t) ha

end Frame

namespace Space

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ}
  {Q Q' : Type} [CommRing Q] [Algebra (ResidueField O) Q] [CommRing Q'] [Algebra (ResidueField O) Q']

structure FPt (S : Space O F n) (ξ : S.A →+* Q) : Prop where
  x0 : S.x0 ≤ RingHom.ker ξ
  alg : ∀ c : O, ξ (algebraMap O S.A c) = algebraMap (ResidueField O) Q (residue O c)

theorem FPt.comp {S : Space O F n} {ξ : S.A →+* Q} (h : S.FPt ξ) (φ : Q →ₐ[ResidueField O] Q') :
    S.FPt ((φ : Q →+* Q').comp ξ) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    have : ξ x = 0 := h.x0 hx
    show φ (ξ x) = 0
    rw [this, map_zero]
  · intro c
    show φ (ξ _) = _
    rw [h.alg, AlgHom.commutes]

structure At (S : Space O F 3) (ξ : S.A →+* Q) (y a : F.G0 → Q) : Prop where
  fpt : S.FPt ξ
  low : S.u.triM ≤ RingHom.ker ξ
  hy : ∀ g, ξ (S.u.r g 1 0) = y g
  ha : ∀ g, ξ (S.u.r g 2 0) = a g

theorem At.comp {S : Space O F 3} {ξ : S.A →+* Q} {y a : F.G0 → Q} (h : S.At ξ y a) (φ : Q →ₐ[ResidueField O] Q') :
    S.At ((φ : Q →+* Q').comp ξ) (fun g => φ (y g)) (fun g => φ (a g)) := by
  refine ⟨h.fpt.comp φ, ?_, fun g => congrArg φ (h.hy g), fun g => congrArg φ (h.ha g)⟩
  intro x hx
  have : ξ x = 0 := h.low hx
  show φ (ξ x) = 0
  rw [this, map_zero]

end Space

end UpperTheory.V.Fr
end
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.framePoint_fiber_nonempty :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ (Q : Type) [CommRing Q] [Algebra k Q] (ρ : NRep F 2 Q), ρ.IsBar (algebraMap k Q) → ρ.triM = ⊥ → (∀ i j, IsLocallyConstant fun g => ρ.r g i j) → (fun g => ρ.r g 1 0) ∈ F.strS Q := by
  intro l _ k _ _ F C₀ hF Q _ _ ρ hbar htri hlc
  have hd0 : ∀ g : F.G0, ρ.r g 0 0 = algebraMap k Q ((F.Ψ (g : F.Γ) : k)) := by
    intro g
    have h := hbar.1 g 0
    simpa [w] using h
  have hd1 : ∀ g : F.G0, ρ.r g 1 1 = algebraMap k Q ((F.Ψ (g : F.Γ) : k))⁻¹ := by
    intro g
    have h := hbar.1 g 1
    simpa [w] using h
  have hup : ∀ g : F.G0, ρ.r g 0 1 = 0 := by
    intro g
    have h : ρ.r g 0 1 ∈ ρ.triM := by
      apply Ideal.subset_span (s := {x | ∃ g i j, i < j ∧ x = ρ.r g i j})
      exact ⟨g, 0, 1, by decide, rfl⟩
    rw [htri, Ideal.mem_bot] at h
    exact h
  have hψ0 : ∀ v (s : F.Gv v), ((ρ.ψ v 0 s : Qˣ) : Q) = algebraMap k Q ((F.Ψ (F.loc v s) : k)) := by
    intro v s
    have h := hbar.2 v 0 s
    simpa [w] using h
  have hψ1 : ∀ v (s : F.Gv v), ((ρ.ψ v 1 s : Qˣ) : Q) = algebraMap k Q ((F.Ψ (F.loc v s) : k))⁻¹ := by
    intro v s
    have h := hbar.2 v 1 s
    simpa [w] using h
  refine ⟨hlc 1 0, ?_, ?_, ?_⟩
  · intro g h
    simp only [map_mul, Matrix.mul_apply, Fin.sum_univ_two, Algebra.smul_def, Units.val_inv_eq_inv_val]
    rw [hd0, hd1]
    ring
  · intro g
    show ρ.r (F.star g) 1 0 = ρ.r g 1 0
    rw [(UpperTheory.V.Fr.star hF).2.2.2.2 ρ g 1 0]
    rfl
  · intro v
    obtain ⟨t, ht⟩ := hF.f3 v
    set d : k := ((F.Ψ (F.loc v t) : k)) - ((F.Ψ (F.loc v t) : k))⁻¹ with hdd
    have hne := Units.ne_zero (F.Ψ (F.loc v t))
    have hd : d ≠ 0 := by
      intro h
      apply ht
      rw [hdd, sub_eq_zero] at h
      rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, pow_two]
      calc ((F.Ψ (F.loc v t) : k)) * (F.Ψ (F.loc v t) : k)
          = (F.Ψ (F.loc v t) : k) * ((F.Ψ (F.loc v t) : k))⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ hne
    refine ⟨algebraMap k Q d⁻¹ * ρ.r (F.loc0 v t) 1 0, fun s => ?_⟩
    have h10 := congrFun (congrFun (ρ.ord v ![s, t]) 1) 0
    simp only [ordProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.succ_zero_eq_one, (by decide : (1 : Fin 2) ≠ 0), if_false, if_true, smul_zero,
      sub_zero, smul_eq_mul, mul_one] at h10
    have hl : ∀ s, ((F.loc0 v s : F.G0) : F.Γ) = F.loc v s := fun _ => rfl
    rw [hd0, hd1, hψ0, hψ1, hl, hl] at h10
    simp only [mul_zero, sub_zero] at h10
    have hinv : (algebraMap k Q ((F.Ψ (F.loc v t) : k)) - algebraMap k Q ((F.Ψ (F.loc v t) : k))⁻¹)
        * algebraMap k Q d⁻¹ = 1 := by
      rw [← map_sub, ← map_mul, ← hdd, mul_inv_cancel₀ hd, map_one]
    simp only [Algebra.smul_def, Units.val_inv_eq_inv_val, map_sub]
    linear_combination algebraMap k Q d⁻¹ * h10 - ρ.r (F.loc0 v s) 1 0 * hinv
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem upT_mul {K : Type} [CommRing K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K} (hA : UpT A) (hB : UpT B) :
    UpT (A * B) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  rcases lt_or_ge c i with hc | hc
  · rw [hA i c hc, zero_mul]
  · rw [hB c j (lt_of_lt_of_le h hc), mul_zero]

private theorem upT_of_comm {K : Type} [Field K] {n : ℕ} {T Z : Matrix (Fin n) (Fin n) K} (hT : UpT T)
    (hd : ∀ i j, i ≠ j → T i i ≠ T j j) (h : UpT (T * Z - Z * T)) : UpT Z := by
  have key : ∀ m : ℕ, ∀ i j : Fin n, n - i.val + j.val = m → j < i → Z i j = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro i j hm hji
      have h0 := h i j hji
      have hji' : j.val < i.val := hji
      rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single i, Finset.sum_eq_single j] at h0
      · have h1 : (T i i - T j j) * Z i j = 0 := by linear_combination h0
        exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 (hd i j hji.ne'))
      · intro c _ hc
        rcases lt_or_gt_of_ne hc with hc | hc
        · have hc' : c.val < j.val := hc
          rw [ih (n - i.val + c.val) (by omega) i c rfl (hc.trans hji), zero_mul]
        · rw [hT c j hc, mul_zero]
      · simp
      · intro c _ hc
        rcases lt_or_gt_of_ne hc with hc | hc
        · rw [hT i c hc, zero_mul]
        · have hc' : i.val < c.val := hc
          have := c.isLt
          rw [ih (n - c.val + j.val) (by omega) c j rfl (hji.trans hc), mul_zero]
      · simp
  exact fun i j hij => key _ i j rfl hij

theorem UpperTheory.V.Fr.pr_brig :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ}, ∀ (K : Type) [Field K] (ρ : NRep F n K) (B : Box F n K), B.Of ρ → ρ.Good → ∀ (v : F.V) (Y : Matrix (Fin n) (Fin n) K), (∀ s, B.ad (F.loc v s) Y - Y ∈ B.b v) → Y ∈ B.b v := by
  intro l _ k _ F n K _ ρ B hOf hG v Y hY
  obtain ⟨s, hs⟩ := hG.ψd v
  have hT := B.tri v s
  have hr : (B.r (F.loc v s)).right = 1 := (B.nu _).trans (F.loc0 v s).2
  have hres : (B.r (F.loc v s)).mat = ρ.r (F.loc0 v s) := hOf.res (F.loc0 v s)
  have h1 : UpT ((B.g v : Matrix (Fin n) (Fin n) K) * ((B.r (F.loc v s)).adFun Y - Y) *
      (((B.g v)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := hY s
  show UpT ((B.g v : Matrix (Fin n) (Fin n) K) * Y * (((B.g v)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
  refine upT_of_comm hT (fun i j hij => ?_) ?_
  · rw [hres, hOf.psi, hOf.psi]
    exact fun e => hs i j hij (Units.ext e)
  · convert upT_mul h1 hT using 1
    simp only [GG.adFun, hr, if_true, GG.mat, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
      Units.inv_mul_cancel_left]
end
