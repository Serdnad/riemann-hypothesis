module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContinuousCoboundaries2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TensorProjMemOfMemBaseChange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LeAdicClosure
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem lc_of_ker {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] (f : G →* H)
    (hf : IsOpen (f.ker : Set G)) : IsLocallyConstant f :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker f hf

theorem UpperTheory.exists_mem_strS_ne_zero_of_frameOk :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∃ b ∈ F.strS k, b ≠ 0 := by
  intro l _ k _ _ F C₀ h
  have hχ0 : ∀ g : F.G0, (F.Ψ⁻¹ ^ 2 * F.delK k) g = (F.Ψ g)⁻¹ ^ 2 := fun g => by
    have : F.del g = 1 := g.2
    simp [Frame.delK, this]
  have hχ : ∀ g : F.G0, (((F.Ψ⁻¹ ^ 2 * F.delK k) g : kˣ) : k) = ((F.Ψ g : k))⁻¹ ^ 2 := fun g => by
    rw [hχ0]; simp
  have hc : (F.Ψ⁻¹ ^ 2 * F.delK k) F.c = -1 := by
    apply Units.ext
    simp [Frame.delK, h.Ψ_c, h.del_c]
  obtain ⟨x, x1, x2, x3, x4, g₁, x5⟩ := UpperTheory.smooth_vector_fixed_by_open_subgroup h (F.Ψ⁻¹ ^ 2 * F.delK k) hc (fun v => by
    obtain ⟨s, hs⟩ := h.f3 v
    refine ⟨s, fun e => hs ?_⟩
    have e' := (hχ0 (F.loc0 v s)).symm.trans e
    rw [inv_pow, inv_eq_one] at e'
    exact e') h.f4'
  have x0 : x 1 = 0 := by
    have := x2 1 1
    rw [mul_one, map_one] at this
    simpa using this
  have hci : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right h.c_sq
  refine ⟨fun g => x g * F.Ψ g, ⟨?_, fun g g' => ?_, fun g => ?_, fun v => ?_⟩, fun e => ?_⟩
  · exact (x1.mul ((lc_of_ker F.Ψ h.Ψ_open).comp Units.val)).comp_continuous continuous_subtype_val
  · have := (F.Ψ g).ne_zero
    simp only [Subgroup.coe_mul, x2, hχ, map_mul, Units.val_mul, smul_eq_mul, Units.val_inv_eq_inv_val]
    field_simp
  · have hs : ((F.star g : F.G0) : F.Γ) = F.c * ((g : F.Γ)⁻¹ * F.c) := by
      rw [← mul_assoc]
      nth_rewrite 2 [← hci]
      rfl
    have h0 := (F.Ψ g).ne_zero
    have e1 := x2 g (g : F.Γ)⁻¹
    rw [mul_inv_cancel, x0, hχ] at e1
    show x (F.star g) * F.Ψ (F.star g) = x g * F.Ψ g
    have hstar : F.Ψ (F.star g) = (F.Ψ g)⁻¹ := by
      rw [hs, map_mul, map_mul, map_inv, h.Ψ_c]
      simp
    rw [hstar, hs, x2, x2, x3, hc, Units.val_inv_eq_inv_val]
    have e2 : x g = -((F.Ψ g : k)⁻¹ ^ 2 * x (g : F.Γ)⁻¹) := by linear_combination -e1
    rw [e2]
    simp only [Units.val_neg, Units.val_one]
    field_simp
    ring
  · obtain ⟨Y, hY⟩ := x4 v
    refine ⟨-Y, fun s => ?_⟩
    have h0 := (F.Ψ (F.loc v s)).ne_zero
    have e : (((F.Ψ⁻¹ ^ 2 * F.delK k) (F.loc v s) : kˣ) : k) = ((F.Ψ (F.loc v s) : k))⁻¹ ^ 2 := hχ (F.loc0 v s)
    show x (F.loc v s) * F.Ψ (F.loc v s) = _
    rw [hY, e, Units.val_inv_eq_inv_val, smul_eq_mul]
    field_simp
    ring
  · exact mul_ne_zero x5 (F.Ψ g₁).ne_zero (congrFun e g₁)
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem lc_of_open_ker {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    (f : G →* H) (hf : IsOpen (f.ker : Set G)) : IsLocallyConstant f :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker f hf

theorem UpperTheory.V.Fr.frame_extension_of_locallyConstant :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ a ∈ F.strS k, ∃ x ∈ Z1C F.loc (chRep (F.Ψ⁻¹ ^ 2 * F.delK k)) (fun _ => ⊥), x.1 F.c = 0 ∧ ∀ g : F.G0, a g = x.1 g * F.Ψ g := by
  classical
  intro l _ k _ _ F C₀ h a ha
  obtain ⟨a1, a2, a3, a4⟩ := ha
  choose γ hγ using a4
  have hd : ∀ g : F.G0, F.del g = 1 := fun g => g.2
  have hcc : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right h.c_sq
  have hconj : ∀ g : F.G0, ((F.conj g : F.G0) : F.Γ) = F.c * g * F.c := fun g => by
    rw [← hcc]; nth_rewrite 1 [hcc]; rfl
  have a0 : a 1 = 0 := by
    have := a2 1 1
    simpa using this
  have ainv : ∀ g, a g⁻¹ = - a g := fun g => by
    have := a2 g g⁻¹
    rw [mul_inv_cancel, a0] at this
    simp only [smul_eq_mul, Subgroup.coe_inv, map_inv] at this
    rw [← mul_add] at this
    have h2 := (mul_eq_zero.1 this.symm).resolve_left (Units.ne_zero _)
    linear_combination h2
  have ac : ∀ g, a (F.conj g) = - a g := fun g => by
    rw [← ainv, ← a3 g⁻¹]; simp [Frame.star]
  have Ψc : ∀ g : F.G0, F.Ψ (F.conj g) = F.Ψ g := fun g => by simp [hconj, h.Ψ_c]
  let b : F.G0 → k := fun g => a g * (((F.Ψ g)⁻¹ : kˣ) : k)
  have b1 : IsLocallyConstant b := by
    refine a1.mul ?_
    exact ((lc_of_open_ker F.Ψ h.Ψ_open).comp_continuous continuous_subtype_val).comp
      (fun u : kˣ => ((u⁻¹ : kˣ) : k))
  have b2 : ∀ g g' : F.G0, b (g * g') = b g + ((F.Ψ g : k)⁻¹) ^ 2 * b g' := fun g g' => by
    simp only [b, a2, smul_eq_mul, Subgroup.coe_mul, map_mul, Units.val_inv_eq_inv_val, Units.val_mul]
    have := (F.Ψ g).ne_zero
    have := (F.Ψ g').ne_zero
    field_simp
  have bc : ∀ g, b (F.conj g) = - b g := fun g => by simp only [b, ac, Ψc, neg_mul]
  let e : ℤˣ → F.Γ := fun u => if u = 1 then 1 else F.c
  have he : ∀ s : F.Γ, s * e (F.del s) ∈ F.del.ker := fun s => by
    rw [MonoidHom.mem_ker, map_mul]
    rcases Int.units_eq_one_or (F.del s) with h1 | h1 <;> simp [e, h1, h.del_c]
  let p : F.Γ → F.G0 := fun s => ⟨s * e (F.del s), he s⟩
  have pc : Continuous p :=
    Continuous.subtype_mk (continuous_id.mul ((lc_of_open_ker F.del h.del_open).comp e).continuous) _
  have p1 : ∀ g : F.G0, p g = g := fun g => Subtype.ext (by simp [p, e, hd])
  have p2 : ∀ g : F.G0, p (g * F.c) = g := fun g =>
    Subtype.ext (by simp [p, e, hd, h.del_c, mul_assoc, h.c_sq])
  have dec : ∀ s : F.Γ, ∃ g : F.G0, s = g ∨ s = g * F.c := fun s => by
    refine ⟨p s, ?_⟩
    rcases Int.units_eq_one_or (F.del s) with h1 | h1
    · left; simp [p, e, h1]
    · right; simp [p, e, h1, mul_assoc, h.c_sq]
  have χ1 : ∀ g : F.G0, (((F.Ψ⁻¹ ^ 2 * F.delK k) g : kˣ) : k) = ((F.Ψ g : k)⁻¹) ^ 2 := fun g => by
    simp [Frame.delK, hd]
  have χ2 : ∀ g : F.G0, (((F.Ψ⁻¹ ^ 2 * F.delK k) (g * F.c) : kˣ) : k) = -((F.Ψ g : k)⁻¹) ^ 2 := fun g => by
    simp [Frame.delK, hd, h.del_c, h.Ψ_c]
  refine ⟨(fun s => b (p s), fun v => - γ v), ⟨b1.comp_continuous pc, fun s t => ?_, fun v s => ?_⟩, ?_, fun g => ?_⟩
  · show b (p (s * t)) = b (p s) + chRep _ s (b (p t))
    rw [chRep_apply]
    obtain ⟨g, rfl | rfl⟩ := dec s <;> obtain ⟨g', rfl | rfl⟩ := dec t
    · rw [← Subgroup.coe_mul, p1, p1, p1, χ1, b2]
    · rw [← mul_assoc, ← Subgroup.coe_mul, p2, p1, p2, χ1, b2]
    · have : (g : F.Γ) * F.c * g' = ((g * F.conj g' : F.G0) : F.Γ) * F.c := by
        simp [hconj, mul_assoc, h.c_sq]
      rw [this, p2, p2, p1, χ2, b2, bc]; ring
    · have : (g : F.Γ) * F.c * (g' * F.c) = ((g * F.conj g' : F.G0) : F.Γ) := by
        simp [hconj, mul_assoc]
      rw [this, p1, p2, p2, χ2, b2, bc]; ring
  · show b (p (F.loc0 v s)) - (chRep _ (F.loc0 v s : F.Γ) (- γ v) - - γ v) ∈ (⊥ : Submodule k k)
    rw [chRep_apply, p1, χ1, Submodule.mem_bot]
    have h1 : F.loc v s = (F.loc0 v s : F.Γ) := rfl
    simp only [b, hγ, h1, smul_eq_mul, Units.val_inv_eq_inv_val]
    have := (F.Ψ (F.loc0 v s)).ne_zero
    field_simp
    ring
  · show b (p F.c) = 0
    have := p2 1
    simp only [OneMemClass.coe_one, one_mul] at this
    simp [this, b, a0]
  · show a g = b (p g) * _
    rw [p1]
    simp [b]
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section

variable {K G W W' V : Type} [Field K] [Group G] [TopologicalSpace G] [AddCommGroup W] [Module K W]
  [AddCommGroup W'] [Module K W'] {Gv : V → Type} [∀ v, Group (Gv v)] (loc : ∀ v, Gv v →* G)

private def trE (G V : Type) (e : W ≃ₗ[K] W') : ((G → W) × (V → W)) ≃ₗ[K] ((G → W') × (V → W')) :=
  (LinearEquiv.piCongrRight fun _ => e).prodCongr (LinearEquiv.piCongrRight fun _ => e)

private theorem trZ (e : W ≃ₗ[K] W') (ρ : Representation K G W) (ρ' : Representation K G W')
    (b : V → Submodule K W) (b' : V → Submodule K W') (h : ∀ g x, ρ' g (e x) = e (ρ g x))
    (hb : ∀ v x, e x ∈ b' v ↔ x ∈ b v) (x : (G → W) × (V → W)) :
    trE G V e x ∈ Z1C loc ρ' b' ↔ x ∈ Z1C loc ρ b := by
  have h1 : (trE G V e x).1 = e ∘ x.1 := rfl
  have h2 : (trE G V e x).2 = e ∘ x.2 := rfl
  simp only [Z1C, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  rw [h1, h2]
  simp only [Function.comp_apply]
  apply and_congr
  · constructor
    · intro hl
      exact IsLocallyConstant.desc _ _ hl e.injective
    · intro hl
      exact hl.comp e
  apply and_congr
  · apply forall_congr'
    intro s
    apply forall_congr'
    intro t
    rw [h, ← map_add (f := _)]
    exact e.injective.eq_iff
  · apply forall_congr'
    intro v
    apply forall_congr'
    intro s
    rw [h, ← map_sub, ← map_sub]
    exact hb v _

omit [TopologicalSpace G] in
private theorem trB (e : W ≃ₗ[K] W') (ρ : Representation K G W) (ρ' : Representation K G W')
    (b : V → Submodule K W) (b' : V → Submodule K W') (h : ∀ g x, ρ' g (e x) = e (ρ g x))
    (hb : ∀ v x, e x ∈ b' v ↔ x ∈ b v) (x : (G → W) × (V → W)) :
    trE G V e x ∈ continuousCoboundaries1 ρ' b' ↔ x ∈ continuousCoboundaries1 ρ b := by
  have h1 : (trE G V e x).1 = e ∘ x.1 := rfl
  have h2 : (trE G V e x).2 = e ∘ x.2 := rfl
  simp only [continuousCoboundaries1, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  rw [h1, h2]
  simp only [Function.comp_apply]
  constructor
  · rintro ⟨X, hX1, hX2⟩
    refine ⟨e.symm X, fun s => ?_, fun v => ?_⟩
    · apply e.injective
      rw [map_sub, ← h, e.apply_symm_apply]
      exact hX1 s
    · rw [← hb v, map_sub, e.apply_symm_apply]
      exact hX2 v
  · rintro ⟨X, hX1, hX2⟩
    refine ⟨e X, fun s => ?_, fun v => ?_⟩
    · rw [hX1 s, map_sub, h]
    · rw [← map_sub, hb v]
      exact hX2 v

private theorem trMap (e : W ≃ₗ[K] W') (ρ : Representation K G W) (ρ' : Representation K G W')
    (b : V → Submodule K W) (b' : V → Submodule K W') (h : ∀ g x, ρ' g (e x) = e (ρ g x))
    (hb : ∀ v x, e x ∈ b' v ↔ x ∈ b v) :
    (Z1C loc ρ b).map (trE G V e : _ →ₗ[K] _) = Z1C loc ρ' b' := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (trZ loc e ρ ρ' b b' h hb x).mpr hx
  · intro hy
    refine ⟨(trE G V e).symm y, ?_, ?_⟩
    · exact (trZ loc e ρ ρ' b b' h hb _).mp (by simpa using hy)
    · simp

private theorem trH (e : W ≃ₗ[K] W') (ρ : Representation K G W) (ρ' : Representation K G W')
    (b : V → Submodule K W) (b' : V → Submodule K W') (h : ∀ g x, ρ' g (e x) = e (ρ g x))
    (hb : ∀ v x, e x ∈ b' v ↔ x ∈ b v) :
    Module.rank K (H1C loc ρ' b') = Module.rank K (H1C loc ρ b) := by
  let E : Z1C loc ρ b ≃ₗ[K] Z1C loc ρ' b' :=
    ((trE G V e).submoduleMap (Z1C loc ρ b)).trans (LinearEquiv.ofEq _ _ (trMap loc e ρ ρ' b b' h hb))
  have hE : ∀ z, (E z : (G → W') × (V → W')) = trE G V e z := fun z => rfl
  symm
  refine LinearEquiv.rank_eq (Submodule.Quotient.equiv _ _ E ?_)
  ext y
  rw [Submodule.mem_map_equiv]
  simp only [Submodule.mem_comap, Submodule.subtype_apply]
  rw [← trB e ρ ρ' b b' h hb, ← hE, E.apply_symm_apply]

end

theorem UpperTheory.V.Fr.n4ch :
    ∀ {k K G V : Type} [Field k] [Field K] (f : k →+* K) [Group G] [TopologicalSpace G] [CompactSpace G] {Gv : V → Type} [∀ v, Group (Gv v)] [Finite V] (loc : ∀ v, Gv v →* G) (χ : G →* kˣ) (b : V → Submodule k k) (b' : V → Submodule K K), (∀ v, (b v = ⊥ ∧ b' v = ⊥) ∨ (b v = ⊤ ∧ b' v = ⊤)) → Z1C loc (chRep ((Units.map f.toMonoidHom).comp χ)) b' = Submodule.span K ((fun y : (G → k) × (V → k) => (f ∘ y.1, f ∘ y.2)) '' (Z1C loc (chRep χ) b : Set ((G → k) × (V → k)))) ∧ Module.rank K (H1C loc (chRep ((Units.map f.toMonoidHom).comp χ)) b') = Module.rank k (H1C loc (chRep χ) b) := by
  intro k K G V _ _ f _ _ _ Gv _ _ loc χ b b' hbb
  letI : Algebra k K := f.toAlgebra
  let ρ' : Representation K G (TensorProduct k K k) :=
    { toFun := fun g => ((chRep χ) g).baseChange K
      map_one' := by
        show ((chRep χ) 1).baseChange K = 1
        rw [map_one]
        exact LinearMap.baseChange_one k k
      map_mul' := fun g g' => by
        show ((chRep χ) (g * g')).baseChange K = ((chRep χ) g).baseChange K * ((chRep χ) g').baseChange K
        rw [map_mul]
        exact LinearMap.baseChange_mul _ _ }
  obtain ⟨hZ, hH⟩ := n4 loc (chRep χ) b ρ' (fun g => rfl)
  let e := TensorProduct.AlgebraTensorModule.rid k K K
  have hρ : ∀ g x, (chRep ((Units.map f.toMonoidHom).comp χ)) g (e x) = e (ρ' g x) := by
    intro g x
    show (((Units.map f.toMonoidHom).comp χ) g : K) • e x = e (((chRep χ) g).baseChange K x)
    have hc : (chRep χ) g = ((χ g : kˣ) : k) • LinearMap.id := rfl
    rw [hc, LinearMap.baseChange_smul, LinearMap.baseChange_id, LinearMap.smul_apply, LinearMap.id_apply,
      ← algebraMap_smul K ((χ g : kˣ) : k) x, map_smul]
    simp [RingHom.algebraMap_toAlgebra]
  have hb : ∀ v x, e x ∈ b' v ↔ x ∈ (b v).baseChange K := by
    intro v x
    rcases hbb v with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, Submodule.baseChange_bot, Submodule.mem_bot, Submodule.mem_bot, LinearEquiv.map_eq_zero_iff]
    · rw [h1, h2, Submodule.baseChange_top]
      simp
  have hM := trMap loc e ρ' (chRep ((Units.map f.toMonoidHom).comp χ)) (fun v => (b v).baseChange K) b' hρ hb
  refine ⟨?_, ?_⟩
  · rw [← hM, hZ, Submodule.map_span, ← Set.image_comp]
    congr 2
    funext y
    refine Prod.ext (funext fun g => ?_) (funext fun v => ?_)
    · show e (1 ⊗ₜ[k] y.1 g) = f (y.1 g)
      simp [e, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    · show e (1 ⊗ₜ[k] y.2 v) = f (y.2 v)
      simp [e, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  · rw [trH loc e ρ' (chRep ((Units.map f.toMonoidHom).comp χ)) _ b' hρ hb, hH]
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem list_forall_eq_zero_of_nonpos_of_sum_eq_zero (L : List ℤ) (h : ∀ x ∈ L, x ≤ 0) (hs : L.sum = 0) : ∀ x ∈ L, x = 0 := by
  induction L with
  | nil => simp
  | cons a L ih =>
    intro x hx
    simp only [List.sum_cons] at hs
    have ha : a ≤ 0 := h a (by simp)
    have hL : ∀ x ∈ L, x ≤ 0 := fun x hx => h x (by simp [hx])
    have hsL : L.sum ≤ 0 := by
      clear ih hs hx
      induction L with
      | nil => simp
      | cons b L ih2 =>
        simp only [List.sum_cons]
        have hb : b ≤ 0 := hL b (by simp)
        have := ih2 (fun x hx => h x (by rcases List.mem_cons.mp hx with rfl | hx <;> simp [hx])) (fun x hx => hL x (by simp [hx]))
        linarith
    rcases List.mem_cons.mp hx with rfl | hx
    · linarith
    · exact ih hL (by linarith) x hx

private theorem w_sub_w_nonpos_of_le (n : ℕ) (i j : Fin n) (hji : j ≤ i) : w n i - w n j ≤ 0 := by
  rw [Fin.le_def] at hji
  unfold w
  split_ifs <;> omega

private theorem eq_of_w_sub_w_eq_zero (n : ℕ) (i j : Fin n) (h : w n i - w n j = 0) : i = j := by
  unfold w at h
  apply Fin.ext
  split_ifs at h <;> omega

theorem UpperTheory.V.Fr.adjoin_image_in_residue_range :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ} (S : Space O F n) {Q : Type} [CommRing Q] (f : ResidueField O →+* Q) (φ : S.A →+* Q), (∀ a : O, φ (algebraMap O S.A a) = f (residue O a)) → (S.u.map φ).triM = ⊥ → (S.u.map φ).IsBar f → ∀ z : S.A, (z : S.R) ∈ Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)}) → φ z ∈ f.range := by
  intro l _ O _ _ F n S Q _ f φ hφ htri hbar z hz
  have hrA : ∀ g i j, S.ρ.r g i j ∈ S.A := fun g i j =>
    Algebra.subset_adjoin (Or.inr ⟨g, i, j, rfl⟩)
  have hψA : ∀ v i g, ((S.ρ.ψ v i g : S.Rˣ) : S.R) ∈ S.A := by
    intro v i g
    apply Algebra.subset_adjoin
    left
    show _ ∈ adicClosure _
    intro N
    exact ⟨_, Algebra.subset_adjoin (Or.inr ⟨v, i, g, rfl⟩), by simp⟩
  have hr' : ∀ g i j, (S.u.map φ).r g i j = φ ⟨S.ρ.r g i j, hrA g i j⟩ := fun g i j => rfl
  have hψ' : ∀ v i g, (((S.u.map φ).ψ v i g : Qˣ) : Q) = φ ⟨_, hψA v i g⟩ := fun v i g => rfl
  have hzero : ∀ g i j, i < j → φ ⟨S.ρ.r g i j, hrA g i j⟩ = 0 := by
    intro g i j hij
    have hm : (S.u.map φ).r g i j ∈ (S.u.map φ).triM := Ideal.subset_span ⟨g, i, j, hij, rfl⟩
    rw [htri, Ideal.mem_bot] at hm
    rw [← hr']
    exact hm
  have hdiag : ∀ g i j, i = j → φ ⟨S.ρ.r g i j, hrA g i j⟩ ∈ f.range := by
    rintro g i j rfl
    rw [← hr', hbar.1 g i]
    exact ⟨_, rfl⟩
  have hψr : ∀ v i g, φ ⟨_, hψA v i g⟩ ∈ f.range := by
    intro v i g
    rw [← hψ', hbar.2 v i g]
    exact ⟨_, rfl⟩
  have hDA : Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)}) ≤ S.A := by
    apply Algebra.adjoin_le
    rintro x (⟨L, -, rfl⟩ | ⟨v, i, g, rfl⟩)
    · apply list_prod_mem
      intro y hy
      obtain ⟨s, -, rfl⟩ := List.mem_map.mp hy
      exact hrA _ _ _
    · exact hψA v i g
  have key : ∀ x (hx : x ∈ Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)})),
      φ ⟨x, hDA hx⟩ ∈ f.range := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨L, hsum, rfl⟩ | ⟨v, i, g, rfl⟩
      · have e : (⟨(L.map fun s => S.ρ.r s.1 s.2.1 s.2.2).prod, hDA (Algebra.subset_adjoin (Or.inl ⟨L, hsum, rfl⟩))⟩ : S.A) =
            (L.map fun s => (⟨S.ρ.r s.1 s.2.1 s.2.2, hrA _ _ _⟩ : S.A)).prod := by
          apply Subtype.ext
          simp [List.map_map, Function.comp_def]
        rw [e, map_list_prod, List.map_map]
        by_cases hex : ∃ s ∈ L, s.2.1 < s.2.2
        · obtain ⟨s, hs, hlt⟩ := hex
          rw [List.prod_eq_zero]
          · exact zero_mem _
          · exact List.mem_map.mpr ⟨s, hs, hzero _ _ _ hlt⟩
        · push_neg at hex
          have hterm := list_forall_eq_zero_of_nonpos_of_sum_eq_zero _ (fun x hx => by
            obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
            exact w_sub_w_nonpos_of_le n _ _ (hex s hs)) hsum
          apply list_prod_mem
          intro y hy
          obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hy
          exact hdiag _ _ _ (eq_of_w_sub_w_eq_zero n _ _ (hterm _ (List.mem_map_of_mem hs)))
      · exact hψr v i g
    | algebraMap r =>
      show φ (algebraMap O S.A r) ∈ f.range
      rw [hφ]
      exact ⟨_, rfl⟩
    | add x y hx hy ihx ihy =>
      show φ (⟨x, hDA hx⟩ + ⟨y, hDA hy⟩) ∈ f.range
      rw [map_add (f := _)]
      exact add_mem ihx ihy
    | mul x y hx hy ihx ihy =>
      show φ (⟨x, hDA hx⟩ * ⟨y, hDA hy⟩) ∈ f.range
      rw [map_mul]
      exact mul_mem ihx ihy
  exact key z hz
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.star :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → (∀ g : F.G0, F.star (F.star g) = g) ∧ (∀ g h : F.G0, F.star (g * h) = F.star h * F.star g) ∧ (∀ g : F.G0, F.Ψ (F.star g) = (F.Ψ g)⁻¹) ∧ Continuous F.star ∧ ∀ {n : ℕ} {K : Type} [CommRing K] (ρ : NRep F n K) (g : F.G0) (i j : Fin n), ρ.r (F.star g) i j = ρ.r g j.rev i.rev := by
  intro l _ k _ _ F C₀ hF
  have hs : ∀ g : F.G0, ((F.star g : F.G0) : F.Γ) = F.c * (g : F.Γ)⁻¹ * F.c⁻¹ := fun g => by
    simp [Frame.star, Frame.conj, MulAut.conjNormal_apply, mul_assoc]
  have hc : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hF.c_sq
  refine ⟨fun g => ?_, fun g h => ?_, fun g => ?_, ?_, fun {n} {K} _ ρ g i j => ?_⟩
  · apply Subtype.ext
    rw [hs, hs, hc]
    simp only [_root_.mul_inv_rev, inv_inv, hc]
    calc F.c * (F.c * ((g : F.Γ) * F.c)) * F.c = (F.c * F.c) * (g : F.Γ) * (F.c * F.c) := by group
      _ = g := by rw [hF.c_sq]; group
  · apply Subtype.ext
    simp only [Subgroup.coe_mul, hs, _root_.mul_inv_rev, hc]
    calc F.c * ((h : F.Γ)⁻¹ * (g : F.Γ)⁻¹) * F.c
        = F.c * (h : F.Γ)⁻¹ * (F.c * F.c) * (g : F.Γ)⁻¹ * F.c := by rw [hF.c_sq]; group
      _ = F.c * (h : F.Γ)⁻¹ * F.c * (F.c * (g : F.Γ)⁻¹ * F.c) := by group
  · rw [hs, map_mul, map_mul, map_inv, map_inv, hF.Ψ_c]
    simp
  · refine continuous_induced_rng.2 ?_
    have : (fun g : F.G0 => ((F.star g : F.G0) : F.Γ)) = fun g : F.G0 => F.c * (g : F.Γ)⁻¹ * F.c⁻¹ := funext hs
    change Continuous (fun g : F.G0 => ((F.star g : F.G0) : F.Γ))
    rw [this]
    exact (continuous_const.mul continuous_subtype_val.inv).mul continuous_const
  · rw [ρ.pol]
    simp only [Matrix.mul_apply, Jmat, Matrix.transpose_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, one_mul]
    have h : ∀ a : Fin n, (j = a.rev) ↔ (a = j.rev) := fun a => by
      constructor <;> rintro rfl <;> simp
    simp [h]
end
