import Mathlib

namespace UpperTheory.Reformulated.B.CoboundaryOfGenerator

noncomputable def ContAction.{u_1, u_2, u_3} {R : Type u_1} [inst : CommRing R]
    {G : Type u_2} [inst_1 : Group G] [TopologicalSpace G]
    {M : Type u_3} [inst_3 : AddCommGroup M] [inst_4 : Module R M] [TopologicalSpace M]
    (rho : Representation R G M) : Prop :=
  Continuous fun p : G × M => rho p.1 p.2

theorem aux2.{u_1, u_2, u_3} {R : Type u_3} [inst : CommRing R]
    {G : Type u_1} [inst_1 : Group G] [inst_2 : TopologicalSpace G]
    {M : Type u_2} [inst_3 : AddCommGroup M] [inst_4 : Module R M] [inst_5 : TopologicalSpace M]
    [IsTopologicalAddGroup M] (rho : Representation R G M) {f f' : G → M}
    (hf : f ∈ {z : G → M | Continuous z ∧ ∀ g h, z (g * h) = z g + rho g (z h)})
    (hf' : f' ∈ {z : G → M | Continuous z ∧ ∀ g h, z (g * h) = z g + rho g (z h)}) :
    Continuous (f + f') ∧ ∀ g h, (f + f') (g * h) = (f + f') g + rho g ((f + f') h) := by
  obtain ⟨hc, hf⟩ := hf
  obtain ⟨hc', hf'⟩ := hf'
  refine ⟨hc.add hc', fun g h => ?_⟩
  simp only [Pi.add_apply, hf g h, hf' g h, map_add]
  abel

theorem aux3.{u_1, u_2, u_3} {R : Type u_3} [inst : CommRing R]
    {G : Type u_1} [inst_1 : Group G] [inst_2 : TopologicalSpace G]
    {M : Type u_2} [inst_3 : AddCommGroup M] [inst_4 : Module R M] [inst_5 : TopologicalSpace M]
    (rho : Representation R G M) :
    Continuous (0 : G → M) ∧ ∀ g h : G,
      (0 : G → M) (g * h) = (0 : G → M) g + rho g ((0 : G → M) h) :=
  ⟨continuous_const, fun g h => by simp⟩

theorem aux4.{u_1, u_2, u_3} {R : Type u_3} [inst : CommRing R]
    {G : Type u_1} [inst_1 : Group G] [inst_2 : TopologicalSpace G]
    {M : Type u_2} [inst_3 : AddCommGroup M] [inst_4 : Module R M] [inst_5 : TopologicalSpace M]
    [ContinuousConstSMul R M] (rho : Representation R G M) (c : R) (f : G → M)
    (hf : f ∈ {z : G → M | Continuous z ∧ ∀ g h, z (g * h) = z g + rho g (z h)}) :
    Continuous (c • f) ∧ ∀ g h, (c • f) (g * h) = (c • f) g + rho g ((c • f) h) := by
  obtain ⟨hc, hf⟩ := hf
  refine ⟨hc.const_smul c, fun g h => ?_⟩
  simp only [Pi.smul_apply, hf g h, map_smul, smul_add]

noncomputable def Z1.{u_1, u_2, u_3} {R : Type u_1} [inst : CommRing R]
    {G : Type u_2} [inst_1 : Group G] [TopologicalSpace G]
    {M : Type u_3} [inst_3 : AddCommGroup M] [inst_4 : Module R M] [inst_5 : TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    (rho : Representation R G M) : Submodule R (G → M) where
  carrier := {f | Continuous f ∧ ∀ g h, f (g * h) = f g + rho g (f h)}
  add_mem' := aux2 rho
  zero_mem' := aux3 rho
  smul_mem' := aux4 rho

theorem aux6.{u_1, u_2} {R : Type u_1} {M : Type u_2} [inst : SMul R M]
    [inst_1 : TopologicalSpace M] [DiscreteTopology M] : ContinuousConstSMul R M :=
  ⟨fun _ => continuous_of_discreteTopology⟩

theorem aux7.{u_1} {R : Type u_1} [inst : CommRing R] : RingHomSurjective (RingHom.id R) :=
  ⟨Function.surjective_id⟩

noncomputable def d0.{u_1, u_2, u_3} {R : Type u_1} [inst : CommRing R]
    {G : Type u_2} [inst_1 : Group G] {M : Type u_3}
    [inst_2 : AddCommGroup M] [inst_3 : Module R M] (rho : Representation R G M) :
    M →ₗ[R] (G → M) :=
  LinearMap.pi fun g => rho g - LinearMap.id

noncomputable def B1.{u_1, u_2, u_3} {R : Type u_1} [inst : CommRing R]
    {G : Type u_2} [inst_1 : Group G] {M : Type u_3}
    [inst_2 : AddCommGroup M] [inst_3 : Module R M] (rho : Representation R G M) :
    Submodule R (G → M) :=
  LinearMap.range (d0 rho)

theorem cobOfGen :
    ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (Γ : Type) [inst_1 : Group Γ]
      [inst_2 : TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
      (χ : Γ →* ℤ_[l]ˣ) (R M : Type)
      [inst_5 : CommRing R] [inst_6 : AddCommGroup M] [inst_7 : Module R M]
      [inst_8 : TopologicalSpace M] [inst_9 : DiscreteTopology M]
      (ρ : Representation R Γ M) (γ : Γ),
      Continuous χ →
      ContAction ρ →
      (∀ g, χ g = 1 → ∀ m, ρ g m = m) →
      (∀ g, χ g ∈ (Subgroup.zpowers (χ γ)).topologicalClosure) →
      Function.Surjective (fun m : M => ρ γ m - m) →
      ∀ z ∈ @Z1 R _ Γ _ _ M _ _ _ _ aux6 ρ,
        (∀ g, χ g = 1 → z g = 0) → z ∈ B1 ρ := by
  intro l _ Γ _ _ _ _ χ R M _ _ _ _ _ ρ γ hχ hρ hker hgen hsurj z hz hz0
  have hzc : Continuous z := hz.1
  have hzm : ∀ g h : Γ, z (g * h) = z g + ρ g (z h) := hz.2
  obtain ⟨m, hm⟩ := hsurj (z γ)
  have hm' : ρ γ m - m = z γ := hm
  have hone : z 1 = 0 := hz0 1 (map_one χ)
  let S : Subgroup Γ :=
    { carrier := {g | z g = ρ g m - m}
      one_mem' := by
        change z 1 = ρ 1 m - m
        simp [hone]
      mul_mem' := by
        intro a b ha hb
        have ha' : z a = ρ a m - m := ha
        have hb' : z b = ρ b m - m := hb
        change z (a * b) = ρ (a * b) m - m
        rw [hzm, ha', hb', map_mul, map_sub, Module.End.mul_apply]
        abel
      inv_mem' := by
        intro a ha
        have ha' : z a = ρ a m - m := ha
        change z a⁻¹ = ρ a⁻¹ m - m
        have h1 := hzm a⁻¹ a
        have h2 : ρ a⁻¹ (ρ a m) = m := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rw [inv_mul_cancel, hone, ha', map_sub, h2] at h1
        rw [eq_neg_of_add_eq_zero_left h1.symm, neg_sub] }
  have hρm : Continuous fun g : Γ => ρ g m :=
    Continuous.comp (g := fun p : Γ × M => ρ p.1 p.2) (f := fun g : Γ => (g, m)) hρ
      (continuous_id.prodMk continuous_const)
  have hSc : IsClosed (S : Set Γ) := isClosed_eq hzc (hρm.sub continuous_const)
  have himg : IsClosed ((S.map χ : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    rw [Subgroup.coe_map]
    exact (hSc.isCompact.image hχ).isClosed
  have hle : (Subgroup.zpowers (χ γ)).topologicalClosure ≤ S.map χ :=
    Subgroup.topologicalClosure_minimal _
      ((Subgroup.zpowers_le).2 ⟨γ, hm'.symm, rfl⟩) himg
  have hall : ∀ g : Γ, g ∈ S := by
    intro g
    obtain ⟨s, hs, hsg⟩ := hle (hgen g)
    have hk : χ (s⁻¹ * g) = 1 := by rw [map_mul, map_inv, hsg, inv_mul_cancel]
    have hmem : s⁻¹ * g ∈ S := by
      change z (s⁻¹ * g) = ρ (s⁻¹ * g) m - m
      rw [hz0 _ hk, hker _ hk, sub_self]
    simpa using S.mul_mem hs hmem
  refine ⟨m, funext fun g => ?_⟩
  exact (hall g).symm

end UpperTheory.Reformulated.B.CoboundaryOfGenerator
