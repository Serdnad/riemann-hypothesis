import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BorelApproximation

noncomputable section

namespace UpperTheory.Reformulated.B.H23

@[reducible] noncomputable def Pl :
    (E : Type) → [inst : Field E] → [NumberField E] → Type :=
  @UpperTheory.Reformulated.B.BorelApproximation.Pl

@[reducible] noncomputable def GLw :
    {E : Type} → [inst : Field E] → [inst_1 : NumberField E] → ℕ → Pl E → Type :=
  @UpperTheory.Reformulated.B.BorelApproximation.GLw

theorem aux3 :
    ∀ (k : Type) [inst : Field k], SubsemiringClass (Subring k) k :=
  @UpperTheory.Reformulated.B.BorelApproximation.aux3

theorem aux4 :
    ∀ (k : Type) [inst : Field k] [inst_1 : ValuativeRel k] [inst_2 : TopologicalSpace k] [IsNonarchimedeanLocalField k],
      IsLocalRing ↥(Valuation.integer (Γ₀ := ValuativeRel.ValueGroupWithZero k) (ValuativeRel.valuation k)) :=
  @UpperTheory.Reformulated.B.BorelApproximation.aux4

noncomputable def blk :
    {α n : Type} → {m : α → Type} → (a : α) × m a ≃ n → n → α :=
  @UpperTheory.Reformulated.B.BorelApproximation.blk

theorem aux6 :
    ∀ (R : Type) [inst : CommRing R] {α n : Type} {m : α → Type} [inst_1 : LinearOrder α] [inst_2 : Fintype n]
      [inst_3 : DecidableEq n] (e : (a : α) × m a ≃ n) {x y : GL n R},
      Membership.mem (γ := Set (GL n R))
          {g : GL n R |
            Matrix.BlockTriangular (↑g : Matrix n n R) (blk (m := m) e)}
          x →
        Membership.mem (γ := Set (GL n R))
            {g : GL n R |
              Matrix.BlockTriangular (↑g : Matrix n n R) (blk (m := m) e)}
            y →
          Membership.mem (γ := Set (GL n R))
            {g : GL n R |
              Matrix.BlockTriangular (↑g : Matrix n n R) (blk (m := m) e)}
            (x * y) :=
  @UpperTheory.Reformulated.B.BorelApproximation.aux6

theorem aux7 :
    ∀ (R : Type) [inst : CommRing R] {α n : Type} {m : α → Type} [inst_1 : LinearOrder α] [inst_2 : Fintype n]
      [inst_3 : DecidableEq n] (e : (a : α) × m a ≃ n),
      Membership.mem (γ := Set (GL n R))
        {g : GL n R |
          Matrix.BlockTriangular (↑g : Matrix n n R) (blk (m := m) e)}
        1 :=
  @UpperTheory.Reformulated.B.BorelApproximation.aux7

theorem aux8 :
    ∀ (R : Type) [inst : CommRing R] {α n : Type} {m : α → Type} [inst_1 : LinearOrder α] [inst_2 : Fintype n]
      [inst_3 : DecidableEq n] (e : (a : α) × m a ≃ n) {x : GL n R},
      Membership.mem (γ := Set (GL n R))
          {g : GL n R |
            Matrix.BlockTriangular (↑g : Matrix n n R) (blk (m := m) e)}
          x →
        Membership.mem (γ := Set (GL n R))
          {g : GL n R |
            Matrix.BlockTriangular (↑g : Matrix n n R) (blk (m := m) e)}
          x⁻¹ :=
  @UpperTheory.Reformulated.B.BorelApproximation.aux8

noncomputable def parab :
    (R : Type) →
      [inst : CommRing R] →
        {α n : Type} →
          {m : α → Type} →
            [LinearOrder α] → [inst_2 : Fintype n] → [inst_3 : DecidableEq n] → (a : α) × m a ≃ n → Subgroup (GL n R) :=
  @UpperTheory.Reformulated.B.BorelApproximation.parab

noncomputable def points :
    (n : Type) → (_ : n) × Unit ≃ n :=
  @UpperTheory.Reformulated.B.BorelApproximation.points

noncomputable def borel :
    (R : Type) →
      [inst : CommRing R] →
        (n : Type) → [inst_1 : Fintype n] → [inst_2 : DecidableEq n] → [LinearOrder n] → Subgroup (GL n R) :=
  @UpperTheory.Reformulated.B.BorelApproximation.borel

noncomputable def iwahori :
    (k : Type) →
      [inst : Field k] →
        [inst_1 : ValuativeRel k] →
          [inst_2 : TopologicalSpace k] →
            [IsNonarchimedeanLocalField k] →
              (n : Type) → [inst_4 : Fintype n] → [inst_5 : DecidableEq n] → [LinearOrder n] → Subgroup (GL n k) :=
  @UpperTheory.Reformulated.B.BorelApproximation.iwahori

@[reducible] noncomputable def complRel :
    {F : Type} →
      [inst : Field F] →
        [inst_1 : NumberField F] →
          (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →
            ValuativeRel (IsDedekindDomain.HeightOneSpectrum.adicCompletion F p) :=
  @UpperTheory.Reformulated.B.BorelApproximation.complRel

theorem zero_contDiffOn_supported :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F]
      (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
      @IsNonarchimedeanLocalField (IsDedekindDomain.HeightOneSpectrum.adicCompletion F p) _
        (complRel p) _ :=
  @UpperTheory.Reformulated.B.BorelApproximation.zero_contDiffOn_supported

noncomputable def iwGL :
    {E : Type} →
      [inst : Field E] →
        [inst_1 : NumberField E] →
          (n : ℕ) →
            (w : Pl E) →
              Subgroup (GLw n w) :=
  @UpperTheory.Reformulated.B.BorelApproximation.iwGL

noncomputable def dcos :
    {E : Type} →
      [inst : Field E] →
        [inst_1 : NumberField E] →
          (n : ℕ) →
            (w : Pl E) →
              GLw n w →
                GLw n w → ℂ :=
  @UpperTheory.Reformulated.B.BorelApproximation.dcos

theorem dcos_right :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [NumberField.IsCMField E] {m : ℕ}
      {w : Pl E}
      (t k g : GLw m w),
      k ∈ iwGL m w →
        dcos m w t (g * k) =
          dcos m w t g := by
  intro E _ _ _ m w t k g hk
  unfold dcos UpperTheory.Reformulated.B.BorelApproximation.dcos
  refine @if_congr _ _ _ (Classical.propDecidable _) (Classical.propDecidable _) _ _ _ _
    ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨x, hx, z, hz, h⟩
    exact ⟨x, hx, z * k⁻¹, Subgroup.mul_mem _ hz (Subgroup.inv_mem _ hk), by
      rw [← mul_assoc, ← h, mul_inv_cancel_right]⟩
  · rintro ⟨x, hx, z, hz, h⟩
    exact ⟨x, hx, z * k, Subgroup.mul_mem _ hz hk, by rw [h, mul_assoc (x * t)]⟩

end UpperTheory.Reformulated.B.H23
