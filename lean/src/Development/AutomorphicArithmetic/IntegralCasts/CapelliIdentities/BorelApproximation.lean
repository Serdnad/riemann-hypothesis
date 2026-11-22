import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.BorelApproximation.Pl :
    (E : Type) → [inst : Field E] → [NumberField E] → Type :=
    fun (E : Type) [Field E] [NumberField E] => IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)

@[reducible] noncomputable def UpperTheory.Reformulated.B.BorelApproximation.GLw :
    {E : Type} → [inst : Field E] → [inst_1 : NumberField E] → ℕ → UpperTheory.Reformulated.B.BorelApproximation.Pl E → Type :=
    fun {E : Type} [Field E] [NumberField E] (n : ℕ) (w : UpperTheory.Reformulated.B.BorelApproximation.Pl E) =>
      GL (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w)

theorem UpperTheory.Reformulated.B.BorelApproximation.aux3 :
    ∀ (k : Type) [inst : Field k], SubsemiringClass (Subring k) k := by
  intro k _
  infer_instance

theorem UpperTheory.Reformulated.B.BorelApproximation.aux4 :
    ∀ (k : Type) [inst : Field k] [inst_1 : ValuativeRel k] [inst_2 : TopologicalSpace k] [IsNonarchimedeanLocalField k],
      IsLocalRing ↥(Valuation.integer (Γ₀ := ValuativeRel.ValueGroupWithZero k) (ValuativeRel.valuation k)) := by
  intro k _ _ _ _
  infer_instance

noncomputable def UpperTheory.Reformulated.B.BorelApproximation.blk :
    {α n : Type} → {m : α → Type} → (a : α) × m a ≃ n → n → α :=
    fun {α n : Type} {m : α → Type} (e : (a : α) × m a ≃ n) (i : n) =>
      Sigma.fst (β := fun (a : α) => m a) ((Equiv.symm e : (a : n) → (a : α) × m a) i)

theorem UpperTheory.Reformulated.B.BorelApproximation.aux6 :
    ∀ (R : Type) [inst : CommRing R] {α n : Type} {m : α → Type} [inst_1 : LinearOrder α] [inst_2 : Fintype n]
      [inst_3 : DecidableEq n] (e : (a : α) × m a ≃ n) {x y : GL n R},
      Membership.mem (γ := Set (GL n R))
          {g : GL n R |
            Matrix.BlockTriangular (↑g : Matrix n n R) (UpperTheory.Reformulated.B.BorelApproximation.blk (m := m) e)}
          x →
        Membership.mem (γ := Set (GL n R))
            {g : GL n R |
              Matrix.BlockTriangular (↑g : Matrix n n R) (UpperTheory.Reformulated.B.BorelApproximation.blk (m := m) e)}
            y →
          Membership.mem (γ := Set (GL n R))
            {g : GL n R |
              Matrix.BlockTriangular (↑g : Matrix n n R) (UpperTheory.Reformulated.B.BorelApproximation.blk (m := m) e)}
            (x * y) := by
  intro R _ α n m _ _ _ e x y hx hy
  exact Matrix.BlockTriangular.mul hx hy

theorem UpperTheory.Reformulated.B.BorelApproximation.aux7 :
    ∀ (R : Type) [inst : CommRing R] {α n : Type} {m : α → Type} [inst_1 : LinearOrder α] [inst_2 : Fintype n]
      [inst_3 : DecidableEq n] (e : (a : α) × m a ≃ n),
      Membership.mem (γ := Set (GL n R))
        {g : GL n R |
          Matrix.BlockTriangular (↑g : Matrix n n R) (UpperTheory.Reformulated.B.BorelApproximation.blk (m := m) e)}
        1 := by
  intro R _ α n m _ _ _ e
  exact Matrix.blockTriangular_one

theorem UpperTheory.Reformulated.B.BorelApproximation.aux8 :
    ∀ (R : Type) [inst : CommRing R] {α n : Type} {m : α → Type} [inst_1 : LinearOrder α] [inst_2 : Fintype n]
      [inst_3 : DecidableEq n] (e : (a : α) × m a ≃ n) {x : GL n R},
      Membership.mem (γ := Set (GL n R))
          {g : GL n R |
            Matrix.BlockTriangular (↑g : Matrix n n R) (UpperTheory.Reformulated.B.BorelApproximation.blk (m := m) e)}
          x →
        Membership.mem (γ := Set (GL n R))
          {g : GL n R |
            Matrix.BlockTriangular (↑g : Matrix n n R) (UpperTheory.Reformulated.B.BorelApproximation.blk (m := m) e)}
          x⁻¹ := by
  intro R _ α n m _ _ _ e x hx
  have hx : Matrix.BlockTriangular (x : Matrix n n R) (UpperTheory.Reformulated.B.BorelApproximation.blk e) := hx
  letI := x.invertible
  change Matrix.BlockTriangular ((x⁻¹ : GL n R) : Matrix n n R) (UpperTheory.Reformulated.B.BorelApproximation.blk e)
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hx

noncomputable def UpperTheory.Reformulated.B.BorelApproximation.parab :
    (R : Type) →
      [inst : CommRing R] →
        {α n : Type} →
          {m : α → Type} →
            [LinearOrder α] → [inst_2 : Fintype n] → [inst_3 : DecidableEq n] → (a : α) × m a ≃ n → Subgroup (GL n R) :=
    fun (R : Type) [inst : CommRing R] {α n : Type} {m : α → Type} [inst_1 : LinearOrder α] [inst_2 : Fintype n]
        [inst_3 : DecidableEq n] (e : (a : α) × m a ≃ n) =>
      {
        carrier :=
          {g : GL n R |
            Matrix.BlockTriangular (↑g : Matrix n n R) (UpperTheory.Reformulated.B.BorelApproximation.blk (m := m) e)},
        mul_mem' := @UpperTheory.Reformulated.B.BorelApproximation.aux6 R inst α n m inst_1 inst_2 inst_3 e,
        one_mem' := UpperTheory.Reformulated.B.BorelApproximation.aux7 R (m := m) e,
        inv_mem' := @UpperTheory.Reformulated.B.BorelApproximation.aux8 R inst α n m inst_1 inst_2 inst_3 e }

noncomputable def UpperTheory.Reformulated.B.BorelApproximation.points :
    (n : Type) → (_ : n) × Unit ≃ n :=
    fun (n : Type) => Equiv.sigmaUnique n fun (x : n) => Unit

noncomputable def UpperTheory.Reformulated.B.BorelApproximation.borel :
    (R : Type) →
      [inst : CommRing R] →
        (n : Type) → [inst_1 : Fintype n] → [inst_2 : DecidableEq n] → [LinearOrder n] → Subgroup (GL n R) :=
    fun (R : Type) [CommRing R] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] =>
      UpperTheory.Reformulated.B.BorelApproximation.parab R (m := fun (a : n) => Unit)
        (UpperTheory.Reformulated.B.BorelApproximation.points n)

noncomputable def UpperTheory.Reformulated.B.BorelApproximation.iwahori :
    (k : Type) →
      [inst : Field k] →
        [inst_1 : ValuativeRel k] →
          [inst_2 : TopologicalSpace k] →
            [IsNonarchimedeanLocalField k] →
              (n : Type) → [inst_4 : Fintype n] → [inst_5 : DecidableEq n] → [LinearOrder n] → Subgroup (GL n k) :=
    fun (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n]
        [DecidableEq n] [LinearOrder n] =>
      Subgroup.map (G := GL n ↥(Valuation.integer (Γ₀ := ValuativeRel.ValueGroupWithZero k) (ValuativeRel.valuation k)))
        (Matrix.GeneralLinearGroup.map
          (Algebra.algebraMap (↥(Valuation.integer (Γ₀ := ValuativeRel.ValueGroupWithZero k) (ValuativeRel.valuation k)))
            k))
        (Subgroup.comap (N :=
          GL n
            (IsLocalRing.ResidueField
              ↥(Valuation.integer (Γ₀ := ValuativeRel.ValueGroupWithZero k) (ValuativeRel.valuation k))))
          (Matrix.GeneralLinearGroup.map
            (IsLocalRing.residue ↥(Valuation.integer (Γ₀ := ValuativeRel.ValueGroupWithZero k) (ValuativeRel.valuation k))))
          (UpperTheory.Reformulated.B.BorelApproximation.borel
            (IsLocalRing.ResidueField
              ↥(Valuation.integer (Γ₀ := ValuativeRel.ValueGroupWithZero k) (ValuativeRel.valuation k)))
            n))

@[reducible] noncomputable def UpperTheory.Reformulated.B.BorelApproximation.complRel :
    {F : Type} →
      [inst : Field F] →
        [inst_1 : NumberField F] →
          (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →
            ValuativeRel (IsDedekindDomain.HeightOneSpectrum.adicCompletion F p) :=
    fun {F : Type} [Field F] [NumberField F] (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) =>
      ValuativeRel.ofValuation Valued.v

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum in
private theorem UpperTheory.Reformulated.B.BorelApproximation.exists_near {F : Type} [Field F] [NumberField F]
    (p : HeightOneSpectrum (NumberField.RingOfIntegers F)) (x : adicCompletion F p)
    (hx : Valued.v x ≤ 1) :
    ∃ a : NumberField.RingOfIntegers F, Valued.v (x - algebraMap _ (adicCompletion F p) a) < 1 := by
  have hb : {y : adicCompletion F p | Valued.v (y - x) < 1} ∈ nhds x := by
    rw [Valued.mem_nhds]
    refine ⟨1, fun y hy => ?_⟩
    simpa using hy
  obtain ⟨k, hk⟩ := (denseRange_algebraMap F p).mem_nhds hb
  have hk : Valued.v (algebraMap F (adicCompletion F p) k - x) < 1 := hk
  have hv : ∀ y : F, Valued.v (algebraMap F (adicCompletion F p) y) = p.valuation F y :=
    fun y => valuedAdicCompletion_eq_valuation' p y
  have hk1 : p.valuation F k ≤ 1 := by
    rw [← hv, ← sub_add_cancel (algebraMap F (adicCompletion F p) k) x]
    exact Valuation.map_add_le _ hk.le hx
  obtain ⟨a, ha⟩ := exists_valuation_sub_lt_of_integer p hk1 1
  refine ⟨a, ?_⟩
  rw [← hv, map_sub, ← IsScalarTower.algebraMap_apply, Units.val_one] at ha
  rw [Valuation.map_sub_swap, ← sub_add_sub_cancel _ (algebraMap F (adicCompletion F p) k)]
  exact Valuation.map_add_lt _ ha hk

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum in
private theorem UpperTheory.Reformulated.B.BorelApproximation.finite_residue {F : Type} [Field F] [NumberField F]
    (p : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    Finite (IsLocalRing.ResidueField (adicCompletionIntegers F p)) := by
  have hfin : Finite (NumberField.RingOfIntegers F ⧸ p.asIdeal) :=
    p.asIdeal.finiteQuotientOfFreeOfNeBot p.ne_bot
  have hmax : ∀ y : adicCompletionIntegers F p, Valued.v y.1 < 1 →
      IsLocalRing.residue _ y = 0 := fun y hy => by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact hy.ne
  let φ : NumberField.RingOfIntegers F →+* IsLocalRing.ResidueField (adicCompletionIntegers F p) :=
    (IsLocalRing.residue _).comp (algebraMap _ _)
  have hker : ∀ a ∈ p.asIdeal, φ a = 0 := fun a ha => by
    refine hmax _ ?_
    rw [algebraMap_adicCompletionIntegers_apply, valuedAdicCompletion_eq_valuation']
    exact (valuation_lt_one_iff_mem p a).2 ha
  refine Finite.of_surjective (Ideal.Quotient.lift p.asIdeal φ hker) fun z => ?_
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨a, ha⟩ := UpperTheory.Reformulated.B.BorelApproximation.exists_near p x.1 x.2
  refine ⟨Ideal.Quotient.mk _ a, ?_⟩
  rw [Ideal.Quotient.lift_mk, eq_comm, ← sub_eq_zero]
  have := hmax (x - algebraMap _ _ a) ha
  rwa [map_sub] at this

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum in
private theorem UpperTheory.Reformulated.B.BorelApproximation.locCompact {F : Type} [Field F] [NumberField F]
    (p : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    LocallyCompactSpace (adicCompletion F p) := by
  have h := (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
    (K := adicCompletion F p)).2
    ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (adicCompletionIntegers F p)),
      UpperTheory.Reformulated.B.BorelApproximation.finite_residue p⟩
  exact locallyCompact_of_proper

theorem UpperTheory.Reformulated.B.BorelApproximation.zero_contDiffOn_supported :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F]
      (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
      @IsNonarchimedeanLocalField (IsDedekindDomain.HeightOneSpectrum.adicCompletion F p) _
        (UpperTheory.Reformulated.B.BorelApproximation.complRel p) _ := by
  intro F _ _ p
  letI := UpperTheory.Reformulated.B.BorelApproximation.complRel p
  haveI : (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  haveI : IsValuativeTopology (p.adicCompletion F) :=
    IsValuativeTopology.of_mem_nhds_zero_iff_vle
      (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ)))
      (fun {s} => Valued.is_topological_valuation s)
  haveI := UpperTheory.Reformulated.B.BorelApproximation.locCompact p
  haveI : ValuativeRel.IsNontrivial (p.adicCompletion F) :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ)))).2 inferInstance
  exact {}

noncomputable def UpperTheory.Reformulated.B.BorelApproximation.iwGL :
    {E : Type} →
      [inst : Field E] →
        [inst_1 : NumberField E] →
          (n : ℕ) →
            (w : UpperTheory.Reformulated.B.BorelApproximation.Pl E) →
              Subgroup (UpperTheory.Reformulated.B.BorelApproximation.GLw n w) :=
    fun {E : Type} [Field E] [NumberField E] (n : ℕ) (w : UpperTheory.Reformulated.B.BorelApproximation.Pl E) =>
      @UpperTheory.Reformulated.B.BorelApproximation.iwahori (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w) _
        (UpperTheory.Reformulated.B.BorelApproximation.complRel w) _
        (UpperTheory.Reformulated.B.BorelApproximation.zero_contDiffOn_supported w) (Fin n) _ _ _

noncomputable def UpperTheory.Reformulated.B.BorelApproximation.dcos :
    {E : Type} →
      [inst : Field E] →
        [inst_1 : NumberField E] →
          (n : ℕ) →
            (w : UpperTheory.Reformulated.B.BorelApproximation.Pl E) →
              UpperTheory.Reformulated.B.BorelApproximation.GLw n w →
                UpperTheory.Reformulated.B.BorelApproximation.GLw n w → ℂ :=
    fun {E : Type} [Field E] [NumberField E] (n : ℕ) (w : UpperTheory.Reformulated.B.BorelApproximation.Pl E)
        (t y : UpperTheory.Reformulated.B.BorelApproximation.GLw n w) =>
      ite
        (∃ x ∈ UpperTheory.Reformulated.B.BorelApproximation.iwGL n w,
          ∃ z ∈ UpperTheory.Reformulated.B.BorelApproximation.iwGL n w, y = x * t * z)
        (h :=
        Classical.propDecidable
          (∃ x ∈ UpperTheory.Reformulated.B.BorelApproximation.iwGL n w,
            ∃ z ∈ UpperTheory.Reformulated.B.BorelApproximation.iwGL n w, y = x * t * z))
        1 0

theorem UpperTheory.Reformulated.B.BorelApproximation.dcos_left :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [NumberField.IsCMField E] {m : ℕ}
      {w : UpperTheory.Reformulated.B.BorelApproximation.Pl E}
      (t k g : UpperTheory.Reformulated.B.BorelApproximation.GLw m w),
      k ∈ UpperTheory.Reformulated.B.BorelApproximation.iwGL m w →
        UpperTheory.Reformulated.B.BorelApproximation.dcos m w t (k * g) =
          UpperTheory.Reformulated.B.BorelApproximation.dcos m w t g := by
  intro E _ _ _ m w t k g hk
  unfold UpperTheory.Reformulated.B.BorelApproximation.dcos
  refine congrArg (fun P : Prop => @ite ℂ P (Classical.propDecidable P) 1 0) (propext ⟨?_, ?_⟩)
  · rintro ⟨x, hx, z, hz, h⟩
    refine ⟨k⁻¹ * x, mul_mem (inv_mem hk) hx, z, hz, ?_⟩
    rw [mul_assoc k⁻¹, mul_assoc k⁻¹, ← h, inv_mul_cancel_left]
  · rintro ⟨x, hx, z, hz, h⟩
    refine ⟨k * x, mul_mem hk hx, z, hz, ?_⟩
    rw [h, mul_assoc k, mul_assoc k]
