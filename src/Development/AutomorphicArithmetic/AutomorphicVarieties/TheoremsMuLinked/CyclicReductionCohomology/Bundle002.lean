module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.OmFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private def SJ {R D M : Type} [CommRing R] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module R M]
    (ρ : Representation R D M) (J : Subgroup D) : Submodule R (D → M) where
  carrier := {z | z ∈ Zl ρ ∧ ∀ g ∈ J, z g = 0}
  add_mem' a b := ⟨add_mem a.1 b.1, fun g hg => by rw [Pi.add_apply, a.2 g hg, b.2 g hg, add_zero]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ => rfl⟩
  smul_mem' c x a := ⟨Submodule.smul_mem _ c a.1, fun g hg => by rw [Pi.smul_apply, a.2 g hg, smul_zero]⟩

private theorem card_step {R A B C : Type} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup C] [Module R C]
    [Finite B] [Finite C] (f : A →ₗ[R] C) (i : LinearMap.ker f → B) (hi : Function.Injective i) :
    Finite A ∧ Nat.card A ≤ Nat.card B * Nat.card C := by
  haveI : Finite (LinearMap.ker f) := Finite.of_injective i hi
  have h : Nat.card A = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
    rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f), Nat.card_congr f.quotKerEquivRange.toEquiv]
  refine ⟨Nat.finite_of_card_ne_zero (h ▸ mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'), ?_⟩
  rw [h]
  exact Nat.mul_le_mul (Nat.card_le_card_of_injective i hi) (Nat.card_le_card_of_injective _ Subtype.val_injective)

theorem UpperTheory.V.Th.unrDev :
    ∀ (l : ℕ) [Fact l.Prime] (D : Type) [Group D] [TopologicalSpace D] (J : Subgroup D), UnrCount l D J → UnrCnt l D J := by
  intro l _ D _ _ J hU k R
  induction k with
  | zero =>
    intro M _ _ _ _ ρ _ hk _
    have : {z | z ∈ Zl ρ ∧ ∀ g ∈ J, z g = 0} ⊆ {0} := fun z _ => funext fun g => by simpa using hk (z g)
    refine ⟨(Set.finite_singleton _).subset this, (Set.ncard_le_ncard this).trans ?_⟩
    rw [Set.ncard_singleton]
    exact Nat.card_pos
  | succ k ih =>
    intro M _ _ _ _ ρ hLC hk hJ
    let μ : M →ₗ[R] M := l • LinearMap.id
    have hμ : ∀ m, μ m = l • m := fun m => rfl
    have hN : ∀ g, LinearMap.ker μ ≤ (LinearMap.ker μ).comap (ρ g) := fun g m hm => by
      have h1 : l • m = 0 := hm
      show l • ρ g m = 0
      rw [← map_nsmul, h1, map_zero]
    have hQ : ∀ g, LinearMap.range μ ≤ (LinearMap.range μ).comap (ρ g) := by
      rintro g _ ⟨m, rfl⟩
      exact ⟨ρ g m, (map_nsmul (ρ g) l m).symm⟩
    let σ := ρ.subrepresentation _ hN
    let τ := ρ.subrepresentation _ hQ
    obtain ⟨f1, c1⟩ := hU R _ σ (fun m => IsLocallyConstant.desc _ Subtype.val (hLC m.1) Subtype.val_injective)
      (fun m => Subtype.ext m.2) fun g hg => LinearMap.ext fun m => Subtype.ext (by
        show ρ g m = m
        rw [hJ g hg]; rfl)
    obtain ⟨f2, c2⟩ := ih _ τ (fun m => IsLocallyConstant.desc _ Subtype.val (hLC m.1) Subtype.val_injective)
      (by
        rintro ⟨_, m, rfl⟩
        refine Subtype.ext ?_
        show l ^ k • l • m = 0
        rw [← mul_smul, ← pow_succ, hk]) fun g hg => LinearMap.ext fun m => Subtype.ext (by
        show ρ g m = m
        rw [hJ g hg]; rfl)
    haveI : Finite (SJ σ J) := f1
    haveI : Finite (SJ τ J) := f2
    let f : SJ ρ J →ₗ[R] SJ τ J :=
      { toFun := fun z => ⟨fun g => ⟨μ (z.1 g), z.1 g, rfl⟩,
          ⟨IsLocallyConstant.desc _ Subtype.val (z.2.1.1.comp μ) Subtype.val_injective, fun g h => Subtype.ext (by
            show μ (z.1 (g * h)) = μ (z.1 g) + ρ g (μ (z.1 h))
            rw [z.2.1.2, map_add (f := _), hμ (ρ g _), hμ (z.1 h), map_nsmul])⟩,
          fun g hg => Subtype.ext (by
            show μ (z.1 g) = 0
            rw [z.2.2 g hg, map_zero])⟩
        map_add' := fun a b => Subtype.ext (funext fun g => Subtype.ext (map_add μ _ _))
        map_smul' := fun c a => Subtype.ext (funext fun g => Subtype.ext (map_smul μ _ _)) }
    have hm : ∀ (z : LinearMap.ker f) g, z.1.1 g ∈ LinearMap.ker μ := fun z g =>
      congrArg Subtype.val (congrFun (congrArg Subtype.val z.2) g)
    let i : LinearMap.ker f → SJ σ J := fun z => ⟨fun g => ⟨z.1.1 g, hm z g⟩,
      ⟨IsLocallyConstant.desc _ Subtype.val z.1.2.1.1 Subtype.val_injective, fun g h => Subtype.ext (z.1.2.1.2 g h)⟩,
      fun g hg => Subtype.ext (z.1.2.2 g hg)⟩
    obtain ⟨f3, c3⟩ := card_step f i fun a b h =>
      Subtype.ext (Subtype.ext (funext fun g => congrArg Subtype.val (congrFun (congrArg Subtype.val h) g)))
    refine ⟨f3, ?_⟩
    have h : Nat.card M = Nat.card (LinearMap.ker μ) * Nat.card (LinearMap.range μ) := by
      rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker μ), Nat.card_congr μ.quotKerEquivRange.toEquiv]
    rw [h, ← Nat.card_coe_set_eq]
    rw [← Nat.card_coe_set_eq] at c1 c2
    exact c3.trans (Nat.mul_le_mul c1.le c2)
end

section

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem polZ_mem {l : ℕ} [Fact l.Prime] (F : GFrame l) {γ : F.Γ} (h : γ ∉ F.η.ker) : γ * F.c ∈ F.η.ker := by
  rw [MonoidHom.mem_ker] at h ⊢
  rw [map_mul, F.η_c, (Int.units_eq_one_or (F.η γ)).resolve_left h]
  simp

private theorem polZ_nmem {l : ℕ} [Fact l.Prime] (F : GFrame l) (g : F.G₀) : (g : F.Γ) * F.c ∉ F.η.ker := by
  have := g.2
  rw [MonoidHom.mem_ker] at this ⊢
  rw [map_mul, F.η_c, this]
  decide

private theorem polZ_proj {l : ℕ} [Fact l.Prime] (F : GFrame l) :
    ∃ p : F.Γ → F.G₀, Continuous p ∧ (∀ g : F.G₀, p g = g) ∧ ∀ g : F.G₀, p (g * F.c) = g := by
  classical
  refine ⟨fun γ => ⟨if γ ∈ F.η.ker then γ else γ * F.c, ?_⟩, ?_, ?_, ?_⟩
  · split_ifs with h
    · exact h
    · exact polZ_mem F h
  · refine Continuous.subtype_mk ?_ _
    refine Continuous.if ?_ continuous_id (continuous_id.mul continuous_const)
    have hc : IsClopen (F.η.ker : Set F.Γ) := ⟨Subgroup.isClosed_of_isOpen _ F.η_open, F.η_open⟩
    intro a ha
    have : frontier {x | x ∈ F.η.ker} = ∅ := hc.frontier_eq
    rw [this] at ha
    exact ha.elim
  · intro g
    exact Subtype.ext (if_pos g.2)
  · intro g
    refine Subtype.ext ((if_neg (polZ_nmem F g)).trans ?_)
    rw [mul_assoc, F.c_sq, mul_one]

private theorem polZ_cases {l : ℕ} [Fact l.Prime] (F : GFrame l) (γ : F.Γ) :
    (∃ g : F.G₀, γ = g) ∨ ∃ g : F.G₀, γ = g * F.c := by
  by_cases h : γ ∈ F.η.ker
  · exact Or.inl ⟨⟨γ, h⟩, rfl⟩
  · refine Or.inr ⟨⟨γ * F.c, polZ_mem F h⟩, ?_⟩
    show γ = γ * F.c * F.c
    rw [mul_assoc, F.c_sq, mul_one]

private theorem polZ_conj {l : ℕ} [Fact l.Prime] (F : GFrame l) (g : F.G₀) :
    (F.conj g : F.Γ) = F.c * g * F.c := by
  show F.c * g * F.c⁻¹ = _
  rw [inv_eq_of_mul_eq_one_right F.c_sq]

private theorem polZ_ext {l : ℕ} [Fact l.Prime] (F : GFrame l) {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (rep : Representation A F.Γ M) (Z : F.G₀ → M) (hl : IsLocallyConstant Z)
    (hm : ∀ g h, Z (g * h) = Z g + rep g (Z h)) (hc : ∀ g, Z (F.conj g) = rep F.c (Z g)) :
    ∃ y ∈ Zl rep, y F.c = 0 ∧ ∀ g : F.G₀, y g = Z g := by
  obtain ⟨p, pc, p1, p2⟩ := polZ_proj F
  have h1 : Z 1 = 0 := by
    have := hm 1 1
    simpa using this
  have cc : ∀ x : F.Γ, x * F.c * F.c = x := fun x => by rw [mul_assoc, F.c_sq, mul_one]
  refine ⟨Z ∘ p, ⟨hl.comp_continuous pc, fun a b => ?_⟩, ?_, fun g => by simp [p1]⟩
  · simp only [Function.comp]
    rcases polZ_cases F a with ⟨g, rfl⟩ | ⟨g, rfl⟩ <;> rcases polZ_cases F b with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · rw [← Subgroup.coe_mul, p1, p1, p1, hm]
    · rw [← mul_assoc, ← Subgroup.coe_mul, p2, p1, p2, hm]
    · have : (g : F.Γ) * F.c * h = ((g * F.conj h : F.G₀) : F.Γ) * F.c := by
        rw [Subgroup.coe_mul, polZ_conj, ← mul_assoc, ← mul_assoc, cc]
      rw [this, p2, p2, p1, hm, hc, map_mul]
      rfl
    · have : (g : F.Γ) * F.c * (h * F.c) = ((g * F.conj h : F.G₀) : F.Γ) := by
        rw [Subgroup.coe_mul, polZ_conj]
        simp only [mul_assoc]
      rw [this, p2, p2, p1, hm, hc, map_mul]
      rfl
  · have := p2 1
    rw [OneMemClass.coe_one, one_mul] at this
    simp [this, h1]

theorem UpperTheory.V.Th.polP :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (n : ℕ) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (P : Matrix (Fin n) (Fin n) R) (χ : F.Γ → R) (rep : Representation A F.Γ (Matrix (Fin n) (Fin n) R)), IsUnit P → IsAdP F ρ P χ rep → (∀ z : F.G₀ → Matrix (Fin n) (Fin n) R, IsLocallyConstant z → (∀ g g', z (g * g') = z g + χ g • (ρ g * z g' * ρ g⁻¹)) → (∀ g, P * z (F.conj g) = -(χ F.c • ((z g)ᵀ * P))) → ∃ y ∈ Zl rep, y F.c = 0 ∧ ∀ g : F.G₀, y g = z g) ∧ (∀ y ∈ Zl rep, y F.c = 0 → (∀ g : F.G₀, P * y (F.conj g) = -(χ F.c • ((y g)ᵀ * P))) ∧ ((∀ g : F.G₀, y g = 0) → y = 0)) := by
  intro l _ F A R _ _ _ n ρ P χ rep hP ⟨a1, a2⟩
  refine ⟨fun z hl hm hc => ?_, fun y ⟨_, hy⟩ hc => ⟨fun g => ?_, fun h0 => ?_⟩⟩
  · exact polZ_ext F rep z hl (fun g h => by rw [a1]; exact hm g h)
      (fun g => hP.mul_left_cancel (by rw [a2]; exact hc g))
  · rw [← a2, polZ_conj, hy, hc, map_zero, add_zero, hy, hc, zero_add]
  · funext γ
    rcases polZ_cases F γ with ⟨g, rfl⟩ | ⟨g, rfl⟩
    · exact h0 g
    · rw [hy, h0, hc, map_zero, add_zero]
      rfl
end

section

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

theorem UpperTheory.V.Th.locCntCongr :
    ∀ (l : ℕ) [Fact l.Prime] (D D' : Type) [Group D] [TopologicalSpace D] [Group D'] [TopologicalSpace D'] (α : D ≃ₜ* D') (ε : D →* ℤ_[l]ˣ) (ε' : D' →* ℤ_[l]ˣ) (d : ℕ), (∀ g, ε g = ε' (α g)) → LocCnt D' ε' d → LocCnt D ε d := by
  intro l _ D D' _ _ _ _ α ε ε' d hε H k hk R M M' _ _ _ _ _ _ _ ρ ρ' b hLC hb
  let β : D' →* D := α.symm.toMulEquiv.toMonoidHom
  let σ : Representation R D' M := ρ.comp β
  let σ' : Representation R D' M' := ρ'.comp β
  have hσ : ∀ g, σ g = ρ (α.symm g) := fun _ => rfl
  have hσ' : ∀ g, σ' g = ρ' (α.symm g) := fun _ => rfl
  have h1 : LC σ := fun m => (hLC m).comp_continuous α.symm.continuous
  have h2 : DualPair k ε' σ σ' b := by
    refine ⟨hb.left, hb.right, fun g x y => ?_⟩
    rw [hσ, hσ', hb.equiv]
    simp only [hε, ContinuousMulEquiv.apply_symm_apply]
  obtain ⟨hf, hc⟩ := H k hk R M M' σ σ' b h1 h2
  let e : Zl ρ ≃ Zl σ :=
    { toFun := fun z => ⟨fun g => z.1 (α.symm g), z.2.1.comp_continuous α.symm.continuous, fun g h => by
        beta_reduce
        rw [map_mul, z.2.2, hσ]⟩
      invFun := fun z => ⟨fun g => z.1 (α g), z.2.1.comp_continuous α.continuous, fun g h => by
        beta_reduce
        rw [map_mul, z.2.2, hσ, ContinuousMulEquiv.symm_apply_apply]⟩
      left_inv := fun z => Subtype.ext (funext fun g => by simp)
      right_inv := fun z => Subtype.ext (funext fun g => by simp) }
  have hi : ρ'.invariants = σ'.invariants := by
    ext m
    simp only [Representation.mem_invariants, hσ']
    exact ⟨fun h g => h _, fun h g => by simpa using h (α g)⟩
  exact ⟨Finite.of_equiv _ e.symm, by rw [Nat.card_congr e, hc, hi]⟩
end

section

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem fixBd_abs {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Finite (IsLocalRing.ResidueField A)] {E S : Type} [AddCommGroup E] [Module A E] [Module.Finite A E]
    (f : S → E →ₗ[A] E) : ∃ C : ℕ, ∀ (m : ℕ) (E' : Type) [AddCommGroup E'] [Module A E'] (r : E →ₗ[A] E')
      (T : Set E'), LinearMap.ker r = IsLocalRing.maximalIdeal A ^ m • (⊤ : Submodule A E) →
      (∀ Y ∈ T, ∃ Z, r Z = Y ∧ ∀ s, r (f s Z) = 0) →
      T.ncard ≤ Nat.card (IsLocalRing.ResidueField A) ^
        (m * Module.finrank A (⨅ s, LinearMap.ker (f s) : Submodule A E) + C) := by
  obtain ⟨e, he⟩ := UpperTheory.V.AlgebraTools.lemma_B f
  refine ⟨e, fun m E' _ _ r T hk hT => ?_⟩
  have h := he m
  set N := (⨅ s, (IsLocalRing.maximalIdeal A ^ m • (⊤ : Submodule A E)).comap (f s)).map
    (IsLocalRing.maximalIdeal A ^ m • (⊤ : Submodule A E)).mkQ with hN
  have hne : Module.length A N ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) h
  have hfin : Finite N := (UpperTheory.V.AlgebraTools.card_eq_pow_length (A := A) (X := N)).1.2 hne
  have hc := (UpperTheory.V.AlgebraTools.card_eq_pow_length (A := A) (X := N)).2 hfin
  have hsub : T ⊆ ((IsLocalRing.maximalIdeal A ^ m • (⊤ : Submodule A E)).liftQ r hk.ge) '' (SetLike.coe N) := by
    intro Y hY
    obtain ⟨Z, rfl, hZ⟩ := hT Y hY
    refine ⟨_, Submodule.mem_map_of_mem (r := Z) ?_, rfl⟩
    rw [Submodule.mem_iInf]
    intro s
    rw [Submodule.mem_comap, ← hk]
    exact hZ s
  have hf : (SetLike.coe N).Finite := Set.toFinite _
  refine (Set.ncard_le_ncard hsub (hf.image _)).trans ((Set.ncard_image_le hf).trans ?_)
  have : (SetLike.coe N).ncard = Nat.card N := rfl
  rw [this, hc]
  refine Nat.pow_le_pow_right Nat.card_pos ?_
  rw [mul_comm]
  exact ENat.toNat_le_of_le_coe h

theorem UpperTheory.V.Th.fixCnt :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (S : Type) (Φ : S → Matrix (Fin n) (Fin n) O →ₗ[O] Matrix (Fin n) (Fin n) O), ∃ C : ℕ, ∀ m, {Y : Mm O n m | ∃ Y', red m Y' = Y ∧ ∀ s, red m (Φ s Y') = 0}.ncard ≤ Nat.card (ResidueField O) ^ (m * Module.finrank O (⨅ s, LinearMap.ker (Φ s) : Submodule O (Matrix (Fin n) (Fin n) O)) + C) := by
  intro l _ O _ _ _ hO _ n S Φ
  obtain ⟨-, hfin, -⟩ := hO
  obtain ⟨C, hC⟩ := fixBd_abs Φ
  refine ⟨C, fun m => hC m (Mm O n m) (Ideal.Quotient.mkₐ O (maximalIdeal O ^ m)).toLinearMap.mapMatrix _ ?_ fun Y hY => hY⟩
  ext Z
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    rw [Matrix.matrix_eq_sum_single Z]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    have h1 : Z i j ∈ maximalIdeal O ^ m := Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (congrFun h i) j)
    have e : Matrix.single i j (Z i j) = Z i j • Matrix.single i j (1 : O) := by simp
    rw [e]
    exact Submodule.smul_mem_smul h1 Submodule.mem_top
  · intro h
    refine Submodule.smul_induction_on h (fun a ha Y _ => ?_) fun a b ha hb => by rw [map_add (f := _), ha, hb, add_zero]
    ext i j
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ ha)
end

section

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

section Abs

variable {K R M : Type} [Group K] [CommRing R] [Ring M] [Module R M] (ρ z : K → M) (χ : K → R)
  (h1 : ρ 1 = 1) (hm : ∀ g h, ρ (g * h) = ρ g * ρ h) (c1 : χ 1 = 1) (cm : ∀ g h, χ (g * h) = χ g * χ h)
  (hz : ∀ g h, z (g * h) = z g + χ g • (ρ g * z h * ρ g⁻¹))

include h1 c1 hz in
private theorem twisted_cocycle_apply_one : z 1 = 0 := by
  have := hz 1 1
  rw [mul_one, inv_one, h1, c1, one_mul, mul_one, one_smul] at this
  exact left_eq_add.1 this

private theorem tw_inv {N : Type} [Monoid N] (ρ : K → N) (h1 : ρ 1 = 1) (hm : ∀ g h, ρ (g * h) = ρ g * ρ h)
    {g : K} (hg : ρ g = 1) : ρ g⁻¹ = 1 := by
  have := hm g g⁻¹
  rw [mul_inv_cancel, h1, hg, one_mul] at this
  exact this.symm

include h1 hm hz in
private theorem tw_add {g : K} (hg : ρ g = 1) (hc : χ g = 1) (h : K) : z (g * h) = z g + z h := by
  rw [hz, tw_inv ρ h1 hm hg, hg, hc, one_mul, mul_one, one_smul]

include h1 hm c1 hz in
private theorem tw_pow {g : K} (hg : ρ g = 1) (hc : χ g = 1) (k : ℕ) : ρ (g ^ k) = 1 ∧ z (g ^ k) = k • z g := by
  induction k with
  | zero => rw [pow_zero, zero_smul]; exact ⟨h1, twisted_cocycle_apply_one ρ z χ h1 c1 hz⟩
  | succ k ih =>
    rw [pow_succ', hm, tw_add ρ z χ h1 hm hz hg hc, hg, ih.1, ih.2, one_mul, succ_nsmul']
    exact ⟨rfl, rfl⟩

include h1 hm c1 cm hz in
private theorem tw_U [TopologicalSpace K] (cρ : IsLocallyConstant ρ) (cχ : IsLocallyConstant χ)
    (cz : IsLocallyConstant z) :
    ∃ U : OpenNormalSubgroup K, ∀ g, g ∈ U ↔ ρ g = 1 ∧ χ g = 1 ∧ z g = 0 := by
  let S : Subgroup K :=
    { carrier := {g | ρ g = 1 ∧ χ g = 1 ∧ z g = 0}
      one_mem' := ⟨h1, c1, twisted_cocycle_apply_one ρ z χ h1 c1 hz⟩
      mul_mem' := fun {a b} ha hb => ⟨by rw [hm, ha.1, hb.1, one_mul], by rw [cm, ha.2.1, hb.2.1, one_mul],
        by rw [tw_add ρ z χ h1 hm hz ha.1 ha.2.1, ha.2.2, hb.2.2, add_zero]⟩
      inv_mem' := fun {a} ha => ⟨tw_inv ρ h1 hm ha.1, tw_inv χ c1 cm ha.2.1, by
        have := tw_add ρ z χ h1 hm hz ha.1 ha.2.1 a⁻¹
        rw [mul_inv_cancel, twisted_cocycle_apply_one ρ z χ h1 c1 hz, ha.2.2, zero_add] at this
        exact this.symm⟩ }
  have hN : S.Normal := ⟨fun u hu g => ⟨by
      rw [hm, hm, hu.1, mul_one, ← hm, mul_inv_cancel, h1], by
      rw [cm, cm, hu.2.1, mul_one, ← cm, mul_inv_cancel, c1], by
      rw [mul_assoc, hz, tw_add ρ z χ h1 hm hz hu.1 hu.2.1, hu.2.2, zero_add, ← hz, mul_inv_cancel,
        twisted_cocycle_apply_one ρ z χ h1 c1 hz]⟩⟩
  have hO : IsOpen (S : Set K) := (cρ {1}).inter ((cχ {1}).inter (cz {0}))
  exact ⟨⟨⟨S, hO⟩, hN⟩, fun g => Iff.rfl⟩

end Abs

private theorem tw_lc {Γ R : Type} [TopologicalSpace Γ] {n : ℕ} (f : Γ → Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, IsLocallyConstant fun g => f g i j) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g0
  have : ∀ᶠ g in nhds g0, ∀ i j, f g i j = f g0 i j :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (h i j).eventually_eq g0
  filter_upwards [this] with g hg
  exact Matrix.ext hg

private theorem pow_mem_of_PL (l : ℕ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (H : Subgroup Γ) (V : Set Γ) (hV : IsOpen V) (hle : (PL l H : Set Γ) ⊆ V) : ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ V := by
  let ι := {U : OpenNormalSubgroup Γ // ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U}
  haveI : Nonempty ι := ⟨⟨⟨⊤, Subgroup.normal_top⟩, fun h _ => ⟨0, trivial⟩⟩⟩
  have hd : Directed (· ⊇ ·) fun U : ι => (U.1 : Set Γ) := by
    intro U U'
    refine ⟨⟨U.1 ⊓ U'.1, fun h hh => ?_⟩, fun a ha => ha.1, fun a ha => ha.2⟩
    obtain ⟨e, he⟩ := U.2 h hh
    obtain ⟨e', he'⟩ := U'.2 h hh
    refine ⟨e + e', ?_, ?_⟩
    · rw [pow_add, pow_mul]
      exact U.1.toSubgroup.pow_mem he _
    · rw [pow_add, mul_comm, pow_mul]
      exact U'.1.toSubgroup.pow_mem he' _
  have hs : Vᶜ ∩ ⋂ U : ι, (U.1 : Set Γ) = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun a ha => ha.1 (hle ?_)
    have := Set.mem_iInter.1 ha.2
    simp only [PL, SetLike.mem_coe, Subgroup.mem_iInf]
    exact fun U hU => this ⟨U, hU⟩
  obtain ⟨U, hU⟩ := hV.isClosed_compl.isCompact.elim_directed_family_closed (fun U : ι => (U.1 : Set Γ))
    (fun U => U.1.toOpenSubgroup.isClosed) (Set.disjoint_iff_inter_eq_empty.mpr hs) hd
  intro h hh
  obtain ⟨e, he⟩ := U.2 h hh
  refine ⟨e, ?_⟩
  by_contra hn
  exact Set.disjoint_left.1 hU hn he

private theorem lc_padic {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (f : ℤ_[l] →+* R) (m : ℕ)
    (hl : (l : R) ^ m = 0) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y0
  have hp : (0 : ℝ) < (l : ℝ) ^ (-m : ℤ) := zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds y0 hp] with y hy
  rw [Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton] at hy
  obtain ⟨c, hc⟩ := hy
  rw [← sub_eq_zero, ← map_sub, hc, map_mul, map_pow, map_natCast, hl, zero_mul]

private theorem pow_one_padic {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (f : ℤ_[l] →+* R) (m : ℕ)
    (hl : (l : R) ^ m = 0) (a : ℤ_[l]) (ha : PadicInt.toZMod a = 1) : f (a ^ l ^ m) = 1 := by
  have : a - 1 ∈ RingHom.ker (PadicInt.toZMod (p := l)) := by
    rw [RingHom.mem_ker, RingHom.map_sub, ha, map_one, sub_self]
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at this
  obtain ⟨c, hc⟩ := dvd_sub_pow_of_dvd_sub this m
  rw [one_pow] at hc
  rw [eq_add_of_sub_eq hc, map_add (f := _), map_mul, map_pow, map_natCast, pow_succ, hl]
  simp

private theorem rho_pow (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (O : Type) [CommRing O]
    [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m : ℕ)
    (hPL : ∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1)
    (hc : IsLocallyConstant fun g : G0.G₀ => red m (mat y.ρ g)) (g : G0.G₀)
    (hg : (g : G0.Γ) ∈ T.H) : ∃ e : ℕ, red m (mat y.ρ (g ^ l ^ e)) = 1 := by
  obtain ⟨e, g', h1, h2⟩ := pow_mem_of_PL l T.H.toSubgroup _
    (G0.η_open.isOpenMap_subtype_val _ (hc.isOpen_fiber 1)) (fun a ha => by
    have hη : a ∈ G0.η.ker := by
      have ha' := ha
      simp only [PL, SetLike.mem_coe, Subgroup.mem_iInf] at ha'
      exact ha' ⟨⟨G0.η.ker, G0.η_open⟩, MonoidHom.normal_ker _⟩ fun h hh =>
        ⟨0, by rw [pow_zero, pow_one]; exact T.H_η h hh⟩
    refine ⟨⟨a, hη⟩, ?_, rfl⟩
    show red m (mat y.ρ _) = 1
    simp [red, mat, hPL ⟨a, hη⟩ ha]) g hg
  have h3 : g' = g ^ l ^ e := Subtype.ext h2
  subst h3
  exact ⟨e, h1⟩

theorem UpperTheory.V.Th.plKill :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m : ℕ) (G : Glob l L) (h : G.Hom G0), (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1) → ∀ z : G.G₀ → Mm O n m, IsLocallyConstant z → (∀ g g', z (g * g') = z g + epsm O G m g • (y.ρm h m g * z g' * y.ρm h m g⁻¹)) → ∀ g : G.G₀, (g : G.Γ) ∈ PL l (T.H.toSubgroup.comap h.p) → z g = 0 ∧ y.ρm h m g = 1 ∧ epsm O G m g = 1 := by
  intro l _ L G0 T O _ _ _ _ _ n y m G h hPL z cz hz g hg
  obtain ⟨-, -, hk, -⟩ := (omFacts l O).2 m
  have hl : (l : Om O m) ^ m = 0 := by
    have := hk 1
    rwa [nsmul_eq_mul, mul_one, Nat.cast_pow] at this
  have hp : Continuous fun g : G.G₀ => h.p₀ g :=
    Continuous.subtype_mk (h.cont.comp continuous_subtype_val) _
  have h0 : IsLocallyConstant fun g : G0.G₀ => red m (mat y.ρ g) := tw_lc _ fun i j => y.cont i j m
  have c1 : IsLocallyConstant fun g : G.G₀ => y.ρm h m g := h0.comp_continuous hp
  let f : ℤ_[l] →+* Om O m := (algebraMap O (Om O m)).comp (algebraMap ℤ_[l] O)
  have c2 : IsLocallyConstant fun g : G.G₀ => epsm O G m g :=
    (lc_padic f m hl).comp_continuous (Units.continuous_val.comp (G.ε_cont.comp continuous_subtype_val))
  have r1 : y.ρm h m 1 = 1 := by simp [Pt.ρm, red, mat]
  have r2 : ∀ a b, y.ρm h m (a * b) = y.ρm h m a * y.ρm h m b := fun a b => by
    simp [Pt.ρm, red, mat, Matrix.map_mul]
  have e1 : epsm O G m ((1 : G.G₀) : G.Γ) = 1 := by simp [epsm]
  have em : ∀ a b : G.G₀, epsm O G m ((a * b : G.G₀) : G.Γ) = epsm O G m a * epsm O G m b := by
    intro a b
    simp [epsm]
  obtain ⟨U, hU⟩ := tw_U (K := G.G₀) (fun g => y.ρm h m g) z (fun g => epsm O G m g) r1 r2 e1 em hz c1 c2 cz
  haveI := T.H.isNormal'
  have hsub := pl_sub l G.Γ (T.H.toSubgroup.comap h.p) G.η.ker G.η_open
    (fun a ha => by rw [MonoidHom.mem_ker, ← h.η]; exact T.H_η _ ha) U fun a ha => by
    obtain ⟨e, he⟩ := rho_pow l L G0 T O n y m hPL h0 (h.p₀ a) ha
    have he' : y.ρm h m (a ^ l ^ e) = 1 := by rw [Pt.ρm, map_pow]; exact he
    have hε : ∀ b : G.G₀, h.p b ∈ T.H → epsm O G m ((b ^ l ^ m : G.G₀) : G.Γ) = 1 := fun b hb => by
      have := pow_one_padic f m hl _ (T.H_ε _ hb)
      rw [h.ε] at this
      rw [← this]
      simp [epsm, f]
    have hρp : ∀ (b : G.G₀) (k : ℕ), y.ρm h m b = 1 → y.ρm h m (b ^ k) = 1 := fun b k hb => by
      induction k with
      | zero => rw [pow_zero]; exact r1
      | succ k ih => rw [pow_succ, r2, ih, hb, one_mul]
    have hH : ∀ k : ℕ, h.p ((a ^ k : G.G₀) : G.Γ) ∈ T.H := fun k => (T.H.toSubgroup.comap h.p).pow_mem ha k
    have := tw_pow (K := G.G₀) (fun g => y.ρm h m g) z (fun g => epsm O G m g) r1 r2 e1 hz
      (hρp _ (l ^ m) he') (hε _ (hH _)) (l ^ m)
    refine ⟨e + m + m, (hU _).2 ⟨?_, ?_, ?_⟩⟩
    · rw [pow_add, pow_add, pow_mul, pow_mul]
      exact this.1
    · rw [pow_add, pow_mul]
      exact hε _ (hH _)
    · rw [pow_add, pow_add, pow_mul, pow_mul]
      exact this.2.trans (Matrix.ext fun i j => hk _)
  obtain ⟨u1, u2, u3⟩ := (hU g).1 (hsub g hg)
  exact ⟨u3, u1, u2⟩
end
