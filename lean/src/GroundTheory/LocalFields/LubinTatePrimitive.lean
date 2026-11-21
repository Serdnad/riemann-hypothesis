import Mathlib
import GroundTheory.LocalFields.LubinTatePoints
import GroundTheory.LocalFields.LubinTateTorsion
import GroundTheory.LocalFields.Eisenstein
import GroundTheory.LocalFields.UnitsBasic

/-! # Primitive points of the Lubin–Tate tower -/

section LubinTateTower

noncomputable section

open IntermediateField

namespace GroundTheory.LocalField

open ValuativeRel Polynomial

namespace FormalGroup

section Tower

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
variable {π : 𝒪[K]} {f g : PowerSeries 𝒪[K]}

variable (Ω) in

def lubinTateField (hπ : Irreducible π) (hf : IsLubinTateSeries π f) (n : ℕ) :
    IntermediateField K Ω :=
  adjoin K (IdealPoint.val ''
    (lubinTateTorsion Ω hf n : Set (IdealPoint Ω (lubinTateFormalGroup hπ hf))))

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] in

theorem finiteDimensional_adjoin_simple (x : Ω) : FiniteDimensional K K⟮x⟯ :=
  adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic x).isIntegral

theorem val_mem_lubinTateField (hπ : Irreducible π) (hf : IsLubinTateSeries π f) {n : ℕ}
    {x : IdealPoint Ω (lubinTateFormalGroup hπ hf)} (hx : x ∈ lubinTateTorsion Ω hf n) :
    x.val ∈ lubinTateField Ω hπ hf n :=
  subset_adjoin K _ (Set.mem_image_of_mem IdealPoint.val (SetLike.mem_coe.mpr hx))

theorem psEval_mem_adjoin_simple (φ : PowerSeries 𝒪[K]) {x : Ω} (hx : valuation Ω x < 1) :
    psEval φ (fun _ => x) ∈ K⟮x⟯ :=
  have := finiteDimensional_adjoin_simple (K := K) x
  psEval_mem φ K⟮x⟯ (fun _ => mem_adjoin_simple_self K x) fun _ => hx

variable (hπ : Irreducible π)

section SepClosed

variable [IsSepClosed Ω]

theorem exists_lubinTateField_eq_adjoin (hf : IsLubinTateSeries π f) (n : ℕ) :
    ∃ l ∈ lubinTateTorsion Ω (hπ := hπ) hf n,
      (∀ a : 𝒪[K], a • l = 0 ↔ a ∈ Ideal.span {π ^ n}) ∧
      (∀ m ∈ lubinTateTorsion Ω (hπ := hπ) hf n, ∃ a : 𝒪[K], a • l = m) ∧
      lubinTateField Ω hπ hf n = K⟮l.val⟯ := by
  obtain ⟨l, hl, hann, hgen⟩ := exists_generator_lubinTateTorsion (Ω := Ω) (hπ := hπ) hf n
  refine ⟨l, hl, hann, hgen, le_antisymm ?_ ?_⟩
  · rw [lubinTateField, adjoin_le_iff]
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨a, rfl⟩ := hgen m hm
    rw [lubinTate_smul_val]
    exact psEval_mem_adjoin_simple _ l.valuation_lt_one
  · rw [adjoin_simple_le_iff]
    exact subset_adjoin K _ (Set.mem_image_of_mem IdealPoint.val (SetLike.mem_coe.mpr hl))

instance finiteDimensional_lubinTateField (hf : IsLubinTateSeries π f) (n : ℕ) :
    FiniteDimensional K (lubinTateField Ω hπ hf n) := by
  obtain ⟨l, -, -, -, h⟩ := exists_lubinTateField_eq_adjoin (Ω := Ω) hπ hf n
  rw [h]
  exact finiteDimensional_adjoin_simple _

theorem lubinTateField_eq (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries π g) (n : ℕ) :
    lubinTateField Ω hπ hf n = lubinTateField Ω hπ hg n := by
  have key : ∀ {f g : PowerSeries 𝒪[K]} (hf : IsLubinTateSeries π f)
      (hg : IsLubinTateSeries π g), lubinTateField Ω hπ hf n ≤ lubinTateField Ω hπ hg n := by
    intro f g hf hg
    rw [lubinTateField, adjoin_le_iff]
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨m', rfl⟩ := (lubinTatePointEquiv hf hg).surjective m
    have hm' : m' ∈ lubinTateTorsion Ω hg n :=
      (lubinTatePointEquiv_mem_torsion_iff hf hg n m').mp hm
    rw [SetLike.mem_coe, lubinTatePointEquiv_val]
    exact psEval_mem _ _ (fun _ => val_mem_lubinTateField hπ hg hm')
      fun _ => m'.valuation_lt_one
  exact le_antisymm (key hf hg) (key hg hf)

omit [IsSepClosed Ω] in

theorem image_val_lubinTateTorsion_ltPoly (n : ℕ) :
    IdealPoint.val '' (lubinTateTorsion Ω (isLubinTateSeries_ltPoly π) n :
      Set (IdealPoint Ω (lubinTateFormalGroup hπ (isLubinTateSeries_ltPoly π)))) =
      ((ltPolyIter π n).map (algebraMap 𝒪[K] K)).rootSet Ω := by
  have hp0 : (ltPolyIter π n).map (algebraMap 𝒪[K] K) ≠ 0 :=
    ((ltPolyIter_monic π n).1.map _).ne_zero
  ext z
  rw [mem_rootSet']
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Polynomial.map_ne_zero hp0, (mem_lubinTateTorsion_ltPoly_iff n x).mp hx⟩
  · rintro ⟨-, hz⟩
    exact ⟨IdealPoint.mk z (valuation_lt_one_of_aeval_ltPolyIter_eq_zero hπ n hz),
      (mem_lubinTateTorsion_ltPoly_iff n _).mpr hz, rfl⟩

instance isGalois_lubinTateField (hf : IsLubinTateSeries π f) (n : ℕ) :
    IsGalois K (lubinTateField Ω hπ hf n) := by
  rw [lubinTateField_eq hπ hf (isLubinTateSeries_ltPoly π), lubinTateField,
    image_val_lubinTateTorsion_ltPoly hπ n]
  have hsep := separable_ltPolyIter hπ n
  have := adjoin_rootSet_isSplittingField (IsSepClosed.splits_codomain _ hsep)
    (L := Ω) (K := K)
  exact IsGalois.of_separable_splitting_field hsep

theorem exists_lubinTateField_eq_adjoin_eisenstein (hf : IsLubinTateSeries π f) (n : ℕ) :
    ∃ α : Ω, lubinTateField Ω hπ hf (n + 1) = K⟮α⟯ ∧
      aeval α ((ltEisenstein π n).map (algebraMap 𝒪[K] K)) = 0 := by
  obtain ⟨l, hl, hann, -, hE⟩ :=
    exists_lubinTateField_eq_adjoin (Ω := Ω) hπ (isLubinTateSeries_ltPoly π) (n + 1)
  refine ⟨l.val, (lubinTateField_eq hπ hf (isLubinTateSeries_ltPoly π) _).trans hE, ?_⟩
  refine aeval_ltEisenstein_eq_zero ((mem_lubinTateTorsion_ltPoly_iff _ l).mp hl) fun h => ?_
  have h1 : π ^ n • l = 0 := (mem_lubinTateTorsion _ _ _).mp
    ((mem_lubinTateTorsion_ltPoly_iff n l).mpr h)
  rw [hann, Ideal.mem_span_singleton, pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit] at h1
  omega

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
  [IsSepClosed Ω] in

theorem adjoin_simple_eq_top_of_eq {E : IntermediateField K Ω} {a : Ω} (hE : E = K⟮a⟯) :
    K⟮(⟨a, hE ▸ mem_adjoin_simple_self K a⟩ : E)⟯ = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  have hy : (y : Ω) ∈ (K⟮(⟨a, hE ▸ mem_adjoin_simple_self K a⟩ : E)⟯).map E.val := by
    rw [adjoin_map, Set.image_singleton]
    change (y : Ω) ∈ K⟮a⟯
    rw [← hE]
    exact y.2
  rw [IntermediateField.mem_map] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  rwa [show z = y from Subtype.ext hzy] at hz

theorem finrank_and_ramificationIndex_lubinTateField_succ (hf : IsLubinTateSeries π f) (n : ℕ) :
    Module.finrank K (lubinTateField Ω hπ hf (n + 1)) = (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n ∧
      ramificationIndex K (lubinTateField Ω hπ hf (n + 1)) =
        (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n := by
  obtain ⟨a, hE, ha⟩ := exists_lubinTateField_eq_adjoin_eisenstein (Ω := Ω) hπ hf n
  set E := lubinTateField Ω hπ hf (n + 1)
  set α : E := ⟨a, hE ▸ mem_adjoin_simple_self K a⟩
  have hgen : K⟮α⟯ = ⊤ := adjoin_simple_eq_top_of_eq hE
  have hα : aeval α (ltEisenstein π n) = 0 := by
    refine Subtype.val_injective ?_
    have h2 := aeval_algHom_apply (E.val.restrictScalars 𝒪[K]) α (ltEisenstein π n)
    simp only [AlgHom.coe_restrictScalars', coe_val] at h2
    rw [ZeroMemClass.coe_zero, ← h2]
    change aeval a (ltEisenstein π n) = 0
    rwa [← aeval_map_algebraMap K]
  have hq := one_lt_card_residueField' K
  have hn : 0 < (ltEisenstein π n).natDegree := by
    rw [(ltEisenstein_monic π n).2]
    exact Nat.mul_pos (by omega) (pow_pos (by omega) n)
  have hEis := isEisensteinAt_ltEisenstein hπ n
  rw [← (ltEisenstein_monic π n).2]
  exact ⟨finrank_eq_natDegree_of_isEisensteinAt hEis hn hα hgen,
    ramificationIndex_eq_natDegree_of_isEisensteinAt hEis hn hα hgen⟩

end SepClosed

end Tower

section Units

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {π : 𝒪[K]}

theorem card_units_quotient_span_pow_succ (hπ : Irreducible π) (n : ℕ) :
    Nat.card (𝒪[K] ⧸ Ideal.span {π ^ (n + 1)})ˣ = (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n := by
  set I := Ideal.span {π ^ (n + 1)}
  have hI : I = 𝓂[K] ^ (n + 1) := by rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hIm : I ≤ 𝓂[K] := by
    rw [hI]
    exact Ideal.pow_le_self (Nat.succ_ne_zero n)
  let ψ : 𝒪[K]ˣ →* (𝒪[K] ⧸ I)ˣ := Units.map (Ideal.Quotient.mk I : 𝒪[K] →* 𝒪[K] ⧸ I)
  have hsurj : Function.Surjective ψ := by
    intro w
    obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective (w : 𝒪[K] ⧸ I)
    obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective (↑w⁻¹ : 𝒪[K] ⧸ I)
    have huv : u * v - 1 ∈ I := by
      rw [← Ideal.Quotient.eq, map_mul, hu, hv, map_one, Units.mul_inv]
    have hunit : IsUnit (u * v) := by
      by_contra h
      have h1 : u * v ∈ 𝓂[K] := (IsLocalRing.mem_maximalIdeal _).mpr h
      have h2 : (1 : 𝒪[K]) ∈ 𝓂[K] := by
        have := Ideal.sub_mem _ h1 (hIm huv)
        rwa [sub_sub_cancel] at this
      exact (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]).ne_top ((Ideal.eq_top_iff_one _).mpr h2)
    refine ⟨(isUnit_of_mul_isUnit_left hunit).unit, Units.ext ?_⟩
    change Ideal.Quotient.mk I u = _
    exact hu
  have hker : ψ.ker = unitFiltration K (n + 1) := by
    ext u
    rw [MonoidHom.mem_ker, mem_unitFiltration, ← hI, ← Ideal.Quotient.eq, Units.ext_iff]
    rfl
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).toEquiv, hker,
    ← Subgroup.index, index_unitFiltration K (by omega), Nat.add_sub_cancel]

end Units

section Galois

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
variable {π : 𝒪[K]} {hπ : Irreducible π} {f : PowerSeries 𝒪[K]}

def galPoint {F : _root_.FormalGroup 𝒪[K]} {E : IntermediateField K Ω} [FiniteDimensional K E]
    (σ : E ≃ₐ[K] E) (x : IdealPoint Ω F) (hx : x.val ∈ E) : IdealPoint Ω F :=
  IdealPoint.mk ((σ ⟨x.val, hx⟩ : E) : Ω) (by
    rw [valuation_coe_lt_one_iff, valuation_algEquiv_apply_of_isAlgebraic,
      ← valuation_coe_lt_one_iff]
    exact x.valuation_lt_one)

omit [TopologicalSpace Ω] [IsValuativeTopology Ω] in

theorem galPoint_val {F : _root_.FormalGroup 𝒪[K]} {E : IntermediateField K Ω}
    [FiniteDimensional K E] (σ : E ≃ₐ[K] E) (x : IdealPoint Ω F) (hx : x.val ∈ E) :
    (galPoint σ x hx).val = ((σ ⟨x.val, hx⟩ : E) : Ω) := rfl

theorem galPoint_smul {E : IntermediateField K Ω} [FiniteDimensional K E] (hf : IsLubinTateSeries π f)
    (σ : E ≃ₐ[K] E) (a : 𝒪[K]) (x : IdealPoint Ω (lubinTateFormalGroup hπ hf)) (hx : x.val ∈ E)
    (hax : (a • x).val ∈ E) :
    galPoint σ (a • x) hax = a • galPoint σ x hx := by
  set xE : E := ⟨x.val, hx⟩
  set φ := (lubinTateHom hπ hf hf a).toPowerSeries
  have hxE : ∀ _ : Unit, valuation Ω ((xE : E) : Ω) < 1 := fun _ => x.valuation_lt_one
  have h1 : (⟨(a • x).val, hax⟩ : E) = psEval φ fun _ => xE :=
    Subtype.ext (psEval_coe E φ (fun _ => xE) hxE)
  have hσ : ∀ _ : Unit, valuation Ω (((σ xE : E)) : Ω) < 1 := fun _ =>
    (galPoint σ x hx).valuation_lt_one
  apply IdealPoint.ext
  rw [galPoint_val, h1, algEquiv_psEval σ φ (fun _ => xE) fun _ => by
      rw [← valuation_coe_lt_one_iff]; exact x.valuation_lt_one,
    lubinTate_smul_val]
  exact (psEval_coe E φ (fun _ => σ xE) hσ).symm

variable [IsSepClosed Ω]

theorem card_units_quotient_eq_finrank (hf : IsLubinTateSeries π f) (n : ℕ) :
    Nat.card (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ = Module.finrank K (lubinTateField Ω hπ hf n) := by
  cases n with
  | zero =>
    obtain ⟨l, hl, -, -, hE⟩ := exists_lubinTateField_eq_adjoin (Ω := Ω) hπ hf 0
    rw [mem_lubinTateTorsion, pow_zero, one_smul] at hl
    rw [hE, hl, IdealPoint.val_zero, adjoin_zero, IntermediateField.finrank_bot, pow_zero,
      Ideal.span_singleton_one]
    have : Subsingleton (𝒪[K] ⧸ (⊤ : Ideal 𝒪[K])) := Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Nat.card_unique
  | succ n =>
    rw [card_units_quotient_span_pow_succ hπ, (finrank_and_ramificationIndex_lubinTateField_succ
      hπ hf n).1]

theorem exists_galEquiv_lubinTateField (hf : IsLubinTateSeries π f) (n : ℕ) :
    ∃ χ : (lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n) ≃*
        (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ,
      ∀ (σ : lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n)
        (x : IdealPoint Ω (lubinTateFormalGroup hπ hf)) (hx : x ∈ lubinTateTorsion Ω hf n)
        (a : 𝒪[K]), Ideal.Quotient.mk _ a = (χ σ : 𝒪[K] ⧸ Ideal.span {π ^ n}) →
          ((σ ⟨x.val, val_mem_lubinTateField hπ hf hx⟩ : lubinTateField Ω hπ hf n) : Ω) =
            (a • x).val := by
  obtain ⟨l, hl, hann, hgen, hE⟩ := exists_lubinTateField_eq_adjoin (Ω := Ω) hπ hf n
  set E := lubinTateField Ω hπ hf n
  set Λ := lubinTateTorsion Ω (hπ := hπ) hf n
  set I := Ideal.span {π ^ n}
  have hmem : ∀ {x}, x ∈ Λ → x.val ∈ E := fun hx => val_mem_lubinTateField hπ hf hx
  have hgalΛ : ∀ (σ : E ≃ₐ[K] E) (x) (hx : x ∈ Λ), galPoint σ x (hmem hx) ∈ Λ := by
    intro σ x hx
    rw [mem_lubinTateTorsion, ← galPoint_smul hf σ _ x (hmem hx) (hmem (Λ.smul_mem _ hx))]
    apply IdealPoint.ext
    rw [galPoint_val]
    have h0 : (⟨(π ^ n • x).val, hmem (Λ.smul_mem _ hx)⟩ : E) = 0 :=
      Subtype.ext (show (π ^ n • x).val = ((0 : E) : Ω) by
        rw [(mem_lubinTateTorsion _ _ _).mp hx]; rfl)
    rw [h0, map_zero]
    rfl
  choose c hc using fun σ : E ≃ₐ[K] E => hgen _ (hgalΛ σ l hl)
  have hmk : ∀ a b : 𝒪[K], a • l = b • l ↔ Ideal.Quotient.mk I a = Ideal.Quotient.mk I b := by
    intro a b
    rw [Ideal.Quotient.eq, ← hann, sub_smul, sub_eq_zero]
  have hgal : ∀ (σ : E ≃ₐ[K] E) (x) (hx : x ∈ Λ), galPoint σ x (hmem hx) = c σ • x := by
    intro σ x hx
    obtain ⟨b, rfl⟩ := hgen x hx
    rw [galPoint_smul hf σ b l (hmem hl), ← hc, smul_comm]
  have hmul : ∀ σ τ : E ≃ₐ[K] E, c (σ * τ) • l = (c σ * c τ) • l := by
    intro σ τ
    rw [hc, mul_smul, hc]
    have h1 : galPoint (σ * τ) l (hmem hl) = galPoint σ (galPoint τ l (hmem hl))
        (hmem (hgalΛ τ l hl)) := rfl
    rw [h1, hgal σ _ (hgalΛ τ l hl), ← hc]
  have hone : c 1 • l = (1 : 𝒪[K]) • l := by
    rw [hc, one_smul]
    rfl
  let χ₀ : (E ≃ₐ[K] E) →* 𝒪[K] ⧸ I :=
    { toFun := fun σ => Ideal.Quotient.mk I (c σ)
      map_one' := by rw [(hmk _ _).mp hone, map_one]
      map_mul' := fun σ τ => by rw [(hmk _ _).mp (hmul σ τ), map_mul] }
  let χ := χ₀.toHomUnits
  have hχ : ∀ σ, (χ σ : 𝒪[K] ⧸ I) = Ideal.Quotient.mk I (c σ) := fun σ => rfl
  have hinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    have h1 : c σ • l = (1 : 𝒪[K]) • l := by
      rw [hmk, map_one, ← hχ, hσ, Units.val_one]
    rw [one_smul, hc] at h1
    have hfix : σ ⟨l.val, hmem hl⟩ = ⟨l.val, hmem hl⟩ := Subtype.ext (congrArg IdealPoint.val h1)
    have htop : Algebra.adjoin K {(⟨l.val, hmem hl⟩ : E)} = ⊤ := by
      rw [← adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic _),
        adjoin_simple_eq_top_of_eq hE, top_toSubalgebra]
    have h2 := AlgHom.ext_of_adjoin_eq_top htop (φ₁ := (σ : E →ₐ[K] E)) (φ₂ := AlgHom.id K E)
      (by rintro _ rfl; exact hfix)
    exact AlgEquiv.ext fun y => congrArg (fun φ : E →ₐ[K] E => φ y) h2
  have hcard : Nat.card (E ≃ₐ[K] E) = Nat.card (𝒪[K] ⧸ I)ˣ := by
    rw [IsGalois.card_aut_eq_finrank, card_units_quotient_eq_finrank (Ω := Ω) hf n]
  have hfin : Finite (𝒪[K] ⧸ I)ˣ := Nat.finite_of_card_ne_zero (by
    rw [← hcard, IsGalois.card_aut_eq_finrank]
    exact Module.finrank_pos.ne')
  refine ⟨MulEquiv.ofBijective χ (hinj.bijective_of_nat_card_le hcard.ge), ?_⟩
  intro σ x hx a ha
  rw [MulEquiv.ofBijective_apply, hχ, ← hmk] at ha
  obtain ⟨b, rfl⟩ := hgen x hx
  rw [← galPoint_val σ (b • l) (hmem hx), hgal σ _ hx, smul_comm, ← ha, smul_comm]

variable (hπ) in

def lubinTateGalEquiv (hf : IsLubinTateSeries π f) (n : ℕ) :
    (lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n) ≃* (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ :=
  Classical.choose (exists_galEquiv_lubinTateField (Ω := Ω) (hπ := hπ) hf n)

theorem lubinTateGalEquiv_spec (hf : IsLubinTateSeries π f) (n : ℕ)
    (σ : lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n)
    (x : IdealPoint Ω (lubinTateFormalGroup hπ hf)) (hx : x ∈ lubinTateTorsion Ω hf n) (a : 𝒪[K])
    (ha : Ideal.Quotient.mk _ a = (lubinTateGalEquiv hπ hf n σ : 𝒪[K] ⧸ Ideal.span {π ^ n})) :
    ((σ ⟨x.val, val_mem_lubinTateField hπ hf hx⟩ : lubinTateField Ω hπ hf n) : Ω) = (a • x).val :=
  Classical.choose_spec (exists_galEquiv_lubinTateField (Ω := Ω) (hπ := hπ) hf n) σ x hx a ha

end Galois

section Main

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsSepClosed Ω]
variable {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]}

theorem finrank_lubinTateField (hf : IsLubinTateSeries π f) {n : ℕ} (hn : 0 < n) :
    Module.finrank K (lubinTateField Ω hπ hf n) = (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  exact (finrank_and_ramificationIndex_lubinTateField_succ hπ hf m).1

theorem ramificationIndex_lubinTateField (hf : IsLubinTateSeries π f) {n : ℕ} (hn : 0 < n) :
    ramificationIndex K (lubinTateField Ω hπ hf n) =
      Module.finrank K (lubinTateField Ω hπ hf n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  rw [(finrank_and_ramificationIndex_lubinTateField_succ hπ hf m).1,
    (finrank_and_ramificationIndex_lubinTateField_succ hπ hf m).2]

theorem residueDegree_lubinTateField (hf : IsLubinTateSeries π f) {n : ℕ} (hn : 0 < n) :
    residueDegree K (lubinTateField Ω hπ hf n) = 1 :=
  residueDegree_eq_one_of_ramificationIndex_eq_finrank K _
    (ramificationIndex_lubinTateField hπ hf hn)

theorem exists_isEisensteinAt_lubinTateField (hf : IsLubinTateSeries π f) {n : ℕ} (hn : 0 < n) :
    ∃ (p : 𝒪[K][X]) (α : Ω), p.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K]) ∧
      p.natDegree = (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ (n - 1) ∧
      aeval α (p.map (algebraMap 𝒪[K] K)) = 0 ∧ lubinTateField Ω hπ hf n = K⟮α⟯ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  obtain ⟨α, hE, hα⟩ := exists_lubinTateField_eq_adjoin_eisenstein (Ω := Ω) hπ hf m
  exact ⟨ltEisenstein π m, α, isEisensteinAt_ltEisenstein hπ m, (ltEisenstein_monic π m).2, hα,
    hE⟩

theorem coeff_zero_ltEisenstein (π : 𝒪[K]) (n : ℕ) : (ltEisenstein π n).coeff 0 = π := by
  have hq := one_lt_card_residueField' K
  rw [ltEisenstein, coeff_add, coeff_C_zero, coeff_zero_eq_eval_zero, eval_pow,
    ← coeff_zero_eq_eval_zero, coeff_zero_ltPolyIter, zero_pow (by omega), add_zero]

theorem exists_norm_eq_uniformizer (hf : IsLubinTateSeries π f) {n : ℕ} (hn : 0 < n) :
    ∃ x : lubinTateField Ω hπ hf n, Algebra.norm K x = (π : K) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  have hfin := (finrank_and_ramificationIndex_lubinTateField_succ (Ω := Ω) hπ hf m).1
  obtain ⟨a, hE, ha⟩ := exists_lubinTateField_eq_adjoin_eisenstein (Ω := Ω) hπ hf m
  rw [hE] at hfin ⊢
  set p := (ltEisenstein π m).map (algebraMap 𝒪[K] K)
  have hpm : p.Monic := (ltEisenstein_monic π m).1.map _
  have hint : IsIntegral K a := (Algebra.IsAlgebraic.isAlgebraic a).isIntegral
  have hmin : minpoly K a = p := by
    refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hpm
      (minpoly.dvd K a ha) ?_).symm
    rw [← adjoin.finrank hint, hfin, natDegree_map_eq_of_injective
      (FaithfulSMul.algebraMap_injective 𝒪[K] K), (ltEisenstein_monic π m).2]
  set pb := adjoin.powerBasis hint
  have hdim : pb.dim = Module.finrank K K⟮a⟯ := by
    rw [adjoin.powerBasis_dim, adjoin.finrank hint]
  have hnorm : Algebra.norm K pb.gen = (-1) ^ Module.finrank K K⟮a⟯ * (π : K) := by
    rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, hdim, adjoin.powerBasis_gen,
      minpoly_gen, hmin, coeff_map, coeff_zero_ltEisenstein]
    rfl
  refine ⟨-pb.gen, ?_⟩
  have h1 : (-1 : K⟮a⟯) = algebraMap K K⟮a⟯ (-1) := by simp
  rw [neg_eq_neg_one_mul, h1, map_mul, Algebra.norm_algebraMap,
    hnorm, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

end Main

section SeparableClosure

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]} (hf : IsLubinTateSeries π f)

example {n : ℕ} (hn : 0 < n) :
    Module.finrank K (lubinTateField (SeparableClosure K) hπ hf n) =
      (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ (n - 1) :=
  finrank_lubinTateField hπ hf hn

example (n : ℕ) : IsGalois K (lubinTateField (SeparableClosure K) hπ hf n) := inferInstance

example (n : ℕ) :
    (lubinTateField (SeparableClosure K) hπ hf n ≃ₐ[K] lubinTateField (SeparableClosure K) hπ hf n)
      ≃* (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ :=
  lubinTateGalEquiv hπ hf n

end SeparableClosure

end FormalGroup

end GroundTheory.LocalField

end

end LubinTateTower

section LubinTatePrimitive

noncomputable section

open IntermediateField

namespace GroundTheory.LocalField

open ValuativeRel Polynomial Topology

namespace FormalGroup

section Associated

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem associated_psEval {φ : PowerSeries 𝒪[K]} (h0 : PowerSeries.constantCoeff φ = 0)
    (h1 : IsUnit (PowerSeries.coeff 1 φ)) (a : 𝒪[L]) (ha : a ∈ 𝓂[L]) :
    Associated a ⟨psEval φ (fun _ => (a : L)), psEval_mem_integer φ (fun _ => a) fun _ => ha⟩ := by
  let _ : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  have _ : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup
  let _ : UniformSpace 𝒪[K] := ⊥
  have _ : DiscreteUniformity 𝒪[K] := ⟨rfl⟩
  have hφc : Continuous[(⊥ : UniformSpace 𝒪[K]).toTopologicalSpace, _]
      (algebraMap 𝒪[K] 𝒪[L]) := by
    rw [UniformSpace.toTopologicalSpace_bot]
    exact continuous_bot
  have hev := hasEval_of_mem_maximalIdeal (a := fun _ : Unit => a) fun _ => ha
  set ε := MvPowerSeries.eval₂Hom hφc hev
  have hval : (⟨psEval φ (fun _ => (a : L)), psEval_mem_integer φ (fun _ => a) fun _ => ha⟩ : 𝒪[L])
      = ε φ := by
    apply Subtype.ext
    rw [MvPowerSeries.coe_eval₂Hom]
    exact psEval_eq_eval₂ φ (fun _ => a) fun _ => ha
  have hεX : ε PowerSeries.X = a := by
    rw [MvPowerSeries.coe_eval₂Hom]
    exact MvPowerSeries.eval₂_X _ _ _
  have hεC : ∀ c : 𝒪[K], ε (PowerSeries.C c) = algebraMap 𝒪[K] 𝒪[L] c := by
    intro c
    rw [MvPowerSeries.coe_eval₂Hom]
    exact MvPowerSeries.eval₂_C _ _ _
  obtain ⟨ψ, hψ⟩ := PowerSeries.X_dvd_iff.mpr h0
  set c := PowerSeries.constantCoeff ψ
  have hc : c = PowerSeries.coeff 1 φ := by
    rw [hψ, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  obtain ⟨χ, hχ⟩ := PowerSeries.X_dvd_iff.mpr
    (show PowerSeries.constantCoeff (ψ - PowerSeries.C c) = 0 by simp [c])
  have hψ' : ψ = PowerSeries.C c + PowerSeries.X * χ := by
    rw [← hχ]
    ring
  have hunit : IsUnit (ε ψ) := by
    rw [hψ', map_add, map_mul, hεX, hεC]
    by_contra hnu
    have hm : algebraMap 𝒪[K] 𝒪[L] c + a * ε χ ∈ 𝓂[L] := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hm' : algebraMap 𝒪[K] 𝒪[L] c ∈ 𝓂[L] := by
      have := Ideal.sub_mem _ hm (Ideal.mul_mem_right (ε χ) _ ha)
      rwa [add_sub_cancel_right] at this
    rw [hc] at hm'
    exact (IsLocalRing.mem_maximalIdeal _).mp hm' (h1.map _)
  rw [hval, hψ, map_mul, hεX]
  exact ⟨hunit.unit, rfl⟩

end Associated

section Torsion

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
variable {π : 𝒪[K]} (hπ : Irreducible π) {f g : PowerSeries 𝒪[K]}

theorem lubinTateTorsion_mono (hf : IsLubinTateSeries π f) {m n : ℕ} (h : m ≤ n) :
    lubinTateTorsion Ω (hπ := hπ) hf m ≤ lubinTateTorsion Ω (hπ := hπ) hf n :=
  Submodule.torsionBy_le_torsionBy_of_dvd _ _ (pow_dvd_pow π h)

theorem lubinTateField_mono (hf : IsLubinTateSeries π f) {m n : ℕ} (h : m ≤ n) :
    lubinTateField Ω hπ hf m ≤ lubinTateField Ω hπ hf n := by
  rw [lubinTateField, adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  exact val_mem_lubinTateField hπ hf (lubinTateTorsion_mono hπ hf h hx)

theorem lubinTateField_le_succ (hf : IsLubinTateSeries π f) (n : ℕ) :
    lubinTateField Ω hπ hf n ≤ lubinTateField Ω hπ hf (n + 1) :=
  lubinTateField_mono hπ hf n.le_succ

theorem lubinTatePointEquiv_primitive_iff (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries π g)
    (n : ℕ) (x : IdealPoint Ω (lubinTateFormalGroup hπ hg)) :
    (lubinTatePointEquiv hf hg x ∈ lubinTateTorsion Ω hf n ∧
        lubinTatePointEquiv hf hg x ∉ lubinTateTorsion Ω hf (n - 1)) ↔
      (x ∈ lubinTateTorsion Ω hg n ∧ x ∉ lubinTateTorsion Ω hg (n - 1)) := by
  rw [lubinTatePointEquiv_mem_torsion_iff, lubinTatePointEquiv_mem_torsion_iff]

theorem aeval_ltEisenstein_of_primitive {k : ℕ}
    {l : IdealPoint Ω (lubinTateFormalGroup hπ (isLubinTateSeries_ltPoly π))}
    (hl : l ∈ lubinTateTorsion Ω (isLubinTateSeries_ltPoly π) (k + 1))
    (hl' : l ∉ lubinTateTorsion Ω (isLubinTateSeries_ltPoly π) k) :
    aeval l.val ((ltEisenstein π k).map (algebraMap 𝒪[K] K)) = 0 :=
  aeval_ltEisenstein_eq_zero ((mem_lubinTateTorsion_ltPoly_iff _ l).mp hl)
    fun h => hl' ((mem_lubinTateTorsion_ltPoly_iff k l).mpr h)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace Ω]
  [IsValuativeTopology Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] in

theorem exists_integer_eq {E : IntermediateField K Ω} {x : Ω} (hxE : x ∈ E)
    (hx : valuation Ω x < 1) : ∃ y : 𝒪[E], ((y : E) : Ω) = x :=
  ⟨⟨⟨x, hxE⟩, ((valuation_coe_lt_one_iff E ⟨x, hxE⟩).mp hx).le⟩, rfl⟩

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω] [TopologicalSpace Ω]
  [IsValuativeTopology Ω] [ValuativeExtension K Ω] in

theorem norm_neg_eq_coeff_zero {E : IntermediateField K Ω} {a : Ω} (hE : E = K⟮a⟯) (ha : a ∈ E)
    {p : 𝒪[K][X]} (hpm : p.Monic) (hfin : Module.finrank K E = p.natDegree)
    (hp : aeval a (p.map (algebraMap 𝒪[K] K)) = 0) :
    Algebra.norm K (-(⟨a, ha⟩ : E)) = ((p.coeff 0 : 𝒪[K]) : K) := by
  subst hE
  have hint : IsIntegral K a := (Algebra.IsAlgebraic.isAlgebraic a).isIntegral
  have hqm : (p.map (algebraMap 𝒪[K] K)).Monic := hpm.map _
  have hmin : minpoly K a = p.map (algebraMap 𝒪[K] K) := by
    refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hqm
      (minpoly.dvd K a hp) ?_).symm
    rw [← adjoin.finrank hint, hfin, natDegree_map_eq_of_injective
      (FaithfulSMul.algebraMap_injective 𝒪[K] K)]
  set pb := adjoin.powerBasis hint
  have hgen : (⟨a, ha⟩ : K⟮a⟯) = pb.gen := by
    rw [adjoin.powerBasis_gen]
    rfl
  have hdim : pb.dim = Module.finrank K K⟮a⟯ := by
    rw [adjoin.powerBasis_dim, adjoin.finrank hint]
  have hnorm : Algebra.norm K pb.gen =
      (-1) ^ Module.finrank K K⟮a⟯ * ((p.coeff 0 : 𝒪[K]) : K) := by
    rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, hdim, adjoin.powerBasis_gen,
      minpoly_gen, hmin, coeff_map]
    rfl
  rw [hgen]
  have h1 : (-1 : K⟮a⟯) = algebraMap K K⟮a⟯ (-1) := by simp
  rw [neg_eq_neg_one_mul, h1, map_mul, Algebra.norm_algebraMap,
    hnorm, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

theorem irreducible_of_eq_adjoin_of_isEisensteinAt {E : IntermediateField K Ω} [FiniteDimensional K E]
    {a : Ω} (hE : E = K⟮a⟯) {p : 𝒪[K][X]} (hp : p.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K]))
    (hn : 0 < p.natDegree) (ha : aeval a (p.map (algebraMap 𝒪[K] K)) = 0) {x : 𝒪[E]}
    (hx : ((x : E) : Ω) = a) : Irreducible x := by
  have haE : a ∈ E := hx ▸ (x : E).2
  set α : E := ⟨a, haE⟩
  have hgen : K⟮α⟯ = ⊤ := adjoin_simple_eq_top_of_eq hE
  have hα : aeval α p = 0 := by
    refine Subtype.val_injective ?_
    have h2 := aeval_algHom_apply (E.val.restrictScalars 𝒪[K]) α p
    simp only [AlgHom.coe_restrictScalars', coe_val] at h2
    rw [ZeroMemClass.coe_zero, ← h2]
    change aeval a p = 0
    rwa [← aeval_map_algebraMap K]
  have := irreducible_of_isEisensteinAt_root hp hn hα hgen
  convert this
  exact Subtype.ext hx

variable [IsSepClosed Ω]

theorem val_mem_lubinTateField_of_mem (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries π g)
    {n : ℕ} {x : IdealPoint Ω (lubinTateFormalGroup hπ hg)} (hx : x ∈ lubinTateTorsion Ω hg n) :
    x.val ∈ lubinTateField Ω hπ hf n :=
  lubinTateField_eq (Ω := Ω) hπ hg hf n ▸ val_mem_lubinTateField hπ hg hx

theorem primitive_spec (hf : IsLubinTateSeries π f) {n : ℕ}
    {l : IdealPoint Ω (lubinTateFormalGroup hπ hf)} (hl : l ∈ lubinTateTorsion Ω hf n)
    (hl' : l ∉ lubinTateTorsion Ω hf (n - 1)) :
    (∀ a : 𝒪[K], a • l = 0 ↔ a ∈ Ideal.span {π ^ n}) ∧
      ∀ m ∈ lubinTateTorsion Ω (hπ := hπ) hf n, ∃ a : 𝒪[K], a • l = m := by
  obtain ⟨l₀, -, hann, hgen⟩ := exists_generator_lubinTateTorsion (Ω := Ω) (hπ := hπ) hf n
  obtain ⟨b, rfl⟩ := hgen l hl
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := by
    cases n with
    | zero => exact absurd hl hl'
    | succ k => exact ⟨k, rfl⟩
  have hb : IsUnit b := by
    by_contra hb
    apply hl'
    have hmem := (IsLocalRing.mem_maximalIdeal b).mpr hb
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
    obtain ⟨c, rfl⟩ := hmem
    rw [Nat.add_sub_cancel, mem_lubinTateTorsion, smul_smul, (hann _).mpr]
    exact Ideal.mem_span_singleton.mpr ⟨c, by ring⟩
  obtain ⟨u, rfl⟩ := hb
  refine ⟨fun a => ?_, fun m hm => ?_⟩
  · rw [smul_smul, hann]
    exact Ideal.mul_unit_mem_iff_mem _ u.isUnit
  · obtain ⟨a, rfl⟩ := hgen m hm
    exact ⟨a * ↑u⁻¹, by rw [smul_smul, mul_assoc, Units.inv_mul, mul_one]⟩

theorem exists_primitive (hf : IsLubinTateSeries π f) {n : ℕ} (hn : 0 < n) :
    ∃ l ∈ lubinTateTorsion Ω (hπ := hπ) hf n, l ∉ lubinTateTorsion Ω (hπ := hπ) hf (n - 1) := by
  obtain ⟨l, hl, hann, -⟩ := exists_generator_lubinTateTorsion (Ω := Ω) (hπ := hπ) hf n
  refine ⟨l, hl, fun h => ?_⟩
  rw [mem_lubinTateTorsion, hann, Ideal.mem_span_singleton,
    pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit] at h
  omega

theorem lubinTateField_eq_adjoin_of_primitive (hf : IsLubinTateSeries π f) {n : ℕ}
    {l : IdealPoint Ω (lubinTateFormalGroup hπ hf)} (hl : l ∈ lubinTateTorsion Ω hf n)
    (hl' : l ∉ lubinTateTorsion Ω hf (n - 1)) :
    lubinTateField Ω hπ hf n = K⟮l.val⟯ := by
  obtain ⟨-, hgen⟩ := primitive_spec hπ hf hl hl'
  refine le_antisymm ?_ ?_
  · rw [lubinTateField, adjoin_le_iff]
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨a, rfl⟩ := hgen m hm
    rw [lubinTate_smul_val]
    exact psEval_mem_adjoin_simple _ l.valuation_lt_one
  · rw [adjoin_simple_le_iff]
    exact val_mem_lubinTateField hπ hf hl

theorem irreducible_of_primitive_ltPoly (hf : IsLubinTateSeries π f) {n : ℕ}
    {l : IdealPoint Ω (lubinTateFormalGroup hπ (isLubinTateSeries_ltPoly π))}
    (hl : l ∈ lubinTateTorsion Ω (isLubinTateSeries_ltPoly π) n)
    (hl' : l ∉ lubinTateTorsion Ω (isLubinTateSeries_ltPoly π) (n - 1))
    {x : 𝒪[lubinTateField Ω hπ hf n]} (hx : ((x : lubinTateField Ω hπ hf n) : Ω) = l.val) :
    Irreducible x := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := by
    cases n with
    | zero => exact absurd hl hl'
    | succ k => exact ⟨k, rfl⟩
  rw [Nat.add_sub_cancel] at hl'
  have hE : lubinTateField Ω hπ hf (k + 1) = K⟮l.val⟯ :=
    (lubinTateField_eq hπ hf (isLubinTateSeries_ltPoly π) _).trans
      (lubinTateField_eq_adjoin_of_primitive hπ _ hl (by rwa [Nat.add_sub_cancel]))
  have hq := one_lt_card_residueField' K
  have hdeg : 0 < (ltEisenstein π k).natDegree := by
    rw [(ltEisenstein_monic π k).2]
    exact Nat.mul_pos (by omega) (pow_pos (by omega) k)
  exact irreducible_of_eq_adjoin_of_isEisensteinAt hE (isEisensteinAt_ltEisenstein hπ k) hdeg
    (aeval_ltEisenstein_of_primitive hπ hl hl') hx

theorem irreducible_of_primitive (hf : IsLubinTateSeries π f) {n : ℕ}
    {l : IdealPoint Ω (lubinTateFormalGroup hπ hf)} (hl : l ∈ lubinTateTorsion Ω hf n)
    (hl' : l ∉ lubinTateTorsion Ω hf (n - 1))
    {x : 𝒪[lubinTateField Ω hπ hf n]} (hx : ((x : lubinTateField Ω hπ hf n) : Ω) = l.val) :
    Irreducible x := by
  have hg₀ : IsLubinTateSeries π (ltPoly π : PowerSeries 𝒪[K]) := isLubinTateSeries_ltPoly π
  obtain ⟨m, rfl⟩ := (lubinTatePointEquiv hf hg₀).surjective l
  replace hl := (lubinTatePointEquiv_mem_torsion_iff hf hg₀ n m).mp hl
  replace hl' := fun h => hl' ((lubinTatePointEquiv_mem_torsion_iff hf hg₀ (n - 1) m).mpr h)
  have hmE : m.val ∈ lubinTateField Ω hπ hf n := val_mem_lubinTateField_of_mem hπ hf hg₀ hl
  obtain ⟨y, hy⟩ := exists_integer_eq hmE m.valuation_lt_one
  have hyirr : Irreducible y := irreducible_of_primitive_ltPoly hπ hf hl hl' hy
  have hym : y ∈ 𝓂[lubinTateField Ω hπ hf n] := hyirr.not_isUnit
  set φ := (lubinTateHom hπ hf hg₀ 1).toPowerSeries
  have hassoc := associated_psEval (K := K) (L := lubinTateField Ω hπ hf n) (φ := φ)
    (lubinTateHom hπ hf hg₀ 1).constantCoeff_eq_zero'
    (by rw [coeff_one_lubinTateHom]; exact isUnit_one) y hym
  have hxe : x = ⟨_, psEval_mem_integer φ (fun _ => y) fun _ => hym⟩ := by
    apply Subtype.ext
    apply Subtype.ext
    rw [hx, lubinTatePointEquiv_val]
    change psEval φ (fun _ => m.val) =
      ((psEval φ (fun _ => (y : lubinTateField Ω hπ hf n)) : lubinTateField Ω hπ hf n) : Ω)
    rw [← psEval_coe _ φ (fun _ => (y : lubinTateField Ω hπ hf n)) (fun _ => by rw [hy]; exact m.valuation_lt_one), hy]
  rw [hxe]
  exact hassoc.irreducible hyirr

theorem norm_neg_eq_uniformizer_of_primitive (hf : IsLubinTateSeries π f) {n : ℕ}
    {l : IdealPoint Ω (lubinTateFormalGroup hπ (isLubinTateSeries_ltPoly π))}
    (hl : l ∈ lubinTateTorsion Ω (isLubinTateSeries_ltPoly π) n)
    (hl' : l ∉ lubinTateTorsion Ω (isLubinTateSeries_ltPoly π) (n - 1)) :
    Algebra.norm K (-(⟨l.val, val_mem_lubinTateField_of_mem hπ hf (isLubinTateSeries_ltPoly π) hl⟩ :
      lubinTateField Ω hπ hf n)) = (π : K) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := by
    cases n with
    | zero => exact absurd hl hl'
    | succ k => exact ⟨k, rfl⟩
  rw [Nat.add_sub_cancel] at hl'
  have hE : lubinTateField Ω hπ hf (k + 1) = K⟮l.val⟯ :=
    (lubinTateField_eq hπ hf (isLubinTateSeries_ltPoly π) _).trans
      (lubinTateField_eq_adjoin_of_primitive hπ _ hl (by rwa [Nat.add_sub_cancel]))
  rw [norm_neg_eq_coeff_zero hE _ (ltEisenstein_monic π k).1 ?_
    (aeval_ltEisenstein_of_primitive hπ hl hl'), coeff_zero_ltEisenstein]
  rw [(finrank_and_ramificationIndex_lubinTateField_succ hπ hf k).1, (ltEisenstein_monic π k).2]

end Torsion

end FormalGroup

end GroundTheory.LocalField

end

end LubinTatePrimitive
