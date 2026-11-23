module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr
open scoped Matrix
set_option linter.overlappingInstances false

private theorem fac_conj {Ω : Type} [Field Ω] [CharZero Ω] (l : ℕ) (A : ValuationSubring Ω) (g x : G ℚ Ω)
    (hl : ¬ A.valuation (l : Ω) < 1) (hx : x ∈ Ine (F := ℚ) A) :
    ∃ A' : ValuationSubring Ω, ¬ A'.valuation (l : Ω) < 1 ∧ g * x * g⁻¹ ∈ Ine (F := ℚ) A' := by
  have h : IsLift (RingEquiv.refl ℚ) ((g.symm : Ω ≃ₐ[ℚ] Ω) : Ω ≃+* Ω) := fun q => g.symm.commutes q
  let σ : Ω ≃+* Ω := ((g.symm : Ω ≃ₐ[ℚ] Ω) : Ω ≃+* Ω)
  have hA : ∀ y : Ω, σ y ∈ A ↔ y ∈ A.comap (σ : Ω →+* Ω) := fun y => by
    rw [ValuationSubring.mem_comap]
    rfl
  refine ⟨A.comap (σ : Ω →+* Ω), ?_, ?_⟩
  · rw [← val_lt_one hA (l : Ω), map_natCast]
    exact hl
  · have hc := conjGal_mem_Ine h hA hx
    convert hc using 1
    ext z
    rfl

theorem UpperTheory.exists_frame_factorization_of_trivial_on_inertia :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ} {L : Type} [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)} (k : GalLink η Ψ σ g₁ B M L Φ) {n : ℕ} (r : G L Ω →* GL (Fin n) (Qbar l)), Continuous r → (∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := L) A, Ψ (galEmb ℚ L Ω s) = 1 → r s = 1) → ∃ r' : Φ.G0 →* GL (Fin n) (Qbar l), Continuous r' ∧ (∀ s, r' (k.p0 s) = r s) ∧ ∀ P : GL (Fin n) (Qbar l), Sd.IsPair σ r 1 P → ∀ g, (r' g).valᵀ * P.val * (r' (Φ.conj g)).val = P.val := by
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ Φ k n r hr hine
  have hgal : ∀ s : G L Ω, galEmb ℚ L Ω s ∈ upl Ω L ⊓ η.ker := fun s => by
    have h := galEmb_mem ℚ L Ω s
    rwa [k.gal] at h
  have hmem : ∀ s : G L Ω, galEmb ℚ L Ω s ∈ upl Ω L := fun s => (hgal s).1
  have hq : ∀ s, (k.p0 s : Φ.Γ) = k.p ⟨galEmb ℚ L Ω s, hmem s⟩ := fun s => rfl
  let q : G L Ω →* Φ.G0 :=
    { toFun := k.p0
      map_one' := by
        apply Subtype.ext
        rw [hq]
        rw [show (⟨galEmb ℚ L Ω 1, hmem 1⟩ : upl Ω L) = 1 from Subtype.ext (map_one _), map_one]
        rfl
      map_mul' := fun s t => by
        apply Subtype.ext
        rw [Subgroup.coe_mul, hq, hq, hq, ← map_mul]
        exact congrArg k.p (Subtype.ext (map_mul _ _ _)) }
  have hqv : ∀ s, ((q s : Φ.G0) : Φ.Γ) = k.p ⟨galEmb ℚ L Ω s, hmem s⟩ := fun s => rfl
  have hqs : Function.Surjective q := by
    intro x
    obtain ⟨u, hu⟩ := k.p_surj x.val
    have hu1 : (u : G ℚ Ω) ∈ galOf ℚ L Ω := by
      rw [k.gal]
      refine ⟨u.2, MonoidHom.mem_ker.mpr ?_⟩
      rw [← k.del u, hu]
      exact MonoidHom.mem_ker.mp x.2
    rw [← range_galEmb ℚ L Ω] at hu1
    obtain ⟨s, hs⟩ := hu1
    refine ⟨s, Subtype.ext ?_⟩
    rw [hqv, ← hu]
    exact congrArg k.p (Subtype.ext hs)
  have hgc : Continuous (galEmb ℚ L Ω) := (galEmbTop ℚ L Ω).1.continuous
  have hqc : Continuous q := by
    refine continuous_induced_rng.2 ?_
    exact k.p_cont.comp (hgc.subtype_mk hmem)
  have hinj : Function.Injective (galEmb ℚ L Ω) := (galEmbTop ℚ L Ω).1.injective
  have hker : ∀ s, q s = 1 → r s = 1 := by
    intro s hs
    have h1 : (⟨galEmb ℚ L Ω s, hmem s⟩ : upl Ω L) ∈ k.p.ker := by
      rw [MonoidHom.mem_ker, ← hqv, hs]
      rfl
    rw [k.p_ker] at h1
    let H' : Subgroup (upl Ω L) := (r.ker.map (galEmb ℚ L Ω)).comap (upl Ω L).subtype
    have hcl : IsClosed (H' : Set (upl Ω L)) := by
      have hk : IsClosed (r.ker : Set (G L Ω)) := by
        haveI : T2Space (Qbar l) := inferInstance
        haveI : T2Space (Matrix (Fin n) (Fin n) (Qbar l)) :=
          (inferInstance : T2Space (Fin n → Fin n → Qbar l))
        haveI h2 : T2Space (GL (Fin n) (Qbar l)) := inferInstance
        haveI : T1Space (GL (Fin n) (Qbar l)) := @T2Space.t1Space _ _ h2
        exact isClosed_singleton.preimage hr
      have hi : IsClosed ((galEmb ℚ L Ω) '' (r.ker : Set (G L Ω))) :=
        (hk.isCompact.image hgc).isClosed
      exact hi.preimage continuous_subtype_val
    have hX : Subgroup.normalClosure
        {s : upl Ω L | ∃ B' : ValuationSubring Ω, ¬ B'.valuation (l : Ω) < 1 ∧ (s : G ℚ Ω) ∈ Ine B' ∧
          η s = 1 ∧ barChar O Ψ s = 1} ≤ H' := by
      unfold Subgroup.normalClosure
      refine (Subgroup.closure_le _).2 ?_
      intro c hc
      rw [Group.mem_conjugatesOfSet_iff] at hc
      obtain ⟨x, ⟨B', hB'l, hxI, hxη, hxbar⟩, hconj⟩ := hc
      obtain ⟨u, hu⟩ := isConj_iff.mp hconj
      have hcv : (c : G ℚ Ω) = u * x * (u : G ℚ Ω)⁻¹ := by
        rw [← hu, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      obtain ⟨A', hA'l, hcI⟩ := fac_conj l B' u x hB'l hxI
      rw [← hcv] at hcI
      have hcη : η c = 1 := by
        rw [hcv, map_mul, map_mul, hxη, mul_one, ← map_mul, mul_inv_cancel, map_one]
      have hcbar : barChar O Ψ c = 1 := by
        rw [hcv, map_mul, map_mul, hxbar, mul_one, ← map_mul, mul_inv_cancel, map_one]
      have hcgal : (c : G ℚ Ω) ∈ galOf ℚ L Ω := by
        rw [k.gal]
        exact ⟨c.2, hcη⟩
      rw [← range_galEmb ℚ L Ω] at hcgal
      obtain ⟨t, ht⟩ := hcgal
      have hΨ : Ψ c = 1 := k.teich A' hA'l c ⟨hcI, c.2⟩ hcbar
      show (c : G ℚ Ω) ∈ r.ker.map (galEmb ℚ L Ω)
      refine ⟨t, ?_, ht⟩
      show r t = 1
      refine hine A' hA'l t ?_ ?_
      · show galEmb ℚ L Ω t ∈ Ine (F := ℚ) A'
        rw [ht]
        exact hcI
      · rw [ht]
        exact hΨ
    have h2 := (Subgroup.topologicalClosure_minimal _ hX hcl) h1
    obtain ⟨t, ht, hts⟩ := h2
    rw [hinj hts] at ht
    exact ht
  have hle : q.ker ≤ r.ker := fun s hs => hker s hs
  let e := QuotientGroup.quotientKerEquivOfSurjective q hqs
  let r' : Φ.G0 →* GL (Fin n) (Qbar l) := (QuotientGroup.lift q.ker r hle).comp e.symm.toMonoidHom
  have hr'q : ∀ s, r' (q s) = r s := by
    intro s
    have he : e.symm (q s) = (s : G L Ω ⧸ q.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift q.ker r hle (e.symm (q s)) = r s
    rw [he]
    rfl
  have hqq : Topology.IsQuotientMap q := Topology.IsQuotientMap.of_surjective_continuous hqs hqc
  have hr'c : Continuous r' := by
    rw [hqq.continuous_iff]
    convert hr using 1
    funext s
    exact hr'q s
  refine ⟨r', hr'c, fun s => hr'q s, ?_⟩
  intro P hP g
  obtain ⟨s, rfl⟩ := hqs g
  obtain ⟨hσ, hσc⟩ := k.c
  have hs'gal : σ * galEmb ℚ L Ω s * σ⁻¹ ∈ galOf ℚ L Ω := by
    rw [k.gal]
    refine ⟨(upl Ω L).mul_mem ((upl Ω L).mul_mem hσ (hmem s)) ((upl Ω L).inv_mem hσ),
      MonoidHom.mem_ker.mpr ?_⟩
    rw [map_mul, map_mul, MonoidHom.mem_ker.mp (hgal s).2, mul_one, ← map_mul, mul_inv_cancel, map_one]
  rw [← range_galEmb ℚ L Ω] at hs'gal
  obtain ⟨s', hs'⟩ := hs'gal
  have hconj : Φ.conj (q s) = q s' := by
    apply Subtype.ext
    rw [show ((Φ.conj (q s) : Φ.G0) : Φ.Γ) = Φ.c * (q s : Φ.Γ) * Φ.c⁻¹ from
      MulAut.conjNormal_apply _ _]
    rw [hqv, hqv, ← hσc, ← map_inv, ← map_mul, ← map_mul]
    apply congrArg k.p
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hs'.symm
  rw [hconj, hr'q, hr'q]
  have h := hP s s' hs'
  rw [MonoidHom.one_apply, Units.val_one, one_smul] at h
  exact h
end

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V
open scoped Pointwise

private theorem orbit_count {G X V : Type} [Group G] [MulAction G X] [Fintype V] (U : Subgroup G) [U.Normal]
    (hU : U.index ≠ 0) (b : X) (p : V → X) (h1 : ∀ v, ∃ γ : G, p v = γ • b)
    (h2 : ∀ g : G, ∃! v, ∃ u ∈ U, g • b = u • p v) :
    ∑ v, U.relIndex (MulAction.stabilizer G (p v)) = U.index := by
  classical
  have hN : U.Normal := inferInstance
  have conj_eq : ∀ γ : G, U.map (MulAut.conj γ).toMonoidHom = U := by
    intro γ
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hN.conj_mem y hy γ
    · intro hx
      refine ⟨γ⁻¹ * x * γ, ?_, ?_⟩
      · simpa using hN.conj_mem x hx γ⁻¹
      · simp [mul_assoc]
  have hrel : ∀ v, U.relIndex (MulAction.stabilizer G (p v)) =
      U.relIndex (U ⊔ MulAction.stabilizer G b) := by
    intro v
    obtain ⟨γ, hγ⟩ := h1 v
    rw [hγ, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    have e := Subgroup.relIndex_map_map (MulAut.conj γ).toMonoidHom U (MulAction.stabilizer G b)
    rw [conj_eq γ] at e
    have hker : (MulAut.conj γ).toMonoidHom.ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff _).mpr (MulEquiv.injective _)
    rw [e, hker, sup_bot_eq, sup_bot_eq, Subgroup.relIndex_sup_left]
  choose γ hγ using h1
  let F : V → G ⧸ (U ⊔ MulAction.stabilizer G b) := fun v => QuotientGroup.mk (γ v)
  have inj : Function.Injective F := by
    intro v w hvw
    have hm : (γ v)⁻¹ * γ w ∈ U ⊔ MulAction.stabilizer G b := QuotientGroup.eq.mp hvw
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at hm
    obtain ⟨a, ha, c, hc, hac⟩ := hm
    have hac' : a * c = (γ v)⁻¹ * γ w := hac
    have hw : γ w = γ v * a * c := by
      rw [mul_assoc, hac', mul_inv_cancel_left]
    have h₁ : γ w • b = (γ v * a * (γ v)⁻¹) • p v := by
      rw [hw, hγ v, mul_smul, MulAction.mem_stabilizer_iff.mp hc, ← mul_smul, inv_mul_cancel_right]
    have h₂ : γ w • b = (1 : G) • p w := by rw [one_smul, hγ w]
    have hu : γ v * a * (γ v)⁻¹ ∈ U := hN.conj_mem a ha (γ v)
    exact (h2 (γ w)).unique ⟨_, hu, h₁⟩ ⟨1, U.one_mem, h₂⟩
  have surj : Function.Surjective F := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨v, ⟨u, hu, e⟩, -⟩ := h2 g
      refine ⟨v, QuotientGroup.eq.mpr ?_⟩
      have hsplit : (γ v)⁻¹ * g = ((γ v)⁻¹ * u * γ v) * ((γ v)⁻¹ * u⁻¹ * g) := by group
      rw [hsplit]
      refine Subgroup.mul_mem_sup ?_ ?_
      · simpa using hN.conj_mem u hu (γ v)⁻¹
      · rw [MulAction.mem_stabilizer_iff]
        rw [hγ v] at e
        simp only [mul_smul, e, inv_smul_smul]
  have hcard : Fintype.card V = (U ⊔ MulAction.stabilizer G b).index := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_eq_of_bijective F ⟨inj, surj⟩
  rw [Finset.sum_congr rfl (fun v _ => hrel v), Finset.sum_const, Finset.card_univ, smul_eq_mul,
    hcard, mul_comm, Subgroup.relIndex_mul_index le_sup_left]

private theorem upl_normal (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (L : Type) [Field L] [NumberField L]
    [Algebra L Ω] [IsAbelianGalois ℚ L] : (upl Ω L).Normal := by
  unfold upl
  constructor
  intro n hn g x hx
  obtain ⟨y, hy, hy'⟩ : ∃ y ∈ maximalRealSubfield L, g⁻¹ (algebraMap L Ω x) = algebraMap L Ω y := by
    refine ⟨((g⁻¹ : Ω ≃ₐ[ℚ] Ω).toAlgHom.restrictNormal L) x, ?_, ?_⟩
    · intro φ
      exact hx (φ.comp ((g⁻¹ : Ω ≃ₐ[ℚ] Ω).toAlgHom.restrictNormal L).toRingHom)
    · exact (AlgHom.restrictNormal_commutes (g⁻¹ : Ω ≃ₐ[ℚ] Ω).toAlgHom L x).symm
  have hn' := hn y hy
  show (g * n * g⁻¹) (algebraMap L Ω x) = algebraMap L Ω x
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hy', hn', ← hy', ← AlgEquiv.mul_apply, mul_inv_cancel,
    AlgEquiv.one_apply]

private theorem cycMod_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hl : Fact l.Prime] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ l) {s : G ℚ Ω} (hs : s ζ = ζ) : cycMod ℚ Ω l 1 s = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  unfold cycMod cycZ
  ext
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Units.val_one]
  change PadicInt.toZModPow 1 ((cyclotomicCharacter Ω l) ((MulSemiringAction.toRingAut (G ℚ Ω) Ω) s)).val = 1
  rw [cyclotomicCharacter.toZModPow]
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  have hl1 : l ^ 1 ≠ 1 := by rw [pow_one]; exact hl.out.one_lt.ne'
  rw [ZMod.val_one'' hl1, pow_one]
  rw [pow_one] at ht
  obtain ⟨i, -, e⟩ := (hζ.isUnit_unit hl.out.ne_zero).eq_pow_of_mem_rootsOfUnity ht
  rw [← e]
  simp [hs]

private theorem val_smul {Ω : Type} [Field Ω] [CharZero Ω] (g : G ℚ Ω) (B : ValuationSubring Ω) (n : ℕ)
    (h : B.valuation (n : Ω) < 1) : (g • B).valuation (n : Ω) < 1 := by
  have key : ∀ (A : ValuationSubring Ω) (x : Ω), x ≠ 0 → (A.valuation x < 1 ↔ x⁻¹ ∉ A) := by
    intro A x hx
    rw [← A.valuation_le_one_iff, not_le, Valuation.one_lt_val_iff _ (inv_ne_zero hx), inv_inv]
  by_cases hn : (n : Ω) = 0
  · rw [hn]
    generalize g • B = C
    haveI : Nontrivial C.ValueGroup := ValuationRing.instNontrivialValueGroup C Ω
    rw [map_zero]
    exact zero_lt_one
  rw [key _ _ hn] at h ⊢
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, map_inv₀, map_natCast]
  exact h


theorem UpperTheory.V.Pr.degEq :
    UpperTheory.V.Pr.DegEq := by
  unfold UpperTheory.V.Pr.DegEq
  intro Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M hL L _ _ _ _ _ Φ k a
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsAbelianGalois ℚ L := k.ab
  haveI : (upl Ω L).Normal := upl_normal Ω L
  refine ⟨?_, ?_⟩
  · have hgal : galOf ℚ (W.Lp L) Ω = upl Ω L := by
      ext s
      unfold galOf upl
      constructor
      · intro h x hx
        exact h ⟨x, hx⟩
      · intro h x
        exact h x.1 x.2
    have hidx : (upl Ω L).index = Module.finrank ℚ (W.Lp L) := by
      rw [← hgal]
      exact (galEmbTop ℚ (W.Lp L) Ω).2.2
    rw [← hidx]
    unfold Fr.Frame.d
    rw [Finset.sum_congr rfl (fun v _ => k.dv v)]
    refine orbit_count (upl Ω L) (by rw [hidx]; exact Module.finrank_pos.ne') B k.pl ?_ ?_
    · intro v
      obtain ⟨γ, -, h⟩ := k.pl_conj v
      exact ⟨γ, h⟩
    · intro g
      exact k.pl_all (g • B) (val_smul g B l hL.atl)
  · rintro ⟨ζ, hζ⟩
    obtain ⟨g, hg⟩ := k.mu a
    apply hg
    have hsD : ((k.j a g : upl Ω L) : G ℚ Ω) ∈ Dec (k.pl a) := (k.j_range a _).mp ⟨g, rfl⟩
    obtain ⟨γ, -, hγ⟩ := k.pl_conj a
    have hM : B.valuation (M : Ω) < 1 := by
      obtain ⟨t, ht⟩ := hL.dvd
      have h1 : B.valuation ((N * t : ℕ) : Ω) ≤ 1 := (B.valuation_le_one_iff _).mpr (natCast_mem B _)
      rw [ht, mul_assoc, Nat.cast_mul, map_mul]
      calc B.valuation (l : Ω) * B.valuation ((N * t : ℕ) : Ω) ≤ B.valuation (l : Ω) :=
            mul_le_of_le_one_right' h1
        _ < 1 := hL.atl
    have hM' : (k.pl a).valuation (M : Ω) < 1 := by
      rw [hγ]
      exact val_smul γ B M hM
    have hker : ((k.j a g : upl Ω L) : G ℚ Ω) ∈ η.ker :=
      k.split (k.pl a) hM' (Subgroup.mem_inf.mpr ⟨hsD, (k.j a g).2⟩)
    have hfix : ((k.j a g : upl Ω L) : G ℚ Ω) ∈ galOf ℚ L Ω := by
      rw [k.gal]
      exact Subgroup.mem_inf.mpr ⟨(k.j a g).2, hker⟩
    unfold galOf at hfix
    exact cycMod_one l (hζ.map_of_injective (algebraMap L Ω).injective) (hfix ζ)
end
