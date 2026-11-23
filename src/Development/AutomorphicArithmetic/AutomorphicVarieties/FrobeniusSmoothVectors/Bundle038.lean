module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle037
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
public import ReciprocityTheory.GaloisValuations.Bundle002
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V
open scoped Pointwise

private theorem padic_hom_ext {l : ℕ} [Fact l.Prime] {k : Type} [CommRing k] [CharP k l] (f g : ℤ_[l] →+* k) : f = g := by
  ext x
  have h := PadicInt.sub_zmodRepr_mem x
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨y, hy⟩ := h
  have e : x = y * l + (x.zmodRepr : ℤ_[l]) := by rw [hy]; ring
  rw [e]
  simp

private theorem cc_sq {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {c : G F Ω} {j : Ω →+* ℂ}
    (h : ∀ x, j (c x) = starRingEnd ℂ (j x)) : c * c = 1 := by
  refine AlgEquiv.ext fun x => j.injective ?_
  rw [AlgEquiv.mul_apply, h, h, starRingEnd_self_apply]
  rfl

private theorem eta_cc {Ω : Type} [Field Ω] [CharZero Ω] {η : G ℚ Ω →* ℤˣ} {D : ℕ} {δ : Ω} (hD : 0 < D)
    (hδ : δ ^ 2 = -(D : Ω)) (hη : ∀ s : G ℚ Ω, s δ = (η s : ℤ) • δ) {c : G ℚ Ω} {j : Ω →+* ℂ}
    (h : ∀ x, j (c x) = starRingEnd ℂ (j x)) : η c = -1 := by
  refine (Int.units_eq_one_or _).resolve_left fun h1 => ?_
  have h2 := h δ
  rw [hη, h1, Units.val_one, one_smul] at h2
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h2.symm
  have h3 := congrArg j hδ
  rw [map_pow, map_neg, map_natCast, hr] at h3
  have h4 : r ^ 2 = -(D : ℝ) := by exact_mod_cast h3
  have h5 : (0 : ℝ) < D := by exact_mod_cast hD
  nlinarith [sq_nonneg r]

private theorem smul_over {Ω : Type} [Field Ω] [CharZero Ω] {l : ℕ} {B : ValuationSubring Ω} (γ : G ℚ Ω)
    (h : B.valuation (l : Ω) < 1) : (γ • B).valuation (l : Ω) < 1 := by
  rw [valuation_lt_one_iff'] at h ⊢
  simpa only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, map_natCast, map_inv₀] using h

private theorem cpt_gal (F Ω : Type) [Field F] [CharZero F] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra F Ω] :
    CompactSpace (G F Ω) := by
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI : IsGalois F Ω := IsGalois.tower_top_of_isGalois ℚ F Ω
  infer_instance

theorem UpperTheory.V.Fr.ok_basic :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ (m : ℕ) (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] (g₁ : G ℚ Ω) (Φ : Frame l (ResidueField O)), UFacts l η Ψ M m (upl Ω L) → Linked l η Ψ σ g₁ B M L Φ → barChar O Ψ g₁ ^ 2 ≠ 1 → IsOpen (Φ.del.ker : Set Φ.Γ) ∧ Φ.c * Φ.c = 1 ∧ Φ.del Φ.c = -1 ∧ (∀ v, Continuous (Φ.loc0 v)) ∧ Continuous Φ.eps ∧ IsOpen (Φ.Ψ.ker : Set Φ.Γ) ∧ Φ.Ψ Φ.c = 1 ∧ Φ.Ψ Φ.g0 ^ 2 ≠ 1 ∧ Fintype.card Φ.Inf = Φ.d ∧ (∀ w, Φ.cw w * Φ.cw w = 1) ∧ (∀ w, Φ.del (Φ.cw w) = -1) ∧ (∃ g : Φ.G0, Φ.om (ResidueField O) g ≠ 1) ∧ (∀ j : ℤ, j = 1 ∨ j = -1 → ∃ g : Φ.G0, Φ.om (ResidueField O) g * Φ.Ψ g ^ j ≠ 1) ∧ (∀ j : ℤ, j = 2 ∨ j = -2 → ∃ g, Φ.om (ResidueField O) g * Φ.Ψ g ^ j * Φ.delK (ResidueField O) g ≠ 1) ∧ (∀ v, ∃ g, Φ.Ψ (Φ.loc v g) ^ 2 ≠ 1) ∧ (¬ ∃ j : ℤ, ∀ g : Φ.G0, Φ.om (ResidueField O) g = Φ.Ψ g ^ j) ∧ (∀ v, ∀ g ∈ Φ.Nv v, Φ.Ψ (Φ.loc v g) = 1) ∧ (∀ v, l ^ m ≤ Φ.dv v) ∧ Nonempty Φ.V := by
  intro Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG m L _ _ _ _ g₁ Φ hU hL hg₁
  obtain ⟨k, S, π, ι, pl, e, c, F, hπ, -⟩ := hL
  haveI : CompactSpace (G (W.Lp L) Ω) := cpt_gal _ _
  have hq : Topology.IsQuotientMap π := F.g.cont.isClosedMap.isQuotientMap F.g.cont F.g.onto
  have hom : ∀ s, Φ.om (ResidueField O) (k.p s) = omO Ω l O s := fun s => by
    apply Units.ext
    show (ZMod.castHom (dvd_refl l) (ResidueField O)).comp PadicInt.toZMod (Φ.eps (k.p s) : ℤ_[l]ˣ) =
      (ZMod.castHom (dvd_pow_self l one_ne_zero) (ResidueField O)).comp (PadicInt.toZModPow 1) (cycZ ℚ Ω l s : ℤ_[l]ˣ)
    rw [k.eps, padic_hom_ext ((ZMod.castHom (dvd_refl l) (ResidueField O)).comp PadicInt.toZMod)]
  have hpl : ∀ v, (k.pl v).valuation (l : Ω) < 1 := fun v => by
    obtain ⟨γ, -, h⟩ := k.pl_conj v
    exact h ▸ smul_over γ hG.over_l
  have h0 : ∀ s (h : s ∈ upl Ω L ⊓ η.ker), k.p ⟨s, h.1⟩ ∈ Φ.del.ker := fun s h => (k.del _).trans h.2
  have f5 : ¬ ∃ j : ℤ, ∀ g : Φ.G0, Φ.om (ResidueField O) g = Φ.Ψ g ^ j := by
    rintro ⟨j, hj⟩
    refine hU.f5 ⟨j, fun s hs => ?_⟩
    have := hj ⟨_, h0 s hs⟩
    rwa [hom, k.psi] at this
  obtain ⟨hσ, hc⟩ := k.c
  obtain ⟨hg, hg0⟩ := k.g0
  obtain ⟨D, δ, hD, -, hδ, hη⟩ := hG.quad
  refine ⟨F.del_open, ?_, F.del_c, fun v => ?_, ?_, ?_, ?_, ?_, ?_, fun w => ?_, fun w => ?_, ?_, fun j hj => ?_,
    fun j hj => ?_, fun v => ?_, f5, fun v g hg => ?_, fun v => ?_, ?_⟩
  · obtain ⟨j, hj⟩ := hG.cc
    rw [← hc, ← map_mul, ← map_one k.p]
    exact congrArg k.p (Subtype.ext (cc_sq hj))
  · refine continuous_induced_rng.2 ?_
    have : Subtype.val ∘ Φ.loc0 v = k.p ∘ k.j v := funext (k.j_loc v)
    exact this ▸ k.p_cont.comp (k.j_cont v)
  · refine hq.continuous_iff.2 ?_
    have : Φ.eps ∘ π = cycZ (W.Lp L) Ω l := funext F.eps
    exact this ▸ continuous_cycZ _ _ l
  · exact hq.isOpen_preimage.1 (Subgroup.isOpen_mono (H₂ := Φ.Ψ.ker.comap π) F.K_Ψ F.g.isOpen)
  · rw [← hc, k.psi]
    exact hG.even
  · rw [← hg0, k.psi]
    exact hg₁
  · classical
    haveI := F.real
    rw [Fintype.card_congr e, Frame.d, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyReal.nrComplexPlaces_eq_zero, add_zero, ← IsTotallyReal.finrank,
      ← sum_locDegree l (Finset.univ.image pl) fun v => by
        rw [← F.loc.mem, Finset.mem_image]; exact ⟨fun ⟨a, _, h⟩ => ⟨a, h⟩, fun ⟨a, h⟩ => ⟨a, Finset.mem_univ _, h⟩⟩,
      Finset.sum_image fun a _ b _ h => F.loc.inj h]
    exact Finset.sum_congr rfl fun v _ => (F.dv v).symm
  · obtain ⟨j, hj, -⟩ := F.cc w
    rw [F.cw, ← map_mul, cc_sq hj, map_one]
  · obtain ⟨j, hj, -⟩ := F.cc w
    rw [F.cw, hπ _ fun x hx => (c w).commutes ⟨x, hx⟩, k.del]
    exact eta_cc hD hδ hη hj
  · by_contra h
    exact f5 ⟨0, fun g => by_contra fun h' => h ⟨g, by simpa using h'⟩⟩
  · obtain ⟨s, hs, h⟩ := hU.f2b j hj
    exact ⟨⟨_, h0 s hs⟩, by rwa [hom, k.psi]⟩
  · obtain ⟨s, hs, h⟩ := hU.f2c j hj
    refine ⟨k.p ⟨s, hs.1⟩, ?_⟩
    rwa [hom, k.psi, Frame.delK, MonoidHom.comp_apply, MonoidHom.mem_ker.1 (h0 s hs), map_one, mul_one]
  · obtain ⟨s, hs, h⟩ := hU.f3 _ (hpl v)
    obtain ⟨g, hg⟩ := (k.j_range v ⟨s, hs.2⟩).2 hs.1
    exact ⟨g, by rwa [k.j_loc, k.psi, hg]⟩
  · obtain ⟨j, hj⟩ := hG.Ψ_l
    have h1 : Φ.eps (Φ.loc v g) = 1 := hg.2
    have h2 : Φ.om (ResidueField O) (Φ.loc v g) = 1 := by rw [Frame.om, MonoidHom.comp_apply, h1, map_one]
    rw [k.j_loc, hom] at h2
    rw [k.j_loc, k.psi, hj _ (hpl v) _ ((k.j_ine v g).1 hg.1), h2, one_pow]
  · exact k.dv v ▸ hU.deg _ (hpl v)
  · exact ⟨(k.pl_all B hG.over_l).exists.choose⟩
end

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V
open scoped Pointwise

namespace UpperTheory.V.Fr.DescentValuationAlt

private theorem smul_val_lt {Ω : Type} [Field Ω] [Algebra ℚ Ω] (g : G ℚ Ω) (A : ValuationSubring Ω) (n : ℕ)
    (hA : A.valuation (n : Ω) < 1) : (g • A).valuation (n : Ω) < 1 := by
  have fix : ∀ y : Ω, g y = y → (y ∈ g • A ↔ y ∈ A) := by
    intro y hy
    have hy' : g • y = y := hy
    constructor
    · intro h
      obtain ⟨s, hs, hgs⟩ := (ValuationSubring.mem_smul_pointwise_iff_exists g y A).mp h
      have : s = y := by
        rw [← inv_smul_smul g s, hgs, inv_smul_eq_iff, hy']
      rwa [this] at hs
    · intro h
      have := ValuationSubring.smul_mem_pointwise_smul g y A h
      rwa [hy'] at this
  have vlt : ∀ (C : ValuationSubring Ω) (x : Ω), x ≠ 0 → (C.valuation x < 1 ↔ x ∈ C ∧ x⁻¹ ∉ C) := by
    intro C x hx
    haveI : Nontrivial C.ValueGroup := GroupWithZero.toNontrivial
    rw [← ValuationSubring.valuation_le_one_iff, ← ValuationSubring.valuation_le_one_iff, map_inv₀,
      inv_le_one₀ ((Valuation.pos_iff _).mpr hx), lt_iff_le_not_ge]
  by_cases h0 : (n : Ω) = 0
  · rw [h0, map_zero]
    haveI : Nontrivial (g • A).ValueGroup := GroupWithZero.toNontrivial
    exact zero_lt_one
  · have hn : g (n : Ω) = n := map_natCast g n
    have hni : g ((n : Ω)⁻¹) = (n : Ω)⁻¹ := by rw [map_inv₀, hn]
    rw [vlt _ _ h0] at hA ⊢
    rw [fix _ hn, fix _ hni]
    exact hA

private theorem descend {U Γ k : Type} [Group U] [TopologicalSpace U] [IsTopologicalGroup U] [CompactSpace U]
    [Group Γ] [TopologicalSpace Γ] [T2Space Γ] [CommRing k] (p : U →* Γ) (hc : Continuous p)
    (hs : Function.Surjective p) (S : Set U) (hk : p.ker = (Subgroup.normalClosure S).topologicalClosure)
    (χ : Γ →* kˣ) (y : U → k) (hl : IsLocallyConstant y) (hy : ∀ s t, y (s * t) = y s + χ (p s) * y t)
    (hS : ∀ s ∈ S, y s = 0) :
    ∃ φ : Γ → k, IsLocallyConstant φ ∧ ∀ s, φ (p s) = y s := by
  have hy1 : y 1 = 0 := by
    have e := hy 1 1
    rw [mul_one, map_one, map_one, Units.val_one, one_mul] at e
    linear_combination -e
  let H : Subgroup U :=
    { carrier := {t | p t = 1 ∧ y t = 0}
      one_mem' := ⟨map_one p, hy1⟩
      mul_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        show p (a * b) = 1 ∧ y (a * b) = 0
        refine ⟨by rw [map_mul, ha1, hb1, one_mul], ?_⟩
        rw [hy, ha2, hb2, mul_zero, add_zero]
      inv_mem' := by
        rintro a ⟨ha1, ha2⟩
        show p a⁻¹ = 1 ∧ y a⁻¹ = 0
        refine ⟨by rw [map_inv, ha1, inv_one], ?_⟩
        have e := hy a a⁻¹
        rw [mul_inv_cancel, hy1, ha2, ha1, map_one, Units.val_one, one_mul, zero_add] at e
        exact e.symm }
  have hH : H.Normal := ⟨fun t ht g => by
    obtain ⟨ht1, ht2⟩ := ht
    show p (g * t * g⁻¹) = 1 ∧ y (g * t * g⁻¹) = 0
    refine ⟨by rw [map_mul, map_mul, map_inv, ht1, mul_one, mul_inv_cancel], ?_⟩
    have e1 := hy (g * t) g⁻¹
    have e2 := hy g t
    have e3 := hy g g⁻¹
    rw [mul_inv_cancel, hy1] at e3
    rw [map_mul, ht1, mul_one] at e1
    rw [ht2, mul_zero, add_zero] at e2
    rw [e1, e2, ← e3]⟩
  have hcl : IsClosed (H : Set U) :=
    (isClosed_eq hc continuous_const).inter (hl.isClosed_fiber 0)
  have hKH : p.ker ≤ H := by
    rw [hk]
    apply Subgroup.topologicalClosure_minimal _ _ hcl
    haveI := hH
    apply Subgroup.normalClosure_le_normal
    intro s hsS
    have hps : p s = 1 := by
      rw [← MonoidHom.mem_ker, hk]
      exact Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hsS)
    exact ⟨hps, hS s hsS⟩
  have hfib : ∀ s t, p s = p t → y s = y t := by
    intro s t hst
    have hk' : s⁻¹ * t ∈ p.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hst, inv_mul_cancel]
    obtain ⟨_, h2⟩ := hKH hk'
    have e := hy s (s⁻¹ * t)
    rw [mul_inv_cancel_left, h2, mul_zero, add_zero] at e
    exact e.symm
  have hq : Topology.IsQuotientMap p := (hc.isClosedMap).isQuotientMap hc hs
  refine ⟨fun γ => y (Function.surjInv hs γ), fun V => ?_, fun s => hfib _ _ (Function.surjInv_eq hs (p s))⟩
  have e : p ⁻¹' ((fun γ => y (Function.surjInv hs γ)) ⁻¹' V) = y ⁻¹' V := by
    ext s
    simp only [Set.mem_preimage]
    rw [hfib _ _ (Function.surjInv_eq hs (p s))]
  apply hq.isOpen_preimage.mp
  rw [e]
  exact hl V

end UpperTheory.V.Fr.DescentValuationAlt

open UpperTheory.V.Fr.DescentValuationAlt in
theorem UpperTheory.V.Fr.frobenius_galoisField_four_compatibility :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ (m : ℕ) (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] (g₁ : G ℚ Ω) (Φ : Frame l (ResidueField O)), UFacts l η Ψ M m (upl Ω L) → Linked l η Ψ σ g₁ B M L Φ → ∀ a : ℕ, a = 1 ∨ a = 2 → StrictCl l η Ψ ((barChar O Ψ)⁻¹ ^ a * etaO O η) (upl Ω L) → Nontrivial (H1C Φ.loc (chRep (Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O))) fun _ => ⊥) := by
  intro Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG m L _ _ _ _ g₁ Φ hU hL a ha hS
  obtain ⟨k, -⟩ := hL
  obtain ⟨y, hyl, hyc, hyn, hyd, hyi⟩ := hS
  have hχ : ∀ s : upl Ω L, (Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) (k.p s)
      = ((barChar O Ψ)⁻¹ ^ a * etaO O η) s := by
    intro s
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.pow_apply,
      MonoidHom.inv_apply, MonoidHom.inv_apply, k.psi]
    congr 1
    simp only [Frame.delK, etaO, MonoidHom.comp_apply, k.del]
  have hUc : IsClosed (upl Ω L : Set (G ℚ Ω)) := Subgroup.isClosed_of_isOpen _ hU.isOpen
  haveI : CompactSpace (upl Ω L) := isCompact_iff_compactSpace.mp hUc.isCompact
  obtain ⟨φ, hφl, hφ⟩ := descend k.p k.p_cont k.p_surj _ k.p_ker (Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O))
    (fun s => y s) (hyl.comp_continuous continuous_subtype_val)
    (fun s t => by rw [hχ s]; exact hyc s t)
    (fun s hs => by
      obtain ⟨B', hB', hI, hη, hb⟩ := hs
      exact hyi B' hB' s (Subgroup.mem_inf.mpr ⟨hI, s.2⟩) hη hb)
  have hρ : ∀ (γ : Φ.Γ) (w : ResidueField O),
      (chRep (Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) γ) w
        = ((Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) γ : ResidueField O) * w := fun γ w => rfl
  have hcoc : ∀ γ δ : Φ.Γ, φ (γ * δ)
      = φ γ + ((Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) γ : ResidueField O) * φ δ := by
    intro γ δ
    obtain ⟨s, rfl⟩ := k.p_surj γ
    obtain ⟨t, rfl⟩ := k.p_surj δ
    rw [← map_mul, hφ, hφ, hφ, hχ]
    exact hyc s t
  have hloc : ∀ v : Φ.V, ∃ b : ResidueField O, ∀ g : Φ.Gv v,
      φ (Φ.loc v g) = ((Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) (Φ.loc v g) : ResidueField O) * b - b := by
    intro v
    obtain ⟨γ, -, hγ⟩ := k.pl_conj v
    have hv : (k.pl v).valuation (l : Ω) < 1 := by
      rw [hγ]
      exact smul_val_lt γ B l hG.over_l
    obtain ⟨b, hb⟩ := hyd _ hv
    refine ⟨b, fun g => ?_⟩
    rw [k.j_loc, hφ, hχ]
    exact hb _ ((k.j_range v _).mp (MonoidHom.mem_range.mpr ⟨g, rfl⟩))
  choose b hb using hloc
  let z : Z1C Φ.loc (chRep (Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O))) (fun _ => ⊥) :=
    ⟨(φ, b), ⟨hφl, fun γ δ => by rw [hρ]; exact hcoc γ δ,
      fun v g => by rw [Submodule.mem_bot, hρ, ← hb v g, sub_self]⟩⟩
  refine ⟨⟨Submodule.Quotient.mk z, 0, fun h => ?_⟩⟩
  have hz := (Submodule.Quotient.mk_eq_zero _).mp h
  rw [Submodule.mem_comap] at hz
  obtain ⟨X, hX1, -⟩ := hz
  apply hyn
  refine ⟨X, fun s hs => ?_⟩
  have e1 := hφ ⟨s, hs⟩
  have e2 := hX1 (k.p ⟨s, hs⟩)
  rw [hρ, hχ] at e2
  rw [← e2]
  exact e1.symm
end

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem fix_fix {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (H : Subgroup (Ω ≃ₐ[ℚ] Ω))
    (h : IsOpen (H : Set (Ω ≃ₐ[ℚ] Ω))) : (IntermediateField.fixedField H).fixingSubgroup = H :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨H, H.isClosed_of_isOpen h⟩

private theorem commutator_le_ker_of_hom_int_units {Γ : Type*} [Group Γ] (η : Γ →* ℤˣ) : commutator Γ ≤ η.ker := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

private theorem conj_ne_self_of_sq_eq_neg_natCast (z : ℂ) (D : ℕ) (hD : 0 < D) (h : z ^ 2 = -(D : ℂ)) :
    starRingEnd ℂ z ≠ z := by
  intro hc
  have him : z.im = 0 := Complex.conj_eq_iff_im.mp hc
  have h1 := congrArg Complex.re h
  simp [pow_two, him] at h1
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  nlinarith [mul_self_nonneg z.re]

theorem UpperTheory.V.Fr.field_ex :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ (m : ℕ) (U : Subgroup (G ℚ Ω)), UFacts l η Ψ M m U → ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : IsCMField L) (_ : Algebra L Ω), IsAbelianGalois ℚ L ∧ upl Ω L = U ∧ galOf ℚ L Ω = U ⊓ η.ker := by
  intro Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG m U hU
  obtain ⟨D, δ, hD, -, hδ2, hδ⟩ := hG.quad
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    simp at hδ2
    omega
  have hker : ∀ s : G ℚ Ω, η s = 1 ↔ s δ = δ := by
    intro s
    constructor
    · intro h
      rw [hδ s, h]
      simp
    · intro h
      rcases Int.units_eq_one_or (η s) with h1 | h1
      · exact h1
      · exfalso
        rw [hδ s, h1] at h
        simp at h
        have h2 : (2 : Ω) * δ = 0 := by linear_combination -h
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact two_ne_zero h3
        · exact hδ0 h3
  have hint : IsIntegral ℚ δ := Algebra.IsIntegral.isIntegral δ
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {δ}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hkerO : IsOpen (η.ker : Set (G ℚ Ω)) := by
    refine Subgroup.isOpen_mono ?_ (IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin ℚ {δ}))
    intro s hs
    rw [MonoidHom.mem_ker, hker]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hs δ
      (IntermediateField.mem_adjoin_simple_self ℚ δ)
  have hHo : IsOpen ((U ⊓ η.ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
    rw [Subgroup.coe_inf]
    exact hU.isOpen.inter hkerO
  have hcomm : commutator (G ℚ Ω) ≤ U ⊓ η.ker := le_inf hU.ab (commutator_le_ker_of_hom_int_units η)
  set L := IntermediateField.fixedField (U ⊓ η.ker) with hLdef
  have hfix : L.fixingSubgroup = U ⊓ η.ker := fix_fix _ hHo
  haveI : FiniteDimensional ℚ L := (InfiniteGalois.isOpen_iff_finite L).mp (by rw [hfix]; exact hHo)
  haveI : NumberField L := ⟨⟩
  have hN : (L.fixingSubgroup).Normal := by
    rw [hfix]
    refine ⟨fun n hn g => ?_⟩
    have hc : g * n * g⁻¹ * n⁻¹ ∈ U ⊓ η.ker :=
      hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
    have he : g * n * g⁻¹ = g * n * g⁻¹ * n⁻¹ * n := by
      group
    rw [he]
    exact Subgroup.mul_mem _ hc hn
  have hAb : @IsAbelianGalois ℚ L _ _ (IntermediateField.algebra' L) := by
    letI : Algebra ℚ L := IntermediateField.algebra' L
    haveI hg : IsGalois ℚ L := (InfiniteGalois.normal_iff_isGalois L).mp hN
    haveI : IsMulCommutative Gal(L/ℚ) := ⟨⟨fun a b => by
      obtain ⟨a', rfl⟩ := AlgEquiv.restrictNormalHom_surjective Ω a
      obtain ⟨b', rfl⟩ := AlgEquiv.restrictNormalHom_surjective Ω b
      have hc : a' * b' * a'⁻¹ * b'⁻¹ ∈ (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Ω) L).ker := by
        rw [IntermediateField.restrictNormalHom_ker, hfix]
        exact hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top a') (Subgroup.mem_top b'))
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at hc
      exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hc)⟩⟩
    exact ⟨⟩
  haveI : IsAbelianGalois ℚ L := by
    convert hAb <;> exact Subsingleton.elim _ _
  have hδL : δ ∈ L := by
    rw [IntermediateField.mem_fixedField_iff]
    intro s hs
    exact (hker s).mp (MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp hs).2)
  have hδL2 : (⟨δ, hδL⟩ : L) ^ 2 = -(D : L) := by
    apply Subtype.ext
    simpa using hδ2
  haveI : NumberField.IsTotallyComplex L := ⟨fun v => by
    rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex, NumberField.InfinitePlace.isReal_iff]
    intro hv
    apply conj_ne_self_of_sq_eq_neg_natCast (v.embedding ⟨δ, hδL⟩) D hD
    · rw [← map_pow, hδL2]
      simp
    · have := RingHom.congr_fun hv ⟨δ, hδL⟩
      rwa [NumberField.ComplexEmbedding.conjugate_coe_eq] at this⟩
  obtain ⟨j, hj⟩ := hG.cc
  have hσU : σ ∈ U := hU.real σ hG.cc
  have hησ : η σ = -1 := by
    rcases Int.units_eq_one_or (η σ) with h | h
    · exfalso
      have hσδ : σ δ = δ := (hker σ).mp h
      apply conj_ne_self_of_sq_eq_neg_natCast (j δ) D hD
      · rw [← map_pow, hδ2]
        simp
      · rw [← hj, hσδ]
    · exact h
  have hcc : ∀ z : L, σ (z : Ω) = ((NumberField.IsCMField.complexConj L z : L) : Ω) := by
    intro z
    apply j.injective
    rw [hj]
    exact (NumberField.IsCMField.complexEmbedding_complexConj L (j.comp (algebraMap L Ω)) z).symm
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · ext s
    change (∀ x ∈ NumberField.maximalRealSubfield L, s (algebraMap L Ω x) = algebraMap L Ω x) ↔ s ∈ U
    constructor
    · intro h
      rw [← fix_fix U hU.isOpen, IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      have hyL : y ∈ L := (IntermediateField.mem_fixedField_iff _ _).mpr fun f hf =>
        (IntermediateField.mem_fixedField_iff _ _).mp hy f (Subgroup.mem_inf.mp hf).1
      have hre : (⟨y, hyL⟩ : L) ∈ NumberField.maximalRealSubfield L := by
        rw [← NumberField.IsCMField.complexConj_eq_self_iff]
        apply Subtype.ext
        rw [← hcc]
        exact (IntermediateField.mem_fixedField_iff _ _).mp hy σ hσU
      exact h _ hre
    · intro hs x hx
      have hσx : σ (x : Ω) = x := by
        rw [hcc, (NumberField.IsCMField.complexConj_eq_self_iff L x).mpr hx]
      show s (x : Ω) = x
      rcases Int.units_eq_one_or (η s) with h1 | h1
      · exact (IntermediateField.mem_fixedField_iff _ _).mp x.2 s (Subgroup.mem_inf.mpr ⟨hs, h1⟩)
      · have hm : σ * s ∈ U ⊓ η.ker := by
          refine Subgroup.mem_inf.mpr ⟨U.mul_mem hσU hs, ?_⟩
          rw [MonoidHom.mem_ker, map_mul, hησ, h1]
          rfl
        have := (IntermediateField.mem_fixedField_iff _ _).mp x.2 (σ * s) hm
        rw [AlgEquiv.mul_apply] at this
        apply σ.injective
        rw [this, hσx]
  · ext s
    change (∀ x : L, s (algebraMap L Ω x) = algebraMap L Ω x) ↔ s ∈ U ⊓ η.ker
    rw [← hfix, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x hx
      exact h ⟨x, hx⟩
    · intro h x
      exact h x x.2
end
