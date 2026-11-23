module

public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsQuotEquiv
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle095
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle073
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle142
public import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OnePointBasisFundamentalDomainVolume
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle008
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle029
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle091
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.HermitianCurvature.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Formalism.HermitianCurvature.StatementD
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle012
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle145
public import Formalism.HermitianCurvature.StatementQ
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle146
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle024
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCutoffLimit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle079
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle144
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle053
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle157
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr

@[expose] public section

section

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FormTies
open scoped Classical

namespace GlobalTheory.MoreColumns

open GlobalTheory.DatumInverseCharacter

theorem sum_append {A F : Type} [Fintype A] [CommRing F] {n m : ℕ} (f : (Fin n → A) → F) (χ : Fin (n + m) → A → F) :
    ∑ x : Fin (n + m) → A, f (fun b => x (Fin.castAdd m b)) * ∏ b, χ b (x b) =
      (∑ y : Fin n → A, f y * ∏ b, χ (Fin.castAdd m b) (y b)) * ∏ b : Fin m, ∑ a, χ (Fin.natAdd n b) a := by
  rw [← (Fin.appendEquiv n m).sum_comp, Fintype.sum_prod_type, Finset.prod_univ_sum, Fintype.piFinset_univ,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun w _ => ?_
  rw [Fin.prod_univ_add]
  simp [mul_assoc]

theorem zpow_sum {F ι : Type} [Field F] {z : F} (hz : z ≠ 0) (s : Finset ι) (a : ι → ℤ) :
    z ^ (∑ i ∈ s, a i) = ∏ i ∈ s, z ^ a i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ hz, ih]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem char_sum (D : Datum H) {N : ℕ} (hN : 0 < N) {I : Ideal (𝓞 E)}
    (hp : I * I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(N : 𝓞 E)})
    (hI : I ⊔ I.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) {F : Type} [Field F] {z : F} (hz : IsPrimitiveRoot z N)
    [Fintype (D.La ⧸ (I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) D.La))] (v : D.La) :
    ∑ x : D.La ⧸ (I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) D.La), z ^ D.EF (qRep x) (cHalf H I • v) =
      if v ∈ (I • ⊤ : Submodule (𝓞 E) D.La) then
        (Nat.card (D.La ⧸ (I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) D.La)) : F) else 0 := by
  obtain ⟨hc, hc1⟩ := HalfPairing.cHalf_spec I hI
  have hz0 : z ≠ 0 := hz.ne_zero hN.ne'
  have hmk : ∀ u : D.La, z ^ D.EF (qRep (Submodule.Quotient.mk u :
      D.La ⧸ (I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) D.La))) (cHalf H I • v) =
      z ^ D.EF u (cHalf H I • v) := by
    intro u
    refine zpow_congr hN hz.pow_eq_one ?_
    rw [← LinearMap.sub_apply, ← map_sub]
    exact dvd_left D hp hc v ((Submodule.Quotient.eq _).1 (qRep_spec _))
  let χ : AddChar (D.La ⧸ (I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) D.La)) F :=
    { toFun := fun x => z ^ D.EF (qRep x) (cHalf H I • v)
      map_zero_eq_one' := by
        have := hmk 0
        rw [map_zero, LinearMap.zero_apply, zpow_zero] at this
        exact this
      map_add_eq_mul' := fun x y => by
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        rw [← Submodule.Quotient.mk_add, hmk, hmk, hmk, map_add (f := _), LinearMap.add_apply, zpow_add₀ hz0] }
  have hiff : χ = 0 ↔ v ∈ (I • ⊤ : Submodule (𝓞 E) D.La) := by
    constructor
    · intro h
      have h1 : ∀ y, (N : ℤ) ∣ D.EF (cHalf H I • v) y := fun y => by
        have h2 : χ (Submodule.Quotient.mk y) = 1 := by rw [h]; rfl
        have h3 : z ^ D.EF y (cHalf H I • v) = 1 := (hmk y).symm.trans h2
        rw [HalfPairing.ef_swap, dvd_neg]
        exact (hz.zpow_eq_one_iff_dvd _).1 h3
      have hNI : (N : 𝓞 E) ∈ I := by
        have : Ideal.span {(N : 𝓞 E)} ≤ I := hp ▸ (Ideal.mul_le_inf.trans inf_le_left)
        exact this (Ideal.subset_span rfl)
      have h4 := mem_of_modN D hNI (modN_of_dvd D hN h1)
      have : v = cHalf H I • v - (cHalf H I - 1) • v := by rw [sub_smul, one_smul, sub_sub_cancel]
      rw [this]
      exact sub_mem h4 (Submodule.smul_mem_smul hc1 trivial)
    · intro h
      ext x
      exact (hz.zpow_eq_one_iff_dvd _).2 (dvd_right D hp hc _ h)
  have := AddChar.sum_eq_ite χ
  rw [Nat.card_eq_fintype_card]
  simp only [← hiff]
  convert this using 2

theorem coeff_more_columns : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n m : ℕ) (d : DeltaDat Xo c n) (φ' : (Fin (n + m) → LevQ Dw d.l₂) → c.F), d.IsLev → Dw.p + Dw.q ≤ n → ∀ (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (ph : (Fin n → LaJ Xo c d) → c.F) (x₀ : Fin n → LaJ Xo c d) (ph' : (Fin (n + m) → LaJ Xo c d) → c.F) (x₀' : Fin (n + m) → LaJ Xo c d), d.PhiPin ph ψ x₀ → (withCoeff d φ').PhiPin ph' ψ x₀' → ∃ ζ : c.F, IsOfFinOrder ζ ∧ ∀ q : Fin (n + m) → LevQ Dw d.l₂, φ' q = ζ * d.φδ (fun b => q (Fin.castAdd m b)) * (if ∀ b : Fin m, levRep (q (Fin.natAdd n b)) ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La) then (Nat.card (LaI Xo c d) : c.F) ^ m else 0) := by
  intro E _ _ _ H Dw l Xo c n m d φ' hd hn ψ ph x₀ ph' x₀' hpin hpin'
  obtain ⟨-, huniq, adj, -, hadj⟩ := HalfPairing.halves_free_and_adjoint E H Dw l Xo c n d hd
  obtain ⟨-, hM, -, hMb, hI, -⟩ := hd
  obtain ⟨ha, hb, hc, hone, hspan, hφ⟩ := hpin
  obtain ⟨ha', hb', hc', hone', hspan', hφ'⟩ := hpin'
  have hM₂ : 0 < d.l₂.M := by have := d.l₂.three_le; omega
  have hpd : 0 < d.pd := Nat.pos_of_mul_pos_left (hM ▸ hM₂)
  have hIJ := half_prod hM hMb
  have hI0 : d.I ≠ ⊥ := by
    intro h
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at hIJ
    exact hpd.ne' (by exact_mod_cast hIJ)
  have hJ0 : d.I.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ ⊥ := by
    intro h
    rw [h, Ideal.mul_bot, eq_comm, Ideal.span_singleton_eq_bot] at hIJ
    exact hpd.ne' (by exact_mod_cast hIJ)
  haveI : Finite (𝓞 E ⧸ d.I.map (H.bar : 𝓞 E →+* 𝓞 E)) := Ideal.finiteQuotientOfFreeOfNeBot _ hJ0
  haveI : Finite (𝓞 E ⧸ d.I) := Ideal.finiteQuotientOfFreeOfNeBot _ hI0
  haveI := Dw.fin
  haveI := Dw.proj
  obtain ⟨e⟩ := HalfPairing.nonempty_equiv_quot (N := Dw.La) (d.I.map (H.bar : 𝓞 E →+* 𝓞 E)) _ Dw.rank
  obtain ⟨e'⟩ := HalfPairing.nonempty_equiv_quot (N := Dw.La) d.I _ Dw.rank
  haveI : Finite (LaJ Xo c d) := Finite.of_equiv _ e.toEquiv.symm
  haveI : Finite (LaI Xo c d) := Finite.of_equiv _ e'.toEquiv.symm
  haveI : Finite (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) :=
    Finite.of_injective (fun k : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d => (k : LaI Xo c d → LaI Xo c d))
      DFunLike.coe_injective
  have hcard : Nat.card (LaJ Xo c d) = Nat.card (LaI Xo c d) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_congr e'.toEquiv, Nat.card_fun, Nat.card_fun,
      Nat.card_congr (Ideal.quotientEquiv d.I _ (H.bar : 𝓞 E ≃+* 𝓞 E) rfl).toEquiv]
  have himg : ∀ {k : ℕ} (hk : Dw.p + Dw.q ≤ k) (x : Fin k → LaJ Xo c d),
      x '' {b | b.val < Dw.p + Dw.q} = Set.range (fun b : Fin (Dw.p + Dw.q) => x (Fin.castLE hk b)) := by
    intro k hk x
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b.val, hb⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨Fin.castLE hk b, b.2, rfl⟩
  have hn' : Dw.p + Dw.q ≤ n + m := hn.trans (Nat.le_add_right _ _)
  have hs₀ := (congrArg (Submodule.span (𝓞 E)) (himg hn x₀)).symm.trans hspan
  have hspan₁ : Submodule.span (𝓞 E) (x₀' '' {b | b.val < Dw.p + Dw.q}) = ⊤ := hspan'
  have hb₁ : ∀ x, ph' x ≠ 0 → Submodule.span (𝓞 E) (x '' {b | b.val < Dw.p + Dw.q}) = ⊤ := hb'
  have hs₀' := (congrArg (Submodule.span (𝓞 E)) (himg hn' x₀')).symm.trans hspan₁
  obtain ⟨g, hg, -⟩ := huniq _ _ hs₀ hs₀'
  have hy₀ : ph (fun b => x₀' (Fin.castAdd m b)) = (((ψ (adj g))⁻¹ : c.Fˣ) : c.F) := by
    have h1 := hc (adj g) g ((hadj _ _).2 rfl) x₀
    rw [hone, mul_one] at h1
    rw [← h1]
    exact ha _ _ fun b hb => (hg ⟨b.1, hb⟩).symm
  have hph : ∀ x : Fin (n + m) → LaJ Xo c d,
      ph' x = ((ψ (adj g) : c.Fˣ) : c.F) * ph (fun b => x (Fin.castAdd m b)) := by
    intro x
    by_cases hx : Submodule.span (𝓞 E) (Set.range (fun b : Fin (Dw.p + Dw.q) => x (Fin.castLE hn' b))) = ⊤
    · obtain ⟨g', hg', -⟩ := huniq _ _ hs₀' hx
      have h1 : ph' (fun b => g' (x₀' b)) = (((ψ (adj g'))⁻¹ : c.Fˣ) : c.F) * ph' x₀' :=
        hc' (adj g') g' ((hadj _ _).2 rfl) x₀'
      have h2 := hc (adj g') g' ((hadj _ _).2 rfl) (fun b => x₀' (Fin.castAdd m b))
      have h3 : ph' x = ph' (fun b => g' (x₀' b)) := ha' _ _ fun b hb => (hg' ⟨b.1, hb⟩).symm
      have h4 : ph (fun b => x (Fin.castAdd m b)) = ph (fun b => g' (x₀' (Fin.castAdd m b))) :=
        ha _ _ fun b hb => (hg' ⟨b.1, hb⟩).symm
      rw [h3, h4, h1, h2, hy₀, hone', mul_one, mul_left_comm, Units.mul_inv, mul_one]
    · have h1 : ph' x = 0 := by
        by_contra h
        exact hx ((congrArg (Submodule.span (𝓞 E)) (himg hn' x)).symm.trans (hb₁ x h))
      have h2 : ph (fun b => x (Fin.castAdd m b)) = 0 := by
        by_contra h
        exact hx ((congrArg (Submodule.span (𝓞 E)) (himg hn _)).symm.trans (hb _ h))
      rw [h1, h2, mul_zero]
  refine ⟨((ψ (adj g) : c.Fˣ) : c.F),
    (Units.coeHom c.F).isOfFinOrder (ψ.isOfFinOrder (isOfFinOrder_of_finite _)), fun q => ?_⟩
  set z : d.c₂.F := (⟨zeta d.l₂.M', d.c₂.zeta_mem⟩ : d.c₂.F) ^ (d.l₂.M' / d.pd) with hzdef
  have hz : IsPrimitiveRoot z d.pd := by
    have h1 : d.pd ∣ d.l₂.M' := (hM ▸ Dvd.intro_left _ rfl : d.pd ∣ d.l₂.M).trans (Nat.dvd_lcm_left _ _)
    have h2 : 0 < d.l₂.M' := Nat.lcm_pos hM₂ d.l₂.A_pos
    have h0 : IsPrimitiveRoot (zeta d.l₂.M') d.l₂.M' := Complex.isPrimitiveRoot_exp _ h2.ne'
    have h3 : IsPrimitiveRoot (⟨zeta d.l₂.M', d.c₂.zeta_mem⟩ : d.c₂.F) d.l₂.M' :=
      IsPrimitiveRoot.of_map_of_injective (f := algebraMap d.c₂.F ℂ) h0 (algebraMap d.c₂.F ℂ).injective
    exact h3.pow h2 (Nat.div_mul_cancel h1).symm
  have hz0 : z ≠ 0 := hz.ne_zero hpd.ne'
  haveI := Fintype.ofFinite (LaJ Xo c d)
  have h1 : d.eF (φ' q) = ∑ᶠ x : Fin (n + m) → LaJ Xo c d, d.eF (ph' x) *
      z ^ (∑ b, Dw.EF (qRep (x b)) (cHalf H d.I • levRep (q b))) := hφ' q
  apply d.eF.injective
  rw [h1, map_mul, map_mul, hφ, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  simp only [zpow_sum hz0, hph, map_mul, mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  rw [sum_append (fun y => d.eF (ph y)) (fun b a => z ^ Dw.EF (qRep a) (cHalf H d.I • levRep (q b)))]
  congr 1
  simp only [char_sum Dw hpd hIJ hI hz]
  rw [Finset.prod_ite_zero]
  simp only [Finset.mem_univ, forall_true_left, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  split_ifs
  · rw [map_pow, map_natCast, ← hcard]
  · rw [map_zero]

end GlobalTheory.MoreColumns
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselShape

theorem bessel_shape : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → (∃ w ∈ R.sm, ∃ v ∈ R.TK, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ≠ 0) → ∃ (l₀ La : R.H → Wp), IsBes R z π l₀ ∧ NzOn R l₀ ∧ ∀ w ∈ R.sm, ∀ v ∈ R.TK, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v = (innerSL ℂ (La v)).smulRight (l₀ w) := by
  intro hH k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDS hG hOK hS hne
  obtain ⟨w₀, hw₀, v₀, hv₀, hne⟩ := hne
  obtain ⟨ξ₀, hξ₀⟩ : ∃ ξ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w₀ v₀ ξ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne (ContinuousLinearMap.ext hcon)
  have hB := GlobalTheory.T.isBes_bessel_integral_of_gap hH k r ε mu h R Wp z π u μW μN μG νq hDS hG hOK hS
  have hnz : NzOn R (fun w => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v₀ ξ₀) := ⟨w₀, hw₀, hξ₀⟩
  set y₀ := be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w₀ v₀ ξ₀ with hy₀
  have hyy : ⟪y₀, y₀⟫_ℂ ≠ 0 := fun h0 => hξ₀ (inner_self_eq_zero.mp h0)
  refine ⟨fun w => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v₀ ξ₀,
    fun v => (starRingEnd ℂ (⟪y₀, y₀⟫_ℂ)⁻¹) •
      ContinuousLinearMap.adjoint (be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w₀ v) y₀,
    hB v₀ hv₀ ξ₀, hnz, ?_⟩
  intro w hw v hv
  ext ξ
  obtain ⟨c, hc⟩ := GlobalTheory.BesselLine.bessel_line hH k r ε mu R Wp z π u μW μN μG νq _ _ hDS hS
    (hB v₀ hv₀ ξ₀) hnz (hB v hv ξ)
  have h1 := hc w hw
  have h2 := hc w₀ hw₀
  rw [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left, h2, h1, ← hy₀, inner_smul_right, Complex.conj_conj]
  congr 1
  field_simp

end GlobalTheory.BesselShape
end

section

open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants

namespace GlobalTheory.GridAtPlace

theorem pow_absorb (C b : ℝ) (r : ℕ) (hb : 3 ≤ b) :
    (b ^ ((6 + C) * ((2 * r + 2 : ℕ) : ℝ))) ^ 2 * (5 / 4 : ℝ) ^ (3 * (r + 1)) ≤
      (b ^ ((7 + C) * ((2 * r + 2 : ℕ) : ℝ))) ^ 2 := by
  have hb0 : 0 < b := by linarith
  have e : b ^ ((7 + C) * ((2 * r + 2 : ℕ) : ℝ)) =
      b ^ ((6 + C) * ((2 * r + 2 : ℕ) : ℝ)) * b ^ (2 * r + 2) := by
    rw [← Real.rpow_natCast b (2 * r + 2), ← Real.rpow_add hb0]
    congr 1
    ring
  rw [e, mul_pow]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  rw [← pow_mul]
  calc (5 / 4 : ℝ) ^ (3 * (r + 1)) ≤ b ^ (3 * (r + 1)) :=
        pow_le_pow_left₀ (by norm_num) (by linarith) _
    _ ≤ b ^ ((2 * r + 2) * 2) := pow_le_pow_right₀ (by linarith) (by omega)

theorem main : ∀ (C b c : ℝ) (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ), 0 ≤ C → GridNum C b c P p.l0 lam → ((30 * (P.r + 1) ^ 2 + 6 : ℕ) : ℝ) ≤ |P.u p.l0 - P.u' p.l0| → (∀ y, 0 < Pst lam c y) ∧ 1 ≤ b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ)) ∧ ∃ Y : Finset ℝ, TBBx5.WaveGrid p (Pst lam c) Y (b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ))) 3 (3 * (P.r + 1)) ∧ TBBx5.LiftGrid p (Pst lam c) Y (b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ))) 3 (3 * (P.r + 1)) := by
  intro C b c P Wp Wq _ _ _ _ _ _ p lam hC hG hcut
  obtain ⟨hc, hcb, hkb, hu, hu', hlam, hgap, hint, hint', hT, hT'⟩ := hG
  have hb3 : 3 ≤ b := by linarith
  have hpos : ∀ y, 0 < Pst lam c y := fun y =>
    Finset.prod_pos (fun s _ => by have := abs_nonneg (y + lam s); linarith)
  have hone : 1 ≤ b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ)) :=
    Real.one_le_rpow (by linarith) (by positivity)
  refine ⟨hpos, hone, ?_⟩
  obtain ⟨Y, hcard, hsep, hon⟩ := GlobalTheory.exists_grid_five_apart_on_cut.1 P.u P.u' p.l0
    (3 * (P.r + 1) * (2 * P.r + 1)) (le_trans (by
      exact_mod_cast GlobalTheory.exists_grid_five_apart_on_cut.2 P.r) hcut)
  have hNQ := GlobalTheory.NormaliserCutBound.main C b c P p.l0 lam (Pst lam c) Y p.hP.1 hC p.hl.1 p.hl.2.1 hc hcb hkb
    hu hu' hlam (fun s t hst _ => hgap s t (by rw [Fin.lt_def]; omega)) hint hint' hT hT'
    (fun y => ⟨(hpos y).le, le_rfl⟩) (fun y hy => (hon y hy).1)
  exact ⟨Y, GlobalTheory.T.waveGrid_liftGrid_of_layout_normaliserBound P Wp Wq p (Pst lam c) Y _ _ 3 (3 * (P.r + 1)) hpos ⟨hsep, hcard, hon⟩ hNQ
    (by linarith) (pow_absorb C b P.r hb3)⟩

end GlobalTheory.GridAtPlace
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

namespace GlobalTheory.BetaCutLimit

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end GlobalTheory.BetaCutLimit

namespace GlobalTheory

open Filter Topology MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
private theorem exists_CCle_four_of_inCC_five {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ}
    {G : _root_.Formalism.FourierDecayAlt.B.Mat k r → E} (hG : _root_.Formalism.FourierDecayAlt.B.InCC A 5 G) : ∃ c, _root_.Formalism.FourierDecayAlt.B.CCle A 4 G c := by
  unfold _root_.Formalism.FourierDecayAlt.B.InCC _root_.Formalism.FourierDecayAlt.B.CCle at hG
  obtain ⟨c, h1, h2⟩ := hG
  exact ⟨c, _root_.Formalism.FourierDecayAlt.P.B5.ckOn_mono (by norm_num) h1, fun u v hu hv hl g hg => h2 u v hu hv (by omega) g hg⟩

open Filter Topology MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
private theorem measurableSet_Qset' (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) : MeasurableSet (_root_.Formalism.FourierDecayAlt.B.Qset Bs) :=
  measurableSet_lt measurable_const (_root_.Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _)

open Filter Topology MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
private theorem aestronglyMeasurable_Qset_indicator_hsVec (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq)
    {G : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp} (hG : ContinuousOn G (_root_.Formalism.FourierDecayAlt.B.GV k r)) :
    AEStronglyMeasurable ((_root_.Formalism.FourierDecayAlt.B.Qset Bs).indicator fun q => _root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs G (_root_.Formalism.FourierDecayAlt.B.gq Bs q)))
      volume := by
  refine (aestronglyMeasurable_indicator_iff (measurableSet_Qset' Bs)).2 ?_
  have h := _root_.Formalism.FourierDecayAlt.P.B7.jc_aesm_J Bs hG (1, 1)
  simp only [_root_.Formalism.FourierDecayAlt.P.bessel_function_trivial_index k r Wp Wq Bs G] at h
  exact _root_.Formalism.FourierDecayAlt.P.JCTx2.hsVec_cont'.comp_aestronglyMeasurable h

open Filter Topology MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
private theorem mem_Qset_iff_bcWeight_pos (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (q : (Fin r → ℂ) × ℂ) :
    q ∈ _root_.Formalism.FourierDecayAlt.B.Qset Bs ↔ 0 < _root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q := Iff.rfl

open Filter Topology MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
private theorem aestronglyMeasurable_weighted_pairing_lemma_2 (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq)
    {G G' : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp} (hG : ContinuousOn G (_root_.Formalism.FourierDecayAlt.B.GV k r))
    (hG' : ContinuousOn G' (_root_.Formalism.FourierDecayAlt.B.GV k r)) :
    AEStronglyMeasurable (fun q : (Fin r → ℂ) × ℂ =>
      (_root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q : ℂ) *
        inner ℂ (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs G (_root_.Formalism.FourierDecayAlt.B.gq Bs q))) (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs G' (_root_.Formalism.FourierDecayAlt.B.gq Bs q))))
      volume := by
  have h := (Complex.continuous_ofReal.measurable.comp (_root_.Formalism.FourierDecayAlt.P.B7.measurable_bcWeight (k := k) (r := r)
    (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z'))).aestronglyMeasurable.mul
    ((aestronglyMeasurable_Qset_indicator_hsVec Bs hG).inner (aestronglyMeasurable_Qset_indicator_hsVec Bs hG'))
  refine h.congr (Eventually.of_forall fun q => ?_)
  by_cases hq : q ∈ _root_.Formalism.FourierDecayAlt.B.Qset Bs
  · simp only [Pi.mul_apply, Function.comp_apply, Set.indicator_of_mem hq]
  · have hw : _root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q = 0 :=
      le_antisymm (not_lt.1 ((mem_Qset_iff_bcWeight_pos Bs q).not.1 hq)) (_root_.Formalism.FourierDecayAlt.P.JCTx2.bcWeight_nonneg' _ _ q)
    simp only [Pi.mul_apply, Function.comp_apply, hw, Complex.ofReal_zero, zero_mul]


open Filter Topology MeasureTheory in
theorem _root_.GlobalTheory.beta_cutF_tendsto : _root_.GlobalTheory.HCXi.BesselXiIntegrable → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (χ : ℝ → ℝ) (A : ℝ) (X F : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)), _root_.Formalism.FourierDecayAlt.C6.IsCut0 χ → _root_.Formalism.FourierDecayAlt.B.AB k r ≤ A → _root_.Formalism.FourierDecayAlt.B.InCC A 5 X → _root_.Formalism.FourierDecayAlt.B.InCC A 5 F → Tendsto (fun ε : ℝ => _root_.Formalism.FourierDecayAlt.B.beta Bs X (_root_.Formalism.FourierDecayAlt.D.cutF Bs χ F ε)) (𝓝[>] 0) (𝓝 (_root_.Formalism.FourierDecayAlt.B.beta Bs X F)) := by
  intro hHC k r Wp Wq _ _ _ _ _ _ Bs χ A X F hχ hA hX hF
  have hint := _root_.GlobalTheory.betaIntegrand_integrable_of_xiExists
    (_root_.GlobalTheory.HCXi.xiExists_of_besselXiIntegrable hHC) k r Wp Wq Bs A X F hA hX hF
  obtain ⟨M, -, hM⟩ := _root_.Formalism.FourierDecayAlt.P.JCTx2.cut_bound hχ
  have hχ' := hχ
  unfold _root_.Formalism.FourierDecayAlt.C6.IsCut0 at hχ'
  obtain ⟨hχc, -, hχ1⟩ := hχ'
  obtain ⟨cF, hcF⟩ := exists_CCle_four_of_inCC_five hF
  obtain ⟨cX, hcX⟩ := exists_CCle_four_of_inCC_five hX
  have hFc : ContinuousOn F (_root_.Formalism.FourierDecayAlt.B.GV k r) := _root_.Formalism.FourierDecayAlt.P.B7.jc_cont (A := A) (by unfold _root_.Formalism.FourierDecayAlt.B.InCC; exact ⟨cF, hcF⟩)
  have hXc : ContinuousOn X (_root_.Formalism.FourierDecayAlt.B.GV k r) := _root_.Formalism.FourierDecayAlt.P.B7.jc_cont (A := A) (by unfold _root_.Formalism.FourierDecayAlt.B.InCC; exact ⟨cX, hcX⟩)
  have hcut : ∀ ε q, (_root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q : ℂ) *
      inner ℂ (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs (_root_.Formalism.FourierDecayAlt.D.cutF Bs χ F ε) (_root_.Formalism.FourierDecayAlt.B.gq Bs q)))
        (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs X (_root_.Formalism.FourierDecayAlt.B.gq Bs q))) =
      (χ (_root_.Formalism.QuantumDeterminants.Gf k r Bs.z Bs.z' (_root_.Formalism.FourierDecayAlt.B.gq Bs q) / ε) : ℂ) *
        ((_root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q : ℂ) *
          inner ℂ (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs F (_root_.Formalism.FourierDecayAlt.B.gq Bs q))) (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs X (_root_.Formalism.FourierDecayAlt.B.gq Bs q)))) := by
    intro ε q
    rw [_root_.Formalism.FourierDecayAlt.P.JCTx2.JF_cutF, _root_.Formalism.FourierDecayAlt.P.JCTx2.hsVec_smul', inner_smul_left, Complex.conj_ofReal]
    ring
  refine tendsto_integral_filter_of_dominated_convergence
    (F := fun ε q => (_root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q : ℂ) *
      inner ℂ (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs (_root_.Formalism.FourierDecayAlt.D.cutF Bs χ F ε) (_root_.Formalism.FourierDecayAlt.B.gq Bs q)))
        (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs X (_root_.Formalism.FourierDecayAlt.B.gq Bs q))))
    (fun q => M * ‖(_root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q : ℂ) *
      inner ℂ (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs F (_root_.Formalism.FourierDecayAlt.B.gq Bs q))) (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs X (_root_.Formalism.FourierDecayAlt.B.gq Bs q)))‖)
    (Eventually.of_forall fun ε => ?_) (Eventually.of_forall fun ε => Eventually.of_forall fun q => ?_)
    (hint.norm.const_mul M) ?_
  · refine aestronglyMeasurable_weighted_pairing_lemma_2 Bs ?_ hXc
    have hcont : ContinuousOn (fun g => ((χ (_root_.Formalism.QuantumDeterminants.Gf k r Bs.z Bs.z' g / ε) : ℝ) : ℂ) • F g)
        (_root_.Formalism.FourierDecayAlt.B.GV k r) :=
      ((Complex.continuous_ofReal.comp (hχc.continuous.comp
        ((_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.Gf_cont Bs.z Bs.z').div_const ε))).continuousOn).smul hFc
    exact hcont
  · rw [hcut, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
  · filter_upwards [_root_.Formalism.FourierDecayAlt.P.B7.ae_mem_good_set_or_weight_zero Bs] with q hq
    simp_rw [hcut]
    rcases hq with hq | hq
    · have hG : 0 < _root_.Formalism.QuantumDeterminants.Gf k r Bs.z Bs.z' (_root_.Formalism.FourierDecayAlt.B.gq Bs q) := (_root_.Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom Bs (by exact hq)).2.2
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioc_mem_nhdsGT hG] with ε hε
      rw [hχ1 _ ((one_le_div hε.1).2 hε.2), Complex.ofReal_one, one_mul]
      rfl
    · simp only [hq, Complex.ofReal_zero, zero_mul, mul_zero]
      exact tendsto_const_nhds

end GlobalTheory
end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.besselNormSq_eq_const_mul_archPairing : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq), ∃ c : ℝ, 0 < c ∧ ∀ (A : ℝ) (F : Mx k r → (Wq →L[ℂ] Wp)), B.AB k r ≤ A → B.InCC A 5 F → B.normSq D F = ENNReal.ofReal (c * B.betaInf D F F).re := by
  first | exact @GlobalTheory.BesselNorm.normSq_eq_betaInf | exact GlobalTheory.BesselNorm.normSq_eq_betaInf | (intros; apply GlobalTheory.BesselNorm.normSq_eq_betaInf <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

theorem _root_.GlobalTheory.T.topDensity_bigCell_eq_prod_levelWeights_mul_topForm : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ), (∀ a, c a ≠ 0) → TBB.Ew p (fun _ => 1) H (P.r + 1) w (TBB.bigPt P.r c) = (∏ i : Fin (P.r + 1), KB.levW P ((i : ℕ) + 1) (c i)) * (p.RR H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c)).re ∧ (p.RR H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c)).im = 0 ∧ 0 ≤ (p.RR H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c)).re := by
  first | exact @GlobalTheory.TopDensity.topDensity_eq | exact GlobalTheory.TopDensity.topDensity_eq | (intros; apply GlobalTheory.TopDensity.topDensity_eq <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

theorem _root_.GlobalTheory.T.integrable_emptyWordDensity_decayingCoefficients : GlobalTheory.HCXi.BesselXiIntegrable → ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), B.CkOn ⊤ (B.GV P.k P.r) H → (∀ m : ℕ, B.InCC A m H) → Cc * ((P.r : ℝ) + 1) ^ 4 * (2 * (P.r : ℝ) + P.k + 1) ^ 3 ≤ A → Integrable (fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c)) := by
  first | exact @GlobalTheory.HatNF.EmptyWordL2.integrable_density_nil | exact GlobalTheory.HatNF.EmptyWordL2.integrable_density_nil | (intros; apply GlobalTheory.HatNF.EmptyWordL2.integrable_density_nil <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

theorem _root_.GlobalTheory.T.inverseEntry_smul_capelliEigenfunction_sum : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (lam : Fin (2 * r + k + 1) → ℝ) (A : ℝ) (i j : Fin (2 * r + k + 1)) (f : B.Mat k r → (Wq →L[ℂ] Wp)), Function.Injective lam → (B.CkOn ⊤ (B.GV k r) (f) ∧ ∀ m : ℕ, B.InCC (A) m (f)) → (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (f) g = ((∏ s, (Y + lam s) : ℝ) : ℂ) • (f) g) → ∃ Fi : Fin (2 * r + k + 1) → B.Mat k r → (Wq →L[ℂ] Wp), (∀ t, (B.CkOn ⊤ (B.GV k r) (Fi t) ∧ ∀ m : ℕ, B.InCC (A - 1) m (Fi t))) ∧ (∀ t, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi t) g = ((∏ s, (Y + (lam s - if s = t then 1 else 0)) : ℝ) : ℂ) • (Fi t) g)) ∧ ∀ g ∈ B.GV k r, g⁻¹ i j • f g = ∑ t, Fi t g := by
  first | exact @GlobalTheory.inv_entry_smul_eigen_split | exact GlobalTheory.inv_entry_smul_eigen_split | (intros; apply GlobalTheory.inv_entry_smul_eigen_split <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

theorem _root_.GlobalTheory.T.capelliWordProduct_decayBound_uniform : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (s : ℂ) (w : List (Bool × ℝ)) (m : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ (A c : ℝ) (X : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) X → B.CCle A (m + w.length * (2 * r + k + 1)) X c → B.CCle A m (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) (K * c) := by
  first | exact @GlobalTheory.capelli_fold_ccle | exact GlobalTheory.capelli_fold_ccle | (intros; apply GlobalTheory.capelli_fold_ccle <;> assumption)
end
