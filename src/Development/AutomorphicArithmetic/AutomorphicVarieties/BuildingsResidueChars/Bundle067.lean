module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle044
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle043
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle059
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle045
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HilbertClassFieldOfGlobalArtinReciprocity
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharParallelWeight
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Bundle002
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoAF
public import GroundTheory.GlobalFields.Adele.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
import Std.Tactic.BVDecide.Normalize.Prop
public import GroundTheory.GlobalFields.Adele.Bundle002

@[expose] public section

section

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.WeilDeligne in
theorem UpperTheory.weil_group_dense_in_galois_group :
    UpperTheory.V.Af.Wd.WeilDense := by
  intro F Ω _ _ _ _ _ w A h
  have hσ := isFrob_frob (h := h)
  have h1 := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω A w h ⟨_, hσ.1⟩ hσ
  have h2 : (Subgroup.zpowers (⟨_, hσ.1⟩ : Dec (F := F) A) ⊔
      (Ine (F := F) A).subgroupOf (Dec (F := F) A)) ≤ (Subgroup.inclusion (Weil_le_Dec h)).range := by
    refine sup_le ?_ fun x hx => ⟨⟨x, Ine_le_Weil h hx⟩, rfl⟩
    exact (Subgroup.zpowers_le).2 ⟨frob h, rfl⟩
  have h3 := Subgroup.topologicalClosure_mono h2
  rw [h1] at h3
  intro g
  exact h3 (Subgroup.mem_top g)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.Pst.DpstMap GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Wd

private theorem cw_cyc {l : ℕ} [Fact l.Prime] (L : FinExt l) (n : ℤ) :
    Continuous fun g : GQ l => (((cycL L g ^ n : (↥L.1)ˣ) : ↥L.1) : Om l) := by
  have h0 := UpperTheory.V.Loc.cycFacts l l
  have h1 : Continuous fun g : GQ l => (((cycL L g : (↥L.1)ˣ) : ↥L.1) : Om l) := by
    have : (fun g : GQ l => (((cycL L g : (↥L.1)ˣ) : ↥L.1) : Om l)) =
        fun g => algebraMap ℚ_[l] (Om l) (((Loc.cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := by
      funext g
      rw [← h0.2.2 g]
      rfl
    rw [this]
    have h2 : Continuous fun z : ℤ_[l] => (z : ℚ_[l]) := continuous_subtype_val
    exact (continuous_algebraMap ℚ_[l] (Om l)).comp (h2.comp (Units.continuous_val.comp h0.1))
  have : (fun g : GQ l => (((cycL L g ^ n : (↥L.1)ˣ) : ↥L.1) : Om l)) =
      fun g => (((cycL L g : (↥L.1)ˣ) : ↥L.1) : Om l) ^ n := by
    funext g
    rw [Units.val_zpow_eq_zpow_val]
    exact map_zpow₀ L.1.val _ _
  rw [this]
  exact h1.zpow₀ n fun g => Or.inl ((map_ne_zero L.1.val).2 (Units.ne_zero (cycL L g)))

private theorem cw_lc {l : ℕ} [Fact l.Prime] (K K' : FinExt l) {C : Type} [Group C] (χ : ↥(GK K) →* C)
    (hχ : ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → χ g = 1) : IsLocallyConstant χ := by
  have := K'.2
  have ho : IsOpen ((GK K' : Subgroup (GQ l)) : Set (GQ l)) := IntermediateField.fixingSubgroup_isOpen K'.1
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  refine ⟨{y | ((x⁻¹ * y : ↥(GK K)) : GQ l) ∈ GK K'}, ?_, ?_, fun y hy => ?_⟩
  · exact ho.preimage (continuous_subtype_val.comp (continuous_const.mul continuous_id))
  · simp
  · have := hχ _ hy
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    exact this.symm

private theorem cw_eta {l : ℕ} [Fact l.Prime] (K K' L : FinExt l) (κ χ : ↥(GK K) →* (↥L.1)ˣ) (m : ℤ)
    (hκc : Continuous (fun g => ((κ g : ↥L.1) : Om l)))
    (hK' : ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → χ g = 1) :
    ∃ η : ↥(GK K) →* (↥L.1)ˣ, (∀ g, κ g = cycL L (g : GQ l) ^ m * χ g * η g) ∧
      Continuous (fun g => ((η g : ↥L.1) : Om l)) := by
  let ε : ↥(GK K) →* (↥L.1)ˣ := (cycL L).comp (GK K).subtype
  refine ⟨κ * ε ^ (-m) * χ⁻¹, fun g => ?_, ?_⟩
  · change κ g = _ * (κ g * cycL L (g : GQ l) ^ (-m) * (χ g)⁻¹)
    rw [zpow_neg]
    generalize cycL L (g : GQ l) ^ m = a
    rw [mul_mul_mul_comm, mul_inv_cancel, mul_one, mul_comm (κ g), mul_inv_cancel_left]
  · have h3 : Continuous fun g => ((((χ g)⁻¹ : (↥L.1)ˣ) : ↥L.1) : Om l) :=
      ((cw_lc K K' χ hK').comp fun u => (((u⁻¹ : (↥L.1)ˣ) : ↥L.1) : Om l)).continuous
    exact (hκc.mul ((cw_cyc L (-m)).comp continuous_subtype_val)).mul h3

private theorem cw_line {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {w : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw)
    (L : FinExt l) (V : Type) [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
    [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V) (h1 : finrank ↥L.1 V = 1) (hV : IsPst P ρ)
    (u : V ⊗[ℚ_[l]] Bst P) (hmem : u ∈ Dpst P ρ) (hu0 : u ≠ 0) (e : ↥L.1) (he0 : e ≠ 0)
    (hu : e • (phiV P ↥L.1 V ^ resDeg l w) u = u) (σ : ↥(Weil h)) (s : ↥L.1)
    (hs : stRep P ρ (weilToGK Bw h σ) u = s • u) (y : WDSpace P ι ρ) :
    haveI := hV.finite; wdRho P ι Bw h hj ρ σ y = ι ((e⁻¹ ^ (-deg σ) * s : ↥L.1) : Om l) • y := by
  refine UpperTheory.weil_deligne_rank_one_line F Ω l P ι w A h O Bw hj L V ρ h1 hV ⟨u, hmem⟩ (fun h0 => hu0 (congrArg Subtype.val h0)) e⁻¹
    (inv_ne_zero he0) (Subtype.ext ?_) σ s (Subtype.ext hs) y
  have h1 : ((phiD P ρ ^ resDeg l w) ⟨u, hmem⟩).1 = (phiV P ↥L.1 V ^ resDeg l w) u := by
    rw [phiD, Module.End.pow_restrict]
    rfl
  rw [h1]
  change (phiV P ↥L.1 V ^ resDeg l w) u = e⁻¹ • u
  exact (eq_inv_smul_iff₀ he0).2 hu

private theorem cw_calc {k : Type} [Field k] (a κ c χ η : kˣ) (l : k) (m d : ℤ) (f : ℕ) (h1 : κ = c ^ m * χ * η)
    (h2 : η = a ^ d) :
    ((a : k) * l ^ (m * (f : ℕ)))⁻¹ ^ (-d) * (χ : k) = (l ^ f) ^ (m * d) * ((κ * c ^ (-m) : kˣ) : k) := by
  have h3 : κ * c ^ (-m) = a ^ d * χ := by
    rw [h1, h2, zpow_neg, mul_comm, mul_assoc (c ^ m), inv_mul_cancel_left, mul_comm]
  rw [h3, inv_zpow', neg_neg, mul_zpow, ← zpow_natCast, ← zpow_mul, ← zpow_mul, Units.val_mul,
    Units.val_zpow_eq_zpow_val, show m * (f : ℕ) * d = (f : ℕ) * (m * d) by ring]
  ring

private theorem cw_fin {l : ℕ} [Fact l.Prime] (ι : Om l ≃+* ℂ) (L : FinExt l) (f : ℕ) (n : ℤ) (x : ↥L.1) :
    ι (((((l : ↥L.1) ^ f) ^ n * x : ↥L.1)) : Om l) = ((l ^ f : ℕ) : ℂ) ^ n * ι (x : Om l) := by
  have h1 : L.1.val (((l : ↥L.1) ^ f) ^ n * x) = ((l : Om l) ^ f) ^ n * L.1.val x := by
    rw [map_mul, map_zpow₀, map_pow, map_natCast]
  refine (congrArg ι h1).trans ?_
  rw [map_mul, map_zpow₀, map_pow, map_natCast, Nat.cast_pow]
  rfl

private theorem cw_unr {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {w : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} (h : IsPlaceOver A w)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O)
    (hj : Induces Bw) {C : Type} [Group C] (η : ↥(GK Bw.Kw) →* C)
    (hηI : ∀ g : ↥(GK Bw.Kw), (g : GQ l) ∈ Loc.Iq l → η g = 1) (σ : ↥(Weil h)) :
    η (weilToGK Bw h σ) = η (weilToGK Bw h (frob h)) ^ deg σ := by
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
  have hτI : (weilToGK Bw h (ineIncl h τ) : GQ l) ∈ Loc.Iq l := by
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_
    have := weilToGK_frobUr hj (ineIncl h τ) (a := 0) (b := 0) (actsAs_zero_iff.mpr τ.2) ⟨x, hx⟩
    simpa using this
  conv_lhs => rw [hτ]
  rw [map_mul, map_mul, hηI _ hτI, mul_one, map_zpow, map_zpow]

theorem UpperTheory.cyclotomicWeilChar_properties :
    UpperTheory.V.Af.Wd.CharWD := by
  intro F Ω _ _ _ _ _ l _ ι w A h O _ _ _ Bw hj L κ χ m hκc hχ hI hκ σ y
  obtain ⟨K', hK'⟩ := hχ
  obtain ⟨η, hκη, hηc⟩ := cw_eta Bw.Kw K' L κ χ m hκc hK'
  have hηI : ∀ g : ↥(GK Bw.Kw), (g : GQ l) ∈ Loc.Iq l → η g = 1 := fun g hg =>
    mul_left_cancel ((hκη g).symm.trans ((hI g hg).trans (mul_one _).symm))
  obtain ⟨u, hu0, hu1, hu2⟩ := UpperTheory.weilDeligne_character_twist_period l Bw.Kw L κ χ η m hκη hηc hηI
  have hF := (UpperTheory.crystalline_period_ring_properties F Ω l w A h O Bw hj).1
  have hmem : u ∈ Dpst (Loc.PP l) (Loc.chRep κ) :=
    (mem_Dpst _ _).2 ⟨K', fun g hg => by rw [hu1, hK' g hg, Units.val_one, one_smul]⟩
  have hl : (l : ↥L.1) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have he0 : (η (weilToGK Bw h (frob h)) : ↥L.1) * (l : ↥L.1) ^ (m * (resDeg l w : ℕ)) ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (zpow_ne_zero _ hl)
  have key := cw_line (Loc.PP l) ι h Bw hj L ↥L.1 (Loc.chRep κ) (Module.finrank_self _) hκ u hmem hu0 _ he0
    (hu2 _ _ hF) σ _ (hu1 _) y
  have h3 := cw_calc _ _ _ _ _ (l : ↥L.1) m (deg σ) (resDeg l w) (hκη (weilToGK Bw h σ)) (cw_unr h Bw hj η hηI σ)
  have h4 := (congrArg (fun x : ↥L.1 => ι (x : Om l)) h3).trans (cw_fin ι L _ _ _)
  rw [← normV_eq_pow (hj.mem_placesOver h)] at h4
  exact key.trans (congrArg (fun z : ℂ => z • y) h4)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

private theorem not_mem_of_distinct_prime {K : Type} [Field K] [NumberField K] {p l : ℕ} (w : HeightOneSpectrum (𝓞 K)) (hp : p.Prime)
    (hl : l.Prime) (hlp : l ≠ p) (hw : (p : 𝓞 K) ∈ w.asIdeal) : (l : 𝓞 K) ∉ w.asIdeal := by
  intro h
  have hc : IsCoprime (l : 𝓞 K) (p : 𝓞 K) := Nat.Coprime.cast ((Nat.coprime_primes hl hp).2 hlp)
  obtain ⟨a, b, hab⟩ := hc
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left a h) (w.asIdeal.mul_mem_left b hw)))

private theorem admissible_twist_cyclotomic {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e N : ℕ) (ρ : G K Ω →* GL (Fin 3) (Qbar l)) (h : Adm3 ι e N ρ) :
    AdmK ι N ![(e : ℤ) - 1, -1, -(e : ℤ) - 1] (tw ρ (cycBar K Ω l)⁻¹) := by
  refine ⟨(UpperTheory.isIrr_twist_and_repIso_of_twist_repIso _ _ 3 _).1 ρ h.irr, h.aut, ?_, by decide⟩
  have h1 := UpperTheory.level_twist_cyclotomic_pow K Ω l 3 N _ ρ (-1) h.level
  rw [zpow_neg_one] at h1
  convert h1 using 1
  funext i
  fin_cases i <;> simp <;> ring
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

open ReciprocityTheory.Neutral.Bridge.HCFR

private theorem UpperTheory.infPow_infIdele_neg_one_of_const_of_isReal {F : Type} [Field F] [NumberField F] (a : (F →+* ℂ) → ℤ)
    (a0 : ℤ) (ha : ∀ φ, a φ = a0) (w : InfinitePlace F) (hw : w.IsReal) :
    infPow a (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele F w (-1)) = (-1) ^ a0 := by
  have hcont : Continuous (Complex.ofRealHom.comp
      (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw)) :=
    Complex.continuous_ofReal.comp
      (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).continuous
  let i0 : {i : w.Completion →+* ℂ // Continuous i} := ⟨_, hcont⟩
  have huniq : ∀ i : {i : w.Completion →+* ℂ // Continuous i}, i = i0 := by
    intro i
    apply Subtype.ext
    ext x
    let E := NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hw
    let g : ℝ →+* ℂ := (i : w.Completion →+* ℂ).comp
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
    have hg : Continuous g := i.2.comp E.symm.continuous
    have hg' := Complex.ringHom_eq_ofReal_of_continuous hg
    have hx : (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
        (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw x) = x :=
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm_apply_apply x
    have := congrArg (fun f : ℝ →+* ℂ => f
      (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw x)) hg'
    simp only [g, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hx] at this
    simpa [i0] using this
  unfold infPow
  rw [Finset.prod_eq_single w]
  · rw [finprod_eq_single _ i0 (fun j hj => absurd (huniq j) hj)]
    rw [ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_fst_self, ha]
    simp
  · intro w' _ hne
    simp [ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_fst_ne F w w' hne]
  · intro h
    exact absurd (Finset.mem_univ w) h

theorem UpperTheory.sign_at_infinity_of_parallel_weight :
    UpperTheory.V.Af.Sol.Parallel → UpperTheory.V.Af.Sol.SignOf := by
  intro hP F Ω _ _ _ _ _ _ l _ ι χ μ hμ hs v v'
  obtain ⟨-, art, a, hart, halg, hlad⟩ := hμ
  have hpar := hP F χ a halg
  have key : ∀ w : InfinitePlace F, ∃ c : _root_.Formalism.ConjugateSelfDual.G F Ω, IsConjEl c ∧
      ((χ.locInf w (-1) : ℂˣ) : ℂ) = ι (μ c) * (-1) ^ (a v.embedding) := by
    intro w
    obtain ⟨j, c, hc, hw⟩ := GlobalTheory.HilbertFromArtin.exists_conj (Ω := Ω) w
      (NumberField.IsTotallyReal.isReal w)
    refine ⟨c, ⟨j, hc⟩, ?_⟩
    have hart' := GlobalTheory.HilbertFromArtin.art_sign_eq hart j c hc
    rw [hw] at hart'
    have h := hlad _ c hart'
    have hl : lPow ι a (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele F w (-1)) = 1 := by
      simp [GlobalTheory.HeckeGal.lPow, ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_snd, GlobalTheory.HeckeGal.locPow_one]
    rw [hl, mul_one, UpperTheory.infPow_infIdele_neg_one_of_const_of_isReal a (a v.embedding) (fun φ => hpar φ v.embedding) w
      (NumberField.IsTotallyReal.isReal w)] at h
    have h2 := congrArg ι h
    rw [RingEquiv.apply_symm_apply] at h2
    rw [h2]
    have hne : ((-1 : ℂ) ^ (a v.embedding)) ≠ 0 := zpow_ne_zero _ (by norm_num)
    rw [mul_assoc, inv_mul_cancel₀ hne, mul_one]
    rfl
  obtain ⟨c, hc, hcv⟩ := key v
  obtain ⟨c', hc', hcv'⟩ := key v'
  apply Units.ext
  rw [hcv, hcv', hs c c' hc hc']
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.adelicSolution_parallel :
    UpperTheory.V.Af.Sol.Parallel := by
  intro F _ _ _ χ a ha
  exact UpperTheory.heckeChar_parallel_weight F χ a ha
end

section

open UpperTheory.V.Sd.Eis

open NumberField IsDedekindDomain GlobalTheory.CuspRep in
private theorem cont_nilM (F : Type) [Field F] [NumberField F] :
    Continuous (fun x : NA F => (nilM x : Matrix (Fin 2) (Fin 2) (Ad F))) := by
  refine continuous_matrix fun i j => ?_
  simp only [nilM, Matrix.of_apply]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

open NumberField IsDedekindDomain GlobalTheory.CuspRep in
theorem UpperTheory.eisenstein_constantTerm_upperBlock :
    UpperTheory.V.Sd.Eis.BlockTop := by
  intro F _ _
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
    exact (Set.countable_range _).to_subtype
  · obtain ⟨C, hC, hx⟩ := GroundTheory.Global.exists_isCompact_forall_exists_sub_mem F
    have hD : IsCompact (C ×ˢ (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) :
        Set (Ad F)) := hC.prod (GroundTheory.Global.isCompact_integralFiniteAdeles F)
    refine ⟨_, isCompact_univ_pi fun _ : BlockIx 2 1 => hD, fun x => ?_⟩
    choose k hk using hx
    exact ⟨fun p => algebraMap F (Ad F) (k (x p)), ⟨fun p => k (x p), rfl⟩, fun p _ => hk (x p)⟩
  · exact Units.continuous_iff.2 ⟨continuous_const.add (cont_nilM F), continuous_const.sub (cont_nilM F)⟩
  · intro x
    refine Units.ext ?_
    change 1 + nilM x = !![((1 : (Ad F)ˣ) : Ad F), x ⟨(0, 1), by decide⟩; 0, 1]
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [nilM]
end

section

open UpperTheory.V.Sd.Eis

private theorem complex_linear_combination_eq_half_of_relations (a b c d e f x y z w κ : ℂ) (hc : c - Complex.I * d ≠ 0)
    (h1 : a * e + b * f = 1) (h2 : c * e + d * f = 0)
    (hp1 : x + w = 0) (hp2 : y - z = Complex.I * κ) (hp3 : x - w = Complex.I * (y + z))
    (hE : e * (c * x + d * y) + f * (c * z + d * w) = 0) :
    e * (a * x + b * y) + f * (a * z + b * w) = κ / 2 := by
  have hw : w = -x := by linear_combination hp1
  have hs : y + z = -2 * Complex.I * x := by
    linear_combination (norm := skip) (Complex.I) * hp3 + (Complex.I) * hp1
    ring_nf; simp only [Complex.I_sq]; ring_nf
  have hy : y = -Complex.I * x + Complex.I * κ / 2 := by
    linear_combination (1/2) * hs + (1/2) * hp2
  have hz : z = -Complex.I * x - Complex.I * κ / 2 := by
    linear_combination (1/2) * hs - (1/2) * hp2
  subst hw hy hz
  apply mul_left_cancel₀ hc
  linear_combination (norm := skip) (a - Complex.I * b) * hE
    + (-κ/2) * (Complex.I * d - c) * h1 + (-κ/2) * (a - Complex.I * b) * h2
  ring_nf; simp only [Complex.I_sq, Complex.I_pow_four]; ring_nf

theorem UpperTheory.eisenstein_lie_algebra_action :
    UpperTheory.V.Sd.Eis.LieAlg := by
  intro h p κ hp1 hp2 hp3 hE
  have hMN : (h : Matrix (Fin 2) (Fin 2) ℝ) * ((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e1 := congrFun (congrFun hMN 0) 0
  have e2 := congrFun (congrFun hMN 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e1 e2
  have hdet : (h : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hMN
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  rw [Matrix.det_fin_two] at hdet
  have hc : ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) - Complex.I * ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) ≠ 0 := by
    intro h0
    have hre := congrArg Complex.re h0
    have him := congrArg Complex.im h0
    simp at hre him
    apply hdet
    rw [hre, him]; ring
  have hent : ∀ (k i j : Fin 2),
      (((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.single (0 : Fin 2) k (1 : ℝ)
        * (h : Matrix (Fin 2) (Fin 2) ℝ)) i j
        = ((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i 0 * (h : Matrix (Fin 2) (Fin 2) ℝ) k j := by
    intro k i j
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]
  simp only [hent, Fin.sum_univ_two, Complex.ofReal_mul] at hE ⊢
  have e1' : ((h : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) * (((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ)
      + ((h : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) * (((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) = 1 := by
    exact_mod_cast e1
  have e2' : ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) * (((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ)
      + ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) * (((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) = 0 := by
    exact_mod_cast e2
  have := complex_linear_combination_eq_half_of_relations _ _ _ _ _ _ (p 0 0) (p 0 1) (p 1 0) (p 1 1) κ hc e1' e2' hp1 hp2 hp3
    (by linear_combination hE)
  linear_combination this
end

section

open UpperTheory.V.Sd.Eis

private theorem UpperTheory.exists_bound_of_continuous_periodic_cocompact (A : Type) [AddCommGroup A] [TopologicalSpace A] (Γ : AddSubgroup A)
    (hC : Cocpt Γ) (g : A → ℝ → ℂ) (hg : Continuous (Function.uncurry g))
    (hgp : ∀ γ ∈ Γ, ∀ (x : A), g (γ + x) = g x) :
    ∃ M : ℝ, ∀ x : A, ∀ t ∈ Set.Icc (-1 : ℝ) 1, ‖g x t‖ ≤ M := by
  obtain ⟨C, hCc, hCx⟩ := hC
  have hK : IsCompact (C ×ˢ Set.Icc (-1 : ℝ) 1) := hCc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨M, fun x t ht => ?_⟩
  obtain ⟨γ, hγ, hxγ⟩ := hCx x
  have h1 : g x = g (x - γ) := by
    have := hgp γ hγ (x - γ)
    rw [add_sub_cancel] at this
    exact this
  rw [h1]
  exact hM (x - γ, t) ⟨hxγ, ht⟩

theorem UpperTheory.eisenstein_period_derivative :
    UpperTheory.V.Sd.Eis.PerDeriv := by
  intro A _ _ _ _ _ _ Γ hC μ D hDt f f' hf hf' hfp hf'p hd
  obtain ⟨M, hM⟩ := UpperTheory.exists_bound_of_continuous_periodic_cocompact A Γ hC f' hf' hf'p
  obtain ⟨N, hN⟩ := UpperTheory.exists_bound_of_continuous_periodic_cocompact A Γ hC f hf hfp
  have hslice : ∀ (g : A → ℝ → ℂ), Continuous (Function.uncurry g) → ∀ t : ℝ, Continuous (fun x => g x t) :=
    fun g hg t => hg.comp (continuous_id.prodMk continuous_const)
  haveI hfin : MeasureTheory.IsFiniteMeasure (μ.restrict D) := MeasureTheory.isFiniteMeasure_restrict.2 hDt
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict D)
    (F := fun t x => f x t) (F' := fun t x => f' x t) (x₀ := (0 : ℝ)) (bound := fun _ => M)
    (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall fun t => (hslice f hf t).aestronglyMeasurable)
    (MeasureTheory.Measure.integrableOn_of_bounded (M := N) hDt (hslice f hf 0).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hN x 0 ⟨by norm_num, by norm_num⟩))
    (hslice f' hf' 0).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x t ht => hM x t ht)
    (MeasureTheory.integrable_const M)
    (Filter.Eventually.of_forall fun x t _ => hd x t)
  exact key.2
end

section

open UpperTheory.V.Sd.Eis
open NumberField Topology Matrix Neutral.B1 GlobalTheory.CuspRep Formalism.L2.Host UpperTheory.V

private theorem cont_map {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    (a : ℕ) (f : R →+* S) (hf : Continuous f) :
    Continuous (fun g : GL (Fin a) R => GeneralLinearGroup.map f g) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_map hf
  · exact Units.continuous_coe_inv.matrix_map hf

private theorem cont_pInf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] : Continuous (TR.pInf F) := by
  have h : Continuous (TR.infEq F).symm :=
    continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
        (continuous_apply w)
  exact h.comp continuous_fst

theorem UpperTheory.eisenstein_smooth_continuous :
    UpperTheory.V.Sd.Eis.SmCont := by
  intro F _ _ _ a φ hU
  have hy := cont_map a (TR.pInf F) (cont_pInf F)
  have hk := cont_map a (pFin F) continuous_snd
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  set k₀ := GeneralLinearGroup.map (pFin F) g₀ with hk₀
  have hy' : Continuous fun g : GA F a => TR.toL (GeneralLinearGroup.map (TR.pInf F) g).val :=
    (Units.continuous_val (M := Matrix (Fin a) (Fin a) (TR.Rinf F))).comp hy
  have hc : ContinuousAt (fun g : GA F a =>
      TR.chart φ.1 (finGL F a k₀) (TR.toL (GeneralLinearGroup.map (TR.pInf F) g).val)) g₀ :=
    ContinuousAt.comp (f := fun g : GA F a => TR.toL (GeneralLinearGroup.map (TR.pInf F) g).val)
      (TR.contDiffAt_chart φ.2 _ (TR.val_mem_invSet _)).continuousAt hy'.continuousAt
  refine hc.congr ?_
  have hk' : Continuous fun g : GA F a => k₀⁻¹ * GeneralLinearGroup.map (pFin F) g :=
    continuous_const.mul hk
  have hn : ∀ᶠ g : GA F a in 𝓝 g₀, TR.finRep F a (k₀⁻¹ * GeneralLinearGroup.map (pFin F) g) φ = φ := by
    refine (hU.preimage hk').mem_nhds ?_
    change TR.finRep F a (k₀⁻¹ * k₀) φ = φ
    rw [inv_mul_cancel, map_one]; rfl
  filter_upwards [hn] with g hg
  rw [TR.chart_val]
  have e := congrFun (congrArg Subtype.val hg) (finGL F a k₀ * TR.infGL F a (GeneralLinearGroup.map (TR.pInf F) g))
  rw [← e]
  change φ.1 (_ * finGL F a _) = _
  rw [← TR.infGL_comm, mul_assoc, ← map_mul, mul_inv_cancel_left, TR.infGL_mul_finGL]
end
