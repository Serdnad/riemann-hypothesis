module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.EqOfIndexTwo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.GdIffIndex
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem dx_cc (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] :
    ∃ σ : G ℚ Ω, ∃ φ : Ω →+* ℂ, ∀ x, φ (σ x) = starRingEnd ℂ (φ x) := by
  obtain ⟨σ, h⟩ := exists_isConjOm (E := ℚ) (Ω := Ω)
  exact ⟨AlgEquiv.ofRingEquiv (f := σ) fun x => by rw [eq_ratCast (algebraMap ℚ Ω), map_ratCast], h⟩

private theorem dx_ker (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω]
    [IsGalois ℚ K] (σ : G ℚ Ω) : AlgEquiv.restrictNormalHom (F := ℚ) K σ = 1 ↔ σ ∈ galOf ℚ K Ω := by
  have h : ∀ x : K, algebraMap K Ω (AlgEquiv.restrictNormalHom (F := ℚ) K σ x) = σ (algebraMap K Ω x) :=
    fun x => AlgEquiv.restrictNormal_commutes σ K x
  refine ⟨fun h1 x => ?_, fun h1 => AlgEquiv.ext fun x => (algebraMap K Ω).injective ?_⟩
  · rw [← h, h1]; rfl
  · rw [h, h1]; rfl

private theorem dx_eta (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω]
    [IsGalois ℚ K] (h2 : Module.finrank ℚ K = 2) : ∃ η : G ℚ Ω →* ℤˣ, η.ker = galOf ℚ K Ω := by
  have hc : Nat.card Gal(K/ℚ) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  have hz : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
  let e : Gal(K/ℚ) ≃* ℤˣ := mulEquivOfPrimeCardEq hc hz
  refine ⟨e.toMonoidHom.comp (AlgEquiv.restrictNormalHom (F := ℚ) K), Subgroup.ext fun σ => ?_⟩
  rw [← dx_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
  exact map_eq_one_iff e e.injective

private theorem dx_unr (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K]
    [Algebra K Ω] [IsGalois ℚ K] (l : ℕ) [hl : Fact l.Prime] (h : ¬ (l : ℤ) ∣ discr K) (A : ValuationSubring Ω)
    (hA : A.valuation (l : Ω) < 1) : Ine (F := ℚ) A ≤ galOf ℚ K Ω := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨p1, p2, p3, -⟩ := places K Ω l A
  obtain ⟨w, hw⟩ := p1 fun ht => (p2 ht).2 hA
  have hm : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal := (p3 w hw).1 hA
  have hb := (CF.unramIff.1 K l hl.out).1 ((CF.unramIff.2.1 K l hl.out).2 h) w hm
  intro σ hσ
  have h1 := Subgroup.mem_map_of_mem (CF.resTo ℚ K Ω) hσ
  rw [CF.ineAbs ℚ K Ω A w hw, hb, Subgroup.mem_bot] at h1
  exact (dx_ker Ω K σ).1 h1

private theorem dx_lc {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group M] (f : Γ →* M)
    (h : IsOpen (f.ker : Set Γ)) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hc : Continuous fun y : Γ => x⁻¹ * y := by fun_prop
  have h1 : (fun y : Γ => x⁻¹ * y) ⁻¹' (f.ker : Set Γ) ∈ nhds x :=
    (h.preimage hc).mem_nhds (by simp)
  filter_upwards [h1] with y hy
  have h2 : f (x⁻¹ * y) = 1 := hy
  rw [map_mul, map_inv, inv_mul_eq_one] at h2
  exact h2.symm

private theorem dx_zpow {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R)
    (Ψ : Γ → Rˣ) (h : AdicCont I fun g => (Ψ g : R)) (j : ℤ) : AdicCont I fun g => ((Ψ g ^ j : Rˣ) : R) := by
  classical
  intro N
  have key : (fun g => Ideal.Quotient.mk (I ^ N) ((Ψ g ^ j : Rˣ) : R)) =
      (fun x : R ⧸ I ^ N => if hx : IsUnit x then ((hx.unit ^ j : (R ⧸ I ^ N)ˣ) : R ⧸ I ^ N) else 0) ∘
        fun g => Ideal.Quotient.mk (I ^ N) (Ψ g : R) := by
    funext g
    have hx : IsUnit (Ideal.Quotient.mk (I ^ N) (Ψ g : R)) := (Ψ g).isUnit.map _
    have e : hx.unit = Units.map (Ideal.Quotient.mk (I ^ N)).toMonoidHom (Ψ g) := Units.ext rfl
    simp only [Function.comp_apply, dif_pos hx]
    rw [e, ← map_zpow]
    rfl
  rw [key]
  exact (h N).comp _

private theorem dx_alg {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] R]
    (I : Ideal R) (hI : (l : R) ∈ I) (f : Γ → ℤ_[l]) (hf : Continuous f) :
    AdicCont I fun g => algebraMap ℤ_[l] R (f g) := by
  intro n
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hpos : (0 : ℝ) < (l : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  filter_upwards [hf.continuousAt.eventually (Metric.closedBall_mem_nhds (f x) hpos)] with y hy
  rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton'] at hy
  obtain ⟨a, ha⟩ := hy
  rw [Ideal.Quotient.eq, ← map_sub, ← ha, map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hI n)

private theorem dx_lmem (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] : (l : O) ∈ IsLocalRing.maximalIdeal O := by
  have h : (IsLocalRing.maximalIdeal O).comap (algebraMap ℤ_[l] O) = IsLocalRing.maximalIdeal ℤ_[l] :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ_[l]) _)
  have h1 : (l : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
  rw [← h, Ideal.mem_comap, map_natCast] at h1
  exact h1

private theorem dx_dir (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {O : Type} [CommRing O] {N : ℕ} [NeZero N]
    (ψ : DirichletCharacter O N) : IsLocallyConstant (Chr.dirG ℚ Ω ψ) :=
  (dx_lc _ (Chr.clsFacts ℚ Ω N).1).comp ψ.toUnitHom

private theorem dx_cont (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter O N) : CharCont (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) := by
  refine dx_zpow _ _ fun n => ?_
  have h1 : AdicCont (IsLocalRing.maximalIdeal O) fun g => (chiO ℚ Ω l O g : O) :=
    dx_alg _ (dx_lmem l O) (fun g => (cycZ ℚ Ω l g : ℤ_[l])) (Units.continuous_val.comp (contTw ℚ Ω l).1)
  have h2 := dx_zpow _ _ h1 (e : ℤ) n
  have h3 := (dx_dir Ω ψ).comp fun u : Oˣ => Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n) (u : O)
  have h4 := h2.mul h3
  convert h4 using 1
  rfl

private theorem dx_place {Ω : Type} [Field Ω] [CharZero Ω] {l : ℕ} [hl : Fact l.Prime] (j : Ω →+* Om l) :
    (Loc.placeJ j).valuation (l : Ω) < 1 := by
  have h0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  have h1 : (l : Ω)⁻¹ ∉ Loc.placeJ j := by
    intro h
    have h2 : ‖j (l : Ω)⁻¹‖ ≤ 1 := h
    have h3 : j (l : Ω)⁻¹ = algebraMap ℚ_[l] (Om l) (l : ℚ_[l])⁻¹ := by simp
    rw [h3, PadicAlgCl.norm_extends, norm_inv, Padic.norm_p, inv_inv] at h2
    exact absurd hl.out.one_lt (by exact_mod_cast h2.not_gt)
  rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, not_le,
    one_lt_inv₀ ((Valuation.pos_iff _).2 h0)] at h1
  exact h1

theorem UpperTheory.V.U3.exists_dat :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N}, GD Ω K l e ψ → Nonempty (Dat Ω K c e ψ) := by
  intro Ω _ _ _ K _ _ _ l hl c N _ e ψ h
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h.quad⟩
  haveI : IsGalois ℚ K := inferInstance
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨η, hη⟩ := dx_eta Ω K h.quad
  obtain ⟨cc, hcc⟩ := dx_cc Ω
  obtain ⟨j⟩ := Loc.exists_emb (Ω := Ω) (v := l)
  obtain ⟨i1, -, i3, -, i5, -⟩ := Loc.iotaFacts j
  have hA : (Loc.placeJ j).valuation (l : Ω) < 1 := dx_place j
  have hI : ∀ g ∈ Loc.Iq l, Loc.iota j g ∈ Ine (F := ℚ) (Loc.placeJ j) := fun g hg => by
    rw [← i3] at hg; exact hg
  have hopen : IsOpen (((η.comp (Loc.iota j)).ker : Subgroup (GQ l)) : Set (GQ l)) := by
    have h1 := (galEmbTop ℚ K Ω).2.1
    rw [← hη] at h1
    exact h1.preimage i1.continuous
  obtain ⟨Kv, -, -, -, -, hKv, -⟩ := Loc.openField (η.comp (Loc.iota j)).ker.subtype hopen.isOpenEmbedding_subtypeVal
  rw [Subgroup.range_subtype] at hKv
  have hd : ¬ (l : ℤ) ∣ discr K := fun hd => h.l_cop (Dvd.dvd.mul_right (Int.natCast_dvd.1 hd) _)
  exact ⟨{
    gd := h
    η := η
    η_ker := hη
    cc := cc
    conj := hcc
    j := j
    ι := Loc.iota j
    ι_cont := i1.continuous
    ι_spec := fun σ x => (Loc.iota_spec j σ x).symm
    Kv := Kv
    Kv_spec := fun g => by rw [← hKv]; rfl
    η_unr := fun g hg => by
      have h1 := dx_unr Ω K l hd _ hA (hI g hg)
      rw [← hη] at h1
      exact h1
    τ_open := ((dx_dir Ω (comp l ψ)).comp_continuous i1.continuous).isOpen_fiber 1
    Ψ_cont := dx_cont Ω e ψ
    Ψ_I := fun g hg => by
      rw [← ((compIne Ω N l hl.out _ hA).2 c.O ψ).1 _ (hI g hg), Chr.Psi, MonoidHom.mul_apply, zpow_natCast,
        MonoidHom.pow_apply, Loc.cycA, ← i5 l]
      rfl }⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem locConst {Γ A : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group A] (ψ : Γ →* A)
    (h : IsOpen (ψ.ker : Set Γ)) : IsLocallyConstant ψ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker ψ h

private theorem open_galOf (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K]
    [Algebra K Ω] : IsOpen (galOf ℚ K Ω : Set (G ℚ Ω)) := by
  let b := Module.finBasis ℚ K
  have e : (galOf ℚ K Ω : Set (G ℚ Ω)) = ⋂ i, {σ : G ℚ Ω | σ (algebraMap K Ω (b i)) = algebraMap K Ω (b i)} := by
    ext σ
    simp only [Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe, mem_galOf]
    refine ⟨fun h i => h _, fun h x => ?_⟩
    have := b.ext (f₁ := σ.toLinearMap ∘ₗ (IsScalarTower.toAlgHom ℚ K Ω).toLinearMap)
      (f₂ := (IsScalarTower.toAlgHom ℚ K Ω).toLinearMap) h
    exact LinearMap.congr_fun this x
  rw [e]
  exact isOpen_iInter_of_finite fun i => isOpen_setOf_apply (F := ℚ) _ (fun t => t = algebraMap K Ω (b i))

private theorem cyc_ine (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (A : ValuationSubring Ω) (hA : ¬ A.valuation (l : Ω) < 1) {σ : G ℚ Ω} (hσ : σ ∈ Ine (F := ℚ) A) :
    cycZ ℚ Ω l σ = 1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  show cyclotomicCharacter Ω l σ.toRingEquiv = 1
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have hN0 : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ n) := ⟨hN0⟩
  have hspec := cyclotomicCharacter.spec (L := Ω) l σ.toRingEquiv ζ hζ.pow_eq_one
  have hv : ¬ A.valuation ((l ^ n : ℕ) : Ω) < 1 := by
    rw [Nat.cast_pow, map_pow, not_lt]
    exact one_le_pow₀ (not_lt.1 hA)
  have h1 : Chr.cls ℚ Ω (l ^ n) σ = 1 := (Chr.clsFacts ℚ Ω (l ^ n)).2.2.2.2 A hv hσ
  have h2 := Chr.cls_spec (l ^ n) σ ζ hζ.pow_eq_one
  rw [h1] at h2
  have h3 := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (hspec.symm.trans h2)
  rw [ZMod.val_injective _ h3]
  simp

private theorem tor_eq_one {R : Type} [CommRing R] {t : Rˣ} (h : tor R t = 1) : t = 1 := by
  have h1 := congrArg (fun x : GL (Fin 3) R => (x : Matrix (Fin 3) (Fin 3) R) 0 0) h
  apply Units.ext
  simpa [tor_val, wt1] using h1

private theorem diagonal_rep_eq_one_iff {Γ R : Type} [Group Γ] [CommRing R] (η : Γ →* ℤˣ) (Ψ : Γ →* Rˣ) (g : Γ) :
    r0 η Ψ g = 1 ↔ η g = 1 ∧ Ψ g = 1 := by
  refine ⟨fun h => ⟨congrArg SemidirectProduct.right h, tor_eq_one (congrArg SemidirectProduct.left h)⟩, fun h => ?_⟩
  refine SemidirectProduct.ext ?_ h.1
  rw [unitaryThreeReflection_left, h.2, map_one]
  rfl

private theorem bar_lc {O Γ : Type} [CommRing O] [IsLocalRing O] [Group Γ] [TopologicalSpace Γ] (Ψ : Γ →* Oˣ)
    (hΨ : CharCont Ψ) : IsLocallyConstant (barChar O Ψ) := by
  refine IsLocallyConstant.desc _ Units.val ?_ Units.val_injective
  have h := (hΨ 1 1).comp (Ideal.Quotient.factor (pow_one (maximalIdeal O)).le)
  simp only [zpow_one] at h
  exact h

theorem UpperTheory.V.U3.dat_facts :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ),
      D.cc * D.cc = 1 ∧ D.η D.cc = -1 ∧ D.Ψ D.cc = 1 ∧ IsLocallyConstant D.η ∧ IsLocallyConstant (barChar c.O D.Ψ) ∧
      (∀ g ∈ D.Kill, r0 D.η D.Ψ g = 1) ∧ IsUnit (2 : c.O) ∧ IsCMField K ∧ Continuous D.ΨQ ∧
      (∀ g, g ∈ D.Kill ↔ ∃ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 ∧ g ∈ Ine (F := ℚ) A ∧ D.η g = 1 ∧ Chr.dirG ℚ Ω ψ g = 1) ∧
      (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Ine (F := ℚ) A ≤ D.η.ker ∧
        ∃ s ∈ Ine (F := ℚ) A, IsUnit ((D.Ψ s : c.O) ^ 2 - 1)) := by
  intro Ω _ _ _ K _ _ _ l hl c N _ e ψ D
  obtain ⟨w, η', a, hlit⟩ := (gdIff Ω K l c e N ψ).1.1 D.gd
  have himag := D.gd.imag
  have hΨ : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := ℚ) A,
      D.Ψ g = Chr.dirG ℚ Ω ψ g := fun A hA g hg => by
    show (chiO ℚ Ω l c.O g) ^ (e : ℤ) * Chr.dirG ℚ Ω ψ g = _
    have : chiO ℚ Ω l c.O g = 1 := by
      unfold chiO
      rw [MonoidHom.comp_apply, cyc_ine Ω l A hA hg, map_one]
    rw [this, _root_.one_zpow, one_mul]
  have hkill : ∀ g, g ∈ D.Kill ↔ ∃ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 ∧ g ∈ Ine (F := ℚ) A ∧
      D.η g = 1 ∧ Chr.dirG ℚ Ω ψ g = 1 := fun g => by
    refine exists_congr fun A => and_congr_right fun hA => and_congr_right fun hg => ?_
    unfold rbar
    rw [diagonal_rep_eq_one_iff]
    refine and_congr_right fun _ => ?_
    unfold barChar
    rw [MonoidHom.comp_apply, hΨ A hA g hg]
    refine ⟨fun h => ?_, fun h => by rw [h, map_one]⟩
    refine (congrFacts Ω l c).2.2.2.1 _ 1 _ hlit.ord ?_ (one_pow _) ?_
    · rw [← MonoidHom.pow_apply, pow_orderOf_eq_one, MonoidHom.one_apply]
    · rw [← residue_eq_zero_iff, map_sub, sub_eq_zero, Units.val_one, map_one]
      exact congrArg Units.val h
  obtain ⟨φ, hφ⟩ := D.conj
  refine ⟨?_, ?_, hlit.par D.cc ⟨φ, hφ⟩, ?_, ?_, fun g hg => ?_, ?_, ?_, ?_, hkill, fun A hA => ?_⟩
  · refine AlgEquiv.ext fun x => φ.injective ?_
    rw [AlgEquiv.mul_apply, hφ, hφ]
    simp
  · refine (Int.units_eq_one_or _).resolve_left fun h => ?_
    have h1 : D.cc ∈ galOf ℚ K Ω := D.η_ker ▸ h
    refine IsTotallyComplex.complexEmbedding_not_isReal (φ.comp (algebraMap K Ω)) ?_
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hφ, h1 x]
  · exact locConst _ (D.η_ker ▸ open_galOf Ω K)
  · exact bar_lc _ D.Ψ_cont
  · obtain ⟨A, hA, hg, h1, h2⟩ := (hkill g).1 hg
    exact (diagonal_rep_eq_one_iff _ _ _).2 ⟨h1, (hΨ A hA g hg).trans h2⟩
  · have := (dvrFacts l c.O).2.2.2.2.2.2.2.2 2 fun h => D.gd.l_odd ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 h)
    simpa using this
  · have : Algebra.IsQuadraticExtension ℚ K := ⟨D.gd.quad⟩
    exact IsCMField.ofCMExtension ℚ K
  · have hf : Continuous (algebraMap ℤ_[l] (PadicAlgCl l)).toMonoidHom := by
      refine ((continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val).congr fun x => ?_
      exact (IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l) x).symm
    have h1 := ((hf.units_map _).comp (continuous_cycZ ℚ Ω l)).zpow (e : ℤ)
    have h2 := (((locConst _ (Chr.clsFacts ℚ Ω N).1).comp ψ.toUnitHom).comp
      (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom)).continuous
    refine (h1.mul h2).congr fun g => ?_
    show _ = Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (chiO ℚ Ω l c.O g ^ (e : ℤ) * Chr.dirG ℚ Ω ψ g)
    rw [map_mul, map_zpow]
    rfl
  · obtain ⟨h1, s, hs, h2⟩ := (gdLoc Ω K l c e N ψ w η' a hlit).1 A hA
    refine ⟨D.η_ker ▸ h1, s, hs, ?_⟩
    rw [Units.val_pow_eq_pow_val] at h2
    exact not_not.1 h2
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

theorem UpperTheory.V.U3.dat_loc :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ),
      ∃ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 ∧ D.ι.range = Dec (F := ℚ) A ∧ (Loc.Iq l).map D.ι = Ine (F := ℚ) A ∧
        Function.Injective D.ι ∧ (∀ x : Ω, x ∈ A ↔ ‖D.j x‖ ≤ 1) ∧ (∀ σ, cycZ ℚ Ω l (D.ι σ) = Loc.cyc l l σ) ∧
        ∀ A' : ValuationSubring Ω, A'.valuation (l : Ω) < 1 → ∃ g : G ℚ Ω,
          (∀ s, s ∈ Dec (F := ℚ) A' ↔ g⁻¹ * s * g ∈ Dec (F := ℚ) A) ∧ ∀ s, s ∈ Ine (F := ℚ) A' ↔ g⁻¹ * s * g ∈ Ine (F := ℚ) A := by
  intro Ω _ _ _ K _ _ _ l _ c N _ e ψ D
  have hι : D.ι = Loc.iota D.j := by
    ext σ x
    apply D.j.injective
    rw [Loc.iota_spec, ← D.ι_spec]
  obtain ⟨hemb, hrange, -, hmap, hcyc, -, -⟩ := Loc.iotaFacts D.j
  have hmem : ∀ x : Ω, x ∈ Loc.placeJ D.j ↔ Valued.v (D.j x) ≤ 1 := fun x => Iff.rfl
  have hA : (Loc.placeJ D.j).valuation (l : Ω) < 1 := by
    have hnot : (l : Ω)⁻¹ ∉ Loc.placeJ D.j := by
      rw [hmem, map_inv₀, map_natCast, map_inv₀, PadicAlgCl.valuation_p, not_le]
      have hl : (1 : NNReal) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
      simpa using hl
    by_contra h
    push_neg at h
    apply hnot
    have hle : (Loc.placeJ D.j).valuation (l : Ω) ≤ 1 :=
      ((Loc.placeJ D.j).valuation_le_one_iff _).2 (natCast_mem _ l)
    rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, le_antisymm hle h, inv_one]
  refine ⟨Loc.placeJ D.j, hA, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hι]; exact hrange
  · rw [hι]; exact hmap
  · rw [hι]; exact hemb.injective
  · intro x
    rw [hmem, ← NNReal.coe_le_coe, PadicAlgCl.valuation_coe, NNReal.coe_one]
  · intro σ
    rw [hι]
    exact DFunLike.congr_fun (hcyc l) σ
  · intro A' hA'
    obtain ⟨-, -, -, -, -, -, -, hconj, -, hact⟩ := ML.placeBasic Ω
    obtain ⟨g, rfl⟩ := hconj (Loc.placeJ D.j) A' l Fact.out hA hA'
    exact ⟨g, (hact _ g).1, (hact _ g).2.1⟩
end
