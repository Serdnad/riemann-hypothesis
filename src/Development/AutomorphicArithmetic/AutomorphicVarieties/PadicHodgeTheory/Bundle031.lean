module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle716
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComparisonIsFiltered
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle150
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.WtMatFix
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PosExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology NumberField IsDedekindDomain

private theorem de_mem {Ω : Type} [Field Ω] {v : ℕ} [Fact v.Prime] (j : Ω →+* Om v) (x : Ω) :
    x ∈ placeJ j ↔ ‖j x‖ ≤ 1 := by
  rw [placeJ, ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff, PadicAlgCl.valuation_def,
    ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]

private theorem de_ine {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {v : ℕ} [Fact v.Prime] {A : ValuationSubring Ω} {j : Ω →+* Om v} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)
    (g : ↥(Dec (F := F) A)) (σ : GQ v) (hi : ∀ y, σ (j y) = j ((g : G F Ω) y)) :
    σ ∈ Iq v ↔ (g : G F Ω) ∈ Ine (F := F) A := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have hnorm : ∀ y, ‖j y‖ < 1 ↔ A.valuation y < 1 := GlobalTheory.DecLocal.norm_lt_one_iff A j hj
  have hle : ∀ y, A.valuation y ≤ 1 ↔ ‖j y‖ ≤ 1 := fun y => by
    rw [A.valuation_le_one_iff y, hj]
  rw [(iqBasic v).2.2.1 σ]
  change _ ↔ (g : G F Ω) ∈ ValuationSubring.decompositionSubgroup F A ∧
    ∀ x, A.valuation x ≤ 1 → A.valuation ((g : G F Ω) x - x) < 1
  constructor
  · intro h
    refine ⟨g.2, fun x hx => ?_⟩
    rw [← hnorm, map_sub, ← hi]
    exact h (j x) ((hle x).mp hx)
  · rintro ⟨-, h⟩ y hy
    obtain ⟨x, hx⟩ := (GlobalTheory.PlaceBridge.denseRange_embedding j).exists_dist_lt y one_pos
    rw [dist_eq_norm] at hx
    have hjx : ‖j x‖ ≤ 1 := by
      have hm := IsUltrametricDist.norm_add_le_max y (-(y - j x))
      rw [norm_neg, ← sub_eq_add_neg, sub_sub_cancel] at hm
      exact hm.trans (max_le hy hx.le)
    have h3 : ‖σ (j x) - j x‖ < 1 := by
      rw [hi, ← map_sub, hnorm]
      exact h x ((hle x).mpr hjx)
    have hdecomp : σ y - y = (σ (y - j x) - (y - j x)) + (σ (j x) - j x) := by
      rw [map_sub]
      ring
    have h1 : ‖σ (y - j x)‖ < 1 := by
      rw [GlobalTheory.PlaceBridge.norm_algEquiv]
      exact hx
    have h5 : ‖σ (y - j x) - (y - j x)‖ < 1 := by
      have hm := IsUltrametricDist.norm_add_le_max (σ (y - j x)) (-(y - j x))
      rw [norm_neg, ← sub_eq_add_neg] at hm
      exact lt_of_le_of_lt hm (max_lt h1 hx)
    rw [hdecomp]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h5 h3)

private theorem de_cyc {F Ω : Type} [Field F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosed Ω]
    {v : ℕ} [Fact v.Prime] {j : Ω →+* Om v} (l : ℕ) [Fact l.Prime]
    (g : G F Ω) (σ : GQ v) (hi : ∀ y, σ (j y) = j (g y)) :
    UpperTheory.V.Loc.cyc v l σ = cycZ F Ω l g := by
  have hjinj : Function.Injective j := j.injective
  simp only [UpperTheory.V.Loc.cyc, ReciprocityTheory.Gal.cycZ, MonoidHom.comp_apply]
  apply Units.ext
  apply (PadicInt.ext_of_toZModPow).mp
  intro n
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have h1 := cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G F Ω) Ω g) ζ hζ.pow_eq_one
  have h2 := cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (GQ v) (Om v) σ) (j ζ)
    (by rw [← map_pow, hζ.pow_eq_one, map_one])
  rw [show (MulSemiringAction.toRingAut (G F Ω) Ω g) ζ = g ζ from rfl] at h1
  rw [show (MulSemiringAction.toRingAut (GQ v) (Om v) σ) (j ζ) = σ (j ζ) from rfl] at h2
  rw [hi, h1, ← map_pow] at h2
  have h4 := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (hjinj h2)
  exact (ZMod.val_injective _ h4).symm

theorem UpperTheory.V.Loc.decEmb :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω] {v : ℕ} [Fact v.Prime], (∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 F)), IsPlaceOver A w → ((v : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ j : Ω →+* Om v, placeJ j = A) ∧ ∀ j : Ω →+* Om v, (∃ w : HeightOneSpectrum (𝓞 F), IsPlaceOver (placeJ j) w ∧ ((v : ℕ) : 𝓞 F) ∈ w.asIdeal) ∧ ∃ φ : ↥(Dec (F := F) (placeJ j)) →* GQ v, IsOpenEmbedding φ ∧ (∀ g y, φ g (j y) = j ((g : G F Ω) y)) ∧ (∀ σ : GQ v, σ ∈ φ.range ↔ ∀ x : F, σ (j (algebraMap F Ω x)) = j (algebraMap F Ω x)) ∧ (∀ g, φ g ∈ Iq v ↔ (g : G F Ω) ∈ Ine (F := F) (placeJ j)) ∧ (∀ (l : ℕ) [Fact l.Prime] g, UpperTheory.V.Loc.cyc v l (φ g) = cycZ F Ω l (g : G F Ω)) ∧ ∀ w : HeightOneSpectrum (𝓞 F), IsPlaceOver (placeJ j) w → φ.range.index = locDeg w := by
  intro F Ω _ _ _ _ _ _ v _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  refine ⟨?_, ?_⟩
  · intro A w hA hw
    obtain ⟨j, hj⟩ := GlobalTheory.PlaceBridge.exists_embedding (l := v) F Ω w A hw hA
    refine ⟨j, ?_⟩
    ext x
    rw [de_mem, hj]
  · intro j
    have hj : ∀ x, x ∈ placeJ j ↔ ‖j x‖ ≤ 1 := de_mem j
    refine ⟨?_, ?_⟩
    · have hlt : (placeJ j).valuation ((v : ℕ) : Ω) < 1 := by
        rw [← GlobalTheory.DecLocal.norm_lt_one_iff _ j hj, map_natCast]
        exact GlobalTheory.PlaceBridge.norm_l_lt_one
      obtain ⟨w, hw, hpo⟩ := GlobalTheory.DecLocal.exists_place_below (p := v) (F := F) (placeJ j) hlt
      exact ⟨w, hpo, hw⟩
    · let K : FinExt v := ⟨IntermediateField.adjoin ℚ_[v] (Set.range fun x => j (algebraMap F Ω x)),
        GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap F Ω))⟩
      haveI : FiniteDimensional ℚ_[v] (K : IntermediateField ℚ_[v] (Om v)) := K.2
      have hK : (K : IntermediateField ℚ_[v] (Om v)) =
          IntermediateField.adjoin ℚ_[v] (Set.range fun x => j (algebraMap F Ω x)) := rfl
      obtain ⟨e, hec, hesc, he⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := F) hj K hK
      let φ : ↥(Dec (F := F) (placeJ j)) →* GQ v := (GK K).subtype.comp e.toMonoidHom
      have hφ : ∀ g, φ g = (e g : GQ v) := fun g => rfl
      have hrange : ∀ σ : GQ v, σ ∈ φ.range ↔ σ ∈ GK K := by
        intro σ
        constructor
        · rintro ⟨g, rfl⟩
          exact (e g).2
        · intro h
          exact ⟨e.symm ⟨σ, h⟩, by rw [hφ, MulEquiv.apply_symm_apply]⟩
      have hopen : IsOpen ((GK K : Subgroup (GQ v)) : Set (GQ v)) :=
        IntermediateField.fixingSubgroup_isOpen (K : IntermediateField ℚ_[v] (Om v))
      refine ⟨φ, ?_, fun g y => he g y, fun σ => by rw [hrange, GlobalTheory.PlaceBridge.mem_GK_iff (E := F) K hK],
        fun g => de_ine hj g (φ g) (he g), fun l _ g => de_cyc l (g : G F Ω) (φ g) (he g), fun w hw => ?_⟩
      · let h : ↥(Dec (F := F) (placeJ j)) ≃ₜ ↥(GK K) :=
          { e.toEquiv with continuous_toFun := hec, continuous_invFun := hesc }
        exact hopen.isOpenEmbedding_subtypeVal.comp h.isOpenEmbedding
      · have hr : φ.range = GK K := by
          ext σ
          exact hrange σ
        rw [hr, ← GlobalTheory.DecLocal.finrank_closure_eq_locDeg v F Ω (placeJ j) j hj w hw,
          IntermediateField.finrank_eq_fixingSubgroup_index]
        rfl
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

noncomputable section

namespace UpperTheory.V.Loc.CrUnipChar

variable {Q A B : Type} [Field Q] [CommRing A] [Algebra Q A] [AddCommGroup B] [Module Q B]

private def ctr (lam : A →ₗ[Q] Q) : A ⊗[Q] B →ₗ[Q] B :=
  (TensorProduct.lid Q B).toLinearMap ∘ₗ lam.rTensor B

private theorem ctr_tmul (lam : A →ₗ[Q] Q) (a : A) (b : B) : ctr lam (a ⊗ₜ[Q] b) = lam a • b := by
  simp [ctr]

private theorem eq_sum [Module.Finite Q A] (x : A ⊗[Q] B) :
    x = ∑ i, Module.finBasis Q A i ⊗ₜ[Q] ctr ((Module.finBasis Q A).coord i) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [ctr_tmul, ← smul_tmul, ← sum_tmul, Basis.coord_apply, Basis.sum_repr]
  | add y z hy hz =>
    simp only [map_add (f := _), tmul_add, Finset.sum_add_distrib]
    rw [← hy, ← hz]

private theorem mem_iff [Module.Finite Q A] (F : Submodule Q B) (x : A ⊗[Q] B) :
    x ∈ LinearMap.range (AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) F.subtype) ↔
      ∀ lam : A →ₗ[Q] Q, ctr lam x ∈ F := by
  constructor
  · rintro ⟨y, rfl⟩ lam
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simpa [ctr_tmul] using F.smul_mem _ b.2
    | add y z hy hz => simpa only [map_add (f := _)] using F.add_mem hy hz
  · intro h
    rw [eq_sum x]
    exact Submodule.sum_mem _ fun i _ => ⟨Module.finBasis Q A i ⊗ₜ ⟨_, h ((Module.finBasis Q A).coord i)⟩, by simp⟩

private theorem ctr_map (lam : A →ₗ[Q] Q) (u : A) (s : B →ₗ[Q] B) (x : A ⊗[Q] B) :
    ctr lam (AlgebraTensorModule.map (u • (LinearMap.id : A →ₗ[A] A)) s x) =
      s (ctr lam x) + s (ctr (lam ∘ₗ LinearMap.mulLeft Q (u - 1)) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [ctr_tmul, sub_mul, sub_smul]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]; abel

private theorem step [Module.Finite Q A] {G : Type} (u : G → A) (hu : ∀ g, IsNilpotent (u g - 1))
    (s : G → B →ₗ[Q] B) (F F' : Submodule Q B) (hs : ∀ g, ∀ b ∈ F', s g b ∈ F')
    (hT : ∀ b ∈ F, (∀ g, s g b - b ∈ F') → b ∈ F') (x : A ⊗[Q] B)
    (hx : ∀ g, AlgebraTensorModule.map (u g • (LinearMap.id : A →ₗ[A] A)) (s g) x = x)
    (hF : ∀ lam : A →ₗ[Q] Q, ctr lam x ∈ F) (lam : A →ₗ[Q] Q) : ctr lam x ∈ F' := by
  haveI : IsNoetherianRing A := isNoetherian_of_tower Q inferInstance
  obtain ⟨k, hk⟩ := IsNoetherianRing.isNilpotent_nilradical A
  have key : ∀ (j : ℕ) (lam : A →ₗ[Q] Q), (∀ a ∈ nilradical A ^ j, lam a = 0) → ctr lam x ∈ F' := by
    intro j
    induction j with
    | zero =>
      intro lam h
      have : lam = 0 := LinearMap.ext fun a => h a (by simp)
      simp [this, ctr]
    | succ j ih =>
      intro lam h
      refine hT _ (hF lam) fun g => ?_
      have e := ctr_map lam (u g) (s g) x
      rw [hx g] at e
      have h2 := hs g _ (ih (lam ∘ₗ LinearMap.mulLeft Q (u g - 1)) fun a ha => h _ (by
        rw [pow_succ']
        exact Ideal.mul_mem_mul (mem_nilradical.2 (hu g)) ha))
      have e2 : s g (ctr lam x) - ctr lam x = -s g (ctr (lam ∘ₗ LinearMap.mulLeft Q (u g - 1)) x) := by
        rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, ← e, sub_self]
      rw [e2]
      exact F'.neg_mem h2
  refine key k lam fun a ha => ?_
  rw [hk] at ha
  rw [(Submodule.mem_bot _).1 ha, map_zero]

private theorem eq_one_of_pow [CharZero Q] {u : A} (hu : IsNilpotent (u - 1)) {n : ℕ} (hn : n ≠ 0)
    (h : u ^ n = 1) : u = 1 := by
  have h1 : IsNilpotent (∑ i ∈ Finset.range n, (u ^ i - 1)) := by
    refine isNilpotent_sum fun i _ => ?_
    obtain ⟨c, hc⟩ := sub_one_dvd_pow_sub_one u i
    rw [hc]
    exact (Commute.all _ _).isNilpotent_mul_right hu
  have h2 : IsUnit ((n : ℕ) : A) := by
    rw [← map_natCast (algebraMap Q A)]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn)).map _
  have h3 : IsUnit (∑ i ∈ Finset.range n, u ^ i) := by
    have := h1.isUnit_add_left_of_commute h2 (Commute.all _ _)
    simpa [Finset.sum_sub_distrib] using this
  have h4 := geom_sum_mul u n
  rw [h, sub_self] at h4
  exact sub_eq_zero.1 (h3.mul_right_eq_zero.1 h4)

private theorem fil {l : ℕ} [Fact l.Prime] {G : Type} [Group G] (φ : G →* GQ l) (K : FinExt l)
    (hK : φ.range = GK K) {A : Type} [CommRing A] [Algebra ℚ_[l] A] [Module.Finite ℚ_[l] A] (κ : G →* Aˣ)
    (hκ : ∀ g, IsNilpotent ((κ g : A) - 1)) :
    FilD φ (chRep κ) 0 = Ddr φ (chRep κ) ∧ FilD φ (chRep κ) 1 = ⊥ := by
  obtain ⟨T⟩ := tiedP l
  let F : ℤ → Submodule ℚ_[l] (Bdr l) := fun a => (((PP l).PD (botExt l)).Fil a).restrictScalars ℚ_[l]
  have hF : ∀ a b, b ∈ F a ↔ b ∈ ((PP l).PD K).Fil a := fun a b => by
    have := (PP l).PD_Fil (botExt l) K a
    exact Set.ext_iff.1 this b
  have hanti : Antitone F := antitone_int_of_succ_le fun a b hb =>
    (hF _ _).2 (((PP l).PD K).Fil_anti a ((hF _ _).1 hb))
  have up : ∀ x ∈ Ddr φ (chRep κ), ∀ n : ℤ, n ≠ 0 → (∀ lam, ctr lam x ∈ F n) →
      ∀ lam, ctr lam x ∈ F (n + 1) := by
    intro x hx n hn h
    refine step (fun g => (κ g : A)) hκ (fun g => ((PP l).actQdR (φ g)).toLinearMap) (F n) (F (n + 1))
      (fun g b hb => ?_) (fun b hb hg => ?_) x (fun g => ?_) h
    · have := ((PP l).PD K).Fil_G ⟨φ g, by rw [← hK]; exact ⟨g, rfl⟩⟩ _ _ ((hF _ _).1 hb)
      rw [(PP l).PD_actdR] at this
      exact (hF _ _).2 this
    · obtain ⟨Θ⟩ := GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL l _ _ T
      obtain ⟨c, -, -, h0, h1⟩ := GlobalTheory.DRFil.graded_invariants T Θ K n b ((hF _ _).1 hb) fun g => by
        obtain ⟨g', hg'⟩ : (g : GQ l) ∈ φ.range := by rw [hK]; exact g.2
        rw [(PP l).PD_actdR, ← hg']
        exact (hF _ _).1 (hg g')
      rw [h0 hn, sub_zero] at h1
      exact (hF _ _).2 h1
    · have := (Submodule.mem_iInf _).1 hx g
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
      exact this
  constructor
  · refine inf_eq_left.2 fun x hx => (mem_iff (F 0) x).2 ?_
    have ex : ∃ a : ℤ, ∀ lam, ctr lam x ∈ F a := by
      clear hx
      induction x using TensorProduct.induction_on with
      | zero => exact ⟨0, fun lam => by simp⟩
      | tmul a b =>
        obtain ⟨n, hn⟩ := ((PP l).PD K).Fil_exh b
        exact ⟨n, fun lam => by rw [ctr_tmul]; exact (F n).smul_mem _ ((hF _ _).2 hn)⟩
      | add y z hy hz =>
        obtain ⟨a, ha⟩ := hy
        obtain ⟨b, hb⟩ := hz
        exact ⟨min a b, fun lam => by
          rw [map_add (f := _)]
          exact (F _).add_mem (hanti (min_le_left _ _) (ha lam)) (hanti (min_le_right _ _) (hb lam))⟩
    obtain ⟨a, ha⟩ := ex
    rcases le_total 0 a with h | h
    · exact fun lam => hanti h (ha lam)
    have key : ∀ m, a ≤ m → m ≤ 0 → ∀ lam, ctr lam x ∈ F m := by
      intro m hm
      induction m, hm using Int.leInduction with
      | base => exact fun _ => ha
      | succ m hm ih => exact fun h => up x hx m (by omega) (ih (by omega))
    exact key 0 h le_rfl
  · refine eq_bot_iff.2 fun x hx => ?_
    have h1 := (mem_iff (F 1) x).1 hx.2
    have key : ∀ m : ℤ, 1 ≤ m → ∀ lam, ctr lam x ∈ F m := by
      intro m hm
      induction m, hm using Int.leInduction with
      | base => exact h1
      | succ m hm ih => exact up x hx.1 m (by omega) ih
    have h0 : ∀ lam, ctr lam x = 0 := fun lam => ((PP l).PD K).Fil_sep _ fun a =>
      (hF _ _).1 (hanti (le_max_left a 1) (key _ (le_max_right _ _) lam))
    rw [Submodule.mem_bot, eq_sum x]
    simp [h0]

end UpperTheory.V.Loc.CrUnipChar

open UpperTheory.V.Loc.CrUnipChar in
theorem UpperTheory.V.Loc.crUnipChar :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] [Module.Finite ℚ_[l] A] [TopologicalSpace A] [IsModuleTopology ℚ_[l] A] [IsTopologicalRing A] (κ : G →* Aˣ), Continuous (fun g => (κ g : A)) → (∀ g, IsNilpotent ((κ g : A) - 1)) → ∀ H : Subgroup G, IsOpen (H : Set G) → CrOn φ (chRep κ) H → ∀ g, φ g ∈ Iq l → κ g = 1 := by
  intro l _ G _ _ _ φ hφ A _ _ _ _ _ _ κ hc hκ H hH hcr g hg
  have hφ' : IsOpenEmbedding (φ.comp H.subtype) := hφ.comp hH.isOpenEmbedding_subtypeVal
  obtain ⟨K, -, -, -, -, hK, hi, -⟩ := openField (φ.comp H.subtype) hφ'
  haveI := K.2
  obtain ⟨f0, f1⟩ := fil (φ.comp H.subtype) K hK (κ.comp H.subtype) fun h => hκ h
  have hca : ReciprocityTheory.Gal.ContAction (chRep (κ.comp H.subtype)) := by
    unfold ReciprocityTheory.Gal.ContAction
    exact ((hc.comp continuous_subtype_val).comp continuous_fst).mul continuous_snd
  have hw := crWt0 (φ.comp H.subtype) hφ' (chRep (κ.comp H.subtype)) hca hcr f0 f1
  obtain ⟨n, hn, -, h, hh⟩ := (φ.comp H.subtype).range.exists_pow_mem_of_index_ne_zero
    (by rw [hi]; exact finrank_pos.ne') (φ g)
  have e : (h : G) = g ^ n := hφ.injective (by rw [map_pow]; exact hh)
  have h1 := LinearMap.congr_fun (hw h (by rw [hh]; exact (Iq l).pow_mem hg n)) 1
  have h2 : (κ g : A) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ← e]
    simpa [chRep] using h1
  exact Units.ext (eq_one_of_pow (Q := ℚ_[l]) (hκ g) hn.ne' h2)
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

theorem UpperTheory.torsionDatum_finiteCocycles_compare :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {η : GQ l →* ℤˣ} {Ψ : GQ l →* Eˣ} {H : Subgroup (GQ l)} {e : ℕ} (hD : TriDat η Ψ H e) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) {B' : Type} [CommRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [TopologicalSpace B'] [IsModuleTopology ℚ_[l] B'] [IsTopologicalRing B'] [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] ℚ_[l] B'] [Algebra E B'] [IsScalarTower ℚ_[l] E B'] (π' : B' →ₐ[E] E) (hπ' : ∀ a, π' a = 0 → IsNilpotent a) (p : B →ₐ[E] B'), Function.Surjective p → ∀ (T : Tor η B) (T' : Tor η B'), T.Good π Ψ → T'.Good π' Ψ → (∀ g i, p (T.t g i : B) = (T'.t g i : B')) → ∀ δ' ∈ UpperTheory.V.Loc.finiteCocycles (MonoidHom.id (GQ l)) (chRep T'.χ2), ∃ δ ∈ UpperTheory.V.Loc.finiteCocycles (MonoidHom.id (GQ l)) (chRep T.χ2), ∀ g, p (δ g) = δ' g := by
  intro hP l _ E _ _ _ _ _ η Ψ H e hD B _ _ _ _ _ _ _ _ _ _ π hπ B' _ _ _ _ _ _ _ _ _ _ π' hπ' p hp T T' hT hT'
    hTT δ' hδ'
  haveI : ContinuousConstSMul E B := contConstSMul_alg E
  haveI : ContinuousConstSMul E B' := contConstSMul_alg E
  haveI : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  have hc : ContAction (chRep T.χ2) := contAction_chRep (T.continuous_χ2 hD.ηlc hT.cont hT.cont_inv)
  have hc' : ContAction (chRep T'.χ2) := contAction_chRep (T'.continuous_χ2 hD.ηlc hT'.cont hT'.cont_inv)
  have hcE : ContAction (resCoef E (chRep T.χ2)) := hc
  have hcE' : ContAction (resCoef E (chRep T'.χ2)) := hc'
  have hid : IsOpenEmbedding (MonoidHom.id (GQ l)) := IsOpenEmbedding.id
  have hI : ∀ g ∈ H, g ∈ Iq l →
      T.χ2 g = Units.map (algebraMap E B : E →* B) (cycA l l E g ^ ((2 * e : ℕ) : ℤ)) := by
    intro g hg hgI
    have h : ∀ i, T.t g i = cycA l l B g ^ ((e : ℤ) * wt1 i) := by
      intro i
      apply Units.ext
      rw [hT.ine g hgI, hD.ΨH g hg hgI, ← algebraMap_cycA (E := E) (B := B),
        zpow_mul, zpow_natCast, ← map_pow (Units.map _),
        ← map_zpow (Units.map (algebraMap E B : E →* B))]
      rfl
    change Units.map _ (η g) * (T.t g 0 / T.t g 2) = _
    rw [hD.ηH g hg, map_one, one_mul, h 0, h 2, map_zpow, algebraMap_cycA, div_eq_mul_inv, ← zpow_sub]
    congr 1
    simp [wt1]
    ring
  have hpos : Positive (MonoidHom.id (GQ l)) (resCoef E (chRep T.χ2)) := by
    refine ⟨?_, ?_⟩
    · refine (((isCrys_isDR_restrict_openSubgroup _ hid _ hcE).2 H hD.isOpen).2).2 ?_
      have hH : IsOpenEmbedding ((MonoidHom.id (GQ l)).comp H.subtype) := hD.isOpen.isOpenEmbedding_subtypeVal
      have hcH : ContAction ((resCoef E (chRep T.χ2)).comp H.subtype : Representation E H B) :=
        (((T.continuous_χ2 hD.ηlc hT.cont hT.cont_inv).comp continuous_subtype_val).comp continuous_fst).mul
          continuous_snd
      refine (isCrys_isDR_restrict_openSubgroup _ hH _ hcH).1 (crUnr _ hH _ hcH ((2 * e : ℕ) : ℤ) fun g hg x => ?_)
      change (T.χ2 g : B) * x = _
      rw [hI g g.2 hg, Algebra.smul_def]
      rfl
    · refine UpperTheory.filtBy_restrictScalars_of_residual_characters π hπ _ _ (fun _ : Unit => (1 : B))
        (fun _ => (Units.map (π : B →* E)).comp T.χ2) ?_ (fun _ => ?_) (fun g _ => ?_)
      · simp [Ideal.span_singleton_one]
      · refine ⟨((2 * e : ℕ) : ℤ), by have := hD.e_pos; omega, H, hD.isOpen, fun g hg hgI => ?_⟩
        apply Units.ext
        change π (T.χ2 g : B) = _
        rw [hI g hg hgI]
        exact π.commutes _
      · rw [Ideal.smul_eq_mul, Ideal.mul_top, RingHom.mem_ker]
        change π ((T.χ2 g : B) * 1 - π (T.χ2 g : B) • (1 : B)) = 0
        simp
  have hχ : ∀ g, p (T.χ2 g : B) = (T'.χ2 g : B') := by
    intro g
    have h : ∀ i, Units.map (p : B →* B') (T.t g i) = T'.t g i := fun i => Units.ext (hTT g i)
    rw [Tor.χ2_apply, Tor.χ2_apply, map_mul, map_intCast, ← h 0, ← h 2, ← map_div]
    rfl
  obtain ⟨δ, hδ, hδp⟩ := (posExact hP _ hid _ _ hcE hcE' hpos p.toLinearMap (fun g x => by
      change p ((T.χ2 g : B) * x) = (T'.χ2 g : B') * p x
      rw [map_mul, hχ])).1 hp δ'
    ((z1fMap (MonoidHom.id (GQ l)) (chRep T'.χ2) (resCoef E (chRep T'.χ2))).2 LinearMap.id (fun _ _ => rfl) δ' hδ')
  exact ⟨δ, (z1fMap (MonoidHom.id (GQ l)) (resCoef E (chRep T.χ2)) (chRep T.χ2)).2 LinearMap.id (fun _ _ => rfl) δ hδ,
    fun g => congrFun hδp g⟩
end
