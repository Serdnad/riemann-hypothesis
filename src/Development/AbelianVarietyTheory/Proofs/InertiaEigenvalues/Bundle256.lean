module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.WeaklyAdmissibleFiltrations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle028
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle234
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH1LevelRepFormula
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle155

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory

open TensorProduct

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    (ρ : Representation LL G V)

theorem corHf_actVB_tmul (g : G) (v : V) (b : B) :
    actVB PD ρ g (v ⊗ₜ[Qp] b) = ρ g v ⊗ₜ[Qp] PD.actB g b := by
  simp [actVB]

noncomputable def corHfRepVB : Representation LL G (V ⊗[Qp] B) where
  toFun g := actVB PD ρ g
  map_one' := by
    ext v b
    simp [corHf_actVB_tmul]
  map_mul' g h := by
    ext v b
    simp [corHf_actVB_tmul]

def corHfRepO (O : Type) [CommRing O] [Algebra O LL] [Module O V] [IsScalarTower O LL V] :
    Representation O G V where
  toFun g := (ρ g).restrictScalars O
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousConstSMul LL V]

theorem index_smul_mem_HfD [CharZero LL] (L : Lattice (O := O) ρ) (hρ : ∀ g, Continuous (ρ g))
    (hρ' : ∀ x, Continuous fun g => ρ g x) (H : Subgroup G) [H.Normal] [H.FiniteIndex]
    (hH : IsOpen (H : Set G)) (Z f₀ : G → V) (hZ : ContinuousOn Z H)
    (hc : ∀ g ∈ H, ∀ h ∈ H, Z (g * h) = Z g + ρ g (Z h))
    (hX : ∃ X : V ⊗[Qp] B, ∀ h ∈ H, Z h ⊗ₜ[Qp] (1 : B) = actVB PD ρ h X - X)
    (h₀ : ∀ g h, f₀ (g * h) - (f₀ g + ρ g (f₀ h)) ∈ L.T) (hZf : ∀ h ∈ H, Z h - f₀ h ∈ L.T) :
    (fun g => H.index • (Submodule.Quotient.mk (f₀ g) : V ⧸ L.T)) ∈ HfD PD L := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  obtain ⟨F, hF, hFc, ⟨x, hx⟩, hY⟩ := exists_corestriction_cocycle O G V (corHfRepO ρ O) H hH hρ hρ'
    Z hZ hc
  obtain ⟨x', hx'⟩ := hY L.T L.stable f₀ 0 h₀ (by simpa using hZf)
  obtain ⟨X, hX⟩ := hX
  have hmul : ∀ a b y, actVB PD ρ a (actVB PD ρ b y) = actVB PD ρ (a * b) y := by
    intro a b y
    exact (LinearMap.congr_fun ((corHfRepVB PD ρ).map_mul a b) y).symm
  have h1 : ∀ g (v : V), actVB PD ρ g (v ⊗ₜ[Qp] (1 : B)) = ρ g v ⊗ₜ[Qp] (1 : B) := by
    intro g v
    rw [corHf_actVB_tmul, map_one]
  obtain ⟨y, hy⟩ := index_smul_cocycle_eq_coboundary LL G (V ⊗[Qp] B) (corHfRepVB PD ρ) H
    (fun g => F g ⊗ₜ[Qp] (1 : B))
    (by
      intro g h
      change _ = _ + actVB PD ρ g _
      rw [h1, hFc, add_tmul]
      rfl)
    ⟨(∑ q : G ⧸ H, actVB PD ρ q.out X) + x ⊗ₜ[Qp] (1 : B), by
      intro h hh
      change _ = actVB PD ρ h _ - _

      rw [hx h hh, finsum_eq_sum_of_fintype, add_tmul, sum_tmul, map_add (f := _), map_sum, h1, sub_tmul]
      have : ∀ q : G ⧸ H, (corHfRepO ρ O q.out (Z (q.out⁻¹ * h * q.out))) ⊗ₜ[Qp] (1 : B) =
          actVB PD ρ h (actVB PD ρ q.out X) - actVB PD ρ q.out X := by
        intro q
        change (ρ q.out _) ⊗ₜ[Qp] (1 : B) = _
        rw [← h1, hX _ (Subgroup.Normal.conj_mem' ‹H.Normal› h hh q.out), map_sub, hmul, hmul]
        congr 3
        group
      rw [Finset.sum_congr rfl fun q _ => this q, Finset.sum_sub_distrib]
      change _ + (ρ h x ⊗ₜ[Qp] (1 : B) - _) = _
      abel⟩
  have hn : (H.index : LL) ≠ 0 := Nat.cast_ne_zero.mpr Subgroup.FiniteIndex.index_ne_zero
  have hFf : F ∈ finiteCocycles PD ρ := by
    refine ⟨⟨hF, hFc⟩, (H.index : LL)⁻¹ • y, fun g => ?_⟩
    have := hy g
    change _ = actVB PD ρ g y - y at this
    rw [map_smul, ← smul_sub, ← this, ← Nat.cast_smul_eq_nsmul LL, inv_smul_smul₀ hn]
  have e : (fun g => H.index • (Submodule.Quotient.mk (f₀ g) : V ⧸ L.T)) =
      LinearMap.compLeft L.T.mkQ G F -
        (LinearMap.pi fun g => actD L g - LinearMap.id) (Submodule.Quotient.mk x') := by
    funext g
    have := (Submodule.Quotient.mk_eq_zero L.T).mpr (hx' g)
    change L.T.mkQ _ = 0 at this
    rw [map_sub, map_sub, map_sub, map_nsmul] at this
    change H.index • L.T.mkQ (f₀ g) = L.T.mkQ (F g) - (L.T.mkQ (corHfRepO ρ O g x') - L.T.mkQ x')
    rw [← sub_eq_zero, ← neg_eq_zero, ← this]
    abel
  rw [e]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨F, hFf, rfl⟩)
    (Submodule.mem_sup_right ⟨_, rfl⟩)

end General

theorem corHf_exists_mul_eq_pow (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (n k : ℕ) (hn : n ≠ 0) (hk : padicValNat l n ≤ k) : ∃ u : O, u * (n : O) = ((l ^ k : ℕ) : O) := by
  have hn' : (n : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have : (n : ℤ_[l]) ∣ (l : ℤ_[l]) ^ k := by
    obtain ⟨m, hm⟩ : l ^ padicValNat l n ∣ n := (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
    have hlm : ¬ l ∣ m := by
      rintro ⟨c, rfl⟩
      apply pow_succ_padicValNat_not_dvd (p := l) hn
      exact ⟨c, by rw [pow_succ, mul_assoc]; simpa only [Nat.padicValNat_def] using hm⟩
    have hu : IsUnit (m : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff]
      exact PadicInt.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hlm)
    have e : (n : ℤ_[l]) = (l : ℤ_[l]) ^ padicValNat l n * m := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ_[l]) hm
    rw [e, hu.mul_right_dvd]
    exact pow_dvd_pow _ hk
  obtain ⟨c, hc⟩ := this
  refine ⟨algebraMap ℤ_[l] O c, ?_⟩
  have := congrArg (algebraMap ℤ_[l] O) hc
  simp only [map_pow, map_natCast, map_mul] at this
  rw [Nat.cast_pow, this, mul_comm]

theorem corHf_nsmul_mem {O G M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (S : Submodule O (G → M)) (f : G → M) (n m : ℕ) (h : ∃ u : O, u * (n : O) = (m : O))
    (hf : (fun g => n • f g) ∈ S) : (fun g => m • f g) ∈ S := by
  obtain ⟨u, hu⟩ := h
  convert S.smul_mem u hf using 1
  funext g
  rw [Pi.smul_apply, ← Nat.cast_smul_eq_nsmul O, ← Nat.cast_smul_eq_nsmul O, smul_smul, hu]


set_option synthInstance.maxHeartbeats 400000 in
theorem pow_smul_mem_HfD_of_restriction : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (V : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (H : Subgroup ↥(GK K)) [H.Normal] [H.FiniteIndex], IsOpen (H : Set ↥(GK K)) → ∀ (Z f₀ : ↥(GK K) → V.V), ContinuousOn Z H → (∀ g ∈ H, ∀ h ∈ H, Z (g * h) = Z g + V.ρ g (Z h)) → (∃ X : TensorProduct ℚ_[l] V.V P.R.B, ∀ h ∈ H, Z h ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) V.ρ h X - X) → (∀ g h, f₀ (g * h) - (f₀ g + V.ρ g (f₀ h)) ∈ V.L.T) → (∀ h ∈ H, Z h - f₀ h ∈ V.L.T) → ∀ k : ℕ, padicValNat l H.index ≤ k → (fun g => (l ^ k : ℕ) • (Submodule.Quotient.mk (f₀ g) : V.V ⧸ V.L.T)) ∈ HfD (P.PD K) V.L := by
  intro l _ P K LL V H _ _ hH Z f₀ hZ hc hX h₀ hZf k hk
  haveI : IsTopologicalAddGroup V.V := IsModuleTopology.topologicalAddGroup ↥LL.1 V.V
  haveI : ContinuousSMul ↥LL.1 V.V := IsModuleTopology.toContinuousSMul ↥LL.1 V.V
  exact corHf_nsmul_mem _ _ H.index _
    (corHf_exists_mul_eq_pow l _ _ k Subgroup.FiniteIndex.index_ne_zero hk)
    (index_smul_mem_HfD (P.PD K) V.ρ V.L
      (fun g => IsModuleTopology.continuous_of_linearMap (V.ρ g)) V.cont H hH Z f₀ hZ hc hX h₀ hZf)

end GlobalTheory
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.NatQuot

theorem exists_continuous_div {O : Type} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O] [T2Space O] {X : Type} [TopologicalSpace X]
    {π : O} (hπ : π ≠ 0) (u : X → O) (hu : Continuous u) (hd : ∀ x, π ∣ u x) :
    ∃ w : X → O, Continuous w ∧ ∀ x, u x = π * w x := by
  choose w hw using hd
  have hemb : Topology.IsClosedEmbedding (fun a : O => π * a) :=
    (continuous_const.mul continuous_id).isClosedEmbedding (mul_right_injective₀ hπ)
  refine ⟨w, hemb.isEmbedding.continuous_iff.2 ?_, hw⟩
  have : ((fun a : O => π * a) ∘ w) = u := funext fun x => (hw x).symm
  rw [this]; exact hu

theorem phi_quot_pow_injective :
    ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
      [IsTopologicalRing O] {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G],
      PadicCoeff p O → ∀ {ε : G →* Oˣ}, Continuous (fun g : G => ((ε g : Oˣ) : O)) →
      ∀ z : H2 (twist ε O), Function.Bijective (fun a : O => a • z) → ∀ k : ℕ,
      Function.Injective (phi ε z (O ⧸ IsLocalRing.maximalIdeal O ^ k)) := by
  intro p O _ _ _ _ _ G _ _ _ hO ε hε z hz k
  haveI : CompactSpace O := hO.compact
  haveI : T2Space O := hO.t2
  haveI hdisc := (quot_pow_maximalIdeal_discrete_finite hO k).1
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hI : IsLocalRing.maximalIdeal O ^ k = Ideal.span {ϖ ^ k} := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hπ : ϖ ^ k ≠ 0 := pow_ne_zero k hϖ.ne_zero
  generalize IsLocalRing.maximalIdeal O ^ k = I at hI hdisc
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro m hm
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective m
  obtain ⟨z₀, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  have hm' : cocycles2Map (twist ε O) (twist ε (O ⧸ I))
      (LinearMap.toSpanSingleton O (O ⧸ I) (Ideal.Quotient.mk I a)) (cont_span _ _)
      (span_twist ε _ _) z₀ ∈ (B2 (twist ε (O ⧸ I))).comap (Z2 (twist ε (O ⧸ I))).subtype :=
    (Submodule.Quotient.mk_eq_zero _).1 hm
  obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem _ _).1 hm'
  have hcf' : ∀ g h : G, (ε g : O) • c h - c (g * h) + c g =
      z₀.1 (g, h) • Ideal.Quotient.mk I a := fun g h => congrFun hcf (g, h)
  choose s hs using (Ideal.Quotient.mk_surjective (I := I))
  have hcs : Continuous (fun g => s (c g)) := continuous_of_discreteTopology.comp hc
  set u : G × G → O := fun q =>
    a * z₀.1 q - ((ε q.1 : O) * s (c q.2) - s (c (q.1 * q.2)) + s (c q.1)) with hu
  have huc : Continuous u :=
    (continuous_const.mul z₀.2.1).sub
      ((((hε.comp continuous_fst).mul (hcs.comp continuous_snd)).sub
        (hcs.comp (continuous_fst.mul continuous_snd))).add (hcs.comp continuous_fst))
  have hud : ∀ q, ϖ ^ k ∣ u q := by
    rintro ⟨g, h⟩
    rw [← Ideal.mem_span_singleton, ← hI, ← Ideal.Quotient.eq_zero_iff_mem]
    have e := hcf' g h
    simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] at e
    simp only [hu, map_sub, map_add (f := _), map_mul, hs]
    rw [e]; ring
  obtain ⟨w, hwc, hw⟩ := exists_continuous_div hπ u huc hud
  have hwZ : w ∈ Z2 (twist ε O) := by
    refine ⟨hwc, fun g h l => ?_⟩
    apply mul_left_cancel₀ hπ
    have e : (ε g : O) * z₀.1 (h, l) - z₀.1 (g * h, l) + z₀.1 (g, h * l) - z₀.1 (g, h) = 0 :=
      z₀.2.2 g h l
    have e1 := hw (h, l)
    have e2 := hw (g * h, l)
    have e3 := hw (g, h * l)
    have e4 := hw (g, h)
    simp only [hu, map_mul, Units.val_mul, mul_assoc] at e1 e2 e3 e4
    show ϖ ^ k * ((ε g : O) * w (h, l) - w (g * h, l) + w (g, h * l) - w (g, h)) = ϖ ^ k * 0
    linear_combination a * e - (ε g : O) * e1 + e2 - e3 + e4
  obtain ⟨b, hb⟩ := hz.2 (Submodule.Quotient.mk ⟨w, hwZ⟩)
  have key : a • (Submodule.Quotient.mk z₀ : H2 (twist ε O)) =
      (ϖ ^ k * b) • (Submodule.Quotient.mk z₀ : H2 (twist ε O)) := by
    simp only at hb
    rw [mul_smul, hb, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.eq]
    refine (separated_dvr_second_cohomology_mem _ _).2 ⟨fun g => s (c g), hcs, funext fun q => ?_⟩
    have e := hw q
    show (ε q.1 : O) * s (c q.2) - s (c (q.1 * q.2)) + s (c q.1) = a * z₀.1 q - ϖ ^ k * w q
    rw [← e, hu]; ring
  have hab : a = ϖ ^ k * b := hz.1 key
  rw [Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton]
  exact ⟨b, hab⟩

end GlobalTheory.NatQuot
end

section

open ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.card_H1_level_rep_formula : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
    {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M) (ϖ : O) (n : ℕ),
    (∀ m : M, ∃ m' : M, ϖ • m' = m) → (∀ m : M, IsLocallyConstant (fun g => ρ g m)) →
    Finite (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRep ρ (ϖ ^ n))) →
    Finite (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) ∧
    Nat.card (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRep ρ (ϖ ^ n))) =
      Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) *
      Nat.card (ρ.invariants ⧸ LinearMap.range (ϖ ^ n • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) := by
  first | exact @GlobalTheory.ShapeNeg.SeqCount.card_H1_level_rep_eq | exact GlobalTheory.ShapeNeg.SeqCount.card_H1_level_rep_eq | (intros; apply GlobalTheory.ShapeNeg.SeqCount.card_H1_level_rep_eq <;> assumption)
end

section

open ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.exists_pow_smul_eq_zero_of_mem_HcLC_of_torsion : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M) (ϖ : O),
    (∀ m : M, ∃ n : ℕ, ϖ ^ n • m = 0) → ∀ x ∈ ReciprocityTheory.ChartRestriction.T2.HcLC ρ, ∃ n : ℕ, ϖ ^ n • x = 0 := by
  first | exact @GlobalTheory.hcLC_exists_pow_smul_eq_zero | exact GlobalTheory.hcLC_exists_pow_smul_eq_zero | (intros; apply GlobalTheory.hcLC_exists_pow_smul_eq_zero <;> assumption)
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
open Formalism.NG (KO)

theorem _root_.GlobalTheory.T.isFGTop_p_pow_inverse_lattice : ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)],
    PadicCoeff p O → FracTop O → ∀ n : ℕ,
    IsFGTop O ((1 : Submodule O (FractionRing O)).comap (LinearMap.lsmul O _ ((p : O) ^ n))) := by
  first | exact @GlobalTheory.isFGTop_comap_lsmul_one | exact GlobalTheory.isFGTop_comap_lsmul_one | (intros; apply GlobalTheory.isFGTop_comap_lsmul_one <;> assumption)
end

section


theorem _root_.GlobalTheory.T.span_of_local_cohomology_shape : ReciprocityTheory.ChartRestriction.T2.JSpan := by
  first | exact @GlobalTheory.jSpan_holds | exact GlobalTheory.jSpan_holds | (intros; apply GlobalTheory.jSpan_holds <;> assumption)
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

theorem _root_.GlobalTheory.T.eq_cyclotomicCharacter_of_isCyc : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] {G : Type} [Group G] [TopologicalSpace G], PadicCoeff p O → ∀ (φ : ℤ_[p] →+* O) (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) → ∀ g : G, ((ε g : Oˣ) : O) = φ ((cyclotomicCharacter (PadicAlgCl p) p (MulSemiringAction.toRingAut (GK p K) (PadicAlgCl p) (i g)) : ℤ_[p]ˣ) : ℤ_[p]) := by
  first | exact @GlobalTheory.CycImage.cyc_eq_image | exact GlobalTheory.CycImage.cyc_eq_image | (intros; apply GlobalTheory.CycImage.cyc_eq_image <;> assumption)
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

theorem _root_.GlobalTheory.T.isAdicComplete_of_padicCoeff' : ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O], PadicCoeff p O → IsAdicComplete (IsLocalRing.maximalIdeal O) O := by
  first | exact @GlobalTheory.isAdicComplete_of_padicCoeff | exact GlobalTheory.isAdicComplete_of_padicCoeff | (intros; apply GlobalTheory.isAdicComplete_of_padicCoeff <;> assumption)
end
