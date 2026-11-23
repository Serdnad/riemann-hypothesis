module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle196
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle010
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
public import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
public import Formalism.SharpRestriction.Divisibility.ProductZerothFirstParts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle083
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle197
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
import Formalism.LocalToGlobal.GroupLattices.PerfectRings.IntermediateMapWittQuadratic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle010
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle080
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HkDict

theorem lift_cosets {H G : Type} [Group H] [Group G] (φ : H →* G) (N J₀ L₀ L₁ : Subgroup H) (J : Subgroup G) (K : Set H)
    (hs : ∀ x, ∃ g ∈ N, φ g = x) (hi : ∀ g g', g ∈ N → g' ∈ N → φ g = φ g' → g = g')
    (hJ : ∀ g, g ∈ N → (φ g ∈ J ↔ g ∈ J₀)) (hLN : ∀ g ∈ L₀, g ∈ N)
    (hc : ∀ g g', g ∈ L₀ → g' ∈ L₁ → Commute g g') (hd : ∀ g, g ∈ L₀ → g ∈ L₁ → g = 1)
    (hK : ∀ g, g ∈ L₀ → (g ∈ J₀ ↔ g ∈ K))
    (hsp : ∀ k ∈ J₀, ∃ k₁ ∈ J₀, ∃ k₂ ∈ J₀, k₁ ∈ L₀ ∧ k₂ ∈ L₁ ∧ k = k₁ * k₂)
    (α : H) (hα : α ∈ L₀) (B : Finset G) (hB : ∀ a ∈ B, ∃ g ∈ L₀, φ g = a) (hDC : Bridge.IsDC J (φ α) B) :
    ∃ R : Finset H, (∀ γ ∈ R, γ ∈ L₀) ∧
      (∀ γ ∈ R, ∃ k₁, (k₁ ∈ K ∧ k₁ ∈ L₀) ∧ ∃ k₂, (k₂ ∈ K ∧ k₂ ∈ L₀) ∧ γ = k₁ * α * k₂) ∧
      (∀ x : H, (∃ k₁, (k₁ ∈ K ∧ k₁ ∈ L₀) ∧ ∃ k₂, (k₂ ∈ K ∧ k₂ ∈ L₀) ∧ x = k₁ * α * k₂) →
        ∃! γ, γ ∈ R ∧ (γ⁻¹ * x ∈ K ∧ γ⁻¹ * x ∈ L₀)) ∧
      ∀ (W : Type) [AddCommMonoid W] (F : G → W), ∑ a ∈ B, F a = ∑ γ ∈ R, F (φ γ) := by
  classical
  choose s hs1 hs2 using hs
  have hsL : ∀ a ∈ B, s a ∈ L₀ := fun a ha => by
    obtain ⟨g, hg, rfl⟩ := hB a ha
    rw [hi _ _ (hs1 _) (hLN g hg) (hs2 _)]
    exact hg
  have hsinj : Function.Injective s := fun a b h => by rw [← hs2 a, ← hs2 b, h]
  have hKJ : ∀ k, k ∈ K ∧ k ∈ L₀ → φ k ∈ J := fun k hk => (hJ k (hLN k hk.2)).2 ((hK k hk.2).2 hk.1)
  refine ⟨B.image s, ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hγ
    exact hsL a ha
  · intro γ hγ
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hγ
    obtain ⟨⟨k₁, h₁⟩, ⟨k₂, h₂⟩, hk⟩ := hDC.1 a ha
    have j₁ : s k₁ ∈ J₀ := (hJ _ (hs1 _)).1 (by rwa [hs2])
    have j₂ : s k₂ ∈ J₀ := (hJ _ (hs1 _)).1 (by rwa [hs2])
    obtain ⟨a₁, ha₁, b₁, hb₁, la₁, lb₁, e₁⟩ := hsp _ j₁
    obtain ⟨a₂, ha₂, b₂, hb₂, la₂, lb₂, e₂⟩ := hsp _ j₂
    have e : s a = s k₁ * α * s k₂ := by
      refine hi _ _ (hs1 _) (N.mul_mem (N.mul_mem (hs1 _) (hLN _ hα)) (hs1 _)) ?_
      rw [map_mul, map_mul, hs2, hs2, hs2]
      exact hk
    have e' : s a = (a₁ * α * a₂) * (b₁ * b₂) := by
      rw [e, e₁, e₂]
      have c := (hc _ _ (L₀.mul_mem hα la₂) lb₁).eq
      calc a₁ * b₁ * α * (a₂ * b₂) = a₁ * (b₁ * (α * a₂)) * b₂ := by simp only [mul_assoc]
        _ = _ := by rw [← c]; simp only [mul_assoc]
    have hb : b₁ * b₂ = 1 := by
      refine hd _ ?_ (L₁.mul_mem lb₁ lb₂)
      have : b₁ * b₂ = (a₁ * α * a₂)⁻¹ * s a := by rw [e', inv_mul_cancel_left]
      rw [this]
      exact L₀.mul_mem (L₀.inv_mem (L₀.mul_mem (L₀.mul_mem la₁ hα) la₂)) (hsL a ha)
    exact ⟨a₁, ⟨(hK _ la₁).1 ha₁, la₁⟩, a₂, ⟨(hK _ la₂).1 ha₂, la₂⟩, by rw [e', hb, mul_one]⟩
  · rintro x ⟨k₁, h₁, k₂, h₂, hx⟩
    have hxL : x ∈ L₀ := hx ▸ L₀.mul_mem (L₀.mul_mem h₁.2 hα) h₂.2
    obtain ⟨a, ⟨ha, haJ⟩, hu⟩ := hDC.2 (φ x) ⟨⟨φ k₁, hKJ _ h₁⟩, ⟨φ k₂, hKJ _ h₂⟩, by rw [hx, map_mul, map_mul]⟩
    have hL : (s a)⁻¹ * x ∈ L₀ := L₀.mul_mem (L₀.inv_mem (hsL a ha)) hxL
    refine ⟨s a, ⟨Finset.mem_image_of_mem s ha, (hK _ hL).1 ((hJ _ (hLN _ hL)).1 ?_), hL⟩, ?_⟩
    · rwa [map_mul, map_inv, hs2]
    · rintro γ ⟨hγ, hγK⟩
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hγ
      have := hKJ _ hγK
      rw [map_mul, map_inv, hs2] at this
      rw [hu b ⟨hb, this⟩]
  · intro W _ F
    rw [Finset.sum_image fun a _ b _ h => hsinj h]
    simp only [hs2]

def rightTr {H G : Type} [Group H] [Group G] (φ : H →* G) (W : Type) [AddCommGroup W] [Module ℂ W] :
    H →* Module.End ℂ (G → W) where
  toFun g := { toFun := fun F h => F (h * φ g), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  map_one' := by ext F h; simp
  map_mul' g g' := by ext F h; simp [mul_assoc]

theorem supp_both {D : D7} (V : HSp D) (f : Formalism.L2.Theta.AE D) (g : GA D V) (h : SuppF V f g) (h' : SuppF V (1 - f) g) :
    g = 1 := by
  apply Subtype.ext
  apply Units.ext
  have : Formalism.L2.Theta.mt V g - 1 = 0 := by
    ext i j
    have a := h i j
    have b := h' i j
    rw [sub_mul, one_mul, a, sub_self] at b
    exact b.symm
  exact sub_eq_zero.1 this



open GlobalTheory.SplitHeckeAdj in
theorem dcOp_eq_label : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank), IsBaseFrame V β Λ N → ∀ P : Pl D.host.E, ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → (∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) → ∀ (d : List ℤ) (x : Bridge.Gf V) (B : Finset (Bridge.Gf V)), d.Pairwise (fun a b => b ≤ a) → _root_.GlobalTheory.Hk3.IsLabElt V P d x → (∀ a ∈ B, _root_.GlobalTheory.Hk3.IsLocElt V P a) → Bridge.IsDC (levEnv V β L).J x B → IsLab V P d ∧ ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (Φ : Bridge.Gf V → W), (∀ h (k : (levEnv V β L).J), _root_.GlobalTheory.Hk3.IsLocElt V P k → Φ (h * k) = Φ h) → Bridge.dcOp B Φ = hkF V P (Finsupp.single d 1) Φ := by
  intro D V β Λ N L hβ P hN hoff d x B hd hx hB hDC
  obtain ⟨e, f, ϖ, α, hP, hϖ, hϖ', -, hxα, hα, hdiv⟩ := hx
  have hG := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
  have h01 := hG.2.2.1 P e f hP
  have hff := h01.1
  have hcf := h01.2.1
  have hff' : (1 - f) * (1 - f) = 1 - f := by
    rw [mul_sub, mul_one, sub_mul, one_mul, hff, sub_self, sub_zero]
  have hcf' : cA D (1 - f) = 1 - f := by rw [map_sub, map_one, hcf]
  obtain ⟨L₀, hL₀⟩ := (hG.1 f hff hcf).1
  obtain ⟨L₁, hL₁⟩ := (hG.1 _ hff' hcf').1
  have h03 := (GlobalTheory.LevSplit.lev_split V β Λ N (flag1L L) hβ).2 P e f hP hN hoff
  have hK := h03.1
  have hsp := h03.2.2
  have hx' : x = fin V α := Subtype.ext hxα
  subst hx'
  have hB' : ∀ a ∈ B, ∃ g ∈ L₀, fin V g = a := fun a ha => by
    obtain ⟨e', f', g, hP', -, h1, h2⟩ := hB a ha
    have h3 : f' = f := (h01.2.2.2.1 e' f' hP').2
    rw [h3] at h2
    exact ⟨g, (hL₀ g).2 h2, Subtype.ext h1.symm⟩
  have main := lift_cosets (fin V) (GfC V) (levG V β (flag1L L)) L₀ L₁ (levEnv V β L).J (KsphC V ∅)
    (fin_lift V) (fun g g' => fin_inj V) (fun g => mem_J V β L)
    (fun g hg => h01.2.2.1 g ((hL₀ g).1 hg))
    (fun g g' h h' => commute_compl V _ hff hcf ((hL₀ g).1 h) ((hL₁ g').1 h'))
    (fun g h h' => supp_both V f g ((hL₀ g).1 h) ((hL₁ g).1 h'))
    (fun g h => hK g ((hL₀ g).1 h))
    (fun k hk => by
      obtain ⟨k₁, h₁, k₂, h₂, s₁, s₂, h⟩ := hsp k hk
      exact ⟨k₁, h₁, k₂, h₂, (hL₀ _).2 s₁, (hL₁ _).2 s₂, h⟩)
    α ((hL₀ α).2 hα) B hB' hDC
  obtain ⟨R, r1, r2, r3, r4⟩ := main
  simp only [hL₀] at r1 r2 r3
  have hR : SphOp V P d R :=
    ⟨e, f, ϖ, α, fun v hv => absurd hv (Finset.notMem_empty v), hP, hϖ, hϖ', hd, fun _ _ => Iff.rfl, fun _ _ _ => rfl,
      hα, hdiv, r1, fun γ hγ => ⟨h01.2.2.1 γ (r1 γ hγ), r2 γ hγ⟩, r3⟩
  refine ⟨⟨R, hR⟩, fun W _ _ Φ hΦ => ?_⟩
  have hfix : ∀ k ∈ hyp V P, rightTr (fin V) W k Φ = Φ := by
    rintro k ⟨hk, e', f', hP', hs⟩
    have h3 : f' = f := (h01.2.2.2.1 e' f' hP').2
    rw [h3] at hs
    have hkf := h01.2.2.1 k hs
    funext h
    exact hΦ h ⟨fin V k, (mem_J V β L hkf).2 ((hK k hs).2 hk)⟩ ⟨e, f, k, hP, hkf, rfl, hs⟩
  have h := ((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors V P).1 d R hR).2 _ (rightTr (fin V) W) Φ hfix
  funext g
  have h1 := congrFun h g
  have h2 : Bridge.dcOp B Φ g = ∑ γ ∈ R, Φ (g * fin V γ) := r4 W fun a => Φ (g * a)
  rw [h2]
  simp only [opOf, hkF, zero_smul, Finsupp.sum_single_index, one_smul, Finset.sum_apply, LinearMap.sum_apply] at h1 ⊢
  exact h1

end GlobalTheory.HkDict
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU GlobalTheory.OnePlace Classical

noncomputable section

namespace GlobalTheory.OnePlaceRead

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime]

theorem constantCoeff_psubst {K κ : Type} [CommRing K] {a : MvPowerSeries κ K} (ha : constantCoeff a = 0)
    {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) : constantCoeff (PowerSeries.subst a f) = 0 := by
  have h := GlobalTheory.BeProps.coeff_subst_range ha f 0
  simpa [hf] using h

theorem constantCoeff_padicLogSeries_unramified_eq_zero : PowerSeries.constantCoeff (FormalGroupSystem.logF p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [FormalGroupSystem.logF]

theorem constantCoeff_logF_C : PowerSeries.constantCoeff (Formalism.MainNotions.GL3Theta.logF p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [Formalism.MainNotions.GL3Theta.logF]

theorem map_expS {ι : Type} {f : MvPowerSeries ι (FormalGroupSystem.K0 p)} (hf : constantCoeff f = 0) :
    MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (FormalGroupSystem.expS p f) =
      product_zeroth_first_parts.expS ℂ_[p] (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) f) := by
  have hf' : constantCoeff (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) f) = 0 := by
    simp [hf]
  ext n
  rw [coeff_map]
  unfold product_zeroth_first_parts.expS
  rw [GlobalTheory.BeProps.coeff_subst_range hf']
  have hd : (n.sum fun _ k => k) = n.degree := by
    simp [Finsupp.sum, Finsupp.degree_apply]
  rw [hd]
  change Formalism.L2.G.Pend.k0ToC p (∑ k ∈ Finset.range (n.degree + 1),
    ((k.factorial : FormalGroupSystem.K0 p))⁻¹ * MvPowerSeries.coeff n (f ^ k)) = _

  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_inv₀, map_natCast, PowerSeries.coeff_exp, ← map_pow, coeff_map]
  simp

theorem subst_bivariateSeries_difference_pair {τ : Type} {Eσ : Type} [Finite Eσ] (be : MvPowerSeries (Fin 2) (FormalGroupSystem.K0 p))
    {η : Eσ → MvPowerSeries τ ℂ_[p]} (hη : ∀ i, constantCoeff (η i) = 0) (i j : Eσ) :
    MvPowerSeries.subst η (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p)
      (sub2 p be (MvPowerSeries.X i) (MvPowerSeries.X j))) =
      GlobalTheory.ThBe0.at2 (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) be) (η i) (η j) := by
  have hs : HasSubst η := hasSubst_of_constantCoeff_zero hη
  have h2 : HasSubst (![MvPowerSeries.X i, MvPowerSeries.X j] : Fin 2 → MvPowerSeries Eσ (FormalGroupSystem.K0 p)) := by
    refine hasSubst_of_constantCoeff_zero fun s => ?_
    fin_cases s <;> simp
  have h2' : HasSubst (fun s => MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p)
      ((![MvPowerSeries.X i, MvPowerSeries.X j] : Fin 2 → MvPowerSeries Eσ (FormalGroupSystem.K0 p)) s)) := by
    refine hasSubst_of_constantCoeff_zero fun s => ?_
    fin_cases s <;> simp
  unfold sub2 GlobalTheory.ThBe0.at2
  rw [map_subst h2, subst_comp_subst_apply h2' hs]
  congr 1
  funext s
  fin_cases s <;> simp [subst_X hs]

theorem read_thOne {n' r0 r1 : ℕ} {κ : Type} (B : OmBasis p n') (be : MvPowerSeries (Fin 2) (FormalGroupSystem.K0 p)) (hbe : BeProp p be)
    (U : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p)) (J : Zidx n' r0 r1 → MvPowerSeries κ ℂ_[p])
    (ξ : Eidx n' r0 r1 ⊕ Eidx n' r0 r1 → MvPowerSeries κ ℂ_[p])
    (hJ : ∀ z, MvPowerSeries.constantCoeff (J z) = 0) (hξ : ∀ i, MvPowerSeries.constantCoeff (ξ i) = 0)
    (h : ∀ i, MvPowerSeries.subst J (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (coordZ B (FormalGroupSystem.K0 p) 1 i)) =
      PowerSeries.subst (ξ i) (Formalism.MainNotions.GL3Theta.logF p)) :
    MvPowerSeries.subst J (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (thOne B be U)) =
      product_zeroth_first_parts.expS ℂ_[p] (-(∑ e : Eidx n' r0 r1, GlobalTheory.ThBe0.at2 (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) be)
        (PowerSeries.subst (ξ (Sum.inl e)) (Formalism.MainNotions.GL3Theta.logF p))
        (PowerSeries.subst (ξ (Sum.inr e)) (Formalism.MainNotions.GL3Theta.logF p)))) *
      MvPowerSeries.subst ξ (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inParam p U)) := by
  have hJs : HasSubst J := hasSubst_of_constantCoeff_zero hJ
  have hξs : HasSubst ξ := hasSubst_of_constantCoeff_zero hξ
  have ha := hasSubst_coordZ (r0 := r0) (r1 := r1) B
  have ha0 : ∀ i, constantCoeff (coordZ B (FormalGroupSystem.K0 p) 1 i : MvPowerSeries (Zidx n' r0 r1) (FormalGroupSystem.K0 p)) = 0 :=
    fun i => (ha.const_coeff i).eq_zero
  have ham : HasSubst (fun i => MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p)
      (coordZ B (FormalGroupSystem.K0 p) 1 i : MvPowerSeries (Zidx n' r0 r1) (FormalGroupSystem.K0 p))) :=
    hasSubst_of_constantCoeff_zero fun i => by simp [ha0 i]
  have hη0 : ∀ i, constantCoeff (PowerSeries.subst (ξ i) (Formalism.MainNotions.GL3Theta.logF p)) = 0 :=
    fun i => constantCoeff_psubst (hξ i) constantCoeff_logF_C
  have hηs : HasSubst (fun i => PowerSeries.subst (ξ i) (Formalism.MainNotions.GL3Theta.logF p)) :=
    hasSubst_of_constantCoeff_zero hη0

  have hbe0 : constantCoeff be = 0 := by
    by_contra hc
    have := (hbe.ab 0 (by simpa using hc)).1
    simp at this
  have hsub0 : ∀ e : Eidx n' r0 r1, constantCoeff (sub2 p be
      (MvPowerSeries.X (Sum.inl e) : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p))
      (MvPowerSeries.X (Sum.inr e))) = 0 := by
    intro e
    have h2 : ∀ s, constantCoeff ((![MvPowerSeries.X (Sum.inl e), MvPowerSeries.X (Sum.inr e)] :
        Fin 2 → MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p)) s) = 0 := by
      intro s; fin_cases s <;> simp
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h2) h2 hbe0
  set Φ : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p) :=
    ∑ e : Eidx n' r0 r1, sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e)) with hΦ
  have hΦ0 : constantCoeff (-Φ) = 0 := by

    rw [map_neg, hΦ, map_sum, Finset.sum_eq_zero fun e _ => hsub0 e, neg_zero]
  have hΦm : constantCoeff (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (-Φ)) = 0 := by
    rw [constantCoeff_map, hΦ0, map_zero]

  have hexp : MvPowerSeries.subst (fun i => PowerSeries.subst (ξ i) (Formalism.MainNotions.GL3Theta.logF p))
      (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (FormalGroupSystem.expS p (-Φ))) =
      product_zeroth_first_parts.expS ℂ_[p] (-(∑ e : Eidx n' r0 r1, GlobalTheory.ThBe0.at2 (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) be)
        (PowerSeries.subst (ξ (Sum.inl e)) (Formalism.MainNotions.GL3Theta.logF p))
        (PowerSeries.subst (ξ (Sum.inr e)) (Formalism.MainNotions.GL3Theta.logF p)))) := by
    rw [map_expS hΦ0]
    unfold product_zeroth_first_parts.expS
    rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.subst_exp _ hη0 hΦm]
    congr 1

    rw [← coe_substAlgHom hηs, map_neg, map_neg, hΦ, map_sum, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [coe_substAlgHom hηs]
    exact subst_bivariateSeries_difference_pair be hη0 _ _

  have hL0 : ∀ i : Eidx n' r0 r1 ⊕ Eidx n' r0 r1, constantCoeff (PowerSeries.subst
      (MvPowerSeries.X i : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p)) (FormalGroupSystem.logF p)) = 0 :=
    fun i => constantCoeff_psubst (by simp) constantCoeff_padicLogSeries_unramified_eq_zero
  have hLm : ∀ i : Eidx n' r0 r1 ⊕ Eidx n' r0 r1, MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (PowerSeries.subst
      (MvPowerSeries.X i : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p)) (FormalGroupSystem.logF p)) =
      PowerSeries.subst (MvPowerSeries.X i) (Formalism.MainNotions.GL3Theta.logF p) := by
    intro i
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)), map_X,
      Formalism.L2.G.Pend.logF_map]
  have hLc : ∀ i : Eidx n' r0 r1 ⊕ Eidx n' r0 r1, constantCoeff (PowerSeries.subst
      (MvPowerSeries.X i : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) ℂ_[p]) (Formalism.MainNotions.GL3Theta.logF p)) = 0 :=
    fun i => constantCoeff_psubst (by simp) constantCoeff_logF_C
  have hcof : MvPowerSeries.subst ξ (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inParam p U)) =
      MvPowerSeries.subst (fun i => PowerSeries.subst (ξ i) (Formalism.MainNotions.GL3Theta.logF p))
        (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) U) := by
    unfold inParam
    rw [map_subst (hasSubst_of_constantCoeff_zero hL0)]
    simp_rw [hLm]
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hLc) hξs]
    congr 1
    funext i
    rw [GlobalTheory.BeProps.subst_psubst hξs (by simp), subst_X hξs]
  rw [hcof, ← hexp, ← subst_mul hηs, ← map_mul]
  unfold thOne ThZ
  rw [map_subst ha, subst_comp_subst_apply ham hJs]
  simp_rw [h]
  rfl

end GlobalTheory.OnePlaceRead

end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory

open GlobalTheory.SmGL GlobalTheory.LocGL in
private theorem clTwist_eq_self_of_eq_one {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (c : IrrCl G) (χ : G →* ℂˣ) (hχ : IsSmoothChar χ) (h1 : χ = 1) : clTwist c χ hχ = c := by
  subst h1; exact clTwist_one c hχ

theorem rankOne_algNorm_locComp (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (π : CuspSub E 1)
    (ψ : HChar E) (hπ : CG.mk π = CG.ofChar ψ) (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin 1) (w.adicCompletion E))) (hσ : π.IsLocComp w σ) :
    algNorm σ = IrrGL.ofChar (ψ.loc w) (ParLaws.isSmoothChar_loc ψ w) := by
  have h1 : (CG.mk π).IsLoc w (Quotient.mk _ σ) := hσ
  rw [hπ] at h1
  have h2 := CG.IsLoc.unique E 1 _ w _ _ h1 (CG.isLoc_ofChar ψ w)
  obtain ⟨e⟩ := Quotient.exact h2
  unfold algNorm IrrGL.nu IrrGL.tw IrrGL.of IrrGL.ofChar
  congr 1
  refine (clTwist_eq_self_of_eq_one _ _ _ ?_).trans ?_
  · ext g
    simp [GlobalTheory.SmGL.detChar, GlobalTheory.SmGL.absPow]
  apply Quotient.sound
  exact ⟨e.trans (Representation.Equiv.refl _)⟩

end GlobalTheory
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong

namespace GlobalTheory.UnipFlag

open Matrix

variable {k : Type} [Field k] {a s : ℕ} {d : Fin s → ℕ}

def lowSpan (e : (Σ i, Fin (d i)) ≃ Fin a) (c : Fin s) : Submodule k (Fin a → k) :=
  GlobalTheory.LowerBlockFlag.f0 e c

theorem exists_sub (k : Type) [Field k] (a s : ℕ) (d : Fin s → ℕ) (e : (Σ i, Fin (d i)) ≃ Fin a)
    (hne : GlobalTheory.SmGL.unipRad k e ≠ ⊥) :
    ∃ W : Submodule k (Fin a → k), W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ g : GL (Fin a) k,
      (∀ v, ((g : Matrix (Fin a) (Fin a) k) - 1).mulVec v ∈ W) →
      (∀ v ∈ W, ((g : Matrix (Fin a) (Fin a) k) - 1).mulVec v = 0) → g ∈ GlobalTheory.SmGL.unipRad k e := by
  have hex : ∃ u ∈ GlobalTheory.SmGL.unipRad k e, u ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne ((Subgroup.eq_bot_iff_forall _).2 h)
  obtain ⟨u, hu, hu1⟩ := hex
  have hij : ∃ i j, (u : Matrix (Fin a) (Fin a) k) i j ≠ (1 : Matrix (Fin a) (Fin a) k) i j := by
    by_contra h
    push_neg at h
    exact hu1 (Units.ext (Matrix.ext h))
  obtain ⟨i, j, hij⟩ := hij
  obtain ⟨hp, hd⟩ := GlobalTheory.SmGL.mem_unipRad.1 hu
  have hlt : GlobalTheory.SmGL.blk e i < GlobalTheory.SmGL.blk e j := by
    rcases lt_trichotomy (GlobalTheory.SmGL.blk e i) (GlobalTheory.SmGL.blk e j) with h | h | h
    · exact h
    · exfalso
      obtain ⟨⟨b, i'⟩, rfl⟩ := e.surjective i
      obtain ⟨⟨b', j'⟩, rfl⟩ := e.surjective j
      simp only [GlobalTheory.SmGL.blk_apply] at h
      subst h
      apply hij
      rw [hd]
      simp [Matrix.one_apply]
    · exfalso
      apply hij
      rw [GlobalTheory.SmGL.mem_parab.1 hp i j h, one_apply_ne (by rintro rfl; exact lt_irrefl _ h)]
  refine ⟨lowSpan e (GlobalTheory.SmGL.blk e i), ?_, ?_, ?_⟩
  · intro hb
    have hm : Pi.single i (1 : k) ∈ lowSpan e (GlobalTheory.SmGL.blk e i) := fun p hp' =>
      Pi.single_eq_of_ne (by rintro rfl; exact lt_irrefl _ hp') _
    rw [hb] at hm
    simpa using congrFun ((Submodule.mem_bot k).1 hm) i
  · intro ht
    have hm : Pi.single j (1 : k) ∈ lowSpan e (GlobalTheory.SmGL.blk e i) := ht ▸ Submodule.mem_top
    have := hm j hlt
    simp at this
  · intro g h1 h2
    have key : ∀ p q, ¬ (GlobalTheory.SmGL.blk e p < GlobalTheory.SmGL.blk e q) →
        ((g : Matrix (Fin a) (Fin a) k) - 1) p q = 0 := by
      intro p q hpq
      have hcol : ((g : Matrix (Fin a) (Fin a) k) - 1) p q =
          (((g : Matrix (Fin a) (Fin a) k) - 1) *ᵥ Pi.single q 1) p := by
        simp [Matrix.mulVec_single_one]
      rw [hcol]
      by_cases hq : GlobalTheory.SmGL.blk e q ≤ GlobalTheory.SmGL.blk e i
      · rw [h2 _ (fun r hr => Pi.single_eq_of_ne (by rintro rfl; exact absurd hq (not_le.2 hr)) _)]
        rfl
      · exact h1 _ p (lt_of_lt_of_le (not_le.1 hq) (not_lt.1 hpq))
    have hg : ∀ p q, (g : Matrix (Fin a) (Fin a) k) p q =
        (1 : Matrix (Fin a) (Fin a) k) p q + ((g : Matrix (Fin a) (Fin a) k) - 1) p q := by
      intro p q
      simp
    refine GlobalTheory.SmGL.mem_unipRad.2 ⟨GlobalTheory.SmGL.mem_parab.2 fun p q hqp => ?_, fun b p q => ?_⟩
    · rw [hg, key p q (not_lt.2 hqp.le), one_apply_ne (by rintro rfl; exact lt_irrefl _ hqp), add_zero]
    · rw [hg, key _ _ (by simp), add_zero]
      simp [Matrix.one_apply]

end GlobalTheory.UnipFlag
end
