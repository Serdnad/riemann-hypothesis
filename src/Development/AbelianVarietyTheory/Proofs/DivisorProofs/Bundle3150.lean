module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1477
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2386
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1658
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointDescendsToPowerSeries
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle149
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSinglePolarisationGeneratorAllTraits
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2913
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2704
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2703
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3092
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle046
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle121
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3093
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2982
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2782
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1564
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1737
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1541
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1466
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow.KeyTop

theorem levelPoint_cast {S : Scheme.{0}} {P : PolAV S} {M : ℕ} {u₁ u₂ : Γ(S, ⊤)ˣ} (h : u₁ = u₂)
    (l : Out.Level P M u₁) {g : ℕ} (hg : P.g = g) : levelPoint (h ▸ l) hg = levelPoint l hg := by
  subst h; rfl

theorem exhaust {K : Type} [Field K] [IsAlgClosed K] {P : PolAV (Sp K)} {M : ℕ} {ze : Γ(Sp K, ⊤)ˣ}
    (lev : Out.Level P M ze) {g : ℕ} (hg : P.g = g) (z : baseOver (Sp K) ⟶ P.A) (hz : z ^ M = 1) :
    ∃ a, levelPoint lev hg a = z := by
  subst hg
  obtain ⟨c, hc⟩ := lev.span K (𝟙 _) z hz
  refine ⟨fun i => ((c i : ℕ) : ZMod M), ?_⟩
  rw [levelPoint_rfl, Out.Level.toPt, ← hc]
  congr 1
  funext i; exact ZMod.val_cast_of_lt (c i).isLt

end GlobalTheory.MBLow.KeyTop

namespace GlobalTheory.MBLow.KeyTop

theorem transfer_of_rule4 : ∀ κ : Rule, Rule4 κ → Transfer κ := by
  intro κ hκ g n hn hodd
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.T.exists_family_localDomain_of_twoFibres g n hn hodd
  refine ⟨max j₁ 1, fun j hj C _ _ _ _ _ e x hg ζ lev k hD => ?_⟩
  have hj1 : j₁ ≤ j := le_trans (le_max_left _ _) hj
  have hj2 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hmodd : Odd (n ^ j) := hodd.pow
  have hm3 : 3 ≤ n ^ j := by
    have h2 := hn.two_le
    have hne : n ≠ 2 := fun h => by subst h; exact (Nat.not_even_iff_odd.mpr hodd) even_two
    have := Nat.le_self_pow (show j ≠ 0 by omega) n
    omega
  obtain ⟨Θ, Γ, π, b, hπ, hb, hJ, ε, hε, hD'⟩ := hD
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  let Φ : (Fin (2 * g) → ZMod ((n ^ j) ^ 2)) ⊕ (Fin (2 * g) → ZMod ((n ^ j) ^ 2)) × Fin g → PowerSeries C :=
    Sum.elim Θ (fun p => Γ p.1 p.2)
  let c : Fin 2 → C := ![(ζ : C), k]
  have hbΦ : ∀ a n, ‖PowerSeries.coeff n (Φ a)‖ ≤ b := by
    rintro (a | ⟨a, i⟩) n
    · exact (hb a n).1
    · exact (hb a n).2 i
  have hsΦ : ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε → ∀ a, Summable fun n => ‖e (PowerSeries.coeff n (Φ a)) * u ^ n‖ := by
    intro u hu hu'
    obtain ⟨hs, -⟩ := hD' u hu hu'
    rintro (a | ⟨a, i⟩)
    · exact (hs a).1
    · exact (hs a).2 i
  obtain ⟨u, o, _, _, jo, c₀, hu0, huε, hc₀, W, _, _, _, _, _, _, β, i₀, i₁, φ, hinj, h0, h1, hunit, hprime, hφ⟩ :=
    GlobalTheory.T.exists_deformation_base_ring_local_domain C e _ (Fin 2) Φ c π b ε hπ hε hbΦ hsΦ
  obtain ⟨-, x₀, hg₀, lev₀, hJ₀, hκ₀⟩ := hD' u hu0 huε
  have hc0 : jo (c₀ 0) = ζ := hc₀ 0
  have hc1 : jo (c₀ 1) = k := hc₀ 1
  have hζ0 : c₀ 0 ≠ 0 := fun h => ζ.ne_zero (by rw [← hc0, h, map_zero])
  let ζ₀ : oˣ := Units.mk0 (c₀ 0) hζ0
  have hu₁ : Units.map (i₁.comp β).toMonoidHom ζ₀ = ζ := Units.ext (by
    show (i₁.comp β) (c₀ 0) = ζ
    rw [h1, hc0])
  have hu₀ : Units.map (i₀.comp β).toMonoidHom ζ₀ = Units.map e.toMonoidHom ζ := Units.ext (by
    show (i₀.comp β) (c₀ 0) = e ζ
    rw [h0, RingHom.comp_apply, hc0])
  have hl₀ := (congrArg unitOn hu₀).symm
  have hl₁ := (congrArg unitOn hu₁).symm
  let l₀ := hl₀ ▸ lev₀
  let l₁ := hl₁ ▸ lev
  have eϑ₀ : (fun a => ∑' n, e (PowerSeries.coeff n (Θ a)) * u ^ n) = fun a => i₀ (φ (Sum.inl a)) :=
    funext fun a => ((hφ (Sum.inl a)).1).symm
  have eJ₀ : (fun a i => ∑' n, e (PowerSeries.coeff n (Γ a i)) * u ^ n) = fun a i => i₀ (φ (Sum.inr (a, i))) :=
    funext fun a => funext fun i => ((hφ (Sum.inr (a, i))).1).symm
  have eϑ₁ : (fun a => ∑' n, PowerSeries.coeff n (Θ a) * π ^ n) = fun a => i₁ (φ (Sum.inl a)) :=
    funext fun a => ((hφ (Sum.inl a)).2).symm
  have eJ₁ : (fun a i => ∑' n, PowerSeries.coeff n (Γ a i) * π ^ n) = fun a i => i₁ (φ (Sum.inr (a, i))) :=
    funext fun a => funext fun i => ((hφ (Sum.inr (a, i))).2).symm
  rw [eϑ₀, eJ₀, ← levelPoint_cast hl₀ lev₀ hg₀] at hJ₀
  rw [eϑ₁, eJ₁, ← levelPoint_cast hl₁ lev hg] at hJ
  have hθ₀ := GlobalTheory.T.isThetaPt_of_thetaConstantsAndFirstJets ℂ x₀ g hg₀ (n ^ j) hmodd (by exact_mod_cast pow_ne_zero _ hn.ne_zero) _ _ _ _ hJ₀
  have hθ₁ := GlobalTheory.T.isThetaPt_of_thetaConstantsAndFirstJets C x g hg (n ^ j) hmodd (by exact_mod_cast pow_ne_zero _ hn.ne_zero) _ _ _ _ hJ
  obtain ⟨P, pt, φ₀, φ₁, hPg, hpt, hpb₀, hpb₁, hL₀, hL₁, hc₀', hc₁'⟩ :=
    hj₁ j hj1 o ζ₀ W β (fun a => φ (Sum.inl a)) ℂ C i₀ i₁ hprime x₀.P x.P hg₀ hg l₀ l₁ hθ₀ hθ₁
  have hk₀ : (κ ℂ x₀ : ℂ) = i₀ (β (c₀ 1)) := by
    rw [hκ₀, ← RingHom.comp_apply i₀ β, h0, RingHom.comp_apply, hc1]
  have := GlobalTheory.T.thetaKeyValue_two_fibres_local_ring κ hκ W ℂ C i₀ i₁ hinj hunit P x₀ x g hg₀ hg (n ^ j) hPg hmodd hm3 _ pt
    (levelPoint l₀ hg₀) (levelPoint l₁ hg) φ₀ φ₁ hpt hpb₀ hpb₁ hL₀ hL₁ hc₀' hc₁'
    (fun z hz => exhaust l₁ hg z hz) _ _ (β (c₀ 1)) hJ₀ hJ hk₀
  rw [this, ← RingHom.comp_apply i₁ β, h1, hc1]

end GlobalTheory.MBLow.KeyTop
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix.PLSnc

theorem int_half {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ) : Mix.int L (fun y => f y / 2) = Mix.int L f / 2 := by
  simp only [Mix.int, integral_div, sub_div]

theorem finsum_mult {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {B : LB X} (hB : B.IsLB) (s : B.Sec)
    (hs : genericPoint X ∈ nonzeroLocus s) {r : ℕ} {z : Fin r → X} (hz : Function.Injective z)
    (h : ∀ w : X, w ∉ nonzeroLocus s → Order.coheight w = 1 → ∃ a, w = z a) (g : X → ℝ) :
    ∑ᶠ w, ((divOfSec hB s hs).mult w : ℝ) * g w =
      ∑ a, ((((divOfSec hB s hs).mult (z a)).toNat : ℕ) : ℝ) * g (z a) := by
  classical
  rw [finsum_eq_sum_of_support_subset (s := Finset.univ.image z), Finset.sum_image fun a _ b _ e => hz e]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (mult_divOfSec_nonneg _)]
  · intro w hw
    have h0 : (divOfSec hB s hs).mult w ≠ 0 := fun e => hw (by simp [e])
    obtain ⟨a, rfl⟩ := h w (fun e => notMem_supp_divOfSec.2 e (CartierDiv.mem_supp_of_mult_ne_zero h0))
      (CartierDiv.coheight_eq_one_of_mult_ne_zero h0)
    simp

theorem poincareLelong_snc : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → SmoothOfRelativeDimension (e + 1) p → ∀ (L : Fin e → MLine p σ) (M : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (nonzeroLocus s).compl) → ∀ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), 2 * Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) (M.logSec s) = ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L u z - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) u := by
  intro F _ X _ _ p σ e hp hsm L M s hs hsnc u hu
  haveI : CharZero F := σ.charZero
  haveI := CxPts.compactSpace σ hp
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ hp
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hp
  let R := AnRead.all p σ (e + 1)
  have hA := R.isAlgAtlas_finAtlas
  generalize R.finAtlas = A at hA
  obtain ⟨r, z, hinj, hco, hT, hall, hl⟩ := GlobalTheory.T.snc_closed_eq_iUnion_closure_codim_one_points F X p (e + 1) hp hsm _ hsnc
  have hS := GlobalTheory.T.isAnalyticSNC_of_algebraicSNC_section F X p σ (e + 1) hp hsm A hA M s hs r z hinj hco hT hl
  choose B hB hBint using fun a => GlobalTheory.T.exists_holomorphic_subAtlas_smooth_closedSubscheme F X (clos (z a)) p _ σ hp (closι (z a)) rfl e A hA
    (GlobalTheory.T.smooth_snc_component_closure_charZero F X p e hp hsm r z hl a)
  have pot (N : MLine p σ) : IsPotential A N.φ.locPot :=
    ((Weight.isCInf_iff_isSmooth R).1 N.cInf).isPotential hA
  have hv (y) : CInfAt (fun y => u y / 2) y :=
    ((hu y).const_mul (1 / 2)).congr (.of_forall fun z => by ring)
  have hvc : Continuous fun y => u y / 2 := continuous_iff_continuousAt.2 fun y => (hv y).continuousAt
  have key := poincareLelong A M.φ.locPot _ _ _ B (pot M)
    (M.φ.isSection_of_isAlgAtlas hA (R.secVal_mem_holSec s)) hS hB (fun y => u y / 2)
    ((hA.smooth_iff R).2 ((cInfAt_iff_smoothOn R isOpen_univ).1 fun y _ => hv y))
    (fun i => (L i).φ.locPot) fun i => pot _
  have e₁ : logNormSec M.φ.locPot (M.φ.locSec (secVal p σ s)) = M.logSec s := funext fun y => by
    rw [Weight.logNormSec_locSec, MLine.logSec]; ring
  have e₂ : Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) (M.logSec s) =
      mInt A (Fin.cons (LocPot.ofFun fun y => u y / 2) fun i => (L i).φ.locPot) (M.logSec s) := by
    rw [(GlobalTheory.T.mixedChernIntegral_eq_mongeAmpereIntegral_compact F X p σ _ A hA _ _ (GlobalTheory.Mix.SecNorm.logSec_basic F X p σ M s).1).2
      (GlobalTheory.T.integrable_logNormSection_mixedChernForms F X p σ _ hp hsm _ M s hs)]
    refine SameForm.mInt_eq (fun i => ?_) _
    refine Fin.cases ?_ (fun i => ?_) i
    · exact Weight.sameForm_ofFun A u
    · exact SameForm.refl _ _
  have e₃ : Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (fun y => u y / 2) =
      mInt A (Fin.cons M.φ.locPot fun i => (L i).φ.locPot) fun y => u y / 2 := by
    have h := GlobalTheory.T.mixedChernIntegral_eq_mongeAmpereIntegral_compact F X p σ _ A hA (Fin.cons M L : Fin (e + 1) → MLine p σ) _ hvc.measurable
    rw [h.2 (h.1.2 (mIntegrableCont A _ (fun i => pot _) _ hvc))]
    congr 1
    exact funext fun i => Fin.cases rfl (fun _ => rfl) i
  have e₄ (a) : mInt (B a) (fun i => (L i).φ.locPot.pullback Subtype.val continuous_subtype_val)
      ((fun y => u y / 2) ∘ Subtype.val) = cycInt L u (z a) / 2 :=
    (hBint a L _ hvc).trans (int_half _ _)
  rw [e₁, ← e₂, ← e₃, int_half] at key
  simp only [e₄] at key
  rw [key, finsum_mult M.φ.isLB s hs hinj (fun w hw => hall w hw), mul_sub, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun a _ => by ring
  · ring

end GlobalTheory.Mix.PLSnc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.CmpTrait

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  rw [← Spec.map_id]; rfl

theorem comp_pow'' {S : Scheme.{0}} {A T T₀ : Over S} [GrpObj A] (ρ : T₀ ⟶ T) (x : T ⟶ A) (n : ℕ) :
    ρ ≫ x ^ n = (ρ ≫ x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem card_le_of_thList {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}
    {m : ℕ} {K : Type} [Field K] [IsAlgClosed K] {x : Sp K ⟶ S} {θ θ' : SecAt G L x} {N N' : ℕ}
    {pt : Fin N → (Over.mk x ⟶ G)} {pt' : Fin N' → (Over.mk x ⟶ G)} {c : Fin N → K} {c' : Fin N' → K}
    (h : ThList G L ρ m x θ pt c) (h' : ThList G L ρ m x θ' pt' c') : N ≤ N' := by
  let e : Over.mk (spMap (RingHom.id K) ≫ x) ⟶ Over.mk x := Over.homMk (spMap (RingHom.id K)) rfl
  have key : ∀ a, ∃ b, pt a = pt' b := fun a => by
    have hp : (e ≫ pt a) ^ (m ^ 2) = 1 := by
      rw [← comp_pow'', (h.2.1 a).1, MonObj.comp_one]
    obtain ⟨b, hb⟩ := h'.2.2 K (RingHom.id K) (e ≫ pt a) hp
    refine ⟨b, Over.OverMorphism.ext ?_⟩
    have hb' : spMap (RingHom.id K) ≫ (pt a).left = spMap (RingHom.id K) ≫ (pt' b).left := hb
    rwa [spMap_id', Category.id_comp, Category.id_comp] at hb'
  choose s hs using key
  have hs' : Function.Injective s := fun a a' he => h.1 ((hs a).trans ((congrArg pt' he).trans (hs a').symm))
  simpa using Fintype.card_le_of_injective s hs'

theorem card_eq_of_thList {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}
    {m : ℕ} {K : Type} [Field K] [IsAlgClosed K] {x : Sp K ⟶ S} {θ θ' : SecAt G L x} {N N' : ℕ}
    {pt : Fin N → (Over.mk x ⟶ G)} {pt' : Fin N' → (Over.mk x ⟶ G)} {c : Fin N → K} {c' : Fin N' → K}
    (h : ThList G L ρ m x θ pt c) (h' : ThList G L ρ m x θ' pt' c') : N = N' :=
  le_antisymm (card_le_of_thList h h') (card_le_of_thList h' h)

theorem isGenSec_of_nz {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} (hL : L.IsLB) {g : ℕ} {K : Type}
    [Field K] {x : Sp K ⟶ S} (hP : PolFib G L g x) {θ : SecAt G L x} (hθ : NZ G L x θ) : IsGenSec G L _ θ := by
  obtain ⟨P, α, -, hp, hw⟩ := hP
  obtain ⟨e, he⟩ := exists_univBasis_of_fibre abelianSchemeLaws_all.2 S (Sp K) G L hL P x α hp hw K (𝟙 _) x
    (Category.id_comp x)
  have h0 : spMap (RingHom.id K) ≫ x = x := by rw [spMap_id', Category.id_comp]
  obtain ⟨a, ha⟩ := he.ex (RingHom.id K) h0 (SecM.ofSec G θ)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_smul] at ha
    obtain ⟨q, -, hq⟩ := hθ
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hq
    have e0 : θ.f j = 0 := congrArg (fun s => s.1 j) ha
    rw [e0, Scheme.basicOpen_zero] at hj
    exact hj
  refine (isGenSec_iff θ).2 fun s => ?_
  obtain ⟨b, hb⟩ := he.ex (RingHom.id K) h0 s
  refine ⟨fnR x (b * a⁻¹), ?_⟩
  rw [hb, ha, smul_smul, ← map_mul, _root_.mul_assoc, inv_mul_cancel₀ ha0, _root_.mul_one]

theorem prim_of_finite {V V' K : Type} [CommRing V] [CommRing V'] [Field K] (f : V →+* V') (i : V' →+* K) {J : Type}
    (c : J → K) (hf : f.Finite) (h : Prim i c) : Prim (i.comp f) c := by
  letI := f.toAlgebra
  letI := i.toAlgebra
  letI := (i.comp f).toAlgebra
  haveI : IsScalarTower V V' K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite V V' := hf
  haveI : Algebra.IsIntegral V V' := Algebra.IsIntegral.of_finite V V'
  have key : ∀ z : K, i.IsIntegralElem z → (i.comp f).IsIntegralElem z := fun z hz =>
    isIntegral_trans (R := V) (A := V') z hz
  obtain ⟨h1, a, ha, ha'⟩ := h
  exact ⟨fun b => key _ (h1 b), a, ha, key _ ha'⟩

theorem exists_ext {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] (f : V →+* V')
    (fK : FractionRing V →+* FractionRing V') {K : Type} [Field K] [IsAlgClosed K] (io : FractionRing V →+* K)
    (hf : f.Finite) (hfK : ∀ a, fK (algebraMap V _ a) = algebraMap V' _ (f a)) :
    ∃ io' : FractionRing V' →+* K, io'.comp fK = io := by
  letI := fK.toAlgebra
  letI := io.toAlgebra
  letI := f.toAlgebra
  haveI : Module.Finite V V' := hf
  haveI : Algebra.IsIntegral V V' := Algebra.IsIntegral.of_finite V V'
  have hint : ∀ b : V', IsAlgebraic (FractionRing V) (algebraMap V' (FractionRing V') b) := fun b => by
    obtain ⟨p, hp, hp0⟩ := Algebra.IsIntegral.isIntegral (R := V) b
    refine (show IsIntegral (FractionRing V) (algebraMap V' (FractionRing V') b) from
      ⟨p.map (algebraMap V (FractionRing V)), hp.map _, ?_⟩).isAlgebraic
    rw [Polynomial.eval₂_map]
    have e : (algebraMap (FractionRing V) (FractionRing V')).comp (algebraMap V (FractionRing V)) =
        (algebraMap V' (FractionRing V')).comp (algebraMap V V') := RingHom.ext hfK
    rw [e, ← Polynomial.hom_eval₂, hp0, map_zero]
  haveI : Algebra.IsAlgebraic (FractionRing V) (FractionRing V') := ⟨fun z => by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V') z
    exact (hint a).mul (hint b).inv⟩
  let φ : FractionRing V' →ₐ[FractionRing V] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨φ.toRingHom, RingHom.ext fun a => φ.commutes a⟩

theorem prim_comp {V K : Type} [CommRing V] [Field K] {i : V →+* K} {J J' : Type} {c : J → K} (h : Prim i c)
    (s : J' → J) (hs : Function.Surjective s) : Prim i (c ∘ s) := by
  obtain ⟨h1, a, ha, ha'⟩ := h
  obtain ⟨b, rfl⟩ := hs a
  exact ⟨fun b => h1 _, b, ha, ha'⟩

theorem cmp_trait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (y : Sp (FractionRing V) ⟶ Xo.XF c) (K : Type) [Field K] [IsAlgClosed K] (io : FractionRing V →+* K) (m m' N N' : ℕ) (d : Fin N → K) (d' : Fin N' → K), Odd m → 3 ≤ m → IsUnit (m : V) → Odd m' → 3 ≤ m' → IsUnit (m' : V) → HasTh₂ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m m' (spMap io ≫ y ≫ pullback.fst _ _) d d' → ∃ a : K, a ≠ 0 ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => d b / a) ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => d' b / a) := by
  intro E _ _ _ H Dw l Xo c V _ _ _ hV y K _ _ io m m' N N' d d' hmo hm3 hmu hmo' hm3' hmu' hd
  have hbase : GlobalTheory.Mum.Base V := ⟨ArcPointDescent.admissibleBase_maximalIdeal_completeDVR hV, hV.2.2⟩
  obtain ⟨T, f, fK, -, -, hff, hfK, hTy⟩ := GlobalTheory.T.exists_unitaryTrait_through_moduliGenericPoint E H Dw l Xo c V hbase hV.1 y
  obtain ⟨io', hio'⟩ := exists_ext f fK io hff hfK
  set i : T.V →+* K := io'.comp (algebraMap T.V (FractionRing T.V)) with hi
  have hinj : Function.Injective i := io'.injective.comp (IsFractionRing.injective T.V (FractionRing T.V))
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  obtain ⟨tK, ⟨mK⟩, ⟨mx⟩⟩ := T.gen
  obtain ⟨m0, -⟩ := ObjMaps.exists_sab_id T.t
  have hpol : GlobalTheory.LN.PolAt T.t (jK T.V) := UnifAfterExt.polAt_of_sabMap m0 mK mx Xo.univ.proper Xo.univ.ample
    Xo.univ.ktriv (jK T.V) (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
  obtain ⟨σ, hσ⟩ := exists_nz_of_polAt abelianSchemeLaws_all.1 abelianSchemeLaws_all.2 E H (Sp T.V) T.t T.V (𝟙 _) T.t m0
    hpol
  have h0 : spMap (RingHom.id T.V) ≫ 𝟙 (Sp T.V) = 𝟙 _ := by rw [Category.comp_id, spMap_id']
  have hσσ : VVRank.pullS T.t.G _ (Over.homMk (spMap (RingHom.id T.V)) h0 : Over.mk (𝟙 (Sp T.V)) ⟶ Over.mk (𝟙 _)) σ = σ := by
    have e : (Over.homMk (spMap (RingHom.id T.V)) h0 : Over.mk (𝟙 (Sp T.V)) ⟶ Over.mk (𝟙 _)) = 𝟙 _ :=
      Over.OverMorphism.ext (spMap_id' T.V)
    rw [e]
    have := VVRank.pullM_id T.t.G T.t.PP.isLB ((1 : ℕ) : ℤ) (SecM.ofSec T.t.G σ)
    rw [VVRank.pullM_ofSec] at this
    exact congrArg (SecM.toSec T.t.G) this
  have hnz : NZ T.t.G T.t.PP.L (𝟙 _) σ := by
    have := hσ T.V (RingHom.id _) _ h0
    rwa [hσσ] at this
  have hmT : ∀ {k : ℕ}, IsUnit (k : V) → IsUnit (k : T.V) := fun h => by simpa using h.map f
  have hmK : ∀ {k : ℕ}, IsUnit (k : V) → (k : K) ≠ 0 := fun h => by
    have := h.map (io.comp (algebraMap V (FractionRing V))); simpa using this.ne_zero
  set x₁ : Sp K ⟶ Sp T.V := spMap i ≫ 𝟙 (Sp T.V) with hx₁
  have ex₁ : spMap io' ≫ jK T.V = x₁ := by rw [hx₁, Category.comp_id, hi, spMap_comp']
  set x : Sp K ⟶ Xo.X := spMap io ≫ y ≫ pullback.fst _ _ with hx
  have ex : spMap io' ≫ T.y ≫ pullback.fst _ _ = x := by rw [hx, hTy, ← hio', spMap_comp']; simp only [Category.assoc]
  set g := Module.finrank ℚ E / 2 * (Dw.p + Dw.q) with hg
  have hPx : PolFib Xo.univ.t.G Xo.univ.t.PP.L g x := GlobalTheory.T.universalTriple_fibre_principallyPolarised_dimension E H Dw l Xo c K x
  obtain ⟨wK, hwK, -⟩ := mK.lin
  obtain ⟨wx, hwx, -⟩ := mx.lin
  have hPK : PolFib tK.G tK.PP.L g (spMap io') :=
    ((GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback _ _ _ _ _ _ _ _ Xo.univ.t.PP.isLB tK.PP.isLB mx.cart ⟨wx, hwx⟩ g K (spMap io')).1).2 (ex ▸ hPx)
  have hP₁ : PolFib T.t.G T.t.PP.L g x₁ :=
    ex₁ ▸ ((GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback _ _ _ _ _ _ _ _ T.t.PP.isLB tK.PP.isLB mK.cart ⟨wK, hwK⟩ g K (spMap io')).1).1 hPK
  set θ := SecAt.pull T.t.G T.t.PP.L σ i with hθdef
  have hθnz : NZ T.t.G T.t.PP.L x₁ θ := hσ K i x₁ rfl
  have hθ : IsGenSec T.t.G T.t.PP.L _ θ := isGenSec_of_nz T.t.PP.isLB hP₁ hθnz
  obtain ⟨pt, cc, hc⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed _ T.t.G T.t.PP.L T.t.PP.rig T.t.PP.isLB T.t.PP.rigGen g m _ K x₁ θ hmo (hmK hmu)
    rfl hP₁
  obtain ⟨pt', cc', hc'⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed _ T.t.G T.t.PP.L T.t.PP.rig T.t.PP.isLB T.t.PP.rigGen g m' _ K x₁ θ hmo'
    (hmK hmu') rfl hP₁
  have hpr : Prim i cc := GlobalTheory.T.thetaConstants_primitive_at_uniformisedTrait E H (Sp T.V) T.t T.V T.cdvr (𝟙 _) T.t ⟨m0⟩ ⟨T.P⟩ σ hnz m _ hmo hm3 (hmT hmu)
    K i pt cc hinj hc
  have hpr' : Prim i cc' := GlobalTheory.T.thetaConstants_primitive_at_uniformisedTrait E H (Sp T.V) T.t T.V T.cdvr (𝟙 _) T.t ⟨m0⟩ ⟨T.P⟩ σ hnz m' _ hmo' hm3'
    (hmT hmu') K i pt' cc' hinj hc'
  have h₁ : HasTh₂ T.t.G T.t.PP.L T.t.PP.rig m m' x₁ cc cc' := ⟨θ, pt, pt', hθ, hc, hc'⟩
  have hK : HasTh₂ tK.G tK.PP.L tK.PP.rig m m' (spMap io') cc cc' :=
    (GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian _ T.t.G T.t.PP.L T.t.PP.rig T.t.PP.isLB T.t.PP.rigGen _ tK.G tK.PP.L tK.PP.rig (jK T.V) mK.φ
      tK.PP.isLB tK.PP.rigGen mK.cart ⟨wK, hwK⟩ m m' _ _ K (spMap io') cc cc').2 (ex₁ ▸ h₁)
  have hX : HasTh₂ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m m' x cc cc' :=
    ex ▸ (GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian _ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig Xo.univ.t.PP.isLB Xo.univ.t.PP.rigGen _ tK.G
      tK.PP.L tK.PP.rig (T.y ≫ pullback.fst _ _) mx.φ tK.PP.isLB tK.PP.rigGen mx.cart ⟨wx, hwx⟩ m m' _ _ K (spMap io')
      cc cc').1 hK
  have eN : N = m ^ (4 * g) := by
    obtain ⟨_, _, _, _, hd1, -⟩ := hd
    obtain ⟨_, _, _, _, hc1, -⟩ := hX
    exact card_eq_of_thList hd1 hc1
  have eN' : N' = m' ^ (4 * g) := by
    obtain ⟨_, _, _, _, -, hd2⟩ := hd
    obtain ⟨_, _, _, _, -, hc2⟩ := hX
    exact card_eq_of_thList hd2 hc2
  subst eN eN'
  obtain ⟨a, s, s', ha, hds, hds'⟩ := (GlobalTheory.T.thetaConstantLists_unique_up_to_perm_scalar _ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig Xo.univ.t.PP.isLB
    Xo.univ.t.PP.rigGen g m m' _ _ K x hmo (hmK hmu) hmo' (hmK hmu') hPx).2 cc d cc' d' hX hd
  have ei : i.comp f = io.comp (algebraMap V (FractionRing V)) := by
    ext v
    simp only [hi, RingHom.comp_apply, ← hfK, ← hio']
  have e1 : (fun b => d b / a) = cc ∘ s := funext fun b => by
    rw [hds b, Function.comp_apply, mul_div_cancel_left₀ _ ha]
  have e2 : (fun b => d' b / a) = cc' ∘ s' := funext fun b => by
    rw [hds' b, Function.comp_apply, mul_div_cancel_left₀ _ ha]
  refine ⟨a, ha, ?_, ?_⟩
  · rw [e1, ← ei]
    exact prim_of_finite f i _ hff (prim_comp hpr s s.surjective)
  · rw [e2, ← ei]
    exact prim_of_finite f i _ hff (prim_comp hpr' s' s'.surjective)

end GlobalTheory.UMin.CmpTrait
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.exists_birationalModel_totallyOrdered_family : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (J : Type) [Finite J] (f : J → X.functionField), (∀ j, f j ≠ 0) → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ X) (φ : X.functionField →+* Y.functionField), IsArithVar (π ≫ p) D ∧ IsModel π φ ∧ Total (fun j => φ (f j)) := by
  first | exact @GlobalTheory.HSNef.exists_model_total | exact GlobalTheory.HSNef.exists_model_total | (intros; apply GlobalTheory.HSNef.exists_model_total <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.KleimanStep

theorem selfInter_nonneg : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → 1 ≤ D →
    (∀ (C : HermLB p) (h : X → ℝ), C.IsNef D → C.IsArithHeight h → ∀ z, z ≠ genericPoint X → 0 ≤ h z) →
    ∀ (C : HermLB p) (c : ℝ), C.IsNef D → C.IsSelfInter c → 0 ≤ c := by
  intro hC hHS k _ X _ p D hX hD hlow C c hnef hc
  obtain ⟨A, hA, hAn, -⟩ := GlobalTheory.AmpleNefSmall.exists_ample_nef_smallSec hC k X p D hX
  obtain ⟨α, hα, hlim⟩ := GlobalTheory.SelfInterGrowth.main hC k X p D hX C A c hc
  refine ge_of_tendsto' hlim fun n => div_nonneg ?_ (by positivity)
  have hpow := GlobalTheory.NefPow.isNef_pow hC k X p D hX C n hnef
  have htens := GlobalTheory.T.hermLineBundle_isNef_tens hC k X p D hX _ _ hpow hAn
  have hamp := GlobalTheory.T.isAmple_tensor_of_nef_fibres_ample k X p D hX _ A hpow.vertical hA
  obtain ⟨h, hh, he⟩ := hα n
  rw [← he]
  exact GlobalTheory.T.height_genericPoint_nonneg_ample_semiPositive hC hHS k X p D hX hD _ h hamp htens.semiPos hh (hlow _ h htens hh)

end GlobalTheory.KleimanStep
end
