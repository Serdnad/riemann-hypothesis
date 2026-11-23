module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle026
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PHilbDegreeBound
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.CechHcSubsingletonOfBij
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle044
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle041
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle044
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle045
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle051
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHCechSES
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle042
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle052
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle048
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle056
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsSumEqOneOfMulEqOne
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGraphClosed
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle050
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart CechC)

noncomputable section

namespace EulerVar

variable {F : Type} [Field F] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)]

theorem quot_congr {X : Type} [AddCommGroup X] [Module F X] {Z Z' B B' : Submodule F X} (hZ : Z = Z')
    (hB : B = B') :
    Module.finrank F (↥Z ⧸ B.comap Z.subtype) = Module.finrank F (↥Z' ⧸ B'.comap Z'.subtype) ∧
      (FiniteDimensional F (↥Z ⧸ B.comap Z.subtype) ↔ FiniteDimensional F (↥Z' ⧸ B'.comap Z'.subtype)) := by
  subst hZ hB
  exact ⟨rfl, Iff.rfl⟩

theorem cechHc_eq_coh {M : Type} [AddCommGroup M] [Module (MRingOver F ι) M] [Module F M]
    [IsScalarTower F (MRingOver F ι) M] (𝓜 : (K → ℤ) → Submodule F M) (c : K → ℤ) (n : ℕ) :
    Module.finrank F (cechHc ι 𝓜 c n) = Module.finrank F (EulerSES.coh (fun n => KH.cechCc ι 𝓜 c n)
      (fun n => (KH.cechD F ι M n).restrictScalars F) n) ∧
    (FiniteDimensional F (cechHc ι 𝓜 c n) ↔ FiniteDimensional F (EulerSES.coh (fun n => KH.cechCc ι 𝓜 c n)
      (fun n => (KH.cechD F ι M n).restrictScalars F) n)) := by
  have hZ : KH.cechZc ι 𝓜 c n = EulerSES.cyc (fun n => KH.cechCc ι 𝓜 c n)
      (fun n => (KH.cechD F ι M n).restrictScalars F) n := by
    simp only [KH.cechZc, EulerSES.cyc, LinearMap.ker_restrictScalars]
  have hB : KH.cechBc ι 𝓜 c n = EulerSES.bnd (fun n => KH.cechCc ι 𝓜 c n)
      (fun n => (KH.cechD F ι M n).restrictScalars F) n := by
    cases n <;> rfl
  exact quot_congr hZ hB

theorem coh_top {M : Type} [AddCommGroup M] [Module (MRingOver F ι) M] [Module F M]
    [IsScalarTower F (MRingOver F ι) M] (𝓜 : (K → ℤ) → Submodule F M) (c : K → ℤ) :
    Subsingleton (EulerSES.coh (fun n => KH.cechCc ι 𝓜 c n) (fun n => (KH.cechD F ι M n).restrictScalars F)
      (∑ k, (Fintype.card (ι k) - 1) + 1)) := by
  have hI : ∀ I : KH.Cell K ι (∑ k, (Fintype.card (ι k) - 1) + 1), False := fun I => by
    have h1 : ∑ k, ((I.1 k).card - 1) ≤ ∑ k, (Fintype.card (ι k) - 1) :=
      Finset.sum_le_sum fun k _ => Nat.sub_le_sub_right (Finset.card_le_univ _) 1
    have := I.2.2
    omega
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  congr 1
  exact Subtype.ext (funext fun I => (hI I).elim)

end EulerVar



open EulerVar in
theorem EulerVar.proof (hSq : KH.CechDSqStatement) (hE : EulerSES.Statement) : EulerVar.Statement := by
  classical
  intro F _ K _ _ ι _ _ V v hV hfV hfW hfU m
  set x : MvPolynomial (Σ k, ι k) F := X v with hx
  set W := V.colon (Ideal.span {x}) with hW
  set U := V ⊔ Ideal.span {x} with hU
  set e : K → ℤ := Pi.single v.1 1 with he

  have hWV : W ≤ Submodule.comap (LinearMap.mulLeft (MvPolynomial (Σ k, ι k) F) x) V := fun p hp => by
    rw [hW, Submodule.mem_colon_span_singleton, smul_eq_mul] at hp
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply, mul_comm]
    exact hp
  let g : (MvPolynomial (Σ k, ι k) F ⧸ W) →ₗ[MvPolynomial (Σ k, ι k) F] (MvPolynomial (Σ k, ι k) F ⧸ V) :=
    Submodule.mapQ W V (LinearMap.mulLeft _ x) hWV
  let h : (MvPolynomial (Σ k, ι k) F ⧸ V) →ₗ[MvPolynomial (Σ k, ι k) F] (MvPolynomial (Σ k, ι k) F ⧸ U) :=
    Submodule.factor (le_sup_left : V ≤ U)
  have hg_mk : ∀ p, g (Ideal.Quotient.mk W p) = Ideal.Quotient.mk V (x * p) := fun p => rfl
  have hh_mk : ∀ p, h (Ideal.Quotient.mk V p) = Ideal.Quotient.mk U p := fun p => rfl
  have hinj : Function.Injective g := by
    refine (injective_iff_map_eq_zero g).2 fun a ha => ?_
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [hg_mk, Ideal.Quotient.eq_zero_iff_mem] at ha
    rw [Ideal.Quotient.eq_zero_iff_mem, hW, Submodule.mem_colon_span_singleton, smul_eq_mul, mul_comm]
    exact ha
  have hsurj : Function.Surjective h := fun b => by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨Ideal.Quotient.mk V p, hh_mk p⟩
  have hex : LinearMap.range g = LinearMap.ker h := by
    ext b
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [LinearMap.mem_range, LinearMap.mem_ker, hh_mk, Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · rintro ⟨a, ha⟩
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [hg_mk, Ideal.Quotient.eq] at ha
      have h1 : x * p ∈ U := Ideal.mem_sup_right (Ideal.mul_mem_right p _ (Ideal.subset_span rfl))
      have h2 : x * p - q ∈ U := Ideal.mem_sup_left ha
      have := U.sub_mem h1 h2
      rwa [sub_sub_cancel] at this
    · intro hq
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hq
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hb
      refine ⟨Ideal.Quotient.mk W r, ?_⟩
      rw [hg_mk, Ideal.Quotient.eq]
      have : x * r - (a + r * x) = -a := by ring
      rw [this]
      exact V.neg_mem ha

  have hVW : NumbersDVR.IsMultiHomogIdeal W := snapper_colon_X hV v
  have hVU : NumbersDVR.IsMultiHomogIdeal U :=
    FieldNumbers.isMultiHomogIdeal_sup_span hV (isWeightedHomogeneous_X F (NumbersDVR.blockWeight ι) v)
  have grV := HilbertSamuel.QuotPartGraded.proof F K ι V ((NumbersDVR.Objects.isMultiHomogIdeal_iff V).1 hV)
  have grW := HilbertSamuel.QuotPartGraded.proof F K ι W ((NumbersDVR.Objects.isMultiHomogIdeal_iff W).1 hVW)
  have grU := HilbertSamuel.QuotPartGraded.proof F K ι U ((NumbersDVR.Objects.isMultiHomogIdeal_iff U).1 hVU)
  have grW' := HilbertSamuel.H1VanishingDevissage.isMGraded_shift grW (-e)
  have hxe : IsWeightedHomogeneous (HilbertSamuel.QuotPartGraded.blockWeight ι) x e := by
    have := isWeightedHomogeneous_X F (HilbertSamuel.QuotPartGraded.blockWeight ι) v
    convert this using 1
    ext k
    simp [HilbertSamuel.QuotPartGraded.blockWeight, he, Pi.single_apply]
  have hg : KH.IsMGradedMap F ι (fun d => quotPart F W (d + -e)) (quotPart F V) g := by
    intro c y hy
    change y ∈ quotPart F W (c + -e) at hy
    rw [HilbertSamuel.QuotPartGraded.quotPart_eq] at hy ⊢
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hy
    refine Submodule.mem_map.2 ⟨x * p, ?_, rfl⟩
    rw [mem_weightedHomogeneousSubmodule]
    have hc : c = e + (c + -e) := by abel
    rw [hc]
    exact hxe.mul hp
  have hh : KH.IsMGradedMap F ι (quotPart F V) (quotPart F U) h := by
    intro c y hy
    rw [HilbertSamuel.QuotPartGraded.quotPart_eq] at hy ⊢
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hy
    exact Submodule.mem_map.2 ⟨p, hp, rfl⟩
  have hCA : ∀ n, KH.cechCc ι (fun d => quotPart F W (d + -e)) m n = KH.cechCc ι (quotPart F W) (m - e) n := by
    intro n
    rw [HilbertSamuel.H1VanishingDevissage.cechCc_shift, sub_eq_add_neg]

  have key := hE F (fun n => CechC F ι (MvPolynomial (Σ k, ι k) F ⧸ W) n)
    (fun n => CechC F ι (MvPolynomial (Σ k, ι k) F ⧸ V) n) (fun n => CechC F ι (MvPolynomial (Σ k, ι k) F ⧸ U) n)
    (fun n => KH.cechCc ι (quotPart F W) (m - e) n) (fun n => KH.cechCc ι (quotPart F V) m n)
    (fun n => KH.cechCc ι (quotPart F U) m n)
    (fun n => (KH.cechD F ι _ n).restrictScalars F) (fun n => (KH.cechD F ι _ n).restrictScalars F)
    (fun n => (KH.cechD F ι _ n).restrictScalars F)
    (fun n => (KH.cechMap F ι g n).restrictScalars F) (fun n => (KH.cechMap F ι h n).restrictScalars F)
    (∑ k, (Fintype.card (ι k) - 1))
    (fun n y hy => KHCechDDeg.full F K ι _ (quotPart F W) (m - e) n y hy)
    (fun n y hy => KHCechDDeg.full F K ι _ (quotPart F V) m n y hy)
    (fun n y hy => KHCechDDeg.full F K ι _ (quotPart F U) m n y hy)
    (fun n y _ => LinearMap.congr_fun (hSq F K ι _ n) y) (fun n y _ => LinearMap.congr_fun (hSq F K ι _ n) y)
    (fun n y _ => LinearMap.congr_fun (hSq F K ι _ n) y)
    (fun n y hy => (KHCechMapDeg.full F K ι _ _ _ _ g m n hg).1 y (by rw [hCA]; exact hy))
    (fun n y hy => (KHCechMapDeg.full F K ι _ _ _ _ h m n hh).1 y hy)
    (fun n y _ => LinearMap.congr_fun (KHCechMapDeg.full F K ι _ _ _ _ g m n hg).2 y)
    (fun n y _ => LinearMap.congr_fun (KHCechMapDeg.full F K ι _ _ _ _ h m n hh).2 y)
    (fun n y _ hy0 => KHCechSES.cechMap_injective hinj n (hy0.trans (map_zero _).symm))
    (fun n y _ => KHCechSES.cechMap_comp_eq_zero hex n y)
    (fun n y hy h0 => by
      obtain ⟨z, hz, hzy⟩ := KHCechSES.cechMap_exact grW' grV hg hinj hex hy h0
      exact ⟨z, (hCA n) ▸ hz, hzy⟩)
    (fun n y hy => KHCechSES.cechMap_lift grV grU hh hsurj hy)
    (fun n => ((cechHc_eq_coh _ _ n).2).1 (hfW (m - e) n))
    (fun n => ((cechHc_eq_coh _ _ n).2).1 (hfV m n))
    (fun n => ((cechHc_eq_coh _ _ n).2).1 (hfU m n))
    (coh_top _ _)
  have eA : ∀ n, (Module.finrank F (EulerSES.coh (fun n => KH.cechCc ι (quotPart F W) (m - e) n)
      (fun n => (KH.cechD F ι (MvPolynomial (Σ k, ι k) F ⧸ W) n).restrictScalars F) n) : ℤ) =
      Module.finrank F (cechHc ι (quotPart F W) (m - e) n) := fun n => by rw [(cechHc_eq_coh _ _ n).1]
  have eB : ∀ n, (Module.finrank F (EulerSES.coh (fun n => KH.cechCc ι (quotPart F V) m n)
      (fun n => (KH.cechD F ι (MvPolynomial (Σ k, ι k) F ⧸ V) n).restrictScalars F) n) : ℤ) =
      Module.finrank F (cechHc ι (quotPart F V) m n) := fun n => by rw [(cechHc_eq_coh _ _ n).1]
  have eC : ∀ n, (Module.finrank F (EulerSES.coh (fun n => KH.cechCc ι (quotPart F U) m n)
      (fun n => (KH.cechD F ι (MvPolynomial (Σ k, ι k) F ⧸ U) n).restrictScalars F) n) : ℤ) =
      Module.finrank F (cechHc ι (quotPart F U) m n) := fun n => by rw [(cechHc_eq_coh _ _ n).1]
  simp only [eA, eB, eC] at key
  have key' := congrArg (Int.cast : ℤ → ℚ) key
  push_cast at key'
  unfold eulerChar
  exact key'

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

theorem twistMul_twist_twistSys {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} (M : SubSystem S x Ω) (a : ℕ) (m c : ℤ) :
    (twistMul M a m).twist (twistSys S x c) = twistMul M a (m + c) := by
  rw [twistMul, twistMul, SubSystem.twist_assoc, twistSys_twist_eq_add]

theorem ModelVeryAmpleEq.proof (hVA : VeryAmpleEq.Statement) (hMS : ModelMulSecs.Statement)
    (hCh : ModelChangeVeryAmple.Statement) : ModelVeryAmpleEq.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e hmod β Q hQ a m _
  have hx : ∃ i, (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) i ≠ 0 := by
    obtain ⟨i, hi⟩ := hmod.1 k₀
    exact ⟨e i, by simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hi⟩
  obtain ⟨L, hL⟩ := exists_lineBundle_twistMul Q a m
  obtain ⟨n, hn⟩ := Generated.full.{0, 0} F Ω N (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) L
  obtain ⟨r, g, -, hg⟩ := GraphClosedAlt.exists_fin_generators
    (L.tensorProd (twistBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) n)) (hn n le_rfl)
  have hgen : IsGraphGen L n g := hg
  have hmod' := GraphModel.full F N Ω _ L n (r + 1) g hx hgen
  have hsec := twist_secs_eq_secOver L n g hgen
  have hH : ∀ c : ℤ, (L.twist (twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).secs =
      secOver F y (a • β + m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) := by
    intro c
    rw [hL, twistMul_twist_twistSys, hMS F K ι Ω y k₀ N e hmod β Q hQ a (m + c), add_smul, add_assoc]
  rw [← hL, hVA F N Ω _ L n (r + 1) g hgen]
  exact hCh F Ω N (Unit ⊕ Unit) (graphIdx N (r + 1)) _ baseBlock (Equiv.refl _) K ι y k₀ e hmod' hmod rfl
    (graphDeg n) (a • β + m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) (fun c => (hsec c).symm.trans (hH c))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem ModelDim.proof : ModelDim.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hmod n
  subst hx
  exact ModelDimEq.full F K ι Ω y k₀ N e hmod n

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)

noncomputable section

section Generic

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ a, Fintype (ι a)] {k : Type} [Field k]


omit [Fintype K] [DecidableEq K] [∀ a, Fintype (ι a)] in
theorem X_mem_mIdealOver_iff {Ω : Type} [Field Ω] [Algebra k Ω] (y : (Σ a, ι a) → Ω) (p : Σ a, ι a) :
    (X p : NumbersDVR.MRing ι k) ∈ mIdealOver k y ↔ y p = 0 := by
  change mConeMapOver k y (X p) = 0 ↔ _
  simp [mConeMapOver, X_ne_zero]

def genPtOf (W : Ideal (NumbersDVR.MRing ι k)) [W.IsPrime] :
    (Σ a, ι a) → FractionRing (NumbersDVR.MRing ι k ⧸ W) :=
  fun p => algebraMap _ _ (Ideal.Quotient.mk W (X p))


omit [Fintype K] [DecidableEq K] [∀ a, Fintype (ι a)] in
theorem aeval_genPtOf (W : Ideal (NumbersDVR.MRing ι k)) [W.IsPrime] (g : NumbersDVR.MRing ι k) :
    aeval (genPtOf W) g = algebraMap _ (FractionRing (NumbersDVR.MRing ι k ⧸ W)) (Ideal.Quotient.mk W g) := by
  have h : (aeval (genPtOf W) : NumbersDVR.MRing ι k →ₐ[k] FractionRing (NumbersDVR.MRing ι k ⧸ W)) =
      (IsScalarTower.toAlgHom k (NumbersDVR.MRing ι k ⧸ W) (FractionRing (NumbersDVR.MRing ι k ⧸ W))).comp
        (Ideal.Quotient.mkₐ k W) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [genPtOf]
  exact congrArg (fun φ : NumbersDVR.MRing ι k →ₐ[k] FractionRing (NumbersDVR.MRing ι k ⧸ W) => φ g) h

theorem mIdealOver_genPtOf (W : Ideal (NumbersDVR.MRing ι k)) [W.IsPrime] (hh : NumbersDVR.IsMultiHomogIdeal W) :
    mIdealOver k (genPtOf W) = W := by
  have hz : ∀ g, aeval (genPtOf W) g = 0 ↔ g ∈ W := fun g => by
    rw [aeval_genPtOf, ← Ideal.Quotient.eq_zero_iff_mem]
    exact (IsFractionRing.injective (NumbersDVR.MRing ι k ⧸ W) (FractionRing (NumbersDVR.MRing ι k ⧸ W))).eq_iff'
      (map_zero _)
  ext f
  change mConeMapOver k (genPtOf W) f = 0 ↔ f ∈ W
  constructor
  · intro h
    rw [← sum_weightedHomogeneousComponent (NumbersDVR.blockWeight ι) f,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
    refine Ideal.sum_mem _ fun b _ => (hz _).mp ?_
    rw [← coeff_mConeMapOver, h, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  · intro hf
    ext e
    rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply,
      ← Finsupp.equivFunOnFinite_symm_coe e, coeff_mConeMapOver]
    exact (hz _).mpr (hh f hf _)

end Generic

theorem DegEq.proof (hGR : GraphRestrict.Statement) (hIR : Kleiman.InterNumRestrict.Statement.{0, 0})
    (hNM : NumModel.Statement) : DegEq.Statement := by
  intro k _ N Ω _ _ x Q n m s _ hgen pp W hsub hW hle hcomap
  classical
  have := hW.isPrime
  have hWy : mIdealOver k (genPtOf W) = W := mIdealOver_genPtOf W hW.multiHomog
  let x' : Fin (N + 1) → FractionRing (NumbersDVR.MRing (graphIdx N m) k ⧸ W) := fun a => genPtOf W ⟨Sum.inl (), a⟩
  let s' : Fin m → FractionRing (NumbersDVR.MRing (graphIdx N m) k ⧸ W) := fun b => genPtOf W ⟨Sum.inr (), b⟩
  have hy : graphVec x' s' = genPtOf W := by
    funext p
    rcases p with ⟨⟨⟩ | ⟨⟩, a⟩ <;> rfl
  have hzero : ∀ p, genPtOf W p = 0 ↔ (X p : NumbersDVR.MRing (graphIdx N m) k) ∈ W := fun p => by
    rw [← X_mem_mIdealOver_iff (k := k), hWy]
  have hxy : ∀ i, x' i ≠ 0 → x i ≠ 0 := fun i h h0 =>
    h ((hzero _).mpr (hle ((X_mem_mIdealOver_iff (graphVec x s) ⟨Sum.inl (), i⟩).mpr h0)))
  have hx' : ∃ i, x' i ≠ 0 := by
    obtain ⟨i, hi⟩ := hW.relevant (Sum.inl ())
    exact ⟨i, fun h => hi ((hzero _).mp h)⟩
  have hs' : ∃ j, s' j ≠ 0 := by
    obtain ⟨j, hj⟩ := hW.relevant (Sum.inr ())
    exact ⟨j, fun h => hj ((hzero _).mp h)⟩
  have hyW : mIdealOver k (graphVec x' s') = W := by rw [hy]; exact hWy
  have hleW : mIdealOver k (graphVec x s) ≤ mIdealOver k (graphVec x' s') := hyW.symm ▸ hle
  have hpp : Kleiman.primeOf (S := k) x' = pp := by
    rw [← comap_mIdealOver_graph (S := k) x' s', hyW, hcomap]
  obtain ⟨Q', r, hR, hgen'⟩ := hGR k N Ω x Q n m s _ x' s' hxy hgen hleW hx' hs'
  have hsub' : Kleiman.IsSubvar x' pp 1 := ⟨hsub.isPrime, hsub.homog, le_of_eq hpp, hsub.relevant, hsub.dim⟩
  have h1 := hIR k Ω N x _ x' hxy (hsub.le.trans hpp.ge) pp 1 hsub' ![Q] ![Q'] (fun _ => r)
    (fun i => by fin_cases i; exact hR)
  have h2 := hNM k (Unit ⊕ Unit) (graphIdx N m) _ (graphVec x' s') baseBlock N (Equiv.refl _) x' rfl
    (GraphModel.full k N _ x' Q' n m s' hx' hgen') 1 ![Q'] ![graphDeg n]
    (fun i => by fin_cases i; exact realises_graph Q' n s' hgen') (by rw [hpp]; exact hsub')
  rw [hyW, hpp] at h2
  have e1 : (fun i => (![Q] i).toSubSystem) = ![Q.toSubSystem] := by
    funext i; fin_cases i; rfl
  have e2 : (fun i => (![Q'] i).toSubSystem) = ![Q'.toSubSystem] := by
    funext i; fin_cases i; rfl
  rw [e1, e2] at h1
  rw [e2] at h2
  rw [← h2, h1]

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
