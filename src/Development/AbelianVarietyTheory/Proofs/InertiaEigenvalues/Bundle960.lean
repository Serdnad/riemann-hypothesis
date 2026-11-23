module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle920
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2267
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle946
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle881
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle868
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle297
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle894
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefficientFieldAlgClosedInFunctionFieldsOfPerio
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle954
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorThetaLiftOfBaseLevelLaw
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle573
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle606
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle200
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
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
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

noncomputable section

namespace GlobalTheory.PlaceRead.LevVal

variable {D : D7}

theorem mem_intLL_of_pow {z : ℂ} {n : ℕ} (hn : n ≠ 0) (h : z ^ n = 1) (hz : ∃ y, D.what₂.embLL y = z) : z ∈ intLL D := by
  obtain ⟨y, rfl⟩ := hz
  have h1 : y ^ n = 1 := D.what₂.embLL.injective (by rw [map_pow, h, map_one])
  have hi : IsIntegral ℤ y := ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn, by simp [h1]⟩
  exact ⟨⟨y, hi⟩, rfl⟩

theorem mem_range_of_pow_of_fixed {K : Type} [Field K] [Countable K] [CharZero K] (f : K →+* ℂ) {z : ℂ} {n : ℕ} (hn : n ≠ 0)
    (h : z ^ n = 1) (hf : ∀ τ : ℂ ≃+* ℂ, (∀ x, τ (f x) = f x) → τ z = z) : ∃ y, f y = z := by
  letI : Algebra K ℂ := f.toAlgebra
  have hi : IsIntegral K z := ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn, by simp [h]⟩
  let L := IntermediateField.adjoin K {z}
  haveI : FiniteDimensional K L := IntermediateField.adjoin.finiteDimensional hi
  haveI : Countable L := (Module.finBasis K L).equivFun.toEquiv.injective.countable
  let r : L := ⟨z, IntermediateField.mem_adjoin_simple_self K z⟩
  obtain ⟨y, hy⟩ := GlobalTheory.CompRat.FixedConst.mem_range_of_fixed (K := K) L.val (r := r) (IsIntegral.of_finite K r) hf
  exact ⟨y, congrArg Subtype.val hy⟩

theorem twistOf_good {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (hψ : TwOK i k Q ψ) (f : D.ntw.Ok i k →+* ℂ) :
    (twistOf ρ.rc f (ρ.ch i) Q ψ).Good ∧
      ∀ x, ∃ σ, (((twistOf ρ.rc f (ρ.ch i) Q ψ).chi x : Circle) : ℂ) = f (ψ σ : (D.ntw.Ok i k)ˣ) ∧ ∃ n ≠ 0, ψ σ ^ n = 1 := by
  classical
  obtain ⟨hsplit, hdisj, hopen, hanti, hzk, hram, -⟩ := hψ
  have hadm : (ρ.B i j b).admitted (half (ρ.ch i) Q) := GlobalTheory.T.chosenPlaces_admissible_goodSetup D D.nd D.ntw ρ hρ i j b Q hsplit hdisj
  let g : (D.ntw.Ok i k)ˣ →* Circle := unitPart.comp (Units.map f.toMonoidHom)
  have hkey : charOf ρ.rc f ψ = ρ.rc.pull (g.comp ψ) := by
    rw [Recip.pull_comp _ hopen]
    rfl
  have hz : D.ntw.zk i k ^ (D.ntw.l i ^ k) = 1 := Units.ext (by simpa using (D.ntw.zk_prim i k).pow_eq_one)
  have hpow : ∀ σ, ψ σ ^ (D.ntw.l i ^ k) = 1 := by
    intro σ
    obtain ⟨m, hm⟩ := hzk σ
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  refine ⟨?_, ?_⟩
  · show (⟨half (ρ.ch i) Q, charOf ρ.rc f ψ, resOf (charOf ρ.rc f ψ)⟩ : Twist D Circle).Good
    rw [hkey]
    refine GlobalTheory.T.artinPullback_isGoodTwist_of_anticyclotomic_tame D D.nd D.ntw ρ.rc hρ.rc Circle (g.comp ψ) (D.ntw.l i) (D.ntw.lPrime i).out
      (fun σ => ⟨k, by rw [MonoidHom.comp_apply, ← map_pow, hpow, map_one]⟩) ?_ ?_ _ ?_ ?_ ?_
    · exact Subgroup.isOpen_mono (H₁ := ψ.ker) (fun x hx => by
        rw [MonoidHom.mem_ker] at hx ⊢
        rw [MonoidHom.comp_apply, hx, map_one]) hopen
    · intro x x' hx
      show g (ψ x') = (g (ψ x))⁻¹
      rw [hanti x x' hx, map_inv]
    · obtain ⟨P, -, h2, h3⟩ := hadm.1.split
      exact h3.mono (Finset.subset_union_right.trans h2)
    · intro P hP hl
      exact Finset.disjoint_left.1 hdisj (mem_half.1 hP).1 (D.ntw.twistExcludedPlaces_contains_residueChar i (show P ∈ placesOver D.host.E (D.ntw.l i) from hl))
    · intro v hv hnc B hB σ hσ
      have hvQ : v ∉ Q := by
        intro hvQ
        by_cases hc : v ∈ ρ.ch i
        · exact hv (mem_half.2 ⟨hvQ, hc⟩)
        · obtain ⟨v', hv'⟩ := GlobalTheory.TwistDet.exists_isConjPl v
          have hv'Q : v' ∈ Q := GlobalTheory.TwistGood.ramExactly_conj D.ntw ψ _ hanti hram v hvQ v' hv'
          have hne := ne_of_split (hsplit v hvQ) hv'
          have hv'c : v' ∈ ρ.ch i := by
            by_contra h
            exact hc (((hρ.ch i).pair v v' hv' hne).2 h)
          exact hnc v' (mem_half.2 ⟨hv'Q, hv'c⟩) (GlobalTheory.TwistDet.isConjPl_symm hv')
      have h1 : ψ σ = 1 := by
        by_contra h
        exact hvQ ((hram v B hB).1 ⟨σ, hσ, h⟩)
      rw [MonoidHom.comp_apply, h1, map_one]
  · intro x
    obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym x
    exact ⟨σ, charOf_eq ρ.rc f hopen hσ (pow_ne_zero _ (D.ntw.lPrime i).out.ne_zero) (hpow σ), _,
      pow_ne_zero _ (D.ntw.lPrime i).out.ne_zero, hpow σ⟩

theorem de_chi_eq_pow {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (x : (AE D)ˣ) :
    ∃ σ, (((ρ.B i j b).de.chi x : Circle) : ℂ) = ρ.eO i b (algebraMap (D.ntw.O0 i) (D.ntw.O i)
        ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) ∧
      ∃ n ≠ 0, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ ^ n = 1 := by
  set ψ := Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) with hψ
  have hopen : IsOpen (ψ.ker : Set (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)) := by
    have : ψ.ker = (D.ntw.delta i).ker := by
      ext σ
      cases b <;> simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [this]; exact D.ntw.delta_open i
  haveI : ψ.ker.FiniteIndex := @Subgroup.finiteIndex_of_finite_quotient _ _ _ (Subgroup.quotient_finite_of_isOpen _ hopen)
  have hpow : ∀ σ, ψ σ ^ ψ.ker.index = 1 := fun σ => by
    rw [← map_pow]; exact ψ.ker.pow_index_mem σ
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym x
  refine ⟨σ, ?_, _, Subgroup.FiniteIndex.index_ne_zero, hpow σ⟩
  rw [hρ.delta i j b]
  exact charOf_eq _ _ hopen hσ Subgroup.FiniteIndex.index_ne_zero (hpow σ)

variable {X : RealSide D} {S : NX.RatDat D.ntw} {YS : NX.NExpRealS X.R X.cG S} (Z : ExportTie YS X.geo.v₀)

theorem de_mem_intLL (hX : FieldOk X) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (x : (AE D)ˣ) :
    (((Z.ρ.B i j b).de.chi x : Circle) : ℂ) ∈ intLL D := by
  obtain ⟨σ, hσ, n, hn, hp⟩ := de_chi_eq_pow Z.good i j b x
  have hz : (((Z.ρ.B i j b).de.chi x : Circle) : ℂ) ^ n = 1 := by
    rw [hσ, ← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, hp, Units.val_one, map_one, map_one]
  haveI : Countable D.what₂.LL := (Module.finBasis ℚ D.what₂.LL).equivFun.toEquiv.injective.countable
  obtain ⟨y, hy⟩ := mem_range_of_pow_of_fixed (embLL0 D) hn hz fun τ hτ => by
    rw [hσ]
    refine GlobalTheory.DeltaFixed.aut_fixes_delta_values Z.ρ Z.good i j b (X.R.C.delAt (D.ntw.l i)) (Z.pin.delta i j b) ?_ τ hτ σ
    unfold Formalism.L2.Host.CharFrame.delAt
    split_ifs
    exacts [hX.vals.del', hX.vals.del]
  exact mem_intLL_of_pow hn hz ⟨y, hy⟩

theorem muC_mem_intLL (hX : FieldOk X) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) {PP : Pl D.host.E}
    (hPP : PP ∈ (Z.ρ.B i j b).G.Pg) (w : (kP PP)ˣ) : (((Z.ρ.B i j b).G.muC PP w : ℂˣ) : ℂ) ∈ intLL D := by
  obtain ⟨k, hk⟩ : ∃ k : Fin 2, PP ∈ placesOver D.host.E (D.host.g k) := Z.good.Pg i j b PP hPP
  have hw : w ^ (D.host.g k - 1) = 1 := by
    rw [← card_residueField_of_type hk, ← Nat.card_units]
    exact pow_card_eq_one'
  have hz : (((Z.ρ.B i j b).G.muC PP w : ℂˣ) : ℂ) ^ (D.host.g k * (D.host.g k - 1)) = 1 := by
    rw [mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, ← map_pow, hw, map_one, Units.val_one, one_pow]
  obtain ⟨x, hx⟩ := hX.roots k _ hz
  have h2 := (D.host.g_prime k).two_le
  exact mem_intLL_of_pow (Nat.mul_ne_zero (by omega) (by omega)) hz ⟨x, hx⟩

theorem levLam_twVia_mem_intLL : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
  ∀ k : (baseOf Z c w j).levJ (twVia Z.ρ ι), (((baseOf Z c w j).levLam (twVia Z.ρ ι) k : ℂˣ) : ℂ) ∈ intLL D := by
  intro D X X0 Y S YS Z c w j H ι hι x
  obtain ⟨hg, hv⟩ := twistOf_good Z.good (c.twI w) j (c.sd w) (c.k' w) (c.Q w) (chr c w) H.ok (viaOk ι)
  have htw : ∀ z, (((twVia Z.ρ ι).chi z : Circle) : ℂ) ∈ intLL D := fun z => by
    obtain ⟨σ, hσ, n, hn, hp⟩ := hv z
    obtain ⟨y, hy⟩ : ∃ y : D.what₂.LL, c.embW w y = algebraMap _ (KE c w) ((chr c w σ : (D.ntw.Ok (c.twI w) (c.k' w))ˣ) : D.ntw.Ok (c.twI w) (c.k' w)) := H.val σ
    refine mem_intLL_of_pow hn ?_ ⟨y, ?_⟩
    · refine (congrArg (· ^ n) hσ).trans ?_
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hp, Units.val_one, map_one]
    · rw [← hι, hy]
      exact hσ.symm
  have hext : ∀ g : G0 (Z.ρ.B (c.twI w) j (c.sd w)).G.Pg (Wc D j).rank,
      ((ext1 (Z.ρ.B (c.twI w) j (c.sd w)).G.P.H (⇑(Z.ρ.B (c.twI w) j (c.sd w)).G.P.chi) g : ℂˣ) : ℂ) ∈ intLL D := fun g => by
    unfold ext1
    split_ifs with h
    · obtain ⟨g', rfl⟩ := (Z.ρ.eG (c.twI w) j (c.sd w)).surjective g
      obtain ⟨g₀, rfl⟩ := (X.R.eG.trans X.cG).surjective g'
      have hu : X.cG (X.R.eG g₀) ∈ D.nexp.U := ((Z.tie (c.twI w) j (c.sd w)).U_eq _).1 h
      have e1 := ((Z.tie (c.twI w) j (c.sd w)).psiU_eq ⟨_, hu⟩ h).trans (H.psi_eq (c.twI w) (c.sd w) ⟨g₀, (H.U_eq g₀).1 hu⟩ hu)
      refine mem_intLL_of_pow (n := Nat.card (Z.ρ.B (c.twI w) j (c.sd w)).G.P.H) Nat.card_pos.ne' ?_ ⟨_, (map_inv₀ _ _).trans e1.symm⟩
      rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
    · exact one_mem _
  have e : (baseOf Z c w j).levLam (twVia Z.ρ ι) x =
      levFn (baseOf Z c w j).F.βS ((baseOf Z c w j).levS (twVia Z.ρ ι)) (Formalism.UG.bc (Lev.swapAE D) x.1.1) := by
    unfold Base.levLam Lev.levCharAfE
    rfl
  rw [e]
  simp only [levFn, Base.levS, Units.val_mul, Units.coe_prod]
  refine mul_mem (mul_mem (hext _) (prod_mem fun PP hPP => prod_mem fun _ _ => muC_mem_intLL Z H.field _ j _ hPP _))
    (prod_mem fun PP _ => ?_)
  rw [MonoidHom.mul_apply, Units.val_mul]
  exact mul_mem (locC_mem (Z.good.base _ j _).de (de_mem_intLL Z H.field _ j _) PP _) (locC_mem (t := twVia Z.ρ ι) hg htw PP _)

end GlobalTheory.PlaceRead.LevVal

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceRead

theorem exists_extend_fractionRing {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
    (hinj : Function.Injective (algebraMap A B)) (e : FractionRing A →+* ℂ) :
    ∃ ε : FractionRing B →+* ℂ, ε.comp (algebraMap A (FractionRing B)) = e.comp (algebraMap A (FractionRing A)) := by
  letI : Algebra A ℂ := (e.comp (algebraMap A (FractionRing A))).toAlgebra
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hinj
  haveI : FaithfulSMul A ℂ := (faithfulSMul_iff_algebraMap_injective A ℂ).2
    (e.injective.comp (IsFractionRing.injective A (FractionRing A)))
  haveI : FaithfulSMul A (FractionRing B) := (faithfulSMul_iff_algebraMap_injective A _).2 (by
    rw [IsScalarTower.algebraMap_eq A B (FractionRing B)]
    exact (IsFractionRing.injective B (FractionRing B)).comp hinj)
  haveI : Algebra.IsAlgebraic A B := inferInstance
  haveI : Algebra.IsAlgebraic B (FractionRing B) := IsLocalization.isAlgebraic _ (nonZeroDivisors B)
  haveI : Algebra.IsAlgebraic A (FractionRing B) := Algebra.IsAlgebraic.trans A B _
  let φ : FractionRing B →ₐ[A] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨φ.toRingHom, RingHom.ext fun a => φ.commutes a⟩

theorem exists_extends_and_emb : ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (ρ : Setup D.ntw), ρ.Good → (∃ ε : KE c w →+* ℂ, Extends ρ ε) ∧
  (NChTie D c → ∀ ε : KE c w →+* ℂ, Extends ρ ε → ∀ x : D.LL0, ε (c.embW w (x : D.what₂.LL)) = embLL0 D x) := by
  intro D c w ρ hρ
  haveI := c.Oe_fin w
  refine ⟨exists_extend_fractionRing (c.Oe_inj w) (ρ.ek (c.twI w) (c.sd w) (c.k' w)), fun hT ε hε x => ?_⟩
  obtain ⟨y, z, hz, hyz⟩ := IsFractionRing.div_surjective (A := D.ntw.O0 (c.twI w))
    ((if c.sd w = true then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) x)
  have hz0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
  have hz1 : algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) z ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hz
  have h0 : (if c.sd w = true then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) x * algebraMap _ _ z = algebraMap _ _ y := by
    rw [← hyz, div_mul_cancel₀ _ hz1]
  have h1 := congrArg ε (hT.embedding_baseField_condition w x y z hz0 h0)
  have key : ∀ t : D.ntw.O (c.twI w), ε (algebraMap (c.Oe w) (FractionRing (c.Oe w))
      (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w) (algebraMap _ (D.ntw.Ok (c.twI w) (c.k' w)) t))) =
      ρ.eO (c.twI w) (c.sd w) t := fun t => by
    rw [← IsScalarTower.algebraMap_apply (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w), hε.apply, hρ.ek_e]
  rw [map_mul, key, key] at h1
  rw [← hρ.e_LL0 (c.twI w) (c.sd w) x]
  let m : FractionRing (D.ntw.O0 (c.twI w)) →+* FractionRing (D.ntw.O (c.twI w)) := IsFractionRing.map (D.ntw.O_inj (c.twI w))
  have hm : ∀ t, ρ.e (c.twI w) (c.sd w) (m (algebraMap _ _ t)) =
      ρ.eO (c.twI w) (c.sd w) (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) t) := fun t =>
    congrArg (ρ.e (c.twI w) (c.sd w)) (IsLocalization.map_eq _ t)
  have h2 := congrArg (fun t => ρ.e (c.twI w) (c.sd w) (m t)) h0
  simp only [map_mul, hm] at h2
  have hne : ρ.eO (c.twI w) (c.sd w) (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) z) ≠ 0 := by
    rw [← hm]
    exact (map_ne_zero _).2 ((map_ne_zero m).2 hz1)
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

end GlobalTheory.PlaceRead
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

private theorem tensor_exists_basis_expansion {O K L M ι : Type*} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    [Field L] [Algebra O L] [AddCommGroup M] [Module O M] [Module K M] [IsScalarTower O K M] [Fintype ι]
    (hinj : ∀ d : O, d ≠ 0 → algebraMap O L d ≠ 0) (v : Module.Basis ι K M) (x : L ⊗[O] M) :
    ∃ cf : ι → L, x = ∑ a, cf a ⊗ₜ v a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨c, e⟩ := hx
    obtain ⟨c', e'⟩ := hy
    refine ⟨c + c', ?_⟩
    rw [e, e']
    simp [TensorProduct.add_tmul, Finset.sum_add_distrib]
  | tmul a f =>
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) fun c => v.repr f c
    choose y hy using hd
    have e : (d : O) • (a ⊗ₜ[O] f) = ∑ c, (y c • a) ⊗ₜ[O] v c := by
      rw [← TensorProduct.tmul_smul]
      conv_lhs => rw [← v.sum_repr f]
      rw [Finset.smul_sum, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [TensorProduct.smul_tmul, ← algebraMap_smul K (y c), hy, smul_assoc]
    have h0 := hinj d (nonZeroDivisors.coe_ne_zero d)
    refine ⟨fun c => (algebraMap O L d)⁻¹ • y c • a, ?_⟩
    rw [← algebraMap_smul L (d : O)] at e
    rw [← inv_smul_smul₀ h0 (a ⊗ₜ[O] f), e, Finset.smul_sum]
    simp only [TensorProduct.smul_tmul']

private theorem tensor_scalar_relation {O L M N ι : Type*} [CommRing O] [Field L] [Algebra O L] [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module ℂ N] [Fintype ι] (ε : L →+* ℂ) (v : ι → M) (r : M → N) (R : L ⊗[O] M →ₛₗ[ε] N)
    (hR : ∀ a f, R (a ⊗ₜ f) = ε a • r f) (hli : LinearIndependent ℂ fun c => r (v c))
    (hsp : ∀ x : L ⊗[O] M, ∃ cf : ι → L, x = ∑ a, cf a ⊗ₜ v a) (A B : L ⊗[O] M) (z : ℂ) (h : R A = z • R B) :
    (B = 0 → A = 0) ∧ (B ≠ 0 → ∃ t : L, ε t = z ∧ A = t • B) := by
  obtain ⟨α, rfl⟩ := hsp A
  have hind := Fintype.linearIndependent_iff.1 hli
  constructor
  · rintro rfl

    rw [map_zero, smul_zero, map_sum] at h
    simp only [hR] at h
    have h2 : ∀ a, α a = 0 := fun a => ε.injective ((hind _ h a).trans (map_zero _).symm)
    simp [h2]
  · obtain ⟨β, rfl⟩ := hsp B
    intro hB

    rw [map_sum, map_sum] at h
    simp only [hR] at h
    have h1 : ∀ a, ε (α a) - z * ε (β a) = 0 := hind (fun a => ε (α a) - z * ε (β a)) (by
      simp only [sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, h, sub_self])
    have h2 : ∃ a, β a ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hB (by simp [hc])
    obtain ⟨a0, ha0⟩ := h2
    have h3 : ε (β a0) ≠ 0 := (map_ne_zero ε).2 ha0
    have ht : ε (α a0 / β a0) = z := by
      rw [map_div₀, sub_eq_zero.1 (h1 a0), mul_div_cancel_right₀ _ h3]
    refine ⟨α a0 / β a0, ht, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    congr 1
    apply ε.injective
    rw [map_mul, ht, sub_eq_zero.1 (h1 a)]

theorem _root_.GlobalTheory.T.chosenField_forms_proportional_of_readings : ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (ρ : Setup D.ntw) (hρ : ρ.Good) (j : Fin D.R.m) (rd : Rd ρ D.nexp (c.twI w) j (c.sd w)), Faithful rd → ∀ (ε : KE c w →+* ℂ) (hε : Extends ρ ε) (A B : KE c w ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) (j.1 + 1) (c.sd w)) (z : ℂ),
  rdF rd hρ hε A = z • rdF rd hρ hε B → (B = 0 → A = 0) ∧ (B ≠ 0 → ∃ t : KE c w, ε t = z ∧ A = t • B) := by
  intro D c w ρ hρ j rd hF ε hε A B z h
  let v := Module.finBasis (FractionRing (D.ntw.O (c.twI w))) (D.nexp.Fm (c.twI w) (j.1 + 1) (c.sd w))
  have hinj : ∀ d : D.ntw.O (c.twI w), d ≠ 0 → algebraMap _ (KE c w) d ≠ 0 := fun d hd h0 => by
    have h1 := congrArg ε h0
    rw [IsScalarTower.algebraMap_apply _ (D.ntw.Ok (c.twI w) (c.k' w)) (KE c w), hε.apply, hρ.ek_e, map_zero] at h1
    exact hd (ρ.eO_injective (c.twI w) (c.sd w) (h1.trans (map_zero _).symm))
  exact tensor_scalar_relation ε v rd (rdF rd hρ hε) (rdF_tmul hρ hε) (hF _ v v.linearIndependent) (tensor_exists_basis_expansion hinj v) A B z h
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

noncomputable section

namespace GlobalTheory.PlaceLift

theorem eMt_fix (D : D7) (μ : D.what₂.Tup) (j : ℕ) (x : D.what₂.MtL μ j) (hx : x ∈ Idx.TjV D μ j) :
    D.what₂.eMt μ j (D.what₂.jMt μ j x) = D.what₂.jMt μ j x := by
  have hL : ∀ y ∈ Idx.TjL D μ j, D.what₂.eMt μ j (D.what₂.jMt μ j y) = D.what₂.jMt μ j y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨v, -, hv⟩ := hz
      rw [← hv]
      exact LinearMap.congr_fun (D.what₂.eMt_idem μ j) _
    | zero => rw [map_zero, map_zero]
    | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
    | smul c a _ ha => rw [Idx.smul_def, LinearMap.map_smulₛₗ, map_smul, ha]
  induction hx using Submodule.span_induction with
  | mem z hz => exact hL z hz
  | zero => rw [map_zero, map_zero]
  | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  | smul c a _ ha => rw [LinearMap.map_smulₛₗ, map_smul, ha]

variable {D : D7} {X : RealSide D} {X0 : BaseLevelRowSide D} (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0)

theorem extV_formOf_eMt (j : Fin D.R.m) (t : X.T) (hμ : Used0 D (Y.tup t)) (c) :
    X.R.toRealDat.extV j (Y.tupT (Y.tup t)) (formOf Y hμ j (D.what₂.jMt (Y.tup t) (j.1 + 1) (Y.eMt j t c))) =
      X.R.toRealDat.extV j t (X.R.jV j t (GlobalTheory.Mem.R3.liftForm X.A3.A X.F.P0 X.F.ψ0 j t c)) :=
  (extV_formOf Y hμ j _).trans (Y.mtRead j t hμ c)

theorem idem_fix (hH : GlobalTheory.Mem.R3.Holds X.R X.F) (j : Fin D.R.m) (t : X.T) (hμ : Used0 D (Y.tup t)) (c)
    (hc : D.what₂.eMt (Y.tup t) (j.1 + 1) (D.what₂.jMt (Y.tup t) (j.1 + 1) (Y.eMt j t c)) =
      D.what₂.jMt (Y.tup t) (j.1 + 1) (Y.eMt j t c)) :
    X.R.jV j t (GlobalTheory.Mem.R3.liftForm X.A3.A X.F.P0 X.F.ψ0 j t c) =
      X.R.jV j t (∑ g, (idemOf X.A3.A.X).coeff g • (X.A3.A.fam.L j t).r g (GlobalTheory.Mem.R3.liftForm X.A3.A X.F.P0 X.F.ψ0 j t c)) := by
  have e2 := GlobalTheory.CenTranslate.liftForm_lvlOp (A3 := X.A3) (F := X.F.lv2) hH.ok.ok2 j t (idemOf X.A3.A.X)
    (fun b => idemOf_central X.A3.A.X hH.ok.ok2.irr b) c
  have e1 := (Y.formsL j t).op_eq c
  have e3 : D.what₂.jMt (Y.tup t) (j.1 + 1) (Y.eMt j t c) =
      D.what₂.jMt (Y.tup t) (j.1 + 1) (Y.eMt j t ((lE D X.A3.A X.F.P0 X.F.ψ0 j t).mulVec c)) := hc.symm.trans e1
  refine Y.hinj j t ?_
  refine (Y.mtRead j t hμ c).symm.trans ?_
  refine (congrArg (fun y => (Y.IL.jMt (Y.tup t) hμ j y).1) e3).trans ?_
  refine (Y.mtRead j t hμ _).trans ?_
  exact congrArg (fun v => X.R.toRealDat.extV j t (X.R.jV j t v)) e2

theorem isAlgV_self (j : Fin D.R.m) (t : X.T) (u : (X.A3.A.fam.L j t).S.Forms)
    (hu : X.R.jV j t u = X.R.jV j t (∑ g, (idemOf X.A3.A.X).coeff g • (X.A3.A.fam.L j t).r g u))
    (κ : X.Γ → (GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups.levV X.R.toRealDat j t).Q) (hκ : ∀ g, GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups.IsLiftV X.R.toRealDat j t g (κ g)) :
    GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups.IsAlgV X.R.toRealDat j t (RealDat.eC (A := X.A3.A) (sg0 D X.A3.A)) κ (X.R.jV j t u) (X.R.jV j t u) := by
  have hs : sg0 D X.A3.A = D.what₂.embLL := sgAt_mk _ X.R.hv0
  refine (congrArg (X.R.HV j t).e hu).trans ?_
  have e3 := map_sum (X.R.jV j t) (fun g => (idemOf X.A3.A.X).coeff g • (X.A3.A.fam.L j t).r g u) Finset.univ
  have e4 := map_sum (X.R.HV j t).e (fun g => (X.R.jV j t) ((idemOf X.A3.A.X).coeff g • (X.A3.A.fam.L j t).r g u)) Finset.univ
  refine ((congrArg (X.R.HV j t).e e3).trans e4).trans ?_
  refine Finset.sum_congr rfl fun g _ => ?_
  have e5 := map_smulₛₗ (X.R.jV j t) ((idemOf X.A3.A.X).coeff g) ((X.A3.A.fam.L j t).r g u)
  have e6 := LinearMap.map_smul (X.R.HV j t).e (D.what₂.embLL ((idemOf X.A3.A.X).coeff g)) (X.R.jV j t ((X.A3.A.fam.L j t).r g u))
  refine ((congrArg (X.R.HV j t).e e5).trans e6).trans ?_
  have hT := GlobalTheory.RationalFormsAction.isTranslate_act_V X.R.toRealDat X.char.grp.red_L X.char.models.jV j t g u
  have e7 : (X.R.HV j t).e (X.R.jV j t ((X.A3.A.fam.L j t).r g u)) =
      Bridge.g0Act (GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups.levV X.R.toRealDat j t).ch (κ g) ((X.R.HV j t).e (X.R.jV j t u)) :=
    funext fun h => hT.2 (κ g) (hκ g) h
  have e8 : D.what₂.embLL ((idemOf X.A3.A.X).coeff g) = RealDat.eC (A := X.A3.A) (sg0 D X.A3.A) g := by
    rw [RealDat.eC, hs]
  rw [e7, e8]

theorem lift_read (hP : GlobalTheory.Mem.R3.Pins X.R X.F X.cG) (hH : GlobalTheory.Mem.R3.Holds X.R X.F) (j : Fin D.R.m) (μ : D.what₂.Tup) (hμ : Used0 D μ)
    (x : D.what₂.MtL μ (j.1 + 1)) (hx : x ∈ Idx.TjV D μ (j.1 + 1)) (v : (X.R.MW j (sg0 D X.A3.A)).Vec) :
    (X.R.HW j (sg0 D X.A3.A)).e (Y.mj.eW j (D.what₂.thetaP μ (j.1 + 1) (D.what₂.jMt μ (j.1 + 1) x))) v =
      X.R.thF j (Y.tupT μ) (formOf Y hμ j (D.what₂.jMt μ (j.1 + 1) x)) v := by
  obtain ⟨t, rfl⟩ : ∃ t, Y.tup t = μ := ⟨_, Y.tupTie μ hμ⟩
  obtain ⟨c, rfl⟩ := (Y.eMt j t).surjective x
  have hC : GlobalTheory.Hk3.Core X.R.toRealDat X.F.lv2 :=
    ⟨X.char.lev, X.char.grp, X.char.fam, X.char.models, X.char.chain, X.char.thP⟩
  choose κ hκ using GlobalTheory.ProjLiftLaw.liftV_exists_core hC j t
  have h1 := GlobalTheory.Mem.ThetaRead3.thetaP_read_plain D X.Γ X.Pl0 X.I0 X.T X.A3 X.core.Q.c.F X.R X.F X.cG X0 Y hP hH j t c
  have h2 := GlobalTheory.ProjLiftLaw.thG_apply_eq hC j t κ hκ _ _
    (isAlgV_self j t _ (idem_fix Y hH j t hμ c (eMt_fix D _ _ _ hx)) κ hκ) v
  have h3 := GlobalTheory.Mem.ThetaRead3.thF_congr X.R.toRealDat Y.hinj j t (Y.tupT (Y.tup t)) (Y.tupT_tup t) _ _ (extV_formOf_eMt Y j t hμ c)
  exact ((congrArg (fun y => (X.R.HW j (sg0 D X.A3.A)).e y v) h1).trans h2).trans (congrArg (fun U => U v) h3).symm

theorem lift_read_at : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ x ∈ Idx.TjV D (D.what₂.muTw w) (j.1 + 1),
  (X.R.HW j (sg0 D X.A3.A)).e (Y.mj.eW j (D.what₂.thetaP (D.what₂.muTw w) (j.1 + 1) (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x))) (X.geo.v₀ j (sg0 D X.A3.A)) =
    X.R.thF j (Y.tupT (D.what₂.muTw w)) (formOf Y (used_of_tw H.tw) j (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) (X.geo.v₀ j (sg0 D X.A3.A)) :=
  fun _ _ _ Y _ _ _ _ _ j H x hx => lift_read Y H.pins H.intersectionNumber_baseChange j _ (used_of_tw H.tw) x hx _

end GlobalTheory.PlaceLift

end
end
