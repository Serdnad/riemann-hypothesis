module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle920
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle848
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2438
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle923
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle822
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1832
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2244
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle236
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NablaDeltaOperatorLatticePreserved
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedLatticeLocalizationFreeLeCoefficientS
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle086
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle094
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.Columns.Bundle032
import Formalism.LocalToGlobal.Columns.Bundle031
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle015
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle881
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle868
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle297
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle894
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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

namespace GlobalTheory.PlaceUnit

theorem card_residueField_ne_zero {E : Type} [Field E] [NumberField E] (P : Pl E) : Nat.card (kP P) ≠ 0 := by
  haveI : Finite (kP P) := P.asIdeal.finiteQuotientOfFreeOfNeBot P.ne_bot
  exact Nat.card_pos.ne'

theorem card_residueField_mem {E : Type} [Field E] [NumberField E] (P : Pl E) : ((Nat.card (kP P) : ℕ) : 𝓞 E) ∈ P.asIdeal := by
  haveI : Finite (kP P) := P.asIdeal.finiteQuotientOfFreeOfNeBot P.ne_bot
  letI : Fintype (kP P) := Fintype.ofFinite _
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, Nat.card_eq_fintype_card]
  exact Nat.cast_card_eq_zero (kP P)

theorem not_mem_of_coprime {E : Type} [Field E] [NumberField E] (P : Pl E) {q l : ℕ} (h : Nat.Coprime q l)
    (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) : ((l : ℕ) : 𝓞 E) ∉ P.asIdeal := by
  intro hl
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  apply P.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : ((a : 𝓞 E) * ((q : ℕ) : 𝓞 E) + (b : 𝓞 E) * ((l : ℕ) : 𝓞 E)) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 E) hab
    push_cast at this
    exact this
  rw [← h1]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hq) (Ideal.mul_mem_left _ _ hl)

theorem not_mem_of_pD {D : D7} (i : D.ntw.Tw) {P : Pl D.host.E} (hP : P ∈ D.ntw.pD i) :
    ((D.ntw.l i : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  have h : P ∈ placesOver D.host.E (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde) := by
    rw [← D.ntw.pD_eq i]; exact hP
  have hl : (D.ntw.l i).Prime := (D.ntw.lPrime i).out
  refine not_mem_of_coprime P ?_ h
  split_ifs with e
  · exact (Nat.coprime_primes D.host.pde'_prime hl).2 (e ▸ D.host.pde_ne.symm)
  · exact (Nat.coprime_primes D.host.pde_prime hl).2 (Ne.symm e)

theorem isUnit_card_residueField_Oe {D : D7} (c : NChoice D) (w : D.what₂.places.Pl) {P : Pl D.host.E}
    (hl : ((D.ntw.l (c.twI w) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) : IsUnit ((Nat.card (kP P) : ℕ) : c.Oe w) := by
  haveI := D.ntw.Ok_fin (c.twI w) (c.k' w)
  have h : IsUnit ((Nat.card (kP P) : ℕ) : D.ntw.Ok (c.twI w) (c.k' w)) :=
    GlobalTheory.ResidueUnit.isUnit_of_coprime _ _ (GlobalTheory.ResidueUnit.card_residueField_coprime P _ (D.ntw.lPrime _).out hl)
      (GlobalTheory.ResidueUnit.natCast_mem_maximalIdeal_of_finite (O := D.ntw.O (c.twI w)) _ (D.ntw.O_l _))
  simpa using h.map (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w))

theorem tupPrime_isUnit : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
  GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) ≠ 0 ∧ (∀ P ∈ X.R.Q (Y.tupT (D.what₂.muTw w)), ((GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) ∧
  IsUnit ((GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) : ℕ) : c.Oe w) := by
  classical
  intro D X X0 Y S YS Z c w j H ι hι
  have hQ := (H.tup ι hι).2
  refine ⟨?_, fun P hP => ?_, ?_⟩
  · refine Finset.prod_ne_zero_iff.2 fun q hq => ?_
    obtain ⟨P, -, rfl⟩ := Finset.mem_image.1 hq
    exact card_residueField_ne_zero P
  · obtain ⟨m, hm⟩ : Nat.card (kP P) ∣ GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) :=
      Finset.dvd_prod_of_mem (fun q : ℕ => q) (Finset.mem_image_of_mem (fun PP => Nat.card (kP PP)) hP)
    rw [hm, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (card_residueField_mem P)
  · rw [GlobalTheory.TwistField.tupPrime, Nat.cast_prod]
    refine IsUnit.prod_iff.2 fun q hq => ?_
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hq
    refine isUnit_card_residueField_Oe c w ?_
    rw [hQ, Finset.mem_union] at hP
    rcases hP with hP | hP
    · rw [Z.good.delta] at hP
      exact not_mem_of_pD _ (mem_half.1 hP).1
    · exact fun h => Finset.disjoint_left.1 H.ok.2.1 (mem_half.1 hP).1 (D.ntw.twistExcludedPlaces_contains_residueChar _ h)

end GlobalTheory.PlaceUnit
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

namespace GlobalTheory.PlaceScale

theorem pow_eq_of_isScale {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) {c c' : ℂ}
    (h : IsScale Rl v₀ B c) (h' : IsScale Rl v₀ B c') : ∃ k : ℕ, k ≠ 0 ∧ c' ^ k = c ^ k := by
  obtain ⟨gR, cR0, cL0, hT, u, hu, hF⟩ := h
  obtain ⟨gR', cR0', cL0', hT', u', hu', hF'⟩ := h'
  have huu : u' = u := funext fun τ => Subtype.ext ((hu' τ).trans (hu τ).symm)
  subst huu
  obtain ⟨a, ⟨k, hk, hak⟩, ha⟩ := GlobalTheory.CoefRoot.coef_root _ _ _ _ _ _ _ _ _ _ _ _ _ hT hT' j
  obtain ⟨F, x, hx⟩ := GlobalTheory.CoeffNonvanish.exists_coefFn_ne_zero (FWT.lamV D j)
  have e1 := hF' F
  rw [ha] at e1
  erw [LinearMap.map_smul, LinearMap.map_smul, hF F] at e1
  have e2 := congrFun e1 x
  simp only [Pi.smul_apply, smul_eq_mul] at e2
  have hc : c' = D.what₂.embLL a * c := by
    have h3 : D.what₂.embLL a * c * coefFn D.what₂.embLL (FWT.lamV D j) (F : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) x =
        c' * coefFn D.what₂.embLL (FWT.lamV D j) (F : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) x := by
      rw [mul_assoc]; exact e2
    exact (mul_right_cancel₀ hx h3).symm
  refine ⟨k, hk, ?_⟩
  rw [hc, mul_pow, ← map_pow, hak, map_one, one_mul]

theorem coefFn_map {D : D7} {n : ℕ} {K : Type} [Field K] (σ : K →+* ℂ) (lam : D.what₂.Tau → DomWeight n)
    (F : Formalism.L2.DIV.Pol K D.what₂.Tau n) : coefFn (RingHom.id ℂ) lam (MvPolynomial.map σ F) = coefFn σ lam F := by
  funext x
  simp only [coefFn, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map, RingHom.id_comp]



theorem exists_scale : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∃ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ) (cc : VsV D j ℂ →ₗ[ℂ] (X.R.cV j).W) (κ : ℂ), IsLow X j u ∧ ExtC X.R.toRealDat j (inC (X.geo.O j).c') (X.geo.O j).c0' cc ∧ κ ≠ 0 ∧
    (∀ x, X.R.ioP j (PiTensorProduct.tprod ℂ u) (cc x) ∈ (baseOf Z c w j).valSpace) ∧
    (∀ x : VsV D j ℂ, harmFn (Wc D j).rank (baseOf Z c w j).w (baseOf Z c w j).F.BS (X.R.ioP j (PiTensorProduct.tprod ℂ u) (cc x)) = κ • coefFn (RingHom.id ℂ) (lamV D j) (x : Pol ℂ D.what₂.Tau (Vc D j).rank)) ∧
    IsScale X.R X.geo.v₀ (baseOf Z c w j) κ ∧ IsRoot1 (Z.ν (c.twI w) j (c.sd w) / κ) := by
  intro D X X0 Y S YS Z c w j H
  have hch := X.char
  have hC : GlobalTheory.Hk3.Core X.R.toRealDat X.F.lv2 := ⟨hch.lev, hch.grp, hch.fam, hch.models, hch.chain, hch.thP⟩
  have hio : IoExt X.R.toRealDat := GlobalTheory.IoExtremal.ioExt D _ _ _ _ _ X.R.toRealDat hC.lev hC.fam hC.models hC.thP
  obtain ⟨ν', hν', -⟩ := H.rat
  obtain ⟨hν0, c₀, hsc, n, hn, hνn⟩ := (Z.scalar (c.twI w) j (c.sd w)).norm ⟨ν', hν'⟩
  obtain ⟨-, -, -, -, u, hu, -⟩ := id hsc
  obtain ⟨cc, hc⟩ := GlobalTheory.ExtCoeff.exists_extC _ _ _ _ _ _ _ j Unit (fun _ => X.A3.A.μ0) (X.geo.O j)
  have hB := Z.good.base (c.twI w) j (c.sd w)
  have hBo := GlobalTheory.BigOn.Exp.TwConj.baseOf_of_realPin hch.lev Z.good Z.pin (c.twI w) j (c.sd w)
  have hO := X.geo.pins j
  obtain ⟨κ, hκ0, hval, hκ⟩ := GlobalTheory.CoefLatConj.exists_coef_scale D _ _ _ X.A3.A X.core X.R.toRealDat X.F.lv2 X.geo.κ X.geo.v₀ X.geo.O
    hC ⟨X.geo.fw⟩ hio j hO cc hc u hu _ hB hBo
  have hfield := hO.2.lift.field
  obtain ⟨gramR, c0R, c0L, hft, hbc⟩ := hO.2.lift.c0
  have hcL : ∀ F : VV D.what₂.LL (lamV D j), cc (GlobalTheory.CoefModel.mapVV D.what₂.embLL (lamV D j) F) = c0L j F := fun F => by
    obtain ⟨v', hv', hv0⟩ := hbc F
    refine (hc v' _ ?_).trans hv0
    change MvPolynomial.map D.what₂.embLL _ = _
    rw [hv', MvPolynomial.map_map, hfield]
  have hκs : IsScale X.R X.geo.v₀ (baseOf Z c w j) κ := ⟨gramR, c0R, c0L, hft, u, hu, fun F =>
    (congrArg (fun z => harmFn _ _ _ (X.R.ioP j (PiTensorProduct.tprod ℂ u) z)) (hcL F)).symm.trans
      ((hκ _).trans (congrArg (κ • ·) (coefFn_map _ _ _)))⟩
  obtain ⟨k, hk, hkk⟩ := pow_eq_of_isScale X.R X.geo.v₀ _ hsc hκs
  refine ⟨u, cc, κ, hu, hc, hκ0, hval, hκ, hκs, n * k, Nat.pos_of_ne_zero (Nat.mul_ne_zero hn hk), ?_⟩
  rw [X.phs j, map_one, one_mul] at hνn
  have e : Z.ν (c.twI w) j (c.sd w) ^ (n * k) = κ ^ (n * k) := by
    rw [pow_mul, hνn, ← pow_mul, mul_comm n k, pow_mul c₀, pow_mul κ, hkk]
  rw [div_pow, e, div_self (pow_ne_zero _ hκ0)]

end GlobalTheory.PlaceScale

end
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

namespace GlobalTheory.PlaceSmall

section BaseChange

variable {E K₀ K ι : Type} [Field E] [NumberField E] [Field K₀] [NumberField K₀] [Field K] [NumberField K] [Fintype ι]
  {n : ℕ}

theorem map_mem_nabAtr (f : K₀ →+* K) (emb : ι → E →+* K₀) (lam : ι → DomWeight n) (M : Submodule (𝓞 E) (Fin n → E))
    (hM : Submodule.IsFullLattice E M) {x : VV K₀ lam} (hx : x ∈ nabAtr emb lam M) :
    (⟨MvPolynomial.map f x.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV f lam _ x.2⟩ : VV K lam) ∈
      nabAtr (fun τ => f.comp (emb τ)) lam M := by
  classical
  unfold nabAtr nabK at hx ⊢
  rw [Submodule.mem_comap] at hx ⊢
  change MvPolynomial.map f x.1 ∈ nabP lam fun τ => dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)
  change x.1 ∈ nabP lam (fun τ => dualFr (tauLat emb τ M)) at hx
  refine GlobalTheory.TransLattice.mem_of_forall_mem_locP _ fun w => ?_
  obtain ⟨w₀, hw₀⟩ : ∃ Q : HeightOneSpectrum (𝓞 K₀),
      ∀ r : 𝓞 K₀, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom f r ∈ w.asIdeal := by
    refine ⟨⟨w.asIdeal.comap (RingOfIntegers.mapRingHom f), Ideal.comap_isPrime _ _, fun h => ?_⟩, fun _ => Iff.rfl⟩
    have h1 : ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 K₀) ∈ w.asIdeal.comap (RingOfIntegers.mapRingHom f) := by
      rw [Ideal.mem_comap, map_natCast]
      exact Ideal.absNorm_mem _
    rw [h, Ideal.mem_bot] at h1
    exact w.ne_bot (Ideal.absNorm_eq_zero_iff.1 (by exact_mod_cast h1))
  have hw : ∀ t : 𝓞 K₀, t ∉ w₀.asIdeal → RingOfIntegers.mapRingHom f t ∉ w.asIdeal :=
    fun t ht h => ht ((hw₀ t).2 h)
  obtain ⟨hLoc, -, -⟩ := GlobalTheory.TransLoc.nabDelLoc_free_leVV
  have hT : ∀ τ, Submodule.IsFullLattice K₀ (tauLat emb τ M) := fun τ => tauLatLattice E K₀ ι n emb τ M hM
  choose C hC using fun τ => basisAtEx K₀ n (tauLat emb τ M) (hT τ) w₀
  let B₀ : ι → GL (Fin n) K₀ := fun τ => inside₂ K₀ n (C τ)
  have hB₀ : ∀ τ, IsBasisAt w₀ (dualFr (tauLat emb τ M)) (B₀ τ) := fun τ =>
    GlobalTheory.DualWeylDual.isBasisAt_dualFr w₀ (hT τ).fg (hC τ)
  have hB : ∀ τ, IsBasisAt w (dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)) (Formalism.UG.bc f (B₀ τ)) := fun τ =>
    GlobalTheory.NabBC.isBasisAt_dualFr_tauLat_comp f emb τ M hM w₀ w hw (C τ) (hC τ)
  have L1 := (hLoc K ι n lam _ (fun τ => dualFr_tauLat_isLattice (fun τ => f.comp (emb τ)) τ M hM) w _ hB).1
  have L0 := (hLoc K₀ ι n lam _ (fun τ => dualFr_tauLat_isLattice emb τ M hM) w₀ B₀ hB₀).1
  have hx0 : x.1 ∈ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal (nabP lam fun τ => dualFr (tauLat emb τ M)) :=
    GlobalTheory.NabBC.mem_localization_of_mem' _ hx
  rw [L0] at hx0
  obtain ⟨g, ⟨s, hs, hsg⟩, hg⟩ := hx0
  rw [L1]
  refine ⟨MvPolynomial.map f g, ⟨RingOfIntegers.mapRingHom f s, hw s hs, ?_⟩, ?_⟩
  · refine (congrArg (· ∈ nabStd K lam) (GlobalTheory.NabBC.map_smul_int f s g)).mpr ?_
    have h1 := (GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K K₀ ι f (RingOfIntegers.mapRingHom f) (fun r => rfl) n lam).1
    have h2 := (GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K K ι (RingHom.id K) (RingHom.id _) (fun r => rfl) n lam).1
    have h3 : MvPolynomial.map f (s • g) ∈ Submodule.span (𝓞 K) (MvPolynomial.map f '' (nabStd K₀ lam : Set (Pol K₀ ι n))) :=
      Submodule.subset_span ⟨_, hsg, rfl⟩
    rw [h1, ← h2] at h3
    have h4 : (MvPolynomial.map (RingHom.id K) '' (nabStd K lam : Set (Pol K ι n))) = (nabStd K lam : Set (Pol K ι n)) := by
      ext y
      simp [MvPolynomial.map_id]
    rw [h4, Submodule.span_eq] at h3
    exact h3
  · change actP lam (fun τ => Formalism.UG.bc f (B₀ τ)) (MvPolynomial.map f g) = MvPolynomial.map f x.1
    rw [← GlobalTheory.ValCmp.use₂]
    exact congrArg (MvPolynomial.map f) hg

end BaseChange

theorem harmLat_le {D : D7} {m n : ℕ} {K₀ K : Type} [Field K₀] [NumberField K₀] [Field K] [NumberField K] (f : K₀ →+* K)
    (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K₀)) (O : Subring ℂ) (w : GlobalTheory.ExportSeries.Weight D n) (B : GLR D n)
    {M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hM : Submodule.IsFullLattice D.host.E M) :
    harmLat (σ.comp f) emb O m w B M ≤ harmLat σ (fun τ => f.comp (emb τ)) O m w B M := by
  refine inf_le_inf_left _ (Submodule.comap_mono (Submodule.span_mono ?_))
  rintro _ ⟨F, hF, rfl⟩
  refine ⟨_, map_mem_nabAtr f emb w.lam M hM hF, funext fun y => ?_⟩
  rw [coefFn, coefFn, MvPolynomial.eval₂Hom_map_hom]

theorem coefLat_eq_small : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → ∀ O : Subring ℂ, intLL D ≤ O → ∀ h, B.coefLat D.what₂.embLL (labLL D) O h = B.coefLat (embLL0 D) (labLL0 D) O h := by
  intro D S T B hB O hO h
  have hm : ∀ τ, B.w.p τ + B.w.q τ ≤ T.rank := fun τ => by
    have h1 := hB.sig τ
    have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (Formalism.BasicNotions.TH.tauE D τ)
    rw [← h1] at h2
    exact h2.le
  have hS := Formalism.IndefR.Fin.PDA.selfDual_isFullLattice S B.F.ΛS hB.frame.sdS
  have hM : Submodule.IsFullLattice D.host.E (B.latAt h) :=
    Formalism.UG.P.csGlob_lattice _ (Module.Finite.iff_fg.2 hS.fg) hS.span_eq_top _
  refine le_antisymm (fun P hP => ?_)
    (harmLat_le D.LL0.val.toRingHom D.what₂.embLL (labLL0 D) O B.w B.F.BS hM)
  have h1 := GlobalTheory.SmallSpan.harmLat_le_span D.LL0.val.toRingHom D.what₂.embLL (labLL0 D) O O (fun a => hO ⟨a, rfl⟩)
    B.w B.F.BS hB.wt hm hM hP
  rw [Submodule.span_eq] at h1
  exact h1

end GlobalTheory.PlaceSmall

end
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

namespace GlobalTheory.PlaceRead

open GlobalTheory.TwistGood

theorem twistOf_good (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X) (hρ : ρ.Good)
    (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ)
    (e : X.Ok i k →+* ℂ) (hψ : Formalism.MainNotions.IntegralHeckeForms.TwOK i k Q ψ) :
    (twistOf ρ.rc e (ρ.ch i) Q ψ).Good ∧ (ρ.B i j b).admitted (twistOf ρ.rc e (ρ.ch i) Q ψ).Q := by
  classical
  obtain ⟨hsplit, hdisj, hopen, hanti, hzk, hram, -⟩ := hψ
  have hadm : (ρ.B i j b).admitted (half (ρ.ch i) Q) := GlobalTheory.T.chosenPlaces_admissible_goodSetup D N X ρ hρ i j b Q hsplit hdisj
  let g : (X.Ok i k)ˣ →* Circle := unitPart.comp (Units.map e.toMonoidHom)
  have hkey : charOf ρ.rc e ψ = ρ.rc.pull (g.comp ψ) := by
    rw [Recip.pull_comp _ hopen]
    rfl
  have hz : X.zk i k ^ (X.l i ^ k) = 1 := Units.ext (by simpa using (X.zk_prim i k).pow_eq_one)
  have hpow : ∀ σ, ψ σ ^ (X.l i ^ k) = 1 := by
    intro σ
    obtain ⟨m, hm⟩ := hzk σ
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  refine ⟨?_, hadm⟩
  show (⟨half (ρ.ch i) Q, charOf ρ.rc e ψ, resOf (charOf ρ.rc e ψ)⟩ : Twist D Circle).Good
  rw [hkey]
  refine GlobalTheory.T.artinPullback_isGoodTwist_of_anticyclotomic_tame D N X ρ.rc hρ.rc Circle (g.comp ψ) (X.l i) (X.lPrime i).out
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
    exact Finset.disjoint_left.1 hdisj (mem_half.1 hP).1 (X.twistExcludedPlaces_contains_residueChar i (show P ∈ placesOver D.host.E (X.l i) from hl))
  · intro v hv hnc B hB σ hσ
    have hvQ : v ∉ Q := by
      intro hvQ
      by_cases hc : v ∈ ρ.ch i
      · exact hv (mem_half.2 ⟨hvQ, hc⟩)
      · obtain ⟨v', hv'⟩ := GlobalTheory.TwistDet.exists_isConjPl v
        have hv'Q : v' ∈ Q := ramExactly_conj X ψ _ hanti hram v hvQ v' hv'
        have hne := ne_of_split (hsplit v hvQ) hv'
        have hv'c : v' ∈ ρ.ch i := by
          by_contra h
          exact hc (((hρ.ch i).pair v v' hv' hne).2 h)
        exact hnc v' (mem_half.2 ⟨hv'Q, hv'c⟩) (GlobalTheory.TwistDet.isConjPl_symm hv')
    have h1 : ψ σ = 1 := by
      by_contra h
      exact hvQ ((hram v B hB).1 ⟨σ, hσ, h⟩)
    rw [MonoidHom.comp_apply, h1, map_one]

theorem twVia_good : ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (ρ : Setup D.ntw), ρ.Good → TwOK (c.twI w) (c.k' w) (c.Q w) (chr c w) → ∀ (j : Fin D.R.m) (ι : KE c w →+* ℂ),
  (twVia ρ ι).Good ∧ (ρ.B (c.twI w) j (c.sd w)).admitted (twVia ρ ι).Q ∧ ∀ τ : ℂ ≃+* ℂ, ConjChar τ (twVia ρ ι) (twVia ρ ((τ : ℂ →+* ℂ).comp ι)) := by
  intro D c w ρ hρ hψ j ι
  obtain ⟨h1, h2⟩ := twistOf_good D D.nd D.ntw ρ hρ (c.twI w) j (c.sd w) (c.k' w) (c.Q w) (chr c w) (viaOk ι) hψ
  refine ⟨h1, h2, fun τ => ⟨rfl, fun x => ?_⟩⟩
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym x
  have hn : D.ntw.l (c.twI w) ^ (c.k' w) ≠ 0 := pow_ne_zero _ (D.ntw.lPrime (c.twI w)).out.ne_zero
  have hp : chr c w σ ^ (D.ntw.l (c.twI w) ^ (c.k' w)) = 1 := by
    obtain ⟨n, hn⟩ := hψ.2.2.2.2.1 σ
    have hz : D.ntw.zk (c.twI w) (c.k' w) ^ (D.ntw.l (c.twI w) ^ (c.k' w)) = 1 :=
      Units.ext (by simpa using (D.ntw.zk_prim (c.twI w) (c.k' w)).pow_eq_one)
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  change ((charOf ρ.rc (viaOk ((τ : ℂ →+* ℂ).comp ι)) (chr c w) x : Circle) : ℂ) =
    τ ((charOf ρ.rc (viaOk ι) (chr c w) x : Circle) : ℂ)
  rw [charOf_eq ρ.rc _ hψ.2.2.1 hσ hn hp, charOf_eq ρ.rc _ hψ.2.2.1 hσ hn hp]
  rfl

end GlobalTheory.PlaceRead

end
end
