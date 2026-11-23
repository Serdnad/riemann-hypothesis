module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1379
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2334
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2329
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1609
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle733
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2297
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1818
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle297
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle086
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowGeneratorEqConstMulVacuumTheta
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle050
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle003
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1976
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1506
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle692
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1344
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingLocalIdentity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLinearWittModelNonvanishing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem exists_sec_sep_of_lcCut : GlobalTheory.Published.NadelVanishingPair → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (M : LB X) (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (D : X → ℚ) (ρ d : ℚ) (x x' : X), M.IsLB → IsEffQDiv Δ → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) = interNumRed ℂ C ![toLB G] / m + ρ * interNumRed ℂ C ![N]) → QNum p N d D → d < ρ → IsClosed ({x} : Set X) → x ≠ x' → LcCut p n (Δ + D) x 0 → ¬ KltAt p n (Δ + D) x' → ∃ s : M.Sec, x ∈ nonzeroLocus s ∧ x' ∉ nonzeroLocus s := by
  intro hNadel X _ _ _ p n hp hn
  letI := algebraΓOfHom p
  intro M Δ m G N D ρ d x x' hM hΔ hm hG hN hdeg hD hdρ hx hxx' hlc hx'
  haveI hNoeth : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  obtain ⟨-, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  obtain ⟨m', D₀, hm', hD₀, rfl, hDn⟩ := hD

  have hq0 : 0 < ρ - d := sub_pos.2 hdρ
  set a : ℕ := (ρ - d).num.toNat with ha_def
  set b : ℕ := (ρ - d).den with hb_def
  have hb : 0 < b := (ρ - d).den_pos
  have hnum : 0 < (ρ - d).num := Rat.num_pos.2 hq0
  have ha : ((a : ℤ) : ℚ) = (ρ - d).num := by
    rw [ha_def, Int.toNat_of_nonneg hnum.le]
  have ha1 : 1 ≤ a := by omega
  have hab : ρ - d = (a : ℚ) / b := by
    have e := Rat.num_div_den (ρ - d)
    rw [← ha, Int.cast_natCast] at e
    exact e.symm
  have hpS : IsProjOver (strHom ℂ (X := X)) := by rwa [strHom_eq (f := p) fun _ => rfl]
  have hNa : IsAmpleLB (lbPow N a) := (isAmpleLB_pow_iff hN.isLB ha1).2 hN
  have hdeg' : ∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) =
      interNumRed ℂ C ![toLB (m' • G + m • D₀)] / ((m * m' : ℕ) : ℚ) +
        interNumRed ℂ C ![lbPow N a] / (b : ℚ) := by
    intro C hC
    have e := hC.interNumRed_of_cls_eq_add hH (isLB_toLB (m' • G + m • D₀))
      (isLB_lbPow (isLB_toLB G) m') (isLB_lbPow (isLB_toLB D₀) m)
      (by rw [cls_lbPow (isLB_toLB G), cls_lbPow (isLB_toLB D₀), ← toPic_apply, ← toPic_apply,
        ← toPic_apply, map_add, map_nsmul, map_nsmul])
    rw [hC.interNumRed_lbPow hH (isLB_toLB G), hC.interNumRed_lbPow hH (isLB_toLB D₀)] at e
    have h1 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    have h2 : (m' : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm'.ne'
    have h3 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hb.ne'
    have hD' := hDn C hC
    rw [div_eq_iff h2] at hD'
    rw [hdeg C hC, e, hC.interNumRed_lbPow hH hN.isLB a, show ρ = d + a / b by linarith]
    push_cast
    rw [hD']
    field_simp
    ring
  obtain ⟨J, hJ, hvan⟩ := hNadel X p n hp hn M (Δ + qWeil D₀ m') (m * m') (m' • G + m • D₀) b
    (lbPow N a) hM (isEffQDiv_add_of_isQCart X p hp Δ _ hΔ ⟨m', D₀, hm', hD₀, rfl⟩)
    (Nat.mul_pos hm hm') (isLogCanonicalMultiple_add_qWeil X p n Δ m m' G D₀ hm hm' hG) hb
    hNa.isNef (IsAmpleLB.isBig ℂ X hpS _ hNa) hdeg'
  have hxJ : x ∈ J.support := (hJ x).2 hlc.2.1
  have hx'J : x' ∈ J.support := (hJ x').2 hx'
  obtain ⟨U, hxU, hU⟩ := exists_open_inter_eq_singleton_of_no_generisation X (J.support : Set X) x
    J.support.isClosed hx hxJ fun z hz hzx => by
      by_contra hne
      obtain ⟨e, -, he, h1⟩ := closure_point_topologicalKrullDim X n z hn
      have h0 := hlc.2.2 z hzx ((hJ z).1 hz)
      have he1 := h1 x hzx (Ne.symm hne)
      rw [he] at h0
      have : e ≤ 0 := by exact_mod_cast h0
      omega
  obtain ⟨s, hs1, hs2⟩ := exists_sec_mem_nonzeroLocus_of_isolated_zero_else ℂ X p hp M hM J x U hx
    hxU hU (hvan 1 one_pos)
  exact ⟨s, hs1, hs2 x' hx'J (Ne.symm hxx')⟩

end GlobalTheory.PairStep
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PairStep

theorem mult_nsmul' {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (D : CartierDiv X) (n : ℕ) (z : X) :
    (n • D).mult z = n * D.mult z := by
  induction n with
  | zero =>
    have h := CartierDiv.mult_add (0 : CartierDiv X) 0 z
    rw [add_zero] at h
    rw [zero_nsmul]; push_cast; omega
  | succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

theorem eff_nsmul' {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} (h : D.Eff) (n : ℕ) :
    (n • D).Eff := by
  induction n with
  | zero => rw [zero_nsmul]; exact CartierDiv.eff_zero
  | succ n ih => rw [succ_nsmul]; exact ih.add h

theorem qNum_smul : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (a c : ℚ) (D : X → ℚ), 0 ≤ c → QNum p N a D → QNum p N (c * a) (c • D) := by
  intro X _ _ p hp N a c D hc hD
  letI := algebraΓOfHom p
  obtain ⟨m, D₀, hm, hE, rfl, hI⟩ := hD
  obtain ⟨u, v, hv, rfl⟩ : ∃ u v : ℕ, 0 < v ∧ c = (u : ℚ) / v := by
    refine ⟨c.num.toNat, c.den, c.den_pos, ?_⟩
    have h0 : ((c.num.toNat : ℕ) : ℤ) = c.num := Int.toNat_of_nonneg (Rat.num_nonneg.2 hc)
    have hd : (c.den : ℚ) ≠ 0 := by exact_mod_cast c.den_pos.ne'
    rw [eq_div_iff hd, Rat.mul_den_eq_num]
    exact_mod_cast h0.symm
  have hv' : (v : ℚ) ≠ 0 := by exact_mod_cast hv.ne'
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨v * m, u • D₀, Nat.mul_pos hv hm, eff_nsmul' hE u, ?_, fun C hC => ?_⟩
  · funext z
    simp only [qWeil, Pi.smul_apply, smul_eq_mul, mult_nsmul']
    push_cast
    field_simp
  · have e := interNumRed_of_cls_eq_nsmul_add ℂ X p hp (toLB (u • D₀)) (toLB D₀) (toLB D₀)
      (isLB_toLB _) (isLB_toLB _) (isLB_toLB _) u 0 C hC
      (by rw [← toPic_apply, ← toPic_apply, map_nsmul, zero_nsmul, add_zero])
    rw [e, Nat.cast_zero, zero_mul, add_zero]
    have h1 := hI C hC
    push_cast
    rw [mul_assoc, ← h1]
    field_simp

end GlobalTheory.PairStep
end
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

open NumberField MeasureTheory MvPolynomial Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.RealLift GlobalTheory.HoweD

namespace GlobalTheory.HoweD.LieFirstD

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ}

def swapTD (P Q R S : ι → ℕ) :
    (⨂[ℂ] w : ι, Formalism.BasicNotions.TH.Pol (R w) (S w) (P w) (Q w)) ≃ₗ[ℂ] ⨂[ℂ] w : ι, Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w) :=
  PiTensorProduct.congr fun w => GlobalTheory.RealLift.LieFirstPf.swapE (P w) (Q w) (R w) (S w)

theorem swapTD_atPl (w : ι) (L' : Module.End ℂ (Formalism.BasicNotions.TH.Pol (R w) (S w) (P w) (Q w)))
    (L : Module.End ℂ (Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)))
    (h : ∀ f, GlobalTheory.RealLift.LieFirstPf.swapE (P w) (Q w) (R w) (S w) (L' f) =
      L (GlobalTheory.RealLift.LieFirstPf.swapE (P w) (Q w) (R w) (S w) f))
    (T : ⨂[ℂ] w : ι, Formalism.BasicNotions.TH.Pol (R w) (S w) (P w) (Q w)) :
    swapTD P Q R S (atPl w L' T) = atPl w L (swapTD P Q R S T) := by
  have e : (swapTD P Q R S).toLinearMap ∘ₗ atPl w L' = atPl w L ∘ₗ (swapTD P Q R S).toLinearMap := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, atPl, swapTD,
      PiTensorProduct.map_tprod, PiTensorProduct.congr_tprod]
    congr 1
    funext i
    by_cases hi : i = w
    · subst hi; simp [h]
    · simp [Function.update_of_ne hi]
  exact LinearMap.congr_fun e T

theorem swapTD_sumPl (L' : ∀ w, Module.End ℂ (Formalism.BasicNotions.TH.Pol (R w) (S w) (P w) (Q w)))
    (L : ∀ w, Module.End ℂ (Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)))
    (h : ∀ w f, GlobalTheory.RealLift.LieFirstPf.swapE (P w) (Q w) (R w) (S w) (L' w f) =
      L w (GlobalTheory.RealLift.LieFirstPf.swapE (P w) (Q w) (R w) (S w) f))
    (T : ⨂[ℂ] w : ι, Formalism.BasicNotions.TH.Pol (R w) (S w) (P w) (Q w)) :
    swapTD P Q R S (sumPl L' T) = sumPl L (swapTD P Q R S T) := by

  simp only [sumPl, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun w _ => swapTD_atPl w (L' w) (L w) (h w) T

end Tensor

theorem lieFirstD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ)
    (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (d' : Darboux (symp (R := AF F) (cA σ) (-1) JB JA) κ) (a b : ℂ)
    (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ) (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ)
    (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ) (om : UG (cA σ) JA →* Module.End ℂ ((κ → AF F) → ℂ)),
    IsCMExt F E σ → IsStd ψ → FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ →
    (∀ x : Matrix α β (AE F E), d'.e xᵀ = d.e x) → IsUSplitting (adeleClass F) ψ d' (actB (cA σ)) om →
    ∃ c, ActsByD τ A om Φ (fun w => fockAct1 (P w) (Q w) (R w) (S w)) c := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d d' a b A C Φ om hCM hψ hfr hΦ hdd hW
  have hfr' : FramedD τ JB JA b a C A := ⟨by rw [mul_comm]; exact hfr.1, hfr.2.2, hfr.2.1⟩
  have hΦ' : IsFockMapD ψ τ d' C A (Φ ∘ₗ (swapTD P Q R S).toLinearMap) := by
    refine ⟨hΦ.1.comp (swapTD P Q R S).injective, fun u hu c hc T => ?_⟩
    have hu' : At (evI F) uᵀ := fun x hx => by rw [← Matrix.transpose_smul, hu x hx, Matrix.transpose_zero]
    have hc' : ∀ w, uᵀ.map (piInf (τ w)) = A w * (c w)ᵀ * (C w)ᵀ := fun w => by
      rw [Matrix.transpose_map, hc w]; simp [Matrix.transpose_mul, Matrix.mul_assoc]
    have key := hΦ.2 uᵀ hu' (fun w => (c w)ᵀ) hc' (swapTD P Q R S T)
    have hr : ∀ t : ℝ, d'.rho ψ (realAd F t • u) = d.rho ψ (realAd F t • uᵀ) := fun t => by
      show schr ψ (d'.e _) = schr ψ (d.e _)
      rw [← hdd, Matrix.transpose_smul, Matrix.transpose_transpose]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hr]
    rwa [swapTD_sumPl (fun w => heisOp (c w)) (fun w => heisOp (c w)ᵀ)
      (fun w f => GlobalTheory.RealLift.LieFirstPf.swapE_heisOp (c w) f)]
  obtain ⟨c, hA⟩ := GlobalTheory.T.howeSplitting_acts_fockAction_plus_traceMultiples F E σ β α κ R S P Q ψ τ JB JA d' b a C A _ om hCM hψ hfr' hΦ' hW
  refine ⟨c, fun γ hγ Y hY T => ?_⟩
  have key := hA γ hγ Y hY ((swapTD P Q R S).symm T)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at key
  rwa [swapTD_sumPl (fun w => fockAct2 (R w) (S w) (P w) (Q w) (Y w) + (c w * (Y w).trace) • 1)
    (fun w => fockAct1 (P w) (Q w) (R w) (S w) (Y w) + (c w * (Y w).trace) • 1) (fun w f => by
      simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add (f := _), map_smul,
        GlobalTheory.RealLift.LieFirstPf.swapE_apply, (GlobalTheory.FockSwap.swap_symmetry (R w) (S w) (P w) (Q w)).2.1]),
    LinearEquiv.apply_symm_apply] at key

end GlobalTheory.HoweD.LieFirstD
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ResW

theorem nu_zero_isUnitary (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] : (nu E 0).IsUnitary := by
  intro x
  simp [nu, GlobalTheory.HeckeGal.Model.absPow, GlobalTheory.Mem.Chr.CharModel.absHom_val]

theorem isUnitarisable_of_twRep {G X : Type} [Group G] [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ G X}
    {χ : G →* ℂˣ} (hχ : ∀ g, ‖((χ g : ℂˣ) : ℂ)‖ = 1) (h : GlobalTheory.SmGL.IsUnitarisable (twRep ρ χ)) :
    GlobalTheory.SmGL.IsUnitarisable ρ := by
  obtain ⟨B, h1, h2, h3⟩ := h
  refine ⟨B, h1, h2, fun g v w => ?_⟩
  have e := h3 g v w
  simp only [twRep_apply, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul] at e
  have hc : ((χ g : ℂˣ) : ℂ) * starRingEnd ℂ ((χ g : ℂˣ) : ℂ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ g]; simp
  rw [← e]
  linear_combination (-(B (ρ g v) (ρ g w))) * hc

theorem isUnitarisable_of_isLocComp_cusp : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (x : CuspSub E a), 1 ≤ a → x.IsUnitary → ∀ (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), x.IsLocComp w σ → GlobalTheory.SmGL.IsUnitarisable σ.ρ := by
  intro E _ _ _ a x ha hu w σ hσ
  have hcex := (GlobalTheory.T.cuspidalLetter_centralExponent_properties E ⟨a, x⟩).1
  have hr : rexp (⟨a, x⟩ : Letter E) = 0 := ((GlobalTheory.T.cuspidalLetterRealExponent_eq_zero_iff_isUnitary E ⟨a, x⟩ ha).1).2 hu
  have hd : (0 : ℝ) < (a : ℝ) * Module.finrank ℚ E := by
    have := Module.finrank_pos (R := ℚ) (M := E)
    have : (1 : ℝ) ≤ a := by exact_mod_cast ha
    positivity
  have hre : (cex (⟨a, x⟩ : Letter E)).re = 0 := by
    have h := hr
    unfold rexp at h
    rcases div_eq_zero_iff.1 h with h | h
    · exact h
    · exact absurd h hd.ne'
  have hdc : ((a : ℂ) * (Module.finrank ℚ E : ℂ)) = (((a : ℝ) * Module.finrank ℚ E : ℝ) : ℂ) := by push_cast; ring
  obtain ⟨χ, hz, -, hn, -⟩ := GlobalTheory.T.exists_idelic_absValue_cpow_character E (-(cex (⟨a, x⟩ : Letter E)) / ((a : ℂ) * (Module.finrank ℚ E : ℂ)))
  have hzre : (-(cex (⟨a, x⟩ : Letter E)) / ((a : ℂ) * (Module.finrank ℚ E : ℂ))).re = 0 := by
    rw [hdc, Complex.div_ofReal_re, Complex.neg_re, hre]; simp
  have hχu : χ.IsUnitary := fun y => by rw [hn y, hzre]; exact nu_zero_isUnitary E y
  have hnorm : IsNormalised (x.twist χ) := by
    have h4 := GlobalTheory.T.cuspidalLetter_centralExponent_properties E ⟨a, x.twist χ⟩
    refine h4.2.2.2.1.1 (h4.2.2.2.2 0 ?_)
    obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 x.ne_bot
    refine ⟨mulChi a χ φ, ⟨φ, hφ, rfl⟩, fun h => h0 ((mulChi a χ).map_eq_zero_iff.1 h), ?_⟩
    have e1 : zc E a φ = cex (⟨a, x⟩ : Letter E) • φ := hcex φ hφ
    have e2 : cex (⟨a, x⟩ : Letter E) + (a : ℂ) * (Module.finrank ℚ E : ℂ) *
        (-(cex (⟨a, x⟩ : Letter E)) / ((a : ℂ) * (Module.finrank ℚ E : ℂ))) = 0 := by
      have : ((a : ℂ) * (Module.finrank ℚ E : ℂ)) ≠ 0 := by
        rw [hdc]; exact_mod_cast hd.ne'
      rw [mul_div_cancel₀ _ this]; ring
    change zc E a (mulChi a χ φ) = (0 : ℂ) • mulChi a χ φ
    rw [hz, e1, ← add_smul, e2, zero_smul, map_zero, zero_smul]
  have hdisc := (GlobalTheory.T.cuspForm_sqIntegrable_and_isDiscrete_splitCentre E a).2 _ hnorm
  obtain ⟨f, h0, hf⟩ := hσ.twist χ
  have hgl : IsLocCompGL (x.twist χ).V w (σ.twist (CuspSub.locDet a χ w) (CuspSub.isOpen_ker_locDet χ w)) :=
    ⟨(x.twist χ).V.subtype ∘ₗ f, fun h => h0 (LinearMap.ext fun v => Subtype.ext (LinearMap.congr_fun h v)),
      fun v => (f v).2, fun g v => congrArg Subtype.val (hf g v)⟩
  have hU := GlobalTheory.DiscreteUnit.isUnitarisable_of_isLocCompGL E a _ hdisc w _ hgl
  exact isUnitarisable_of_twRep (χ := CuspSub.locDet a χ w) (fun g => hχu _) hU

end GlobalTheory.ResW
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weilRepresentation_real_moves_frame_detChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ mu : GA D W → ℂ, Formalism.L2.Pj.MuVal W χV mu → ∀ (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsMod W hr X → IsSympl X bas → ∀ (x : Frame X.Ψ r), IsONFr X x → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), IsThetaFunO ψ V W f → Reads θ V W hr X bas idx f φ x → ∀ u ∈ GinfC W, Reads θ V W hr X bas idx (om (1, u) f) (mu u • φ) (frMove θ W hr X u x) := by
  first | exact @GlobalTheory.RealMove.om_real_reads | exact GlobalTheory.RealMove.om_real_reads | (intros; apply GlobalTheory.RealMove.om_real_reads <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem isOpen_globLev : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → IsOpen (globLev S K' : Set (finU (E := E) (n := n))) := by
  intro E _ _ _ hU n S K' hK
  have hT : {w : Pl E | ¬ K' w = KL n w}.Finite := Filter.eventually_cofinite.1 hK.2
  let f : ∀ w : Pl E, finU (E := E) (n := n) → UL n w := fun w x => ⟨cLoc w x.1, GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w x.1⟩
  have hf : ∀ w, Continuous (f w) := fun w =>
    Continuous.subtype_mk ((GlobalTheory.DefU.Inert.continuous_cLoc w).comp continuous_subtype_val) _
  have h1 : ∀ w, f w 1 = 1 := fun w => Subtype.ext (by simp [f])
  have hA : ∀ᶠ k : finU (E := E) (n := n) in nhds 1, ∀ w : Pl E, cLoc w (k : UA E n) ∈ GlobalTheory.LFun.KGL w (n := n) := by
    filter_upwards [(UpperTheory.unitaryAdelic_localComponents_continuous_levels_open E n).2.2] with k hk w
    exact (SetLike.ext_iff.1 (GlobalTheory.SmGL.SphCompletion.KO_completion w n) _).1 (hk w)
  have hB : ∀ᶠ k : finU (E := E) (n := n) in nhds 1, ∀ w ∈ {w : Pl E | ¬ K' w = KL n w}, f w k ∈ K' w := by
    refine (Filter.eventually_all_finite hT).2 fun w _ => ?_
    have ho : IsOpen ((f w) ⁻¹' (K' w : Set (UL n w))) := ((hK.1 w).1).preimage (hf w)
    exact ho.mem_nhds (by simp [h1])
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  filter_upwards [hA, hB] with x hxA hxB
  refine Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun _ => ?_
  refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨f w x, ?_, rfl⟩)
  by_cases hw : K' w = KL n w
  · rw [hw]
    exact Subgroup.mem_subgroupOf.2 (hxA w)
  · exact hxB w hw

end GlobalTheory.BCT
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

theorem _root_.GlobalTheory.T.formPart_compl_complexPointsInOpen_eq_zero : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (Y : Var F) (β : (atlas Y σ).Fld) (W : Y.X.Opens), genericPoint Y.X ∈ W → ∀ s : ℤˣ, (atlas Y σ).part β s (ptsIn Y.str σ W)ᶜ = 0 := by
  first | exact @GlobalTheory.FlagCell2Null.part_compl_ptsIn | exact GlobalTheory.FlagCell2Null.part_compl_ptsIn | (intros; apply GlobalTheory.FlagCell2Null.part_compl_ptsIn <;> assumption)
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.pow_generator_eq_const_mul_vacuum_theta : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → l.A = 1 → ∀ (k : U.Comp) (n g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw), Even n → IsSympl (U.X k) bas → IdxIs c σ (U.X k) idx e → ∀ v : TF n g, IsVac (U.X k) bas (H.w0 : E) (tens (stdL E n) (U.X k).Λ) v → ∃ C : ℂ, C ≠ 0 ∧ ∀ x : (U.X k).dom, IsUnitFr (U.X k) x.1 → (∃ ϑ, GenReads U k bas idx e x ϑ) ∧ ∀ ϑ, GenReads U k bas idx e x ϑ → IsTheta1 (U.X k) bas idx (H.w0 : E) x.1 (U.X k).Λ ϑ ∧ MeanOne (U.X k) bas idx x.1 (U.X k).Λ ϑ ∧ ∀ z : Fin n → Fin g → ℂ, ∏ b, ϑ (z b) = C * thA (U.X k) bas idx v x.1 z := by
  first | exact @GlobalTheory.AdTh.prod_gen_eq_const_mul_thA | exact GlobalTheory.AdTh.prod_gen_eq_const_mul_thA | (intros; apply GlobalTheory.AdTh.prod_gen_eq_const_mul_thA <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rationalLift_readings_scale_classSum_eigenspaces : GlobalTheory.Hk3.HoweUnram → GlobalTheory.LowRow.ConjRatLift5 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (F : Face D A) (ph : ℂ), GlobalTheory.Hk3.Core R F → IsStdChar D R.ψ (-1) → GlobalTheory.ConjScalar.ConjScalarAt R → ∀ fw : FWTie T R κ v₀, BarTie fw → IoExt R → R.LUnif → (∀ i, OMPins T R κ v₀ O i) → ∀ i : Fin D.R.m, (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph → ∀ (ℓ : Lvl D.what₂.LL G) (Z : Submodule D.what₂.LL (A.fam.L i A.μ0).S.Forms), Formalism.DivisionValues.IsRatHerm (Formalism.DivisionValues.cmMax D.what₂.LL) ((A.fam.L i A.μ0).HZ ℓ Z) ((A.fam.L i A.μ0).XQ ℓ Z) → (∀ a k, (A.fam.L i A.μ0).fE ℓ Z a k ∈ Formalism.DivisionValues.cmMax D.what₂.LL) → (∀ z ∈ Z, R.jV i A.μ0 z ∈ LinearMap.range (LinearMap.adjoint (R.thG i A.μ0))) → ∀ (σ : D.what₂.LL →+* ℂ) (a : Pl D.host.E → List ℤ → D.what₂.LL), ∃ l : ℝ, ∀ x x' y y', GlobalTheory.ConjScalar.EigK R i a ((A.fam.L i A.μ0).toF ℓ Z x) → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph ((A.fam.L i A.μ0).toF ℓ Z x) y → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph x' y' → ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ = (l : ℂ) * GlobalTheory.LiftLower.csumAt (A.fam.L i A.μ0).S σ ((A.fam.L i A.μ0).toF ℓ Z x) x' := by
  first | exact @GlobalTheory.ConjScalar.readings_scale_core | exact GlobalTheory.ConjScalar.readings_scale_core | (intros; apply GlobalTheory.ConjScalar.readings_scale_core <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.double_scaling_local_identity : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
      (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd → GlobalTheory.DblScal.LocOps omd v →
      ∀ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd → ∃ cd : GlobalTheory.DblScal.UD σ W.J → ℂ, GlobalTheory.DblScal.IsShapeD omd t c ιd cd := by
  first | exact @GlobalTheory.DblShape.shape_dbl | exact GlobalTheory.DblShape.shape_dbl | (intros; apply GlobalTheory.DblShape.shape_dbl <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.triple_linear_witt_model_nonvanishing : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v)
    (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι →
    ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
    (∀ μ : @Measure (Fin a × Fin (a + a') → Fv F v) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫⁻ x, ‖φ₁ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    ∀ ν : @Measure (Matrix (Fin a) (Fin (a + a')) (Fv F v)) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      ∫⁻ Y, ‖ι φ₁ Y‖ₑ ^ 2 ∂ν = ∫⁻ Y, ‖ι φ Y‖ₑ ^ 2 ∂ν := by
  first | exact @GlobalTheory.LinearModelL2.linIso_lintegral_eq | exact GlobalTheory.LinearModelL2.linIso_lintegral_eq | (intros; apply GlobalTheory.LinearModelL2.linIso_lintegral_eq <;> assumption)
end
