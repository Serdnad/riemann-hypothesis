module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle384
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle403
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle126
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle153
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardTorsionMulFinrank
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle377
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachDeltaInvariantCoboundaries
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle178
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle252
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.BdRTied

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

def tu : P.R.BdRˣ := Units.map (P.ιB : P.R.B →* P.R.BdR) (isUnit_tB P).unit

theorem tu_val : (tu P : P.R.BdR) = P.ιB P.tB := by
  simp [tu]

theorem tz_eq (a : ℤ) : tz P a = ((tu P ^ a : P.R.BdRˣ) : P.R.BdR) := by
  rw [tz, tu, ← map_zpow]
  rfl

theorem fil_anti_le {a b : ℤ} (h : a ≤ b) (x : P.R.BdR) (hx : x ∈ Fil P b) : x ∈ Fil P a := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, b = a + n := ⟨(b - a).toNat, by omega⟩
  subst b
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    change x ∈ (P.PD (botExt l)).Fil (a + ↑(n + 1)) at hx
    exact ih (by omega) ((P.PD (botExt l)).Fil_anti (a + n) (by simpa [add_assoc] using hx))

theorem ι_injective : Function.Injective P.ιB := fun a b h =>
  (P.PD (botExt l)).ι_inj (by rw [P.PD_ι, P.PD_ι]; exact h)

theorem fil_mul (a b : ℤ) (x y : P.R.BdR) (hx : x ∈ Fil P a) (hy : y ∈ Fil P b) : x * y ∈ Fil P (a + b) :=
  (P.PD (botExt l)).Fil_mul a b x y hx hy

theorem fil_act (a : ℤ) (g : GQ l) (x : P.R.BdR) (hx : x ∈ Fil P a) : P.actQdR g x ∈ Fil P a := by
  have h := (P.PD (botExt l)).Fil_G ⟨g, mem_GK_botExt g⟩ a x hx
  rwa [P.PD_actdR] at h

theorem actQ_tpow (g : GQ l) (a : ℤ) : P.actQ g (((isUnit_tB P).unit ^ a : P.R.Bˣ) : P.R.B) =
    algebraMap ℚ_[l] P.R.B ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * (((isUnit_tB P).unit ^ a : P.R.Bˣ) : P.R.B) := by
  have h : Units.map (P.actQ g : P.R.B →* P.R.B) (isUnit_tB P).unit =
      Units.map (algebraMap ℚ_[l] P.R.B : ℚ_[l] →* P.R.B) (P.χQ g) * (isUnit_tB P).unit := by
    apply Units.ext
    simpa [Algebra.smul_def] using localPrime_galoisAction_periodT P g
  have h2 := congrArg (fun u : P.R.Bˣ => ((u ^ a : P.R.Bˣ) : P.R.B)) h
  simp only [mul_zpow, ← map_zpow, Units.val_mul, Units.coe_map] at h2
  rw [← map_zpow P.χQ]
  exact h2

theorem act_tz (g : GQ l) (a : ℤ) : P.actQdR g (tz P a) =
    algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * tz P a := by
  have hι : ∀ b : P.R.B, P.actQdR g (P.ιB b) = P.ιB (P.actQ g b) := fun b => by
    have h := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ b
    rw [P.PD_actB, P.PD_actdR, P.PD_ι, P.PD_ι] at h
    exact h.symm
  rw [tz, hι, actQ_tpow, map_mul, AlgHom.commutes]

variable {AI : LocAinf l P}

theorem fil_step (T : LocTied l P AI) (a : ℤ) (x : P.R.BdR) : x ∈ Fil P a ↔ P.ιB P.tB * x ∈ Fil P (a + 1) := by
  have h := ((GlobalTheory.MemLoc.TiedUnif.tied_uniformiser l P AI T).2.2 (botExt l) a (P.ιB P.tB * x))
  change x ∈ (P.PD (botExt l)).Fil a ↔ P.ιB P.tB * x ∈ (P.PD (botExt l)).Fil (a + 1)
  rw [h]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, e⟩
    have hu : IsUnit (P.ιB P.tB) := tu_val P ▸ (tu P).isUnit
    rwa [hu.mul_left_cancel e]

theorem fil_tz (T : LocTied l P AI) (b : ℤ) : ∀ (a : ℤ) (x : P.R.BdR), x ∈ Fil P a ↔ tz P b * x ∈ Fil P (a + b) := by
  induction b using Int.induction_on with
  | zero => intro a x; simp [tz_eq]
  | succ b ih =>
    intro a x
    rw [ih a x, fil_step P T (a + b), tz_eq, tz_eq, zpow_add_one, Units.val_mul, tu_val, ← add_assoc]
    ring_nf
  | pred b ih =>
    intro a x
    rw [ih a x, fil_step P T (a + (-(b : ℤ) - 1)), tz_eq, tz_eq, ← tu_val, ← mul_assoc, ← Units.val_mul,
      ← zpow_one_add]
    ring_nf

theorem isField (T : LocTied l P AI) : IsField P.R.BdR := by
  obtain ⟨-, -, hF, -⟩ := GlobalTheory.MemLoc.BdRField.bdR_isField l
  exact MulEquiv.isField hF T.eD.toMulEquiv

theorem unit_of_fil (T : LocTied l P AI) (x : P.R.BdR) (h0 : x ∈ Fil P 0) (h1 : x ∉ Fil P 1) :
    ∃ y ∈ Fil P 0, x * y = 1 := by
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  have he : GlobalTheory.MemLoc.IsEps AI.ε := hC.ε ▸ GlobalTheory.MemLoc.core_isEps l C
  obtain ⟨-, hker, hunit, -, -⟩ := GlobalTheory.MemLoc.thetaD_props l
  have h0' : T.eD x ∈ Formalism.Per.FilD l 0 := (T.fil (botExt l) 0 x).1 h0
  obtain ⟨w, hw⟩ := (GlobalTheory.MemLoc.TiedUnif.mem_FilD_iff he 0 (T.eD x)).1 h0'
  rw [zpow_zero, Units.val_one, one_mul] at hw
  have hθ : Formalism.Per.θD l w ≠ 0 := by
    intro hz
    apply h1
    change x ∈ (P.PD (botExt l)).Fil 1
    rw [T.fil, hw]
    have := GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD 1 ((hker w).1 hz)
    simpa using this
  obtain ⟨w', hw'⟩ := (hunit w hθ).exists_right_inv
  refine ⟨T.eD.symm (algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) w'), ?_, T.eD.injective ?_⟩
  · change _ ∈ (P.PD (botExt l)).Fil 0
    rw [T.fil, RingEquiv.apply_symm_apply]
    exact GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD_zero w'
  · rw [map_mul, RingEquiv.apply_symm_apply, hw, ← map_mul, hw', map_one, map_one]

theorem exact_deg (x : P.R.BdR) (hx : x ≠ 0) : ∃ a : ℤ, x ∈ Fil P a ∧ x ∉ Fil P (a + 1) := by
  classical
  obtain ⟨a₀, ha₀⟩ := (P.PD (botExt l)).Fil_exh x
  have hc : ∃ c, x ∉ Fil P c := by
    by_contra h
    push_neg at h
    exact hx ((P.PD (botExt l)).Fil_sep x h)
  obtain ⟨c, hc⟩ := hc
  have hbd : ∀ z : ℤ, x ∈ Fil P z → z ≤ c := fun z hz => by
    by_contra hlt
    exact hc (fil_anti_le P (le_of_lt (not_le.1 hlt)) x hz)
  obtain ⟨a, ha, hmax⟩ := Int.exists_greatest_of_bdd ⟨c, hbd⟩ ⟨a₀, ha₀⟩
  exact ⟨a, ha, fun h => by have := hmax _ h; omega⟩

end GlobalTheory.PMon.BdRTied

namespace GlobalTheory.PMon

theorem bdR_tied : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    IsField P.R.BdR ∧ Function.Injective P.ιB ∧
    (∀ (a b : ℤ) (x : P.R.BdR), x ∈ Fil P a ↔ tz P b * x ∈ Fil P (a + b)) ∧
    (∀ x ∈ Fil P 0, x ∉ Fil P 1 → ∃ y ∈ Fil P 0, x * y = 1) ∧
    (∀ x : P.R.BdR, x ≠ 0 → ∃ a : ℤ, x ∈ Fil P a ∧ x ∉ Fil P (a + 1)) ∧
    (∀ (a b : ℤ) (x y : P.R.BdR), x ∈ Fil P a → y ∈ Fil P b → x * y ∈ Fil P (a + b)) ∧
    (∀ (a : ℤ) (g : GQ l) (x : P.R.BdR), x ∈ Fil P a → P.actQdR g x ∈ Fil P a) ∧
    (∀ (a : ℤ) (g : GQ l), P.actQdR g (tz P a) = algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * tz P a) ∧
    (∀ a b : ℤ, tz P (a + b) = tz P a * tz P b) ∧ tz P 0 = 1 ∧ tz P 1 = P.ιB P.tB := by
  intro l _ P AI T
  refine ⟨BdRTied.isField P T, BdRTied.ι_injective P, fun a b x => BdRTied.fil_tz P T b a x,
    fun x h0 h1 => BdRTied.unit_of_fil P T x h0 h1, BdRTied.exact_deg P, BdRTied.fil_mul P,
    BdRTied.fil_act P, fun a g => BdRTied.act_tz P g a, fun a b => ?_, ?_, ?_⟩
  · rw [BdRTied.tz_eq, BdRTied.tz_eq, BdRTied.tz_eq, zpow_add, Units.val_mul]
  · rw [BdRTied.tz_eq, zpow_zero, Units.val_one]
  · rw [BdRTied.tz_eq, zpow_one, BdRTied.tu_val]

end GlobalTheory.PMon
end
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.RedAct

theorem ringHom_padicInt_eq {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] (f : ℤ_[l] →+* k)
    (z : ℤ_[l]) : f z = ((ZMod.castHom (dvd_refl l) k).comp PadicInt.toZMod) z := by
  have h := PadicInt.sub_zmodRepr_mem z
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  have hz : z = (z.zmodRepr : ℤ_[l]) + l * c := by rw [← hc]; ring
  rw [hz]
  simp only [map_add (f := _), map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

theorem map_act {l : ℕ} [Fact l.Prime] {O k : Type} [CommRing O] [Algebra ℤ_[l] O] [Field k] [CharP k l]
    (f : O →+* k) (c : ℤ_[l]) (a : O⟦X⟧) :
    PowerSeries.map f (GlobalTheory.CycFr.act O c a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l c (PowerSeries.map f a) := by
  have hb : PowerSeries.map f (GlobalTheory.CycFr.bin O c) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.onePlusPow k l c := by
    ext n
    rw [GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.onePlusPow, PowerSeries.coeff_map, PowerSeries.coeff_map,
      PowerSeries.binomialSeries_coeff, PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one,
      ← Algebra.algebraMap_eq_smul_one]
    exact ringHom_padicInt_eq (f.comp (algebraMap ℤ_[l] O)) _
  rw [GlobalTheory.CycFr.act_apply, GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi, ← hb]
  have h := PowerSeries.map_subst (GlobalTheory.CycFr.hasSubst_bin O c) (h := f) a
  have h2 : PowerSeries.map f (GlobalTheory.CycFr.bin O c - 1) = PowerSeries.map f (GlobalTheory.CycFr.bin O c) - 1 := by
    rw [map_sub, map_one]
  rw [← h2]
  exact h

theorem deltaPi_one_add {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] (b : k⟦X⟧) :
    GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l (1 + l) b = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.gammaPi k l b := by
  have h := PowerSeries.binomialSeries_nat (R := ℤ_[l]) (A := ℤ_[l]) (1 + l)
  rw [Nat.cast_add, Nat.cast_one] at h
  rw [GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi, GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.gammaPi, GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.onePlusPow, h]
  simp

theorem chi_surjective {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (hK : K.1 ≤ MaximalUnramifiedExtension l) (χ : W.Gam →* ℤ_[l]ˣ)
    (hχ : ∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = (W.χΓ g : ↥(OL LL))) :
    Function.Surjective χ := by
  intro u
  obtain ⟨χ', h1, -, h3⟩ := GlobalTheory.Cyc.exists_integral_cyclotomicChar l P
  obtain ⟨g, hg, hgu⟩ := h3 K 0 (le_trans (le_inf le_rfl hK) le_sup_left) u (by simp)
  refine ⟨W.resΓ ⟨g, hg⟩, Units.ext (GlobalTheory.algebraMap_padicInt_OL_injective LL ?_)⟩
  rw [hχ]
  apply Subtype.ext
  have h := W.χΓ_res ⟨g, hg⟩
  rw [P.PD_χ, ← h1] at h
  refine h.trans ?_
  change algebraMap ℚ_[l] ↥LL.1 ((χ' g : ℤ_[l]) : ℚ_[l]) = _
  rw [hgu]
  rfl

theorem card_torsion {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (hK : K.1 ≤ MaximalUnramifiedExtension l) (hl : l ≠ 2) (h : K.1 ≤ Ks K 1) :
    W.DelF.card = l - 1 := by
  have p1 : Module.finrank ↥(K0 K) ↥K.1 = 1 := by
    rw [Algebra.finrank_eq_one_iff_bijective_algebraMap]
    exact ⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun x => ⟨⟨x.1, x.2, hK x.2⟩, rfl⟩⟩
  have hc := GlobalTheory.TorsionCard.card_torsion_mul_finrank P K LL W hl h
  rw [p1, mul_one] at hc
  exact hc

theorem gamma_eq_act {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (χ : W.Gam →* ℤ_[l]ˣ)
    (hχ : ∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = (W.χΓ g : ↥(OL LL))) (g : W.Gam) :
    W.γ₀ g = GlobalTheory.CycFr.act ↥(OL LL) (χ g : ℤ_[l]) :=
  GlobalTheory.WachTie.γ₀_eq W (P.PD_p K) χ hχ g

theorem action_of_surjective {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀]
    [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] O] (χ : W.Gam →* ℤ_[l]ˣ)
    (hχ : ∀ g, algebraMap ℤ_[l] O (χ g : ℤ_[l]) = (W.χΓ g : O)) (hs : Function.Surjective χ)
    (hγ : ∀ g, W.γ₀ g = GlobalTheory.CycFr.act O (χ g : ℤ_[l])) (hc : W.DelF.card = l - 1)
    {k : Type} [Field k] [CharP k l] (r : O →+* k) :
    (∃ γ : W.Gam, (W.χΓ γ : O) = 1 + (l : O) ∧
      ∀ a, PowerSeries.map r (W.γ₀ γ a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.gammaPi k l (PowerSeries.map r a)) ∧
    ∃ e : {δ // δ ∈ W.DelF} ≃ {z : ℤ_[l] // z ^ (l - 1) = 1}, ∀ δ a,
      PowerSeries.map r (W.γ₀ δ.1 a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l (e δ).1 (PowerSeries.map r a) := by
  have h2l := (Fact.out : l.Prime).two_le
  have hχi : Function.Injective χ := fun a b hab =>
    W.χΓ_inj (Units.ext (by rw [← hχ, ← hχ, hab]))
  have hcard : Nat.card (CommGroup.torsion W.Gam) = l - 1 := by
    rw [← hc, ← Set.ncard_coe_finset, ← Nat.card_coe_set_eq]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
    rw [CommGroup.mem_torsion, Finset.mem_coe, GlobalTheory.WachTie.mem_DelF_iff]
  have hpow : ∀ δ ∈ W.DelF, δ ^ (l - 1) = 1 := fun δ hδ => by
    have h1 : (⟨δ, (GlobalTheory.WachTie.mem_DelF_iff W δ).1 hδ⟩ : CommGroup.torsion W.Gam) ^ (l - 1) = 1 := by
      rw [← hcard]; exact pow_card_eq_one'
    exact congrArg Subtype.val h1
  constructor
  · have hu : IsUnit (1 + (l : ℤ_[l])) := by
      have h1 := IsLocalRing.isUnit_or_isUnit_one_sub_self (-(l : ℤ_[l]))
      rw [sub_neg_eq_add, IsUnit.neg_iff] at h1
      exact h1.resolve_left PadicInt.p_nonunit
    obtain ⟨g, hg⟩ := hs hu.unit
    have hg' : (χ g : ℤ_[l]) = 1 + l := by rw [hg, hu.unit_spec]
    refine ⟨g, by rw [← hχ, hg', map_add (f := _), map_one, map_natCast], fun a => ?_⟩
    rw [hγ, map_act, hg', deltaPi_one_add]
  · let f : {δ // δ ∈ W.DelF} → {z : ℤ_[l] // z ^ (l - 1) = 1} := fun δ =>
      ⟨χ δ.1, by rw [← Units.val_pow_eq_pow_val, ← map_pow, hpow δ.1 δ.2, map_one, Units.val_one]⟩
    have hf : Function.Bijective f := by
      refine ⟨fun a b hab => Subtype.ext (hχi (Units.ext (congrArg Subtype.val hab))), fun z => ?_⟩
      have hu : IsUnit z.1 := IsUnit.of_pow_eq_one z.2 (by omega)
      obtain ⟨g, hg⟩ := hs hu.unit
      have hg' : (χ g : ℤ_[l]) = z.1 := by rw [hg, hu.unit_spec]
      refine ⟨⟨g, (W.DelF_def g).2 ⟨l - 1, by omega, hχi (Units.ext ?_)⟩⟩, Subtype.ext hg'⟩
      rw [map_pow, Units.val_pow_eq_pow_val, hg', z.2, map_one, Units.val_one]
    refine ⟨Equiv.ofBijective f hf, fun δ a => ?_⟩
    rw [hγ, map_act]
    rfl

theorem gamma_action_reduction : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], (∃ γ : (S.W H).Gam, ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) ∧ ∀ a, PowerSeries.map (algebraMap S.O k) ((S.W H).γ₀ γ a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.gammaPi k l (PowerSeries.map (algebraMap S.O k) a)) ∧ ∃ e : {δ // δ ∈ (S.W H).DelF} ≃ {z : ℤ_[l] // z ^ (l - 1) = 1}, ∀ δ a, PowerSeries.map (algebraMap S.O k) ((S.W H).γ₀ δ.1 a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l (e δ).1 (PowerSeries.map (algebraMap S.O k) a) := by
  intro l _ P H S k _ _ _
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.exists_cyclotomicChar_padicInt_units P S.K S.LL (S.W H)
  exact action_of_surjective (S.W H) χ hχ (chi_surjective P S.K S.LL _ S.hyp.1.2.1.1 χ hχ)
    (gamma_eq_act P S.K S.LL _ χ hχ)
    (card_torsion P S.K S.LL _ S.hyp.1.2.1.1 S.hyp.1.2.1.2.1 S.hyp.1.2.1.2.2.2.2.1) (algebraMap S.O k)

end GlobalTheory.RedAct
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.TripleTrace

open GlobalTheory.BlockComplement

theorem continuous_twO (D : D7) (a : D.nd.Loc) : Continuous (D.ntw.twist₂ a) := by
  have hl := GlobalTheory.TwistedSelmerCompare.natCast_mem_maximalIdeal (l := D.nd.l a) (D.nd.O a)
  have hl0 : ((D.nd.l a : ℕ) : D.ntw.O0 (D.ntw.twOf a)) ≠ 0 := by
    intro h0
    have := congrArg ((iotaOQ D.nd D.naut a).comp (D.ntw.twist₂ a)) h0
    rw [map_natCast, map_zero] at this
    exact (D.nd.lPrime a).out.ne_zero (by exact_mod_cast this)
  have hp : ((IsLocalRing.maximalIdeal (D.nd.O a)).comap (D.ntw.twist₂ a)).IsPrime := Ideal.comap_isPrime _ _
  have hm : ((IsLocalRing.maximalIdeal (D.nd.O a)).comap (D.ntw.twist₂ a)).IsMaximal := hp.isMaximal fun h => by
    apply hl0
    rw [← Ideal.mem_bot, ← h, Ideal.mem_comap, map_natCast]
    exact hl
  have he := IsLocalRing.eq_maximalIdeal hm
  refine continuous_of_continuousAt_zero (D.ntw.twist₂ a) ?_
  rw [ContinuousAt, map_zero,
    (D.ntw.twistBaseCoefficientRing_isAdic _).hasBasis_nhds_zero.tendsto_iff (D.nd.O_adic a).hasBasis_nhds_zero]
  refine fun n _ => ⟨n, trivial, fun x hx => ?_⟩
  rw [← he] at hx
  exact Ideal.le_comap_pow _ n hx

theorem trace_of_block {K : Type} [Field K] {n a t : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (M' : Matrix (Fin a) (Fin a) K) (c : Fin t → K) (e : (Fin n → K) ≃ₗ[K] ((Fin a → K) × (Fin t → K)))
    (h : ∀ u, e (M.mulVec u) = (M'.mulVec (e u).1, fun j => c j * (e u).2 j)) :
    M.trace = M'.trace + ∑ j, c j := by
  have e1 : e.conj (Matrix.toLin' M) =
      LinearMap.prodMap (Matrix.toLin' M') (Matrix.toLin' (Matrix.diagonal c)) := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨u, rfl⟩ := e.surjective x
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, Matrix.toLin'_apply, h]
    refine Prod.ext rfl ?_
    funext j
    simp [Matrix.mulVec_diagonal]
  rw [← Matrix.trace_toLin'_eq, ← LinearMap.trace_conj' _ e, e1, LinearMap.trace_prodMap',
    Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq, Matrix.trace_diagonal]

theorem trace_eq : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (a : D.nd.Loc) (π : D.nd.X a) (ρ : Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O a)) (s : D.ntw.Sig (D.ntw.twOf a)) (Sg : List (Part D.naut.CG)), GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsRhoPt D a π ρ → HasParamX D.nd D.naut a π Sg → GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsTriple D a s Sg → ∀ g, ((ρ g : GL (Fin D.R.r) (D.nd.O a)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)).trace = D.ntw.twist₂ a ((D.ntw.rhoS _ s g : GL (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))) : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))).trace := by
  rintro hC D i π ρ s Sg ⟨hρ, r₀, ⟨-, -, hr3⟩, e, he⟩ ⟨P, hP, -, -, -, hB4, -⟩ ⟨-, -, -, hT⟩ g
  have hι := GlobalTheory.CoeffEmbedding.continuous_iotaOQ _ _ _ D.nd D.naut i
  have hinj : Function.Injective (iotaOQ D.nd D.naut i) :=
    (D.naut.iotaQ i).injective.comp (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i)))
  apply hinj
  revert g
  rw [← funext_iff]
  refine AE.eq_of_continuous hC (hι.comp hρ.matrix_trace)
    (hι.comp ((continuous_twO D i).comp (D.ntw.rhoS_cont _ s).matrix_trace)) ?_
  filter_upwards [hT, ae_chiBar D.naut i, ae_epsBar D.naut i, eventually_out i,
    isoLoc_sum (A := D.naut) (twistIso D.nd D.naut (Sg ++ [muPart D.nd D.naut i]) D.naut.etaTinv),
    isoLoc_sum (A := D.naut) (twistIso D.nd D.naut Sg D.naut.etaTinv)]
    with w h1 h2 h3 h4 h5 h8 hw B σ hB hσ
  apply (D.naut.iotaQC i).injective
  have hq := normV_ne_zero w
  have h6 := D.naut.pt_loc i P π hP w (h4 hw)
  rw [← hr3 w (h4 hw) B σ hB hσ, ← hB4 w hw] at h6
  have h9 := map_trace_eq_sum _ _ _ h6
  have h10 := map_trace_eq_sum _ _ _ (h1 (h4 hw) B σ hB hσ)
  rw [D.naut.frobEig_tw _ _ h5.1, Multiset.sum_map_mul_right, Multiset.map_id', h5.2] at h9
  rw [D.naut.frobEig_tw _ _ h8.1, Multiset.sum_map_mul_right, Multiset.map_id', h8.2] at h10
  have h7 : ∑ c : Fin D.R.t, D.naut.iotaQC i (chiBar D.naut i (c.1 + 1) σ) =
      sumPart D.naut ⟨1, muEta D.naut i, D.R.t⟩ w *
        ((normV w : ℕ) : ℂ) ^ ((((1 - (D.R.nV : ℝ)) / 2 : ℝ)) : ℂ) := by
    rw [sumPart, ← List.sum_map_mul_right, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range,
      Finset.sum_range]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [chiBar_succ c.1 c.2, map_mul, map_zpow₀, h2 hw B σ hB hσ, h3 hw B σ hB hσ, ← Complex.cpow_intCast,
      mul_assoc, mul_assoc, ← Complex.cpow_add _ _ hq, ← Complex.cpow_add _ _ hq]
    congr 2
    push_cast
    ring
  have h11 := congrArg (fun x => D.naut.iotaQC i (D.naut.iotaQ i x)) (trace_of_block _ _ _ e (he σ))
  have h12 : iotaO D.nd D.naut i ((r₀ σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) _).trace =
      iotaO D.nd D.naut i ((ρ σ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).trace +
        ∑ c : Fin D.R.t, D.naut.iotaQC i (chiBar D.naut i (c.1 + 1) σ) := by

    simp only [map_add (f := _), map_sum] at h11
    refine Eq.trans ?_ (h11.trans ?_)
    · exact congrArg (fun x => D.naut.iotaQC i (D.naut.iotaQ i x)) (AddMonoidHom.map_trace (toK D.nd i) _)
    · congr 1
      exact congrArg (fun x => D.naut.iotaQC i (D.naut.iotaQ i x)) (AddMonoidHom.map_trace (toK D.nd i) _).symm
  refine Eq.trans ?_ h10.symm
  have h13 := h12.symm.trans h9
  rw [h7] at h13
  simp only [twistIso, muPart, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, add_zero, add_mul] at h13
  exact add_right_cancel h13

end GlobalTheory.TripleTrace

end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory

theorem piTensor_isSubquotient_jac_degZero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ), N = 0 → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (π : Representation ℂ (GL (Fin N) k) V) (d : Fin 0 → ℕ) (X : Fin 0 → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (e : (Σ a, Fin (d a)) ≃ Fin N),
    IsSubquotient (piTensor ρ) (GlobalTheory.SmGL.jac e π) := by
  intro k _ _ _ _ N hN V _ _ _ π d X _ _ ρ e
  subst hN
  have hK : twKer π (unipRad k e) 1 = ⊥ := by
    refine le_bot_iff.1 (Submodule.span_le.2 ?_)
    rintro w ⟨n, v, rfl⟩
    have h1 : (n : GL (Fin 0) k) = 1 := Subsingleton.elim _ _
    simp [h1]
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hx : (Submodule.Quotient.mk v : Jacquet π (unipRad k e)) ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero, hK, Submodule.mem_bot]; exact hv
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (Jacquet π (unipRad k e)),
      φ (Submodule.Quotient.mk v) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 h)
  let L : Jacquet π (unipRad k e) →ₗ[ℂ] PiTensorProduct ℂ X :=
    (PiTensorProduct.isEmptyEquiv (Fin 0)).symm.toLinearMap ∘ₗ φ
  refine IsSubquotient.of_surjective ⟨L, fun g => ?_⟩ ?_
  · have hg : g = 1 := Subsingleton.elim _ _
    subst hg
    rw [map_one, map_one]
    rfl
  · have hsurj : Function.Surjective φ := fun c =>
      ⟨(c / φ (Submodule.Quotient.mk v)) • Submodule.Quotient.mk v, by simp [hφ]⟩
    exact (PiTensorProduct.isEmptyEquiv (Fin 0)).symm.surjective.comp hsurj

end GlobalTheory
end
