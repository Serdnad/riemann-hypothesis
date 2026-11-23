module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle021
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle249
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle160
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle087
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle084
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle240
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle329
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle159
import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergDerivativeDiagonalHalfEqSchrodingerDer
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle294
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawCombinationsOperatorDatum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.MoveZero

variable {D : D7}

section Lin

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

def sOpLin (β : Frame p S n) (P : Pair k n) (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) :
    (GA D S → ℂ) →ₗ[ℂ] (GA D S → ℂ) where
  toFun := sOp β P q χ ε
  map_add' a b := by
    have h : formAt β P (a + b) = formAt β P a + formAt β P b := by
      funext P₁; simp [formAt, map_add (f := _)]
    simp only [sOp, h, map_add (f := _), Pi.add_apply]
  map_smul' c a := by
    have h : formAt β P (c • a) = c • formAt β P a := by
      funext P₁; simp [formAt, map_smul]
    simp only [sOp, h, map_smul, Pi.smul_apply, RingHom.id_apply]

end Lin

variable {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

theorem S_lin (o : TDat c k ι) (ε : ℕ → ι → 𝓀[k]ˣ) (j : ℕ) :
    ∃ L : (GA D (c.X j) → ℂ) →ₗ[ℂ] (GA D (c.X j) → ℂ), ∀ f, o.S ε j f = L f := by
  refine ⟨o.I.foldr (fun i G => (sOpLin (o.β j i) (o.Q j i) o.q (resChar (o.χ i) (o.hχ i) o.q) (ε j i)).comp G)
    LinearMap.id, fun f => ?_⟩
  unfold TDat.S
  induction o.I with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, LinearMap.comp_apply, ih]; rfl

theorem S_smul (o : TDat c k ι) (ε : ℕ → ι → 𝓀[k]ˣ) (j : ℕ) (a : ℂ) (f : GA D (c.X j) → ℂ) :
    o.S ε j (a • f) = a • o.S ε j f := by
  obtain ⟨L, hL⟩ := S_lin o ε j
  rw [hL, hL, map_smul]

theorem S_sum (o : TDat c k ι) (ε : ℕ → ι → 𝓀[k]ˣ) (j : ℕ) {α : Type} (s : Finset α) (f : α → GA D (c.X j) → ℂ) :
    o.S ε j (∑ a ∈ s, f a) = ∑ a ∈ s, o.S ε j (f a) := by
  obtain ⟨L, hL⟩ := S_lin o ε j

  rw [hL, map_sum]; simp only [hL]

theorem lift_smul {S T : HSp D} (kd : KerDat S T) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (x : DefSp S) (y : DefSp T)
    (P : PolF D T.rank S.rank) (a : ℂ) (φ : GA D S → ℂ) :
    kd.lift ψ θ x y P (a • φ) = a • kd.lift ψ θ x y P φ := by
  funext h
  simp only [KerDat.lift, liftT_apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext g; ring

end GlobalTheory.SeeSaw.MoveZero

noncomputable section

namespace GlobalTheory.SeeSaw.MoveZero

variable {D : D7} {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

theorem col_zero (t : Tup c) (ψ : t.Col 0) : t.col 0 ψ = ψ := rfl

theorem col_succ (t : Tup c) (j : ℕ) (ψ : t.Col 0) : t.col (j + 1) ψ = t.K j (t.col j ψ) := rfl

theorem col_mem (t : Tup c) (hI : t.Is) : ∀ j, j ≤ D.R.m → ∀ ψ ∈ t.Ram 0, t.col j ψ ∈ t.Ram j := by
  intro j
  induction j with
  | zero => intro _ ψ hψ; exact hψ
  | succ j ih =>
    intro hj ψ hψ
    rw [col_succ]
    exact hI.stabK j (by omega) _ (ih (by omega) ψ hψ)

theorem iterS_mem (o : TDat c k ι) (t : Tup c) (ε : ℕ → ι → 𝓀[k]ˣ) (S₀ : (ι → 𝓀[k]ˣ) → t.Col 0 → t.Col 0)
    (hR : ReadS o t ε S₀) : ∀ i, ∀ ψ ∈ t.Ram 0, iterS S₀ ε i ψ ∈ t.Ram 0 := by
  intro i
  induction i with
  | zero => intro ψ hψ; exact hψ
  | succ i ih => intro ψ hψ; exact (hR.S₀ _ _ (ih ψ hψ)).1

theorem stepK (t : Tup c) (hK : t.KBack) {j : ℕ} (hj : j < D.R.m) {a b : t.Col j} (ha : a ∈ t.Ram j) (hb : b ∈ t.Ram j)
    (x : ℂ) (h : ∀ α y, t.rd j α a y = x • t.rd j α b y) :
    ∀ γ y', t.rd (j + 1) γ (t.K j a) y' = x • t.rd (j + 1) γ (t.K j b) y' := by
  intro γ y'
  obtain ⟨hc, hB⟩ := hK j hj
  obtain ⟨n, y, P, hP⟩ := hB y'
  have e1 := hP a ha γ
  simp_rw [h, lift_smul, ← Finset.smul_sum, ← hP b hb γ] at e1
  rw [smul_comm] at e1
  exact smul_right_injective _ hc e1

theorem stepB (o : TDat c k ι) (t : Tup c) (ε : ℕ → ι → 𝓀[k]ˣ) (S₀ : (ι → 𝓀[k]ˣ) → t.Col 0 → t.Col 0)
    (hI : t.Is) (hK : t.KBack) (hL : LiftS o t) (hR : ReadS o t ε S₀) (η : ι → 𝓀[k]ˣ) :
    ∀ j, j ≤ D.R.m → ∀ ψ ∈ t.Ram 0, ∀ α y, o.S (fun _ => η) j (t.rd j α (t.col j ψ) y) =
      (∏ l ∈ Finset.range j, o.cL l) • t.rd j α (t.col j (S₀ η ψ)) y := by
  intro j
  induction j with
  | zero =>
    intro _ ψ hψ α y
    rw [Finset.range_zero, Finset.prod_empty, one_smul, col_zero, col_zero]
    exact ((hR.S₀ η ψ hψ).2 α y).symm
  | succ j ih =>
    intro hj ψ hψ γ y'
    have hj' : j < D.R.m := by omega
    obtain ⟨hc, hB⟩ := hK j hj'
    obtain ⟨n, y, P, hP⟩ := hB y'
    have m1 := col_mem t hI j hj'.le ψ hψ
    have m2 := col_mem t hI j hj'.le _ (hR.S₀ η ψ hψ).1
    have e1 := hP _ m1 γ
    have e2 := hP _ m2 γ
    apply smul_right_injective _ hc
    show t.cK j • o.S (fun _ => η) (j + 1) (t.rd (j + 1) γ (t.K j (t.col j ψ)) y') =
      t.cK j • ((∏ l ∈ Finset.range (j + 1), o.cL l) • t.rd (j + 1) γ (t.K j (t.col j (S₀ η ψ))) y')
    calc t.cK j • o.S (fun _ => η) (j + 1) (t.rd (j + 1) γ (t.K j (t.col j ψ)) y')
        = o.S (fun _ => η) (j + 1) (t.cK j • t.rd (j + 1) γ (t.K j (t.col j ψ)) y') := by rw [S_smul]
      _ = ∑ a, ∑ α, o.S (fun _ => η) (j + 1) ((t.ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P a)
            (t.rd j α (t.col j ψ) (y a))) := by
          rw [e1, S_sum]; simp only [S_sum]
      _ = ∑ a, ∑ α, (o.cL j * ∏ l ∈ Finset.range j, o.cL l) • (t.ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P a)
            (t.rd j α (t.col j (S₀ η ψ)) (y a)) := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun α _ => ?_
          rw [(hL j hj' α γ (P a) _ (hR.ram j hj'.le _ m1 α (y a))).2 η, ih hj'.le ψ hψ α (y a), lift_smul, smul_smul]
      _ = (o.cL j * ∏ l ∈ Finset.range j, o.cL l) • (t.cK j • t.rd (j + 1) γ (t.K j (t.col j (S₀ η ψ))) y') := by
          rw [e2]; simp only [Finset.smul_sum]
      _ = t.cK j • ((∏ l ∈ Finset.range (j + 1), o.cL l) • t.rd (j + 1) γ (t.K j (t.col j (S₀ η ψ))) y') := by
          rw [Finset.prod_range_succ, smul_comm, mul_comm]

theorem stepC (o : TDat c k ι) (t : Tup c) (ε : ℕ → ι → 𝓀[k]ˣ) (S₀ : (ι → 𝓀[k]ˣ) → t.Col 0 → t.Col 0)
    (hI : t.Is) (hK : t.KBack) (hL : LiftS o t) (hR : ReadS o t ε S₀) :
    ∀ i, 2 * i ≤ D.R.m → ∀ ψ ∈ t.Ram 0, t.up i ψ ∈ t.Ram (2 * i) ∧
      ∀ α y, t.rd (2 * i) α (t.up i ψ) y = o.cS i • t.rd (2 * i) α (t.col (2 * i) (iterS S₀ ε i ψ)) y := by
  intro i
  induction i with
  | zero =>
    intro _ ψ hψ
    refine ⟨hψ, fun α y => ?_⟩
    simp only [TDat.cS, Finset.range_zero, Finset.prod_empty, one_smul]
    rfl
  | succ i ih =>
    intro hi ψ hψ
    obtain ⟨hu, hr⟩ := ih (by omega) ψ hψ
    have hφ := iterS_mem o t ε S₀ hR i ψ hψ
    have hS := hI.stabS (2 * i) (by omega) _ hu
    have hw := col_mem t hI (2 * i) (by omega) _ (hR.S₀ (ε (2 * i)) _ hφ).1
    have hv := col_mem t hI (2 * i) (by omega) _ hφ
    have h0 : ∀ α y, t.rd (2 * i) α (t.S (2 * i) (t.up i ψ)) y =
        (o.cS i * ∏ l ∈ Finset.range (2 * i), o.cL l) •
          t.rd (2 * i) α (t.col (2 * i) (S₀ (ε (2 * i)) (iterS S₀ ε i ψ))) y := by
      intro α y
      rw [hR.S (2 * i) (by omega) _ hu α y, hr α y, S_smul, mul_smul]
      congr 1
      exact stepB o t ε S₀ hI hK hL hR (ε (2 * i)) (2 * i) (by omega) _ hφ α y
    have h1 := stepK t hK (j := 2 * i) (by omega) hS hw _ h0
    have hlt1 : 2 * i < D.R.m := by omega
    have hlt2 : 2 * i + 1 < D.R.m := by omega
    have h2 := stepK t hK (j := 2 * i + 1) hlt2 (hI.stabK (2 * i) hlt1 _ hS) (hI.stabK (2 * i) hlt1 _ hw) _ h1
    refine ⟨hI.stabK (2 * i + 1) hlt2 _ (hI.stabK (2 * i) hlt1 _ hS), fun α y => ?_⟩
    have hc : o.cS (i + 1) = o.cS i * ∏ l ∈ Finset.range (2 * i), o.cL l := by
      simp only [TDat.cS, Finset.prod_range_succ]
    rw [hc]
    exact h2 α y

end GlobalTheory.SeeSaw.MoveZero

namespace GlobalTheory.SeeSaw

theorem commX_of_laws : ∀ (D : D7) (c : Comm D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι) (t : Tup c) (ε : ℕ → ι → 𝓀[k]ˣ)
    (S₀ : (ι → 𝓀[k]ˣ) → t.Col 0 → t.Col 0),
    t.Is → t.KBack → t.TailRd → LiftS o t → ReadS o t ε S₀ → CommX o t ε S₀ := by
  intro D c k _ _ _ _ ι o t ε S₀ hI hK hT hL hR n h ψ hψ F
  obtain ⟨hu, hr⟩ := MoveZero.stepC o t ε S₀ hI hK hL hR n h.le ψ hψ
  exact hT (2 * n) h _ hu _ (MoveZero.col_mem t hI (2 * n) h.le _ (MoveZero.iterS_mem o t ε S₀ hR n ψ hψ)) _ hr F

end GlobalTheory.SeeSaw
end
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace StdExProof

theorem qt_facts (T : ℕ) [Fact T.Prime] : Nat.card 𝓀[ℚ_[T]] = T ∧ Irreducible ((T : 𝒪[ℚ_[T]])) := GlobalTheory.T.padic_residueField_card_and_prime_irreducible T

theorem not_sq_dvd (E : Type) [Field E] [NumberField E] (T : ℕ) (hT : T.Prime) (hs : GlobalTheory.St.G.SplitsIn E T)
    (w : HeightOneSpectrum (𝓞 E)) (hw : (T : 𝓞 E) ∈ w.asIdeal) : ¬ w.asIdeal ^ 2 ∣ Ideal.span {(T : 𝓞 E)} :=
  GlobalTheory.T.not_sq_dvd_of_rationalPrimeSplitsCompletely E T hT hs w hw

theorem places_over (D : D7) (π π' : 𝓞 D.host.E) (T : ℕ) (hπ' : (π' : D.host.E) = star (π : D.host.E))
    (hT : π * π' = (T : 𝓞 D.host.E)) (hne : π ≠ 0) (x : HeightOneSpectrum (𝓞 D.host.F)) :
    (T : 𝓞 D.host.F) ∈ x.asIdeal ↔ ∃ w ∈ Formalism.L2.Col.divs π, w.under (𝓞 D.host.F) = x :=
  GlobalTheory.T.places_dvd_norm_iff_under_primes_dvd D π π' T hπ' hT hne x

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_int (p : SplitPt D k) (x : 𝓞 D.host.E) : p.pr (incA D (x : D.host.E)) ∈ 𝒪[k] := by
  have h1 : IsIntegral ℤ (p.pr (incA D (x : D.host.E))) := (x.2).map ((p.pr.comp (incA D)).toIntAlgHom)
  have h2 : IsIntegral 𝒪[k] (p.pr (incA D (x : D.host.E))) := h1.tower_top
  exact (Valuation.integer.integers (valuation k)).mem_of_integral h2

theorem val_pr_eq_one (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : Formalism.L2.NTheta.IsIdemAt p.e w)
    (y : 𝓞 D.host.E) (hy : y ∉ w.asIdeal) : valuation k (p.pr (incA D (y : D.host.E))) = 1 := by
  have hy0 : y ≠ 0 := fun h => hy (h ▸ w.asIdeal.zero_mem)
  have hyE : (y : D.host.E) ≠ 0 := by exact_mod_cast hy0
  have hI : finPart D (p.e * incA D ((y : D.host.E))⁻¹) ∈ intAE D := not_not.1 (mt (hw.2 y hy0).2 hy)
  have h1 : p.pr (incA D ((y : D.host.E))⁻¹) ∈ 𝒪[k] := by
    rw [p.int_iff, p.sec_pr]; exact hI
  have h2 := pr_int p y
  have hmul : p.pr (incA D (y : D.host.E)) * p.pr (incA D ((y : D.host.E))⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hyE, map_one, map_one]
  have e1 : valuation k (p.pr (incA D (y : D.host.E))) ≤ 1 := h2
  have e2 : valuation k (p.pr (incA D ((y : D.host.E))⁻¹)) ≤ 1 := h1
  have e3 := congrArg (valuation k) hmul
  rw [map_mul, map_one] at e3
  refine le_antisymm e1 ?_
  by_contra hlt
  push_neg at hlt
  have : valuation k (p.pr (incA D (y : D.host.E))) * valuation k (p.pr (incA D ((y : D.host.E))⁻¹)) < 1 :=
    mul_lt_one_of_lt_of_le hlt e2
  rw [e3] at this
  exact lt_irrefl _ this

theorem isLat_std (p : SplitPt D k) (S : HSp D) (β : Frame p S (Fin S.rank)) (hb : β.b = 1) (L : Lat S)
    (hL : ∀ z, z ∈ L ↔ z ∈ intVec D _) : β.IsLat L (stdLat k (Fin S.rank)) := by
  intro x
  have hL' : ∀ z : Fin S.rank → D.host.E, z ∈ L ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = z i := fun z => by
    rw [hL z]
    exact ⟨fun h i => ⟨⟨z i, h i⟩, rfl⟩, fun h i => by obtain ⟨b, hb⟩ := h i; exact hb ▸ b.2⟩
  rw [hb, Matrix.one_mulVec, GlobalTheory.FinPl.Model.mem_latV_std S L hL' p.v, mem_stdLat]
  refine forall_congr' fun i => ?_
  rw [p.int_iff]
  exact ⟨fun h => ⟨GlobalTheory.FinPl.FrameLat.sec_mem_idAt p _, h⟩, fun h => h.2⟩

def scPair (c : 𝒪[k]) (hc : IsUnit c) {n : Type} [Fintype n] (i : n) : Pair k n where
  lat := stdLat k n
  isLat := inferInstance
  fn := c • (stdPair k i).fn
  fn_ne h := (stdPair k i).fn_ne (LinearMap.ext fun x => (hc.smul_eq_zero).1 (LinearMap.congr_fun h x))

theorem scPair_hasVal (c : 𝒪[k]) (hc : IsUnit c) {n : Type} [Fintype n] (i : n) (x : n → k) (hx : ∀ j, x j ∈ 𝒪[k]) :
    (scPair c hc i).HasVal x (residue 𝒪[k] (c * ⟨x i, hx i⟩)) :=
  ⟨mem_stdLat.2 hx, by
    show c • residue 𝒪[k] ⟨x i, _⟩ = _
    rw [map_mul, Algebra.smul_def]; rfl⟩

end StdExProof
end GlobalTheory.AdForm

namespace GlobalTheory.AdForm.StdExProof
open GlobalTheory.AdForm

theorem stdEx' : StdEx' := by
  intro B X I hI _hP l Z u ψ hψ L hL
  haveI hTf : Fact (B.T u).Prime := ⟨l.pr.T_prime u⟩
  obtain ⟨hcard, hirr⟩ := qt_facts (B.T u)
  have hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u)) := l.pr.piT_cop u
  have hne : X.piT u ≠ 0 := by
    intro h0
    rw [h0, map_zero, isCoprime_zero_left] at hcop
    exact not_isUnit_zero hcop
  have hmem : ∀ i : (B.primes X).vT u, X.piT u ∈ i.1.asIdeal := fun i => (Formalism.L2.Col.mem_divs hne _).1 i.2
  have hconj : ∀ i : (B.primes X).vT u, B.fields.conjO (X.piT u) ∉ i.1.asIdeal := by
    intro i hc
    obtain ⟨a, b, hab⟩ := hcop
    exact i.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ i.1.asIdeal.add_mem (Ideal.mul_mem_left _ a (hmem i)) (Ideal.mul_mem_left _ b hc)))
  have hcP : ∀ i : (B.primes X).vT u, GlobalTheory.IdemSupport.cP (D := I.rec7 l Z) i.1 ≠ i.1 := by
    intro i h
    apply hconj i
    have h1 : X.piT u ∈ (GlobalTheory.IdemSupport.cP (D := I.rec7 l Z) i.1).asIdeal := by rw [h]; exact hmem i
    have h2 := (GlobalTheory.IdemSupport.mem_cP (D := I.rec7 l Z) i.1 (X.piT u)).1 h1
    have h3 : B.fields.conjO (X.piT u) = GlobalTheory.IdemSupport.cO (I.rec7 l Z) (X.piT u) := RingOfIntegers.ext rfl
    rw [h3]; exact h2
  choose e he using fun i : (B.primes X).vT u => GlobalTheory.StdFrames.exists_isIdemAt (hcP i)
  have hsplitT := (GlobalTheory.St.G.record_facts (I.rec7 l Z) u).1
  have hsp : ∀ i : (B.primes X).vT u, ∃ p : SplitPt (I.rec7 l Z) ℚ_[B.T u], p.e = e i := fun i =>
    (GlobalTheory.InhPt.exists_splitPt_frame_char (I.rec7 l Z)).1 ℚ_[B.T u] (B.T u) hTf.out hcard hirr i.1 (e i) (he i) (he i).1
      (l.pr.vT_norm u _ i.2) (not_sq_dvd _ (B.T u) hTf.out hsplitT i.1 (by
        have h := Ideal.mul_mem_right (B.fields.conjO (X.piT u)) _ (hmem i)
        rw [l.pr.piT_norm u] at h
        exact h))
  choose p hpe using hsp
  have hidem : ∀ i, Formalism.L2.NTheta.IsIdemAt (p i).e i.1 := fun i => (hpe i).symm ▸ he i
  let wE : (B.primes X).vT u → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E) := fun i => i.1
  have hv : ∀ i : (B.primes X).vT u, HeightOneSpectrum.under (𝓞 (I.rec7 l Z).host.F) (wE i) = (p i).v := by
    intro i
    obtain ⟨ε, h1, h2⟩ := (p i).above
    exact GlobalTheory.IdemUnder.under_eq_of_isIdemAt _ _ _ _ ε (hidem i) h1 h2
  have hover := fun x => places_over (I.rec7 l Z) (X.piT u) (B.fields.conjO (X.piT u)) (B.T u) rfl (l.pr.piT_norm u) hne x
  have hTv : ∀ i, ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ (p i).v.asIdeal := fun i =>
    (hover (p i).v).2 ⟨wE i, i.2, hv i⟩
  have hunit : ∀ i, (p i).UnitAA := fun i => GlobalTheory.FinPl.UnitAt.unitAA_level I l Z u (p i) (hTv i)
  have hpart2 := fun i => (GlobalTheory.InhPt.exists_splitPt_frame_char (I.rec7 l Z)).2 ℚ_[B.T u] (p i)
  choose χ hχ using fun i => (hpart2 i).2 ψ hψ
  choose β hβ using fun j i => (hpart2 i).1 ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank) 1 1 (mul_one 1) (mul_one 1)
  have hβ' : ∀ j i, (β j i).b' = 1 := fun j i => by
    have := (β j i).bb'
    rwa [hβ j i, one_mul] at this
  have hrank : ∀ j, 0 < ((I.rec7 l Z).sp.X j).rank := by
    intro j
    obtain ⟨hs, h1, -⟩ := hI.spaces
    rw [show (I.rec7 l Z).sp.X j = B.sp.X j from rfl, h1 j]
    show 0 < B.R.k + j * (B.R.t + 1)
    have := B.R.m_add_three_le_k
    omega
  let c : (B.primes X).vT u → 𝒪[ℚ_[B.T u]] := fun i =>
    ⟨(p i).pr (incA (I.rec7 l Z) (B.fields.conjO (X.piT u) : B.fields.E)), pr_int (p i) (B.fields.conjO (X.piT u))⟩
  have hcv : ∀ i, valuation ℚ_[B.T u] ((p i).pr (incA (I.rec7 l Z) (B.fields.conjO (X.piT u) : B.fields.E))) = 1 :=
    fun i => val_pr_eq_one (p i) (hidem i) (B.fields.conjO (X.piT u)) (hconj i)
  have hc : ∀ i, IsUnit (c i) := fun i =>
    (Valuation.integer.integers (valuation ℚ_[B.T u])).isUnit_iff_valuation_eq_one.2 (hcv i)
  let last : ∀ j, Fin ((I.rec7 l Z).sp.X j).rank := fun j => ⟨((I.rec7 l Z).sp.X j).rank - 1, by have := hrank j; omega⟩
  let Q : ∀ j, (B.primes X).vT u → Pair ℚ_[B.T u] (Fin ((I.rec7 l Z).sp.X j).rank) := fun j i => scPair (c i) (hc i) (last j)
  have hStd : StdT I l Z u p β Q L := by
    refine ⟨⟨Equiv.refl _, fun i => hidem i⟩, fun j hj => ⟨hL j hj, fun i => ⟨isLat_std (p i) _ (β j i) (hβ j i) (L j) (hL j hj), ?_⟩⟩⟩
    intro z hz r hr
    have hz' : ∀ r', IsIntegral ℤ (z r') := (hL j hj z).1 hz
    have hx : ∀ r', (p i).pr (incA (I.rec7 l Z) (z r')) ∈ 𝒪[ℚ_[B.T u]] := fun r' => pr_int (p i) ⟨z r', hz' r'⟩
    change r.1 + 1 = ((I.rec7 l Z).sp.X j).rank at hr
    have hrl : r = last j := Fin.ext (by show r.1 = _ - 1; omega)
    subst hrl
    refine ⟨c i * ⟨_, hx (last j)⟩, ?_, ?_⟩
    · show (p i).pr (incA (I.rec7 l Z) (B.fields.conjO (X.piT u) : B.fields.E)) * (p i).pr (incA (I.rec7 l Z) (z (last j))) = _
      rw [← map_mul]
      exact congrArg _ (map_mul _ _ _).symm
    · rw [hβ' j i, Matrix.one_mulVec]
      exact scPair_hasVal (c i) (hc i) (last j) _ hx
  refine ⟨ℚ_[B.T u], inferInstance, inferInstance, inferInstance, inferInstance, (B.primes X).vT u, p, Finset.univ.toList,
    ⟨(B.T u : 𝒪[ℚ_[B.T u]]), hirr⟩, χ, β, Q, ⟨Finset.nodup_toList _, fun i => Finset.mem_toList.2 (Finset.mem_univ _),
    GlobalTheory.AdForm.StdT.places_injective I hI _hP l Z u p β Q L hStd, fun x => Iff.rfl, hunit⟩,
    fun i => ⟨(hχ i).2.2.2 (hunit i), (hχ i).1⟩, hcard, fun i => ⟨?_, hcv i⟩, fun x => ?_, hβ, hStd⟩
  · have hm : (p i).pr (incA (I.rec7 l Z) (X.piT u : B.fields.E)) *
        (p i).pr (incA (I.rec7 l Z) (B.fields.conjO (X.piT u) : B.fields.E)) = (B.T u : ℚ_[B.T u]) := by
      have : ((X.piT u : B.fields.E) * (B.fields.conjO (X.piT u) : B.fields.E)) = ((B.T u : ℕ) : B.fields.E) := by
        exact_mod_cast congrArg (fun x : 𝓞 B.fields.E => (x : B.fields.E)) (l.pr.piT_norm u)
      have h2 : (p i).pr (incA (I.rec7 l Z) (X.piT u : B.fields.E)) *
          (p i).pr (incA (I.rec7 l Z) (B.fields.conjO (X.piT u) : B.fields.E)) =
          (p i).pr (incA (I.rec7 l Z) (((B.T u : ℕ) : B.fields.E))) := by
        rw [← map_mul, ← this]
        exact congrArg _ (map_mul _ _ _).symm
      rw [h2]
      exact map_natCast ((p i).pr.comp (incA (I.rec7 l Z))) (B.T u)
    have hv2 := congrArg (valuation ℚ_[B.T u]) hm
    rw [map_mul, hcv i, mul_one] at hv2
    rw [hv2]
    rfl
  · rw [hover x]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨wE i, i.2, hv i⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, hv ⟨w, hw⟩⟩

end GlobalTheory.AdForm.StdExProof
end
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.heisenbergDerivative_diagonalHalf_eq_schrodingerDerivative : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ (τ : D.what₂.Tau) (X : Matrix (Fin B.rank) (Fin A.rank) ℂ) (x : Mx D B.rank A.rank), sch ψ A B ν 𝓨 (Formalism.IndefR.Datum.dRho (heisO ψ (dblSp A) B) θ τ (X * (dblDec A).qX.map (tauE D τ)) f) x = deriv (fun t : ℝ => sch ψ A B ν 𝓨 f (x + lineAt θ τ X t)) 0 := by
  first | exact @GlobalTheory.StdUnn.DiagDeriv.sch_dRho_diag | exact GlobalTheory.StdUnn.DiagDeriv.sch_dRho_diag | (intros; apply GlobalTheory.StdUnn.DiagDeriv.sch_dRho_diag <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.chain_first_stage_L_values_positive : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, LPos D := by
  first | exact @GlobalTheory.ChainTw.lPos_of_rapidDecay | exact GlobalTheory.ChainTw.lPos_of_rapidDecay | (intros; apply GlobalTheory.ChainTw.lPos_of_rapidDecay <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LinkKapMx

theorem mxAt_linkKappa : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ') (S : HSp D) (P : Pl D → Prop) (w : WO S L'), MxAt P w → MxAt P (l.κ S w) := by
  intro D ρ B L' ζ' l S P w hw
  exact GlobalTheory.LastOpPf.mxAt_kap _ S hw

end GlobalTheory.LinkKapMx
end

section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.lastSeeSaw_combinations_operatorDatum : ∀ D : D7, GlobalTheory.FinPl.LastOp D := by
  first | exact @GlobalTheory.LastOpPf.lastOp | exact GlobalTheory.LastOpPf.lastOp | (intros; apply GlobalTheory.LastOpPf.lastOp <;> assumption)
end
