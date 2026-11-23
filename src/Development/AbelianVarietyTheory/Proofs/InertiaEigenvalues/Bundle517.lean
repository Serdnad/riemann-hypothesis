module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle507
public import Formalism.LocalToGlobal.Divisibility.RowSideTie
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle397
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsJumpMultiset
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle512
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle058
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowBoundsOfAllLettersThick
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle506
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle439
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle005
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBlochKatoConditionOfWachModules
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolynomialEqZeroOfFunction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle103
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle503
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle153
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle508
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle292
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.eq_zero_of_frobenius_periodic_mem_deRhamFil_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h d : ℕ), 0 < h → 0 < d → ∀ c : P.R.B, (l : P.R.B) ^ d * P.φB^[h] c = c → (∀ j < h, ev P j c ∈ Fil P 0) → c = 0 := by
  first | exact @GlobalTheory.PMon.no_fil_zero_neg_slope | exact GlobalTheory.PMon.no_fil_zero_neg_slope | (intros; apply GlobalTheory.PMon.no_fil_zero_neg_slope <;> assumption)
end

section

open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

theorem _root_.GlobalTheory.T.detCharacterLabel_root_of_harishChandraConstituent : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (n : ℕ) (ψ : Gn g (n + 1) → ℂ) (f : (ZMod g)[X]), IsIrr ψ →
    HasLabel L ψ f → ∀ (σ : Gn g n → ℂ), IsIrr σ → ∀ (θ : (ZMod g)ˣ →* ℂˣ) (c : ZMod g), GlobalTheory.GLp.IsCharLab L θ c →
    (ip ψ (hc n 1 σ (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (n + 1)) ≠ 0 → f.IsRoot c) ∧
    (ip ψ (hc 1 n (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) σ (n + 1)) ≠ 0 → f.IsRoot c) := by
  first | exact @GlobalTheory.GLq.DetRoot.root_of_hc_det | exact GlobalTheory.GLq.DetRoot.root_of_hc_det | (intros; apply GlobalTheory.GLq.DetRoot.root_of_hc_det <;> assumption)
end

section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

namespace GlobalTheory

theorem etaJ_eq_zero_of_untwisted (D : D7) (j : ℕ) (w : D.what₂.places.Pl) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (hw : D.what₂.muAt w = D.what₂.mu0) : D.what₂.etaJ j w = 0 := by
  rw [D.etaJ_tie j w h1 h2]
  refine Finset.sum_eq_zero fun i hi => ?_
  exact absurd (by rw [((D.nd.locs_mem j w i).1 hi).2]; exact hw) (D.nd.w_tw i)

theorem etaJ_join : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → m ≤ D.R.m → ∀ (S0 : IndefData (A.side P ψ Zs)) (M : MtFam D) (Tn : NormalizedLocalCompatibility D M), TupTie D A S0 tup → (∀ y, y ∈ S0.Tw ↔ S0.μ y ≠ A.μ0) → (∀ (i : Fin m), ∀ y ∈ S0.Tw, FormsTie D.what₂.embLL ((D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)).comp (eMt i (S0.μ y)).toLinearMap) (lH D A P ψ i (S0.μ y)) (lE D A P ψ i (S0.μ y)) (D.what₂.eMt (tup (S0.μ y)) ((i : ℕ) + 1)) ∧ OLatTie D.what₂.embLL (D.what₂.MtLat (tup (S0.μ y)) ((i : ℕ) + 1)) ((D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)).comp (eMt i (S0.μ y)).toLinearMap) (lNab D A P ψ i (S0.μ y)) ∧ Idx.Z0 D (tup (S0.μ y)) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)) (eMt i (S0.μ y) ((lZ0 D A P ψ Zs i (S0.μ y)).mulVec (Pi.single k 1))))) → HeckeStdTw Tn.B → (∀ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → LatStable Tn.B j w) → (∀ i, SpecPr D i) → ∀ (i : Fin m) w, D.what₂.etaJ ((i : ℕ) + 1) w = @ite _ (D.plEq w ∈ S0.Tw) (Classical.propDecidable _) (A.fam.etaJ P ψ Zs i (S0.μ (D.plEq w)) (D.plEq w)) 0 := by
  intro D G _ _ Pl0 T m A P ψ Zs tup eMt s hOk hm S0 M Tn hTup hTw hMt hH hLat hSpec i w
  have hj1 : 1 ≤ (i : ℕ) + 1 := Nat.le_add_left _ _
  have hj2 : (i : ℕ) + 1 ≤ D.R.m := Nat.lt_of_lt_of_le i.2 hm
  by_cases h : D.plEq w ∈ S0.Tw
  · rw [if_pos h]
    have hne : D.what₂.muAt w ≠ D.what₂.mu0 := by
      rw [hTup.muAt w, ← hTup.mu0]
      exact fun e => (hTw _).1 h (hTup.inj e)
    have htw : D.what₂.muTw w = tup (S0.μ (D.plEq w)) :=
      ((D.what₂.muAt_or w).resolve_left hne).symm.trans (hTup.muAt w)
    obtain ⟨hM1, hM2, hM3⟩ := hMt i _ h
    obtain ⟨hZ, hE⟩ := GlobalTheory.T.rationalFormLength_eq_definiteFamily D G Pl0 T m A P ψ Zs tup eMt s hOk i (S0.μ (D.plEq w)) hM1 hM2 hM3
    rw [GlobalTheory.T.sum_localCongruenceLength_eq_rationalLength D M Tn ((i : ℕ) + 1) w hj1 hj2 hne hH (hLat _ w hj1 hj2 hne) (htw ▸ hZ)
      (fun i' _ => hSpec i'), htw]
    exact hE w
  · rw [if_neg h]
    refine etaJ_eq_zero_of_untwisted D _ w hj1 hj2 ?_
    rw [hTup.muAt w, ← hTup.mu0]
    congr 1
    by_contra hn
    exact h ((hTw _).2 hn)

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory.TateDualInv

section Bridge

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N
open ReciprocityTheory.Gal (cycZ)

variable {l : ℕ} [Fact l.Prime]

theorem isJumpV_zero_of_invariant (P : LocPrime l) (K LL : FinExt l) {V : Type} [AddCommGroup V] [Module ↥LL.1 V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (x : V) (hx : x ≠ 0)
    (h : ∀ g, ρ g x = x) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) : IsJumpV (P.PD K) ρ τ 0 := by
  have := LL.2
  refine GlobalTheory.HTW.isJumpV_of_injective (P.PD K) (Representation.trivial ↥LL.1 ↥(GK K) ↥LL.1) ρ
    (LinearMap.toSpanSingleton ↥LL.1 V x) (LinearMap.ker_eq_bot.1 (LinearMap.ker_toSpanSingleton _ hx))
    (fun g v => by simp [h]) τ 0 fun h0 => ?_
  have h1 := GlobalTheory.CrysExt.finrank_fildR_trivial (P.PD K) (LL := ↥LL.1) τ 0
  have h2 := GlobalTheory.CrysExt.finrank_fildR_trivial (P.PD K) (LL := ↥LL.1) τ (0 + 1)
  rw [h0, h1] at h2
  simp at h2

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] [IsAlgClosed Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) (P : LocPrime l)

theorem cycLL_eq (g : ↥(GK Bw.Kw)) :
    ((cycLL (P.PD Bw.Kw) ↥Bw.LL.1 g : (↥Bw.LL.1)ˣ) : ↥Bw.LL.1) =
      Bw.toLL (algebraMap ℤ_[l] O ((cycZ E Ω l (Bw.e.symm g : ↥Gw) : ℤ_[l]ˣ) : ℤ_[l])) := by
  change algebraMap ℚ_[l] ↥Bw.LL.1 (((P.PD Bw.Kw).χ g : ℚ_[l]ˣ) : ℚ_[l]) = _
  rw [P.PD_χ, ← GlobalTheory.BlockJumps.cycZ_eq_chi Bw P g]
  exact (congrArg Subtype.val (Bw.eO_alg _)).symm

theorem dot_dual {O L : Type} [CommRing O] [CommRing L] (φ : O →+* L) {m : ℕ} (A : GL (Fin m) O) (ε : O)
    (x y : Fin m → L) :
    ((A : Matrix (Fin m) (Fin m) O).map φ).mulVec x ⬝ᵥ
      ((ε • (A : Matrix (Fin m) (Fin m) O)⁻¹.transpose).map φ).mulVec y = φ ε * (x ⬝ᵥ y) := by
  have h1 : (ε • (A : Matrix (Fin m) (Fin m) O)⁻¹.transpose).map φ =
      φ ε • (((A : Matrix (Fin m) (Fin m) O)⁻¹).map φ).transpose := by
    ext a b
    simp
  have h2 : ((A : Matrix (Fin m) (Fin m) O)⁻¹).map φ * (A : Matrix (Fin m) (Fin m) O).map φ = 1 := by
    rw [← Matrix.map_mul, ← Matrix.coe_units_inv, Units.inv_mul, Matrix.map_one _ φ.map_zero φ.map_one]
  rw [h1, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]

omit [IsAlgClosed Ω] in
theorem rep_apply {m : ℕ} (r : ↥Gw →* GL (Fin m) O) (g : ↥(GK Bw.Kw)) (x : Fin m → ↥Bw.LL.1) :
    Bw.rep r g x = (((r (Bw.e.symm g) : GL (Fin m) O) : Matrix (Fin m) (Fin m) O).map Bw.toLL).mulVec x := rfl

omit [IsAlgClosed Ω] in
theorem card_emb : Nat.card (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥Bw.LL.1) = Module.finrank ℚ_[l] ↥Bw.Kw.1 := by
  have : FiniteDimensional ℚ_[l] ↥Bw.Kw.1 := Bw.Kw.2
  rw [← AlgHom.card ℚ_[l] ↥Bw.Kw.1 (Loc.Om l), ← Nat.card_eq_fintype_card]
  exact Nat.card_congr
    { toFun := fun τ => Bw.LL.1.val.comp τ
      invFun := fun τ => τ.codRestrict Bw.LL.1.toSubalgebra (Bw.LL_split τ)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem dot_bijective {L : Type} [Field L] (m : ℕ) :
    Function.Bijective (dotProductBilin L L : (Fin m → L) →ₗ[L] (Fin m → L) →ₗ[L] L) := by
  have hi : Function.Injective (dotProductBilin L L : (Fin m → L) →ₗ[L] (Fin m → L) →ₗ[L] L) := by
    intro x y h
    funext i
    simpa using LinearMap.congr_fun h (Pi.single i 1)
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).1 hi⟩

theorem local_noInv (AI : LocAinf l P) (T : LocTied l P AI) {m : ℕ} (r r' : ↥Gw →* GL (Fin m) O)
    (hd : ∀ g, ((r' g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O) =
      algebraMap ℤ_[l] O ((cycZ E Ω l (g : Ω ≃ₐ[E] Ω) : ℤ_[l]ˣ) : ℤ_[l]) •
        ((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O)⁻¹.transpose)
    (hdR : Bw.IsdRW P r) (hj : ∀ τ, ¬ IsJumpV (P.PD Bw.Kw) (Bw.rep r) τ (-1))
    (x : Fin m → ↥Bw.LL.1) (hx : ∀ g, Bw.rep r' g x = x) : x = 0 := by
  by_contra h0
  have : FiniteDimensional ℚ_[l] ↥Bw.Kw.1 := Bw.Kw.2
  have hc := card_emb Bw
  obtain ⟨⟨τ⟩, -⟩ := Nat.card_pos_iff.1 (hc ▸ Module.finrank_pos (R := ℚ_[l]) (M := ↥Bw.Kw.1))
  have hJ := isJumpV_zero_of_invariant P Bw.Kw Bw.LL (Bw.rep r') x h0 hx τ
  have hm := (GlobalTheory.DRDual.twisted_dual_deRham l P AI T Bw.Kw Bw.LL _ (Bw.rep r) _ (Bw.rep r')
    (dotProductBilin _ _) 1 (dot_bijective m) (fun g x y => by
      rw [zpow_one, cycLL_eq, rep_apply, rep_apply, hd]
      exact dot_dual _ _ _ _ _) (by simpa [IsDR, LocBridge.IsdRW] using hdR)).2 τ (-1) hc
  have h1 : multV (P.PD Bw.Kw) (Bw.rep r) τ (-1) = 0 := by
    unfold multV
    rw [not_not.1 (hj τ), sub_self]
  rw [h1, show -(-1 : ℤ) - 1 = 0 by norm_num] at hm
  apply hJ
  have hfin := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T Bw.Kw Bw.LL _ (Bw.rep r')).1
  have hle : FildR (P.PD Bw.Kw) (Bw.rep r') τ 0 ≤ DdR (P.PD Bw.Kw) (Bw.rep r') := le_trans inf_le_left inf_le_left
  have := Submodule.finiteDimensional_of_le hle
  refine Submodule.eq_of_le_of_finrank_eq (inf_le_inf_left _ ?_) ?_
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero =>
      set_option synthInstance.maxHeartbeats 200000 in
        simp
    | tmul v b => exact ⟨v ⊗ₜ[ℚ_[l]] ⟨b.1, (P.PD Bw.Kw).Fil_anti 0 b.2⟩, rfl⟩
    | add x y hx hy => simp only [map_add]; exact Submodule.add_mem _ hx hy
  · unfold multV at hm
    omega

end Bridge

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

section Global

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

def dualHom (i : X.Tw) (s : X.Sig i) : Gen.GE N →* Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i) where
  toFun := Tdual i s
  map_one' := by simp [Tdual, ← Tgl_coe]
  map_mul' g h := by
    simp only [Tdual, ← Tgl_coe, map_mul, Units.val_mul, Matrix.mul_inv_rev, Matrix.transpose_mul, smul_mul_smul_comm]

end Global


open scoped Pointwise in
theorem noInv_tateDual : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), (∃ AI, Nonempty (LocTied (D.ntw.l i) (D.loc (D.ntw.l i)) AI)) → HodgeL bkP i s → NoJump bkP i s → ∀ v ∈ placesOver D.host.E (D.ntw.l i), NoInv i (Tdual i s) v := by
  rintro D bkP i s ⟨AI, ⟨T⟩⟩ hH hJ v hv A hA x hx
  let φ := algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))
  let M : Gen.GE D.nd → Matrix (Fin D.R.r) (Fin D.R.r) (FractionRing (D.ntw.O0 i)) := fun g => (Tdual i s g).map φ
  have hmul : ∀ g h, M (g * h) = M g * M h := fun g h => by
    simp only [M, ← Matrix.map_mul]
    exact congrArg (fun Y => Matrix.map Y φ) ((dualHom i s).map_mul g h)
  have hone : M 1 = 1 := by
    have : Tdual i s 1 = 1 := (dualHom i s).map_one
    simp only [M, this, Matrix.map_one _ φ.map_zero φ.map_one]
  obtain ⟨k, hk⟩ := exists_smul_eq_of_isPlaceOver (F := D.host.E) hA (D.nd.plOm.2 v)
  have hy : ∀ g ∈ DecV D.nd v, (M g).mulVec ((M k).mulVec x) = (M k).mulVec x := by
    intro g hg
    have h1 : k⁻¹ * g * k ∈ Dec (F := D.host.E) A := by
      have hg' : g • D.nd.plOm.1 v = D.nd.plOm.1 v := hg
      change (k⁻¹ * g * k) • A = A
      rw [mul_smul, mul_smul, hk, hg', ← hk, inv_smul_smul]
    have h2 : (M (k⁻¹ * g * k)).mulVec x = x := hx _ h1
    conv_rhs => rw [← h2]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hmul, ← hmul]
    congr 2
    group
  have : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  let Bw := bkP.br i v hv
  have hz := local_noInv Bw (D.loc (D.ntw.l i)) AI T ((Tgl i s).comp (DecV D.nd v).subtype)
    ((dualHom i s).toHomUnits.comp (DecV D.nd v).subtype)
    (fun g => by
      change Tdual i s g = _ • (((Tgl i s g : GL (Fin D.R.r) (D.ntw.O0 i)) :
        Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)))⁻¹.transpose
      rw [Tgl_coe]
      rfl)
    (hH v hv _ (Set.mem_insert_of_mem _ rfl)).1
    (fun τ h => by
      have := hJ v hv τ (-1) h
      omega)
    (fun a => Br.toLLK Bw ((M k).mulVec x a)) (fun g => by
      rw [rep_apply]
      funext a
      have h3 := congrArg (Br.toLLK Bw) (congrFun (hy _ (Bw.e.symm g).2) a)
      rw [← h3, RingHom.map_mulVec]
      congr 1
      ext b c
      exact congrArg Subtype.val (Br.toLLK_alg Bw _).symm)
  have h4 : (M k).mulVec x = 0 := funext fun a => (Br.toLLK Bw).injective (by
    rw [Pi.zero_apply, map_zero]; exact congrFun hz a)
  have h5 := congrArg (M k⁻¹).mulVec h4
  rwa [Matrix.mulVec_mulVec, ← hmul, inv_mul_cancel, hone, Matrix.one_mulVec, Matrix.mulVec_zero] at h5

end GlobalTheory.TateDualInv

end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.RSJ
open scoped ComplexConjugate

namespace GlobalTheory.ZEul


open Classical in
def rsTerm (q : ℕ) {n : ℕ} (α β : Fin n → ℂ) (x : ℝ) (v : Fin n → ℤ) : ℂ :=
  if (∀ i, 0 ≤ v i) ∧ Antitone v then
    schurAt (fun i => (v i).toNat) α * conj (schurAt (fun i => (v i).toNat) β) *
      ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, (v i).toNat)
  else 0

theorem rsTerm_zero (q : ℕ) {n : ℕ} (α β : Fin n → ℂ) (x : ℝ) : rsTerm q α β x 0 = 1 := by
  have h : (fun _ : Fin n => (0 : ℕ)) = fun i => ((0 : Fin n → ℤ) i).toNat := by funext i; simp
  have hs : schurAt (fun i => ((0 : Fin n → ℤ) i).toNat) α = 1 := by
    rw [← h, schurAt, schur_zero]; simp
  have hs' : schurAt (fun i => ((0 : Fin n → ℤ) i).toNat) β = 1 := by
    rw [← h, schurAt, schur_zero]; simp
  rw [rsTerm, if_pos ⟨fun i => le_rfl, antitone_const⟩, hs, hs']
  simp

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}

def lastRow (g : GA E (m + 1)) : Fin (m + 1) → Ad E := fun j => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j

def uInt (φ φ' : GA E (m + 1) → ℂ) (Φ : (Fin (m + 1) → Cinf E) → ℂ) (N : ℕ) (x : ℝ) (g : GA E (m + 1)) : ℂ :=
  whit φ (g * infGL E (m + 1) (secInv fun i => pInf E (lastRow g i))) *
    conj (whit φ' (g * infGL E (m + 1) (secInv fun i => pInf E (lastRow g i)))) *
    Φ (fun i => pInf E (lastRow g i)) * indN N (fun i => GlobalTheory.RSJ.pFin E (lastRow g i)) * (detPow E (m + 1) x g : ℂ)

end GlobalTheory.ZEul
end
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.rowBounds_of_all_letters_thick : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : WordDat (nLet i w hw)) (d : ℕ) (bd : Prop), RamifiedCoefficientChains.aux₃ D HW F 25 → LiftingTheory.aux₃ D HW F 10 23 32 32 → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → WordBase L HW i r ρ π w hw Cx hG Wd → WordBox L Wd → WordBaseC (HW := HW) ρ π hG Wd → @WordsAT (D.nd.l i) _ (nLet_neZero i w hw) Wd d → RowL i r ρ π w hw Cx (bdCD L bd (D.nd.l i) w (rowC C₂).K₁ (rowC C₂).K₂ (rowC C₂).K₃) := by
  first | exact @GlobalTheory.RowsThick.rowL_of_allThick | exact GlobalTheory.RowsThick.rowL_of_allThick | (intros; apply GlobalTheory.RowsThick.rowL_of_allThick <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.rowBounds_of_nonThick_letter : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : WordDat (nLet i w hw)), ArcLiftingSetup.aux₃ D HW F 320 → LiftingTheory.aux₃ D HW F 10 23 32 32 → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → π ∈ D.nd.Zgood i → WordBase L HW i r ρ π w hw Cx hG Wd → WordBox L Wd → WordsNT Wd → RowL i r ρ π w hw Cx (bdCD L (bandOf L HW 320 i r ρ w) (D.nd.l i) w (rowC C₂).K₁ (rowC C₂).K₂ (rowC C₂).K₃) := by
  first | exact @GlobalTheory.NLink.RowNT.main | exact GlobalTheory.NLink.RowNT.main | (intros; apply GlobalTheory.NLink.RowNT.main <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.localBlochKatoCondition_of_wachModules : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (M0 h0 cB : ℕ), LocalSituation.Conclusion4 D HW F → WAll D HW F → CrysOnCond D HW F → TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i → JointConditionTameBound D HW F i r π M0 h0 cB → TruncatedSeriesCountingIdentities.admTB i r π cB := by
  first | exact @GlobalTheory.TBLocal.main | exact GlobalTheory.TBLocal.main | (intros; apply GlobalTheory.TBLocal.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.AdjUp

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def upVec (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (y : (R.HW i (sg0 D A)).H) : GA D (Vc D i) → (R.cV i).W :=
  fun h => ∑ k, upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v y) h • b k

theorem val_zero (R : RealDat D A Ks) (i : Fin D.R.m) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    val R i v 0 = 0 := by
  funext g
  simp [val]

theorem upLift_zero {V W : HSp D} (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ν : Measure (GA D W))
    (𝓖 : Set (GA D W)) (f : WO V W → ℂ) (h : GA D V) : upLift om ν 𝓖 f 0 h = 0 := by
  simp [upLift]

end GlobalTheory.AdjUp

end

namespace GlobalTheory.AdjUp

theorem adjoint_formula_of_kernel {H₁ H₂ W Gv Gw : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [FiniteDimensional ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [FiniteDimensional ℂ H₂]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [MeasurableSpace Gv] [MeasurableSpace Gw]
    (th : H₁ →ₗ[ℂ] H₂) {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ W) (μW : Measure Gw) (μV : Measure Gv)
    (φ : H₂ → Gw → ℂ) (ψ : H₁ → Gw → ℂ) (ext : H₁ →ₗ[ℂ] (Gv → W)) (K : Fin n → H₂ → Gv → ℂ) (P c : ℝ)
    (hP0 : 0 ≤ P) (hc : 0 < c)
    (hPW : ∀ y z, ⟪y, z⟫_ℂ = (P : ℂ) * ∫ g, star (φ y g) * φ z g ∂μW)
    (hφ : ∀ u, φ (th u) = ψ u) (hφ0 : φ 0 = 0) (hK0 : ∀ k h, K k 0 h = 0)
    (hcV : ∀ u u', ⟪u, u'⟫_ℂ = (c : ℂ) * ∫ h, ⟪ext u h, ext u' h⟫_ℂ ∂μV ∧
      ∀ a a' : W, Integrable (fun h => star ⟪a, ext u h⟫_ℂ * ⟪a', ext u' h⟫_ℂ) μV)
    (h3 : ∀ y u, ∫ g, star (φ y g) * ψ u g ∂μW = ∫ h, ⟪∑ k, K k y h • b k, ext u h⟫_ℂ ∂μV)
    (h4 : ∀ y, ∃ u, ext u = fun h => ∑ k, K k y h • b k) :
    ∃ a : ℝ, 0 < a ∧ ∀ x y, ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ =
      (a : ℂ) * ∑ k, ∫ h, star (K k x h) * K k y h ∂μV := by
  choose U hU using h4
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hcoord : ∀ y k h, ⟪b k, ext (U y) h⟫_ℂ = K k y h := fun y k h => by
    rw [hU y]; exact b.orthonormal.inner_right_fintype _ k
  have hadj : ∀ y u, ⟪LinearMap.adjoint th y, u⟫_ℂ = (((P / c : ℝ)) : ℂ) * ⟪U y, u⟫_ℂ := by
    intro y u
    rw [LinearMap.adjoint_inner_left, hPW, hφ, h3, (hcV (U y) u).1, hU y, Complex.ofReal_div]
    field_simp
  have hsum : ∀ x y h, ⟪ext (U x) h, ext (U y) h⟫_ℂ = ∑ k, star (K k x h) * K k y h := by
    intro x y h
    rw [← b.sum_inner_mul_inner]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hcoord, ← hcoord, ← inner_conj_symm]
    rfl
  by_cases hzero : P = 0
  · refine ⟨1, one_pos, fun x y => ?_⟩
    have h0 : ∀ z : H₂, z = 0 := fun z => by
      have := hPW z z
      rw [hzero, Complex.ofReal_zero, zero_mul] at this
      exact inner_self_eq_zero.1 this
    rw [h0 x, h0 y, map_zero, inner_zero_left]
    simp [hK0]
  · have hpos : 0 < P := lt_of_le_of_ne hP0 (Ne.symm hzero)
    refine ⟨P ^ 2 / c, by positivity, fun x y => ?_⟩
    have hint : ∀ k ∈ Finset.univ, Integrable (fun h => star (K k x h) * K k y h) μV := by
      intro k _
      have := (hcV (U x) (U y)).2 (b k) (b k)
      simpa only [hcoord] using this
    have e1 : ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ =
        (((P / c : ℝ)) : ℂ) * (((P / c : ℝ)) : ℂ) * ⟪U x, U y⟫_ℂ := by
      rw [hadj x, ← inner_conj_symm, hadj y, map_mul, Complex.conj_ofReal, inner_conj_symm, mul_assoc]
    have e2 : ⟪U x, U y⟫_ℂ = (c : ℂ) * ∑ k, ∫ h, star (K k x h) * K k y h ∂μV := by
      rw [(hcV (U x) (U y)).1, ← integral_finsetSum _ hint]
      simp only [hsum]
    rw [e1, e2]
    push_cast
    field_simp

end GlobalTheory.AdjUp
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.harmonic_polynomial_eq_zero_of_function : ∀ (D : D7) (m n : ℕ) (w : Weight D n) (B : GLR D n), w.Good → (∀ τ, w.p τ + w.q τ ≤ m) → ∀ P ∈ harm m w B, harmFn m w B P = 0 → P = 0 := by
  first | exact @GlobalTheory.ExportSeries.HarmInj.harm_inj | exact GlobalTheory.ExportSeries.HarmInj.harm_inj | (intros; apply GlobalTheory.ExportSeries.HarmInj.harm_inj <;> assumption)
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

theorem _root_.GlobalTheory.T.exists_lattice_idempotent_position_involution_stable : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι) (a : K.O), B.P.Separable → K.Small a → IsFrame B e π S → ∃ N : ℕ, ∀ M ∈ B.Lin, ∃ p : ι → ℤ, Pos B a e N M p := by
  first | exact @GlobalTheory.UnitLemma.Desc.exists_pos | exact GlobalTheory.UnitLemma.Desc.exists_pos | (intros; apply GlobalTheory.UnitLemma.Desc.exists_pos <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Prism GlobalTheory.PrismS

theorem _root_.GlobalTheory.T.existsUnique_unramifiedIntegers_coords_basis : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (emb : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)), Function.Injective emb → ∀ (d : ℕ) (o : Module.Basis (Fin d) ℤ_[l] ↥(OL LL)) (y : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL)), ∃! c : Fin d → WK K, ∀ k, y k = ∑ i, o i * embW (emb k) (c i) := by
  first | exact @GlobalTheory.PrismSplit.existsUnique_coords | exact GlobalTheory.PrismSplit.existsUnique_coords | (intros; apply GlobalTheory.PrismSplit.existsUnique_coords <;> assumption)
end
