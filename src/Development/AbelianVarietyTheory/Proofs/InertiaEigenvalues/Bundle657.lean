module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineSubrepresentation
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinTensorAinfGaloisStableKummerFixed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle179
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle633
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle632
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle629
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle097
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle631

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

theorem GlobalTheory.BKGal.HatVal.Epow_smul_jB_toBcris_eq_sum : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (σ : D.MMl) (c : ι → ι → OA l O), (∀ j, inclL t ϖ D.toPhiMod (c j) = inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O)) → ∃ s : ι → ZMod a → invL l (S O K e), (∀ j τ, (s j τ : K⟦X⟧) = E K l e ^ η * σ.1 τ j) ∧ toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ (H + η) • R.jB (toBcris t ϖ D.toPhiMod σ) = ∑ j, ϖ.iB t K (s j) • R.jB (fun i => toB l O (c j i)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R σ c hc
  have hσM : E K l e ^ η • σ.1 ∈ D.Mext (invL l (S O K e)) :=
    D.smul_mem_Mext (le_trans (A_le_S l e) (le_away _ _)) σ.2
  refine ⟨fun j τ => ⟨E K l e ^ η * σ.1 τ j, mem_tot.1 hσM τ j⟩, fun j τ => rfl, ?_⟩
  set ej : ι → Vec K a ι := fun j _ => Pi.single j 1 with hej
  have hejM : ∀ j, ej j ∈ D.M := fun j => mem_tot.2 fun τ => mem_vecs.2 fun i => by
    simp only [hej]
    rcases eq_or_ne i j with rfl | h
    · rw [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  have hL : ∀ j, E K l e ^ H • ej j ∈ D.L := fun j => D.lower _ (hejM j)
  have hcol : ∀ j τ i, (D.mxInv τ *ᵥ (E K l e ^ H • ej j) τ) i = E K l e ^ H * D.mxInv τ i j := by
    intro j τ i
    simp only [hej, Pi.smul_apply, Matrix.mulVec_smul, Matrix.mulVec_single_one, smul_eq_mul,
      Matrix.col_apply, Matrix.transpose_apply]
  have hℓ : ∀ j i τ, E K l e ^ H * D.mxInv τ i j ∈ A O K := fun j i τ => by
    rw [← hcol]; exact D.mem_extc_iff.1 (mem_tot.1 (hL j) τ) i
  set ℓ : ι → ι → ZMod a → A O K := fun j i τ => ⟨_, hℓ j i τ⟩ with hℓdef
  have hcj : ∀ j, c j = fun i => ϖ.iTot t K (ℓ j i) := by
    intro j
    apply inclL_injective t ϖ D.toPhiMod
    rw [hc j]
    have hv : E K l e ^ H • ej j ∈ ME D.toPhiMod := mem_ME_of_mem_L (hL j)
    have h1 := toW_of_mx t ϖ D.toPhiMod ⟨_, hv⟩ (ℓ j) (fun τ => by
      have h2 : (fun i => ((ℓ j i τ : A O K) : K⟦X⟧)) = D.mxInv τ *ᵥ (E K l e ^ H • ej j) τ :=
        funext fun i => (hcol j τ i).symm
      change (E K l e ^ H • ej j) τ = D.mx τ *ᵥ fun i => ((ℓ j i τ : A O K) : K⟦X⟧)
      rw [h2, Matrix.mulVec_mulVec, D.mx_mul_mxInv, Matrix.one_mulVec])
    rw [← inclL_apply] at h1
    rw [← h1]
    ext1 i
    rw [toW_apply, Pi.smul_apply, smul_eq_mul]
    rcases eq_or_ne i j with rfl | h
    · have h3 : (fun τ => (⟨(E K l e ^ H • ej i) τ i, mem_tot.1 hv τ i⟩ : invE l e (A O K))) =
          fun τ => ⟨(((fun _ => EIn l e (A O K)) ^ H : ZMod a → A O K) τ : K⟦X⟧),
            le_away _ _ (((fun _ => EIn l e (A O K)) ^ H : ZMod a → A O K) τ).2⟩ :=
        funext fun τ => Subtype.ext (by simp [hej, EIn])
      rw [h3, ϖ.iW_of_mem t K]
      simp only [map_pow, ϖ.iTot_E t K, Pi.single_eq_same, mul_one]
    · have h3 : (fun τ => (⟨(E K l e ^ H • ej j) τ i, mem_tot.1 hv τ i⟩ : invE l e (A O K))) = 0 :=
        funext fun τ => Subtype.ext (by simp [hej, Pi.single_eq_of_ne h])
      rw [h3, map_zero, Pi.single_eq_of_ne h, mul_zero]
  have hB : ∀ f : ZMod a → A O K, toB l O (ϖ.iTot t K f) =
      ϖ.iB t K (fun τ => ⟨f τ, le_away _ _ (A_le_S l e (f τ).2)⟩) := fun f => by
    rw [toB, AlgHom.comp_apply, ← ϖ.iC_of_mem t K, ← ϖ.iB_of_mem t K]
  have hE : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) =
      toB l O (ϖ.iTot t K (fun _ => EIn l e _)) := by rw [ϖ.iTot_E t K]
  rw [← LinearEquiv.map_smul]

  simp only [← LinearEquiv.map_smul, ← map_sum]
  congr 1
  ext i
  simp only [Pi.smul_apply, Finset.sum_apply, hcj, hB, toBcris_apply, hE, smul_eq_mul,
    ← map_pow, ← map_mul, ← map_sum]
  congr 1
  funext τ
  apply Subtype.ext
  simp only [Pi.mul_apply, Pi.pow_apply, Finset.sum_apply, Subalgebra.coe_mul, Subalgebra.coe_pow,
    AddSubmonoidClass.coe_finsetSum, hℓdef]
  change (E K l e) ^ (H + η) * (D.mxInv τ *ᵥ σ.1 τ) i = ∑ j, E K l e ^ η * σ.1 τ j * (E K l e ^ H * D.mxInv τ i j)
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation GlobalTheory.RegularRing

theorem _root_.GlobalTheory.T.isCrys_of_crystallinePeriods_le_span : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), IsStd P AI → ∀ (LL : FinExt l) (T : QLat LL) (F K'' : FinExt l), IsCrys (P.PD K'') (T.ρ.comp (inclG K'')) → (∀ m ∈ DcrisK₀ (P.PD K'') (T.ρ.comp (inclG K'')), m ∈ Submodule.span ↥(MaximalUnramifiedExtension l) (↑(DcrisK₀ (P.PD F) (T.ρ.comp (inclG F))) : Set (P.R.B ⊗[ℚ_[l]] T.V))) → IsCrys (P.PD F) (T.ρ.comp (inclG F)) := by
  first | exact @GlobalTheory.BKGal.isCrys_of_dcris_le_span | exact GlobalTheory.BKGal.isCrys_of_dcris_le_span | (intros; apply GlobalTheory.BKGal.isCrys_of_dcris_le_span <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.BKGal GlobalTheory.Per

theorem _root_.GlobalTheory.T.exists_frob_inv_mul_mem_inertia : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (Fr : Gl l), (pc Pl h hN hF hS).IsFrob Fr → ∃ Φ : Gl l, (∀ x : Om l, x ∈ MaximalUnramifiedExtension l → ‖x‖ ≤ 1 → ‖(Φ : GQ l) x - x ^ l‖ < 1) ∧ Φ⁻¹ * Fr ∈ (pc Pl h hN hF hS).Iner := by
  first | exact @GlobalTheory.FrobLiftUnr.exists_frob_inv_mul_mem_iner | exact GlobalTheory.FrobLiftUnr.exists_frob_inv_mul_mem_iner | (intros; apply GlobalTheory.FrobLiftUnr.exists_frob_inv_mul_mem_iner <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.breuilKisin_tensorAinf_galoisStable_kummerFixed : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → Ident.Stable (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) ∧ ∀ g : Gl l, sQ l g ∈ ϖ.GfieldInf a → ∀ v : ME P, I.act (sQ l g) g (toW (thetaW a LL) ϖ P v) = toW (thetaW a LL) ϖ P v := by
  first | exact @GlobalTheory.BKGal.StableFix.main | exact GlobalTheory.BKGal.StableFix.main | (intros; apply GlobalTheory.BKGal.StableFix.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

theorem _root_.GlobalTheory.T.hodgeJumps_mem_latticeCoefficientExtension : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T : LocLat (Gl l) ℚ_[l] ↥LL.1 ↥(OL LL)) (k : ℕ) (b : Module.Basis (Fin k) ↥LL.1 T.V) (hb : IsLatBasis T b) (U : Set ℤ), (∀ τ, JumpsInV (pc Pl h hN hF hS).PD T.ρ τ U) → ∀ τ, JumpsInV (pc Pl h hN hF hS).PD (extLat hL T b hb).ρ τ U := by
  first | exact @GlobalTheory.BaseCoef.jumpsInV_extLat | exact GlobalTheory.BaseCoef.jumpsInV_extLat | (intros; apply GlobalTheory.BaseCoef.jumpsInV_extLat <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

theorem _root_.GlobalTheory.T.isPotentiallyCrystalline_latticeCoefficientExtension : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T : LocLat (Gl l) ℚ_[l] ↥LL.1 ↥(OL LL)) (k : ℕ) (b : Module.Basis (Fin k) ↥LL.1 T.V) (hb : IsLatBasis T b), (pc Pl h hN hF hS).IsPotCrys T.ρ → (pc Pl h hN hF hS).IsPotCrys (extLat hL T b hb).ρ := by
  first | exact @GlobalTheory.BaseCoef.isPotCrys_extLat | exact GlobalTheory.BaseCoef.isPotCrys_extLat | (intros; apply GlobalTheory.BaseCoef.isPotCrys_extLat <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

theorem _root_.GlobalTheory.T.inertiaThroughCharacters_latticeCoefficientExtension : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T : LocLat (Gl l) ℚ_[l] ↥LL.1 ↥(OL LL)) (k : ℕ) (b : Module.Basis (Fin k) ↥LL.1 T.V) (hb : IsLatBasis T b) (Sig : Finset ((pc Pl h hN hF hS).Iner →* (↥LL.1)ˣ)), (pc Pl h hN hF hS).InertiaThrough T.ρ Sig → (pc Pl h hN hF hS).InertiaThrough (extLat hL T b hb).ρ (mapSig (incl hL).toRingHom Sig) := by
  first | exact @GlobalTheory.BaseCoefIner.main | exact GlobalTheory.BaseCoefIner.main | (intros; apply GlobalTheory.BaseCoefIner.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.CoverRing

variable {l : ℕ} [hl : Fact l.Prime]

theorem smul_eq_zero_ainf {c : ℤ_[l]} (hc : c ≠ 0) {z : Ainf l} (h : c • z = 0) : z = 0 := by
  have h1 := PadicInt.unitCoeff_spec hc
  rw [h1, Algebra.smul_def, map_mul, map_pow, map_natCast, mul_assoc] at h
  have h2 : (l : Ainf l) ^ c.valuation * z = 0 :=
    ((PadicInt.unitCoeff hc).isUnit.map (algebraMap ℤ_[l] (Ainf l))).mul_right_eq_zero.1 h
  have key : ∀ n : ℕ, ∀ z : Ainf l, (l : Ainf l) ^ n * z = 0 → z = 0 := by
    intro n
    induction n with
    | zero => intro z h; simpa using h
    | succ n ih => intro z h; exact ih z (ainf_torsionFree _ (by rw [← mul_assoc, ← pow_succ']; exact h))
  exact key _ z h2

theorem one_tmul_inj {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Nontrivial O]
    {x y : Ainf l} (h : (1 : O) ⊗ₜ[ℤ_[l]] x = (1 : O) ⊗ₜ[ℤ_[l]] y) : x = y := by
  set b := Module.Free.chooseBasis ℤ_[l] O
  obtain ⟨i, hi⟩ : ∃ i, b.repr 1 i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact one_ne_zero (b.repr.injective (by ext i; simp [hc i]))
  have h1 := congrArg (fun w => TensorProduct.lid ℤ_[l] (Ainf l) ((b.coord i).rTensor (Ainf l) w)) h
  simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Module.Basis.coord_apply] at h1
  rw [← sub_eq_zero, ← smul_sub] at h1
  exact sub_eq_zero.1 (smul_eq_zero_ainf hi h1)

variable {a : ℕ} [NeZero a]

theorem exists_root {e : ℕ} [NeZero e] (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a]
    (γ : TameGal ↥LL.1 l e a) :
    ∃ c : Wq l a, ∀ τ, algebraMap ↥(OL LL) ↥LL.1 (emb (thetaW a LL) τ c) = γ.root τ := by
  obtain ⟨z, ω, hω, hz, -⟩ := exists_gen l a
  have he : e = l ^ a - 1 := by
    have := TameDescentExponentData.succ_eq (K := ↥LL.1) (l := l) (e := e) (a := a); omega
  set w : ↥LL.1 := ((thetaW a LL (WittVector.teichmuller l z) : ↥(OL LL)) : ↥LL.1) with hwdef
  have hw : (w : Om l) = ω := by
    refine (algebraMap (Om l) ℂ_[l]).injective ?_
    have h1 := congrArg (fun y : OC l => (y : ℂ_[l])) (intToOC_thetaW a LL (WittVector.teichmuller l z))
    simp only [coe_intToOC, wA_teich, WittVector.fontaineTheta_teichmuller] at h1
    exact h1.trans (GlobalTheory.MemLoc.IsTiltOf.untilt_eq hz)
  have hwp : IsPrimitiveRoot w e := by
    rw [he]
    refine IsPrimitiveRoot.of_map_of_injective (f := (LL.1).val) ?_ Subtype.val_injective
    simpa [hw] using hω
  have hpow : (((γ.left : (↥LL.1)ˣ) : ↥LL.1)) ^ e = 1 := (mem_rootsOfUnity' _ _).1 γ.left.2
  obtain ⟨k, -, hk⟩ := hwp.eq_pow_of_pow_eq_one hpow
  refine ⟨WittVector.teichmuller l z ^ k, fun τ => ?_⟩
  change ((thetaW a LL ((sigma l a ^ (-τ).val) (WittVector.teichmuller l z ^ k)) : ↥(OL LL)) : ↥LL.1) = _
  rw [map_pow, sigma_pow_teich, map_pow, map_pow, SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, ← hwdef,
    TameGal.root, powL_apply]
  simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, ← hk]
  ring

end GlobalTheory.BKGal.CoverRing


open GlobalTheory.BKGal.CoverRing GlobalTheory.BKGal.CoverBridge in
theorem GlobalTheory.BKGal.covers_ringEndo : ∀ {l : ℕ} [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e)
    (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (g : GQ l) (γ : TameGal ↥LL.1 l e a),
    Covers ↥LL.1 (thetaW a LL) ϖ g γ →
      ∃ ψ : (Wq l a)⟦X⟧ →+* (Wq l a)⟦X⟧, ∀ x, ϖ.ev a (ψ x) = Per.σA g (ϖ.ev a x) := by
  intro l _ a e _ _ ϖ LL _ _ g γ hcov
  obtain ⟨c, hc⟩ := exists_root LL γ
  refine ⟨(rescale c).comp (PowerSeries.map ((sigma l a ^ γ.shift.val : Wq l a ≃ₐ[ℤ_[l]] Wq l a) :
    Wq l a →+* Wq l a)), fun x => ?_⟩
  have h := hcov (toAc (thetaW a LL) ↥LL.1 x)
    (toAc (thetaW a LL) ↥LL.1 (rescale c (PowerSeries.map ((sigma l a ^ γ.shift.val : Wq l a ≃ₐ[ℤ_[l]] Wq l a) :
      Wq l a →+* Wq l a) x))) (fun τ => toAc_rescale (thetaW a LL) γ c hc x τ)
  rw [PiSys.iTot_toAc, PiSys.iTot_toAc, galOA_tmul] at h
  exact (one_tmul_inj h).symm
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.bcrisTensorLattice_filZero_galois_stable :
    ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O]
      [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
      [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
      (T : LocLat (GlobalTheory.BKGal.Gl l) ℚ_[l] K O) (g : GlobalTheory.BKGal.Gl l)
      (C : GlobalTheory.MemLoc.Core l),
      ∀ v ∈ Submodule.span O {w : TW (GlobalTheory.BKReal.OB l O) T |
        ∃ (β : Per.Bcris l) (x : ↥T.L.T),
          C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x},
        GlobalTheory.BKGal.actB (GlobalTheory.BKGal.sQ l) T g v ∈
          Submodule.span O {w : TW (GlobalTheory.BKReal.OB l O) T |
            ∃ (β : Per.Bcris l) (x : ↥T.L.T),
              C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  exact @GlobalTheory.BKGal.FilStable.fil_zero_stable
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.action_of_covers : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (k : GQ l) (γ : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ k γ → (∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ γ.shift.val) ∧ k (ϖ.seq 0) = (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0 := by
  first | exact @GlobalTheory.BKGal.covers_action | exact GlobalTheory.BKGal.covers_action | (intros; apply GlobalTheory.BKGal.covers_action <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.covers_of_action' : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (γ : TameGal ↥LL.1 l e a), ∀ k ∈ ϖ.GKinf, (∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ γ.shift.val) → k (ϖ.seq 0) = (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0 → Covers ↥LL.1 (thetaW a LL) ϖ k γ := by
  first | exact @GlobalTheory.BKGal.covers_of_action | exact GlobalTheory.BKGal.covers_of_action | (intros; apply GlobalTheory.BKGal.covers_of_action <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.mem_kummerTowerUnramified_of_covers_one : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (k : GQ l), Covers ↥LL.1 (thetaW a LL) ϖ k (1 : TameGal ↥LL.1 l e a) → k ∈ ϖ.GfieldInf a := by
  first | exact @GlobalTheory.CoverOne.main | exact GlobalTheory.CoverOne.main | (intros; apply GlobalTheory.CoverOne.main <;> assumption)
end
