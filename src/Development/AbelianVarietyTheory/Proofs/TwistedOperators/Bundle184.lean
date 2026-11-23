module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle167
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainParIffStepGap
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.coeff_e0_eq_eGood_mul_eGood : ∀ (D : D7) (τ : ∀ k : Fin 2, (ZMod (D.host.g k))[X] → GlobalTheory.BadShare.GG (D.host.g k) D.R.r → ℂ), (∀ k, ∀ f ∈ GlobalTheory.BadShare.sqSet (D.host.g k) D.R.r, ∀ x, (D.ntypes.eSer k f).coeff x = GlobalTheory.BadShare.zc (τ k f) x) → ∀ γ : G0g D.nd, D.ntypes.e0.coeff γ = GlobalTheory.BadShare.eGood (fun _ => τ 0) (D.nd.chiT 0) (fun v => γ ⟨0, v⟩) * GlobalTheory.BadShare.eGood (fun _ => τ 1) (D.nd.chiT 1) (fun v => γ ⟨1, v⟩) := by
  first | exact @GlobalTheory.GoodProjProd.goodProjector_coeff_eq_prod_at_two_typePrimes | exact GlobalTheory.GoodProjProd.goodProjector_coeff_eq_prod_at_two_typePrimes | (intros; apply GlobalTheory.GoodProjProd.goodProjector_coeff_eq_prod_at_two_typePrimes <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.range_levelIdempotentProduct_and_centralProduct : ∀ (g₁ g₂ N : ℕ) [Fact g₁.Prime] [Fact g₂.Prime] (ι₁ ι₂ G M : Type) [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] [Group G] [Fintype G] [AddCommGroup M] [Module ℂ M] (Φ : G ≃* (ι₁ → GlobalTheory.BadShare.GG g₁ N) × (ι₂ → GlobalTheory.BadShare.GG g₂ N)) (L₁ : ι₁ → GlobalTheory.BadShare.Lev g₁ N) (L₂ : ι₂ → GlobalTheory.BadShare.Lev g₂ N) (P : Subgroup G) (χ : P → ℂ) (ρ : Representation ℂ G M) [Fintype ((ι₁ → GlobalTheory.BadShare.GG g₁ N) × (ι₂ → GlobalTheory.BadShare.GG g₂ N))] (c : (ι₁ → GlobalTheory.BadShare.GG g₁ N) × (ι₂ → GlobalTheory.BadShare.GG g₂ N) → ℂ), (∀ g : G, g ∈ P ↔ (∀ v, (L₁ v).Mem ((Φ g).1 v)) ∧ ∀ v, (L₂ v).Mem ((Φ g).2 v)) → (∀ g : P, χ g = (∏ v, (L₁ v).chi ((Φ g).1 v)) * ∏ v, (L₂ v).chi ((Φ g).2 v)) → GlobalTheory.BadShare.conv c c = c → (∀ a, GlobalTheory.BadShare.conv c a = GlobalTheory.BadShare.conv a c) → LinearMap.range (GlobalTheory.BadShare.op (M := M) (ρ.comp Φ.symm.toMonoidHom) (GlobalTheory.BadShare.tens2 (GlobalTheory.BadShare.tens fun v => (L₁ v).e) (GlobalTheory.BadShare.tens fun v => (L₂ v).e))) = eig ρ P χ ∧ LinearMap.range (GlobalTheory.BadShare.op (M := M) (ρ.comp Φ.symm.toMonoidHom) (GlobalTheory.BadShare.conv c (GlobalTheory.BadShare.tens2 (GlobalTheory.BadShare.tens fun v => (L₁ v).e) (GlobalTheory.BadShare.tens fun v => (L₂ v).e)))) = eig ρ P χ ⊓ LinearMap.ker ((∑ g : G, c (Φ g) • ρ g) - LinearMap.id) := by
  first | exact @GlobalTheory.LevRange.ranges | exact GlobalTheory.LevRange.ranges | (intros; apply GlobalTheory.LevRange.ranges <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.UnitaryIdemCut

section Gen

open Matrix Formalism.UG

variable {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]

def cutM (b : A) (hb : b * b = b) : Matrix n n A →* Matrix n n A where
  toFun M := b • M + (1 - b) • 1
  map_one' := by rw [← add_smul]; simp
  map_mul' M N := by
    have h1 : b * (1 - b) = 0 := by linear_combination -hb
    have h2 : (1 - b) * b = 0 := by linear_combination -hb
    have h3 : (1 - b) * (1 - b) = 1 - b := by linear_combination hb
    simp only [add_mul, mul_add, smul_mul_smul_comm, hb, h1, h2, h3, zero_smul, add_zero, zero_add, mul_one]

def cutGL (b : A) (hb : b * b = b) : GL n A →* GL n A := Units.map (cutM b hb)

theorem cutGL_val (b : A) (hb : b * b = b) (g : GL n A) :
    (cutGL b hb g).val = b • g.val + (1 - b) • 1 := rfl

theorem map_cut (φ : A →+* B) (b : A) (M : Matrix n n A) :
    (b • M + (1 - b) • (1 : Matrix n n A)).map φ = φ b • M.map φ + (1 - φ b) • (1 : Matrix n n B) := by
  ext i j
  by_cases h : i = j <;> simp [h]

theorem bc_cutGL (φ : A →+* B) (b : A) (hb : b * b = b) (b' : B) (hb' : b' * b' = b') (e : φ b = b')
    (g : GL n A) : bc φ (cutGL b hb g) = cutGL b' hb' (bc φ g) := by
  subst e
  exact Units.ext (map_cut φ b g.val)

theorem bc_cutGL_eq_one (φ : A →+* B) (b : A) (hb : b * b = b) {g : GL n A} (hg : bc φ g = 1) :
    bc φ (cutGL b hb g) = 1 := by
  rw [bc_cutGL φ b hb _ (by rw [← map_mul, hb]) rfl, hg, map_one]

theorem cutGL_conj (b : A) (hb : b * b = b) (β g : GL n A) :
    cutGL b hb (β * g * β⁻¹) = β * cutGL b hb g * β⁻¹ := by
  apply Units.ext
  simp only [cutGL_val, Units.val_mul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, Units.mul_inv]

theorem cutGL_mem_UJ (σ : A →+* A) (J : Matrix n n A) (b : A) (hb : b * b = b) (hσ : σ b = b) {g : GL n A}
    (hg : g ∈ UJ σ J) : cutGL b hb g ∈ UJ σ J := by
  have hg' : cT σ g.val * J * g.val = J := hg
  show cT σ (b • g.val + (1 - b) • 1) * J * (b • g.val + (1 - b) • 1) = J
  have e : cT σ (b • g.val + (1 - b) • (1 : Matrix n n A)) = b • cT σ g.val + (1 - b) • 1 := by
    unfold cT
    rw [map_cut, hσ, transpose_add, transpose_smul, transpose_smul, transpose_one]
  have h1 : b * (1 - b) = 0 := by linear_combination -hb
  have h2 : (1 - b) * b = 0 := by linear_combination -hb
  have h3 : (1 - b) * (1 - b) = 1 - b := by linear_combination hb
  rw [e]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, hb, h1, h2, h3, zero_smul, add_zero,
    zero_add, mul_one, one_mul, hg']
  rw [← add_smul]; simp

def cutUJ (σ : A →+* A) (J : Matrix n n A) (b : A) (hb : b * b = b) (hσ : σ b = b) : UJ σ J →* UJ σ J :=
  ((cutGL b hb).comp (UJ σ J).subtype).codRestrict _ fun g => cutGL_mem_UJ σ J b hb hσ g.2

end Gen

section Ad

open NumberField IsDedekindDomain Formalism.UG Formalism.L2.DIV
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem idem_mem_intAd (a : FiniteAdeleRing (𝓞 F) F) (ha : a * a = a) : a ∈ intAd F := by
  intro v
  have h : a v * a v = a v := congrArg (fun x : FiniteAdeleRing (𝓞 F) F => x v) ha
  rcases eq_or_ne (a v) 0 with h0 | h0
  · rw [h0]; exact zero_mem _
  · rw [mul_left_cancel₀ h0 (h.trans (mul_one _).symm)]; exact one_mem _

theorem cutGL_mem_St (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (b : E ⊗[F] Formalism.L2.Herm.Af F) (hb : b * b = b)
    (hi : b ∈ Formalism.L2.Herm.intAf F E) {g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hg : g ∈ St β) :
    cutGL b hb g ∈ St β := by
  obtain ⟨y, rfl⟩ := hg
  refine ⟨cutGL (⟨b, hi⟩ : Formalism.L2.Herm.intAf F E) (Subtype.ext hb) y, ?_⟩
  show β * intGL F E n _ * β⁻¹ = cutGL b hb (β * intGL F E n y * β⁻¹)
  rw [cutGL_conj]
  unfold intGL
  rw [bc_cutGL _ _ _ b hb rfl]

theorem bc_cutGL_mem_St {A : Type} [CommRing A] (φ : A →+* E ⊗[F] Formalism.L2.Herm.Af F)
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (b : A) (hb : b * b = b)
    (hi : φ b ∈ Formalism.L2.Herm.intAf F E) {g : GL (Fin n) A} (hg : bc φ g ∈ St β) :
    bc φ (cutGL b hb g) ∈ St β := by
  have hb' : φ b * φ b = φ b := by rw [← map_mul, hb]
  rw [bc_cutGL φ b hb _ hb' rfl]
  exact cutGL_mem_St β _ hb' hi hg

end Ad

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sigR_algebraMap {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (r : R) : sigR R σ (algebraMap R (R ⊗[F] E) r) = algebraMap R (R ⊗[F] E) r := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem exists_cutHA {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (r : R)
    (hb : algebraMap R (R ⊗[F] E) r * algebraMap R (R ⊗[F] E) r = algebraMap R (R ⊗[F] E) r) :
    ∃ κ : HA R σ J →* HA R σ J, ∀ g, HA.mat R σ J (κ g) = cutGL _ hb (HA.mat R σ J g) :=
  ⟨cutUJ (sigR R σ) (JR R J) _ hb (sigR_algebraMap R σ r), fun _ => rfl⟩

theorem mem_GfC_iff {D : D7} (V : HSp D) (g : GA D V) :
    g ∈ GfC V ↔ Formalism.UG.bc (infPart D) (matHom V g) = 1 := Iff.rfl

theorem finE_eq {D : D7} (V : HSp D) (g : GA D V) : finE V g = Formalism.UG.bc (toEAf D) (matHom V g) :=
  Units.ext (finE_val V g)

theorem exists_cut : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (ε : AF D.host.F), ε * ε = ε → ∃ κ : GA D V →* GA D V, ∀ g, Formalism.L2.Theta.mt V (κ g) = algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.mt V g + (1 - algebraMap (AF D.host.F) (AE D) ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) ∧ (Stab V β g → Stab V β (κ g)) := by
  intro D V β ε hε
  have hb : algebraMap (AF D.host.F) (AE D) ε * algebraMap (AF D.host.F) (AE D) ε = algebraMap (AF D.host.F) (AE D) ε := by
    rw [← map_mul, hε]
  obtain ⟨κ, hκ⟩ := exists_cutHA (AF D.host.F) D.sp.cm.sig V.gram ε hb
  have hκ' : ∀ g, matHom V (κ g) = cutGL _ hb (matHom V g) := hκ
  refine ⟨κ, fun g => ⟨congrArg Units.val (hκ' g), fun h => ⟨?_, ?_⟩⟩⟩
  · have h1 := (mem_GfC_iff V g).1 h.1
    rw [mem_GfC_iff, hκ']
    exact bc_cutGL_eq_one (infPart D) _ hb h1
  · have h1 := h.2
    rw [finE_eq] at h1
    have hi : toEAf D (algebraMap (AF D.host.F) (AE D) ε) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      Subring.subset_closure (Or.inr ⟨⟨sndA D.host.F ε, idem_mem_intAd _ (by rw [← map_mul, hε])⟩, rfl⟩)
    rw [finE_eq, hκ']
    exact bc_cutGL_mem_St (toEAf D) β _ hb hi h1

end GlobalTheory.UnitaryIdemCut

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR.Links Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.WeilSignShift (NcGapGt NcGapGe minSig lamS lamT StepGap)
open GlobalTheory.Chain.ItPairCompare

namespace GlobalTheory.Chain.ParOfSizes

section HC

variable {R : Ranks} (P : HCParam R) {h₀ : ℝ}

theorem b_le_of_le {i j : Fin R.m} (h : i.1 ≤ j.1) : P.b i ≤ P.b j := by
  rcases h.lt_or_eq with hlt | heq
  ·
    have h1 := gap_of_lt P hlt
    have h2 := gap_of_le P (le_refl i.1)
    have ht : (0 : ℚ) ≤ R.t := Nat.cast_nonneg _
    linarith
  · exact le_of_eq (congrArg P.b (Fin.ext heq))

theorem le_b_sub (hg : ∀ (i : ℕ) (h : i + 1 < R.m), h₀ ≤ ((P.b ⟨i + 1, h⟩ - P.b ⟨i, by omega⟩ : ℚ) : ℝ))
    {i j : Fin R.m} (h : i.1 < j.1) : h₀ ≤ ((P.b j - P.b i : ℚ) : ℝ) := by
  have hi : i.1 + 1 < R.m := by omega

  have hstep := hg i.1 hi
  have hmono : P.b ⟨i.1 + 1, hi⟩ ≤ P.b j := b_le_of_le P (show i.1 + 1 ≤ j.1 by omega)
  have hq : (P.b ⟨i.1 + 1, hi⟩ - P.b ⟨i.1, by omega⟩ : ℚ) ≤ P.b j - P.b i := by
    have e : (⟨i.1, by omega⟩ : Fin R.m) = i := Fin.ext rfl
    rw [e]
    linarith
  exact hstep.trans (by exact_mod_cast hq)

theorem hermitianParam_oppositeSign_entries_dist_ge_gap (hg : ∀ (i : ℕ) (h : i + 1 < R.m), h₀ ≤ ((P.b ⟨i + 1, h⟩ - P.b ⟨i, by omega⟩ : ℚ) : ℝ))
    (j : ℕ) (x y : Idx R j) (hx : sgn R j x = false) (hy : sgn R j y = true) :
    h₀ ≤ |((val P j x - val P j y : ℚ) : ℝ)| := by
  rw [← Rat.cast_abs]
  rcases x with a | i | a
  · simp [sgn] at hx
  · simp only [sgn, decide_eq_false_iff_not, not_or, not_le] at hx
    obtain ⟨hij, hodd⟩ := hx
    have hi1 : i.1 - 1 < R.m := by omega
    rcases y with c | i2 | ⟨⟨i2, hi2⟩, a⟩
    ·
      have h1 := neg_b_lt_v P c ⟨i.1 - 1, hi1⟩
      have h2 := le_b_sub P hg (i := ⟨i.1 - 1, hi1⟩) (j := i) (show i.1 - 1 < i.1 by omega)
      refine h2.trans (Rat.cast_le.mpr ?_)
      simp only [val]
      rw [abs_sub_comm]
      exact le_abs.mpr (Or.inl (by linarith))
    · simp only [sgn, decide_eq_true_eq] at hy
      rcases lt_trichotomy i2.1 i.1 with h2 | h2 | h2
      · refine (le_b_sub P hg h2).trans (Rat.cast_le.mpr ?_)
        simp only [val]
        rw [abs_sub_comm]
        exact le_abs.mpr (Or.inl (by linarith))
      · exfalso
        rw [h2] at hy
        rcases hy with hy | hy
        · omega
        · exact hodd hy
      · refine (le_b_sub P hg h2).trans (Rat.cast_le.mpr ?_)
        simp only [val]
        exact le_abs.mpr (Or.inl (by linarith))
    ·
      have hi3 : i2.1 + 1 < R.m := by omega
      have g1 := gap_of_lt P (i := i2) (j := ⟨i2.1 + 1, hi3⟩) (show i2.1 < i2.1 + 1 by omega)
      have g2 := le_b_sub P hg (i := ⟨i2.1 + 1, hi3⟩) (j := i) (show i2.1 + 1 < i.1 by omega)
      have ha0 : (0 : ℚ) ≤ (a.1 : ℚ) := Nat.cast_nonneg _
      have ha1 : (a.1 : ℚ) + 1 ≤ R.t := by exact_mod_cast a.2
      refine g2.trans (Rat.cast_le.mpr ?_)
      simp only [val]
      rw [abs_sub_comm]
      exact le_abs.mpr (Or.inl (by linarith))
  · simp [sgn] at hx

theorem le_val_sub (hg : ∀ (i : ℕ) (h : i + 1 < R.m), h₀ ≤ ((P.b ⟨i + 1, h⟩ - P.b ⟨i, by omega⟩ : ℚ) : ℝ))
    (j : ℕ) (c : ℚ) (x y : Idx R j) (h : sgn R j x ≠ sgn R j y) :
    h₀ ≤ |(((val P j x + c) - (val P j y + c) : ℚ) : ℝ)| := by
  rw [add_sub_add_right_eq_sub]
  by_cases hx : sgn R j x = false
  · have hy : sgn R j y = true := by
      cases hy' : sgn R j y
      · exact absurd (hx.trans hy'.symm) h
      · rfl
    exact hermitianParam_oppositeSign_entries_dist_ge_gap P hg j x y hx hy
  · have hx' : sgn R j x = true := by simpa using hx
    have hy : sgn R j y = false := by
      cases hy' : sgn R j y
      · rfl
      · exact absurd (hx'.trans hy'.symm) h
    rw [← neg_sub, Rat.cast_neg, abs_neg]
    exact hermitianParam_oppositeSign_entries_dist_ge_gap P hg j y x hy hx'

end HC

end GlobalTheory.Chain.ParOfSizes

end
end

section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta.MixStab

variable {L : Type} [Field L]

theorem sum_hi {M : Type} [AddCommMonoid M] (N : ℕ) (f : Fin N → M)
    (hf : ∀ i : Fin N, i.1 < N - N / 2 → f i = 0) : ∑ i, f i = ∑ k, f (hi N k) := by
  rw [← Finset.sum_image (s := Finset.univ) (g := hi N) (f := f)]
  · symm
    refine Finset.sum_subset (Finset.subset_univ _) fun i _ hni => hf i ?_
    by_contra hc
    have := i.isLt
    exact hni (Finset.mem_image.2 ⟨⟨i.1 - (N - N / 2), by omega⟩, Finset.mem_univ _, Fin.ext (by simp only [hi]; omega)⟩)
  · intro x _ y _ hxy
    have := congrArg Fin.val hxy
    simp only [hi] at this
    exact Fin.ext (by omega)

theorem embLow_hi {n' n : ℕ} (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (k : Fin (n' / 2)) (l : Fin (n / 2)) :
    embLow n' n z (hi n' k) (hi n l) = z k l := by
  rw [embLow, dite_eq_left ⟨by simp [hi], by simp [hi]⟩]
  congr 1 <;> ext <;> simp [hi]

theorem embLow_eq_zero {n' n : ℕ} (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (r : Fin n') (c : Fin n)
    (h : r.1 < n' - n' / 2 ∨ c.1 < n - n / 2) : embLow n' n z r c = 0 := by
  rw [embLow, dite_eq_right (by omega)]

theorem mul_embLow_mul_apply {n' n : ℕ} (A : Matrix (Fin n') (Fin n') L) (B : Matrix (Fin n) (Fin n) L)
    (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (r : Fin n') (c : Fin n) :
    (A * embLow n' n z * B) r c = ∑ l, (∑ k, A r (hi n' k) * z k l) * B (hi n l) c := by
  rw [Matrix.mul_apply, sum_hi n]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_apply, sum_hi n']
    · simp only [embLow_hi]
    · intro i hi'
      rw [embLow_eq_zero z i _ (Or.inl hi'), mul_zero]
  · intro j hj
    rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro i _
    rw [embLow_eq_zero z i j (Or.inr hj), mul_zero]

theorem lowBlock_mul_apply {n' n : ℕ} (A : Matrix (Fin n') (Fin n') L) (B : Matrix (Fin n) (Fin n) L)
    (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (r : Fin (n' / 2)) (c : Fin (n / 2)) :
    (lowBlock A * z * lowBlock B) r c = ∑ l, (∑ k, A (hi n' r) (hi n' k) * z k l) * B (hi n l) (hi n c) := by
  simp only [Matrix.mul_apply, lowBlock, Matrix.submatrix_apply]

theorem exists_hi {N : ℕ} (r : Fin N) (hr : N - N / 2 ≤ r.1) : ∃ k, r = hi N k :=
  ⟨⟨r.1 - (N - N / 2), by have := r.isLt; omega⟩, Fin.ext (by simp only [hi]; omega)⟩

theorem mul_embLow_mul_eq {n' n : ℕ} (A : Matrix (Fin n') (Fin n') L) (B : Matrix (Fin n) (Fin n) L)
    (hB : ∀ i j : Fin n, j < i → B i j = 0) (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (r : Fin n') (c : Fin n)
    (h : n' - n' / 2 ≤ r.1 ∨ c.1 < n - n / 2) :
    (A * embLow n' n z * B) r c = embLow n' n (lowBlock A * z * lowBlock B) r c := by
  by_cases hc : c.1 < n - n / 2
  · rw [embLow_eq_zero _ r c (Or.inr hc), mul_embLow_mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [hB (hi n l) c (Fin.lt_def.2 (by simp only [hi]; omega)), mul_zero]
  · have hr : n' - n' / 2 ≤ r.1 := by omega
    obtain ⟨r', rfl⟩ := exists_hi r hr
    obtain ⟨c', rfl⟩ := exists_hi c (by omega)
    rw [mul_embLow_mul_apply, embLow_hi, lowBlock_mul_apply]

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_mixLat_iff {n' n : ℕ} (x : Matrix (Fin n') (Fin n) L) : x ∈ mixLat L n' n ↔
    ∀ r c, (n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n / 2 → x r c = 0) ∧
      (n' / 2 ≤ r.1 → c.1 < n - n / 2 → x r c ∈ intL L) := Iff.rfl

theorem borel_mid_int {σ : L →+* L} {N : ℕ} (hv : ∀ x, Valued.v (σ x) = Valued.v x) {b : GU σ N}
    (hb : IsBorelU b) (i : Fin N) (hi' : i.rev = i) : b.1.1 i i ∈ intL L := by
  have h := P.fSatake_unit_diag hb i
  rw [hi'] at h
  have h2 := congrArg Valued.v h
  rw [map_mul, hv, map_one] at h2
  rw [mem_intL]
  by_contra hc
  rw [not_le] at hc
  have : (1 : WithZero (Multiplicative ℤ)) < Valued.v (b.1.1 i i) * Valued.v (b.1.1 i i) := one_lt_mul'' hc hc
  rw [h2] at this
  exact lt_irrefl _ this

theorem row_mul_eq {n' n : ℕ} (A : Matrix (Fin n') (Fin n') L) (hA : ∀ i j : Fin n', j < i → A i j = 0)
    (a : Matrix (Fin n') (Fin n) L) (ha : a ∈ mixLat L n' n) (r : Fin n') (hr : n' / 2 ≤ r.1) (j : Fin n) :
    (A * a) r j = A r r * a r j := by
  rw [mem_mixLat_iff] at ha
  rw [Matrix.mul_apply, Finset.sum_eq_single r]
  · intro i _ hir
    rcases lt_or_gt_of_ne hir with h1 | h1
    · rw [hA r i h1, zero_mul]
    · rw [(ha i j).1 (Or.inl (by have := Fin.lt_def.1 h1; omega)), mul_zero]
  · simp

theorem borel_mul_mem {σ : L →+* L} {n' n : ℕ} (hv : ∀ x, Valued.v (σ x) = Valued.v x) {g : GU σ n} {h : GU σ n'}
    (hg : IsBorelU g) (hh : IsBorelU h) (a : Matrix (Fin n') (Fin n) L) (ha : a ∈ mixLat L n' n) :
    (h.1.1 * a * g.1.1 : Matrix (Fin n') (Fin n) L) ∈ mixLat L n' n := by
  have ha' := (mem_mixLat_iff a).1 ha
  rw [mem_mixLat_iff]
  intro r c
  constructor
  · intro hrc
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [row_mul_eq _ hh a ha r (by omega)]
    rcases hrc with hr | ⟨hr, hc⟩
    · rw [(ha' r j).1 (Or.inl hr), mul_zero, zero_mul]
    · by_cases hjc : j.1 ≤ c.1
      · rw [(ha' r j).1 (Or.inr ⟨hr, by omega⟩), mul_zero, zero_mul]
      · rw [hg j c (Fin.lt_def.2 (by omega)), mul_zero]
  · intro hr hc
    rw [Matrix.mul_apply, Finset.sum_eq_single c]
    · rw [row_mul_eq _ hh a ha r hr]
      by_cases hz : a r c = 0
      · rw [hz, mul_zero, zero_mul]; exact zero_mem _
      · have h1 : ¬ (n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n / 2) := fun e => hz ((ha' r c).1 e)
        have hrr : r.rev = r := Fin.ext (by rw [Fin.val_rev]; omega)
        have hcc : c.rev = c := Fin.ext (by rw [Fin.val_rev]; omega)
        exact mul_mem (mul_mem (borel_mid_int hv hh r hrr) ((ha' r c).2 hr hc)) (borel_mid_int hv hg c hcc)
    · intro j _ hjc
      rcases lt_or_gt_of_ne hjc with h1 | h1
      · rw [row_mul_eq _ hh a ha r hr, (ha' r j).1 (Or.inr ⟨hr, by have := Fin.lt_def.1 h1; omega⟩), mul_zero, zero_mul]
      · rw [hg j c h1, mul_zero]
    · simp

end GlobalTheory.SphTheta.MixStab

namespace GlobalTheory.SphTheta


open MixStab in
theorem borel_mixLat_lowBlock : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (g : GU σ n) (h : GU σ n'), IsBorelU g → IsBorelU h → (∀ a : Matrix (Fin n') (Fin n) L, a ∈ mixLat L n' n → (h.1.1 * a * g.1.1 : Matrix (Fin n') (Fin n) L) ∈ mixLat L n' n) ∧ ∀ (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L), ∃ a ∈ mixLat L n' n, (∀ (r : Fin n') (c : Fin n), c.1 < n - n / 2 → a r c = 0) ∧ (h.1.1 * embLow n' n z * g.1.1 : Matrix (Fin n') (Fin n) L) = a + embLow n' n (lowBlock h.1.1 * z * lowBlock g.1.1) := by
  intro L _ _ ϖ σ q hU n n' g h hg hh
  refine ⟨fun a ha => borel_mul_mem hU.2.1 hg hh a ha, fun z => ?_⟩
  have key : ∀ (r : Fin n') (c : Fin n), n' - n' / 2 ≤ r.1 ∨ c.1 < n - n / 2 →
      (h.1.1 * embLow n' n z * g.1.1 - embLow n' n (lowBlock h.1.1 * z * lowBlock g.1.1)) r c = 0 := fun r c e => by
    rw [Matrix.sub_apply, sub_eq_zero]
    exact mul_embLow_mul_eq _ _ hg _ r c e
  refine ⟨h.1.1 * embLow n' n z * g.1.1 - embLow n' n (lowBlock h.1.1 * z * lowBlock g.1.1), ?_,
    fun r c hc => key r c (Or.inr hc), (sub_add_cancel _ _).symm⟩
  rw [mem_mixLat_iff]
  intro r c
  refine ⟨fun e => key r c (by omega), fun _ hc => ?_⟩
  rw [key r c (Or.inr hc)]
  exact zero_mem _

end GlobalTheory.SphTheta
end
end
