module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1349
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1967
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle927
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle928
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle124
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1684
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle433
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1867
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOrientedVacuumIsometryMovedLattices
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.UniformSpace.Uniformizable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DiagWSB

variable {F : Type} [Field F] [NumberField F] {v : Pl (F := F)} {κ : Type} [Fintype κ]

def diagG (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)) (Φ : (κ ⊕ κ → Fv F v) → ℂ)
    (w : (κ → Fv F v) × (κ → Fv F v)) : ℂ :=
  ∫ x, ψ (x ⬝ᵥ w.2) * Φ (Sum.elim (x + w.1) x) ∂μ

omit [Fintype κ] in
theorem elim_add_elim {R : Type} [AddCommGroup R] (a b c d : κ → R) :
    Sum.elim a b + Sum.elim c d = Sum.elim (a + c) (b + d) := by
  funext i; rcases i with i | i <;> rfl

theorem elim_dot_elim {R : Type} [CommRing R] (a b c d : κ → R) :
    Sum.elim a b ⬝ᵥ Sum.elim c d = a ⬝ᵥ c + b ⬝ᵥ d := by
  simp [dotProduct, Fintype.sum_sum_type]

theorem diagW_eq (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)) (Φ : (κ ⊕ κ → Fv F v) → ℂ)
    (w : (κ → Fv F v) × (κ → Fv F v)) :
    diagW ψ μ Φ w = ψ (⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * diagG ψ μ Φ w := by
  unfold diagW diagG
  rw [← integral_const_mul]
  congr 1
  funext x
  simp [schr, elim_add_elim, AddChar.map_add_eq_mul, mul_comm, mul_left_comm, mul_assoc]

omit [Fintype κ] in
theorem continuous_elim_add (a : κ → Fv F v) : Continuous fun x : κ → Fv F v => Sum.elim (x + a) x :=
  continuous_pi fun i => by rcases i with i | i <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop

theorem integrable_integrand (ψ : AddChar (Fv F v) ℂ) (hψ : Continuous ψ) (μ : @Measure (κ → Fv F v) (borel _))
    (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) (Φ : (κ ⊕ κ → Fv F v) → ℂ) (hΦ : Φ ∈ SB (κ ⊕ κ → Fv F v))
    (w : (κ → Fv F v) × (κ → Fv F v)) :
    Integrable (fun x => ψ (x ⬝ᵥ w.2) * Φ (Sum.elim (x + w.1) x)) μ := by
  let _ : MeasurableSpace (κ → Fv F v) := borel _
  have _ : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  have _ := hμ
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (hψ.comp (continuous_id.dotProduct continuous_const)).mul
      (hΦ.1.continuous.comp (continuous_elim_add w.1))
  · apply HasCompactSupport.mul_left
    refine HasCompactSupport.intro (K := (fun y : κ ⊕ κ → Fv F v => y ∘ Sum.inr) '' tsupport Φ)
      (hΦ.2.image (by fun_prop)) ?_
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hx ⟨_, h, rfl⟩

theorem diagG_zero (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)) :
    diagG ψ μ (0 : (κ ⊕ κ → Fv F v) → ℂ) = 0 := by
  funext w; simp [diagG]

theorem diagG_add (ψ : AddChar (Fv F v) ℂ) (hψ : Continuous ψ) (μ : @Measure (κ → Fv F v) (borel _))
    (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) {Φ Ψ : (κ ⊕ κ → Fv F v) → ℂ} (hΦ : Φ ∈ SB (κ ⊕ κ → Fv F v))
    (hΨ : Ψ ∈ SB (κ ⊕ κ → Fv F v)) : diagG ψ μ (Φ + Ψ) = diagG ψ μ Φ + diagG ψ μ Ψ := by
  funext w
  simp only [diagG, Pi.add_apply, mul_add]
  exact integral_add (integrable_integrand ψ hψ μ hμ Φ hΦ w) (integrable_integrand ψ hψ μ hμ Ψ hΨ w)

theorem diagG_smul (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)) (a : ℂ)
    (Φ : (κ ⊕ κ → Fv F v) → ℂ) : diagG ψ μ (a • Φ) = a • diagG ψ μ Φ := by
  funext w
  simp only [diagG, Pi.smul_apply, smul_eq_mul, ← integral_const_mul]
  congr 1; funext x; ring

theorem diagG_schr (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _))
    (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) (Φ : (κ ⊕ κ → Fv F v) → ℂ) (p₁ p₂ q₁ q₂ : κ → Fv F v)
    (w : (κ → Fv F v) × (κ → Fv F v)) :
    diagG ψ μ (schr ψ (Sum.elim p₁ p₂, Sum.elim q₁ q₂) Φ) w =
      ψ (-(p₂ ⬝ᵥ w.2) + (w.1 - p₂) ⬝ᵥ q₁ - p₂ ⬝ᵥ q₂ + ⅟(2 : Fv F v) * (p₁ ⬝ᵥ q₁ + p₂ ⬝ᵥ q₂)) *
        diagG ψ μ Φ (w + (p₁ - p₂, q₁ + q₂)) := by
  let _ : MeasurableSpace (κ → Fv F v) := borel _
  have _ : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  have _ := hμ
  unfold diagG
  rw [← integral_sub_right_eq_self _ p₂, ← integral_const_mul]
  congr 1
  funext x
  simp only [schr, elim_dot_elim, elim_add_elim, Prod.fst_add, Prod.snd_add, Prod.fst, Prod.snd]
  have e : Sum.elim (x - p₂ + w.1 + p₁) (x - p₂ + p₂) = Sum.elim (x + (w.1 + (p₁ - p₂))) x := by
    congr 1 <;> abel
  rw [e, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub]
  ring

theorem sb_mul {X : Type} [TopologicalSpace X] {f g : X → ℂ} (hf : IsLocallyConstant f) (hg : g ∈ SB X) :
    (fun w => f w * g w) ∈ SB X :=
  ⟨hf.mul hg.1, hg.2.mul_left⟩

theorem sb_mul_translate {X : Type} [TopologicalSpace X] [AddGroup X] [ContinuousAdd X] {f g : X → ℂ}
    (hf : IsLocallyConstant f) (hg : g ∈ SB X) (t : X) : (fun w => f w * g (w + t)) ∈ SB X :=
  ⟨hf.mul (hg.1.comp_continuous (continuous_id.add continuous_const)), (hg.2.comp_homeomorph (Homeomorph.addRight t)).mul_left⟩

omit [Fintype κ] in
theorem isLocallyConstant_indicator {X : Type} [TopologicalSpace X] {S : Set X} (hS : IsClopen S) (c : ℂ) :
    IsLocallyConstant (S.indicator fun _ => c) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ S
  · exact ⟨S, hS.isOpen, hx, fun y hy => by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
  · exact ⟨Sᶜ, hS.compl.isOpen, hx, fun y hy => by rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

theorem diagW_mem_SB : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ]
    (ψ : AddChar (Fv F v) ℂ), Continuous ψ → ψ ≠ 1 →
    ∀ (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ Φ₀ ∈ SB (κ ⊕ κ → Fv F v), ∀ c : ℂ, c ≠ 0 → ∀ U : Set ((κ → Fv F v) × (κ → Fv F v)), IsOpen U → IsCompact U →
      0 ∈ U → (∀ w, diagW ψ μ Φ₀ w = U.indicator (fun _ => c) w) →
    ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), diagW ψ μ Φ ∈ SB ((κ → Fv F v) × (κ → Fv F v)) := by
  intro F _ _ v κ _ ψ hψ h1 μ hμ Φ₀ hΦ₀ c hc U hUo hUc h0U hU Φ hΦ
  have _ := GlobalTheory.WeilM.nonarch_field (Fv F v)
  have hlc := GlobalTheory.WeilM.isLocallyConstant_addChar ψ hψ

  have hph : ∀ a : Fv F v, IsLocallyConstant fun w : (κ → Fv F v) × (κ → Fv F v) => ψ (a * (w.1 ⬝ᵥ w.2)) :=
    fun a => hlc.comp_continuous (continuous_const.mul (continuous_fst.dotProduct continuous_snd))
  let N : Submodule ℂ ((κ ⊕ κ → Fv F v) → ℂ) :=
    { carrier := {Φ | Φ ∈ SB (κ ⊕ κ → Fv F v) ∧ diagG ψ μ Φ ∈ SB ((κ → Fv F v) × (κ → Fv F v))}
      zero_mem' := ⟨zero_mem _, by rw [diagG_zero]; exact zero_mem _⟩
      add_mem' := fun ha hb => ⟨add_mem ha.1 hb.1, by
        rw [diagG_add ψ hψ μ hμ ha.1 hb.1]; exact add_mem ha.2 hb.2⟩
      smul_mem' := fun a Φ h => ⟨Submodule.smul_mem _ a h.1, by
        rw [diagG_smul]; exact Submodule.smul_mem _ a h.2⟩ }
  have hNle : N ≤ SB (κ ⊕ κ → Fv F v) := fun Φ h => h.1
  have hS : ∀ w, ∀ φ ∈ N, schr ψ w φ ∈ N := by
    rintro ⟨P, Q⟩ φ ⟨hφ1, hφ2⟩
    refine ⟨GlobalTheory.SchrSBFin.schr_mem_SB v ψ hψ (P, Q) φ hφ1, ?_⟩
    rw [← Sum.elim_comp_inl_inr P, ← Sum.elim_comp_inl_inr Q]
    have e : diagG ψ μ (schr ψ (Sum.elim (P ∘ Sum.inl) (P ∘ Sum.inr), Sum.elim (Q ∘ Sum.inl) (Q ∘ Sum.inr)) φ) =
        fun w => ψ (-((P ∘ Sum.inr) ⬝ᵥ w.2) + (w.1 - P ∘ Sum.inr) ⬝ᵥ (Q ∘ Sum.inl) - (P ∘ Sum.inr) ⬝ᵥ (Q ∘ Sum.inr) +
          ⅟(2 : Fv F v) * ((P ∘ Sum.inl) ⬝ᵥ (Q ∘ Sum.inl) + (P ∘ Sum.inr) ⬝ᵥ (Q ∘ Sum.inr))) *
          diagG ψ μ φ (w + (P ∘ Sum.inl - P ∘ Sum.inr, Q ∘ Sum.inl + Q ∘ Sum.inr)) :=
      funext fun w => diagG_schr ψ μ hμ φ _ _ _ _ w
    rw [e]
    refine sb_mul_translate (hlc.comp_continuous ?_) hφ2 _
    fun_prop

  have hUcl : IsClopen U := ⟨hUc.isClosed, hUo⟩
  have hW₀ : diagW ψ μ Φ₀ ∈ SB ((κ → Fv F v) × (κ → Fv F v)) := by
    rw [show diagW ψ μ Φ₀ = U.indicator (fun _ => c) from funext hU]
    exact ⟨isLocallyConstant_indicator hUcl c,
      HasCompactSupport.intro hUc fun x hx => Set.indicator_of_notMem hx _⟩
  have hG : ∀ Φ : (κ ⊕ κ → Fv F v) → ℂ, diagG ψ μ Φ =
      fun w => ψ (-⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * diagW ψ μ Φ w := by
    intro Φ
    funext w
    rw [diagW_eq, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  have h0N : Φ₀ ∈ N := ⟨hΦ₀, by rw [hG]; exact sb_mul (hph _) hW₀⟩
  have hne : Φ₀ ≠ 0 := by
    rintro rfl
    have h := hU 0
    rw [Set.indicator_of_mem h0U, diagW_zero] at h
    simp at h
    exact hc h.symm
  have hN := GlobalTheory.SchrIrred.schr_irreducible v ψ hψ h1 N hNle hS Φ₀ h0N hne
  have hΦN : Φ ∈ N := hN ▸ hΦ
  rw [show diagW ψ μ Φ = fun w => ψ (⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * diagG ψ μ Φ w from funext (diagW_eq ψ μ Φ)]
  exact sb_mul (hph _) hΦN.2

end GlobalTheory.DiagWSB

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Poinc.Tors.LiesOverExt

theorem sumF_algebraMap {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] {Ix : Type} (x : Ix → FractionRing R) (s : FractionRing R)
    (h : SumF I (FractionRing R) x s) :
    SumF I F (fun i => algebraMap (FractionRing R) F (x i)) (algebraMap (FractionRing R) F s) := by
  letI : Module R (FractionRing R) := Module.compHom (FractionRing R) (algebraMap R (FractionRing R))
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  obtain ⟨N, hN, hs, hx, hS⟩ := h
  let φ : FractionRing R →ₗ[R] F :=
    { toFun := algebraMap (FractionRing R) F
      map_add' := map_add _
      map_smul' := fun r y => by
        show algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r • y) =
          algebraMap R (FractionRing R) r • algebraMap (FractionRing R) F y
        rw [smul_eq_mul, map_mul, Algebra.smul_def] }
  refine ⟨N.map φ, hN.map φ, Submodule.mem_map_of_mem hs, fun i => Submodule.mem_map_of_mem (hx i), fun n => ?_⟩
  obtain ⟨S, hS⟩ := hS n
  refine ⟨S, fun T hT => ?_⟩
  have := Submodule.mem_map_of_mem (f := φ) (hS T hT)
  rw [Submodule.map_smul''] at this

  simpa [φ, map_sub, map_sum] using this

theorem exists_frm_pull {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} (g : GtPtF D (FractionRing R)) (w : Frm D (FractionRing R) k g.b)
    (hw : w.IsGen) :
    ∃ w' : Frm D F k (GlobalTheory.TorusExt.gtExt D (algebraMap (FractionRing R) F) (RingHom.comp_id _) g).b, w'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) (J), Good D.P.L z J →
        val w' r z J = val w (r ≫ spMap (algebraMap (FractionRing R) F)) z J := by
  have hb := GlobalTheory.TorusExt.gtExt_b (D := D) (algebraMap (FractionRing R) F) (RingHom.comp_id _) g
  have h0 : spMap (algebraMap (FractionRing R) F) ≫ (DegPre.zeroF D (FractionRing R)).left =
      (DegPre.zeroF D F).left :=
    congrArg (fun q => q.left) (MonObj.comp_one (M := D.P.A)
      (GlobalTheory.TorusExt.extMap (R := R) (algebraMap (FractionRing R) F) (RingHom.comp_id _)))
  obtain ⟨w', hw', hv⟩ := exists_gen D.P.isLB
    (φ' := DegPre.lineφ D F (GlobalTheory.TorusExt.gtExt D (algebraMap (FractionRing R) F) (RingHom.comp_id _) g).b)
    (ε' := DegPre.lineε k)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by
      fin_cases i
      · exact congrArg (fun q => h q ^ _) h0
      · exact congrArg (fun q => h q ^ _) (congrArg (fun q => q.left) hb).symm)
    (LB.pullGen D.P.L _ _ w (spMap (algebraMap (FractionRing R) F))) (pullGen_isGen _ _ _ _ hw _)
  exact ⟨w', hw', fun Z r z J hJ => (hv Z r z J hJ).trans (val_pull hJ _ _ _)⟩

theorem exists_frAt_pull {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {F : Type} [Field F] [Algebra (FractionRing R) F] (x : TFK (R := R) (FractionRing R) ⟶ A.A) (fr : FrAt x)
    (hfr : fr.IsGen) (x' : TFK (R := R) F ⟶ A.A) (hx : x'.left = spMap (algebraMap (FractionRing R) F) ≫ x.left) :
    ∃ fr' : FrAt x', fr'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (TFK (R := R) F).left) (z : Z) (J), Good A.L z J →
      val fr' r z J = val fr (r ≫ spMap (algebraMap (FractionRing R) F)) z J := by
  obtain ⟨fr', hfr', hv⟩ := exists_gen A.isLB (φ' := fun _ : Fin 1 => x'.left) (ε' := fun _ => 1)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by rw [hx])
    (LB.pullGen A.L _ _ fr (spMap (algebraMap (FractionRing R) F))) (pullGen_isGen _ _ _ _ hfr _)
  exact ⟨fr', hfr', fun Z r z J hJ => (hv Z r z J hJ).trans (val_pull hJ _ _ _)⟩

theorem exists_frm_pow {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {b : TF (R := R) F ⟶ D.P.A} (w : Frm D F 1 b) (hw : w.IsGen) (k : ℕ) :
    ∃ wk : Frm D F k b, wk.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) (J), Good D.P.L z J →
      val wk r z J = val w r z J ^ k := by
  obtain ⟨wk, hwk, hv⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b) (ε' := DegPre.lineε k)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by fin_cases i <;> simp [DegPre.lineε])
    (GeneratorPullback.powGen D.P.L _ _ w k) (powGen_isGen _ _ _ _ hw k)
  exact ⟨wk, hwk, fun Z r z J hJ => (hv Z r z J hJ).trans (val_pow _ _ _ _ _)⟩


open GlobalTheory.TorsionExt GlobalTheory.FieldBaseChange in
theorem liesOver_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif I D A G) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (g : GtPtF D.toPre (FractionRing R)) (w : Frm D.toPre (FractionRing R) 1 g.b) (x : TFK (R := R) (FractionRing R) ⟶ A.A) (fr : FrAt x), w.IsGen → fr.IsGen → GlobalTheory.Poinc.Tors.LiesOver U.toUnifPre w₀ g w x fr → ∀ (x' : TFK (R := R) F ⟶ A.A), x'.left = spMap (algebraMap (FractionRing R) F) ≫ x.left → ∃ (w' : Frm D.toPre F 1 (GlobalTheory.TorusExt.gtExt D.toPre (algebraMap (FractionRing R) F) (RingHom.comp_id _) g).b) (fr' : FrAt x'), w'.IsGen ∧ fr'.IsGen ∧ GlobalTheory.Poinc.Tors.LiesOver U.toUnifPre w₀ (GlobalTheory.TorusExt.gtExt D.toPre (algebraMap (FractionRing R) F) (RingHom.comp_id _) g) w' x' fr' := by
  intro R _ _ _ I hI D A G _ _ hGs U F _ _ _ w₀ hw₀ g w x fr hw hfr hlies x' hx'
  have hG : GlobalFnsSt := GlobalTheory.firstFiveLaws.1.globalFns
  obtain ⟨w', hw', hvw'⟩ := exists_frm_pull D.toPre F g w hw
  obtain ⟨fr', hfr', hvfr'⟩ := exists_frAt_pull x fr hfr x' hx'
  refine ⟨w', fr', hw', hfr', ?_⟩
  intro k hk wk' hwk'v hwk' s s'' v hexp hval
  obtain ⟨wk, hwk, hwkv⟩ := exists_frm_pow w hw k
  obtain ⟨wkF, hwkF, hvwkF⟩ := exists_frm_pull D.toPre F g wk hwk
  have hc : ∀ χ, coef s'' (GlobalTheory.TorusExt.gtExt D.toPre (algebraMap (FractionRing R) F) (RingHom.comp_id _) g) wk' χ =
      coef s'' (GlobalTheory.TorusExt.gtExt D.toPre (algebraMap (FractionRing R) F) (RingHom.comp_id _) g) wkF χ := fun χ =>
    GlobalTheory.UT.ThetaSum.coef_congr _ hwkF (fun z J hJ => by
      rw [hwk'v z J hJ, hvw' _ _ z J hJ, hvwkF _ _ z J hJ, hwkv _ _ z J hJ]) s'' χ
  obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG U (FractionRing R) hk w₀ hw₀
  obtain ⟨e', he'⟩ := GlobalTheory.exists_linearEquiv_expandsF hG U F hk w₀ hw₀
  have cc : ∀ t, e' (abPull (FractionRing R) F A k t) = famPull D.toPre (FractionRing R) F hG k (e t) := fun t =>
    (he' _ _).1 (expandsF_pull U.toUnifPre hG ((he _ _).2 rfl))
  obtain ⟨n, c, σ, hσ⟩ := (isExtension_famPull D.toPre (FractionRing R) F hG hk).exists_sum s''
  choose a ha using fun i => GlobalTheory.ZH.SecComb.exists_valAt (e.symm (σ i)) hfr
  have sK : ∀ i, SumF I (FractionRing R) (coef (σ i) g wk) (a i) := fun i =>
    hlies k hk wk (fun z J hJ => hwkv _ _ z J hJ) hwk (e.symm (σ i)) (σ i) (a i)
      ((he _ _).2 (e.apply_symm_apply _)) (ha i)
  have comb := GlobalTheory.UT.EvalZero.sumF_comb hI F Finset.univ c _ _ fun i => sumF_algebraMap I F _ _ (sK i)
  have lin := ((GlobalTheory.UT.CoefBasic.coef_basic R D.toPre F k
    (GlobalTheory.TorusExt.gtExt D.toPre (algebraMap (FractionRing R) F) (RingHom.comp_id _) g)).2.2 wkF hwkF).2.1
  have hcoef : ∀ χ, coef s'' (GlobalTheory.TorusExt.gtExt D.toPre (algebraMap (FractionRing R) F) (RingHom.comp_id _) g) wk' χ =
      ∑ i, c i * algebraMap (FractionRing R) F (coef (σ i) g wk χ) := fun χ => by
    have h0 : coef 0 (GlobalTheory.TorusExt.gtExt D.toPre (algebraMap (FractionRing R) F) (RingHom.comp_id _) g) wkF χ = 0 := by
      have := lin 0 0 1 χ
      rw [smul_zero, add_zero, _root_.one_mul] at this
      exact left_eq_add.1 this
    let Lc : Fam D.toPre F k →ₗ[F] F :=
      { toFun := fun s => coef s (GlobalTheory.TorusExt.gtExt D.toPre (algebraMap (FractionRing R) F) (RingHom.comp_id _) g) wkF χ
        map_add' := fun s s' => by simpa using lin s s' 1 χ
        map_smul' := fun c s => by simpa [h0] using lin s 0 c χ }
    rw [hc χ, hσ]
    show Lc _ = _

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul]
    exact congrArg (c i * ·) (GlobalTheory.T.fourierCoefficient_familyPullback_fractionField R D.toPre F hG k (σ i) g wk wkF hwk hwkF
      (fun z J hJ => hvwkF _ _ z J hJ) χ)

  let u : Fin n → AbSec A F k := fun i => abPull (FractionRing R) F A k (e.symm (σ i))
  have hs : (s : AbSec A F k) = ∑ i, c i • u i := by
    apply e'.injective

    rw [(he' _ _).1 hexp, map_sum, hσ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, cc, e.apply_symm_apply]
  have hcomb : IsComb u c s := fun j => by
    rw [hs]
    exact (map_sum (chartLin (abelianBase A F) _ j) (fun i => c i • u i) Finset.univ).trans rfl
  have hvu : ∀ i, ValAt (u i) x' fr' (algebraMap (FractionRing R) F (a i)) := fun i =>
    GlobalTheory.T.value_pulledBackSection_eq_image_fieldExtension R A F k _ x fr x' fr' hx' hfr (fun z J hJ => hvfr' _ _ z J hJ) _ (ha i)
  have hval' := ((GlobalTheory.ZH.SecComb.lin_comb_value_act R A F k).2 (Fin n) c u).2 s hcomb |>.1 x' fr' _ hvu
  have hv : v = ∑ i, c i * algebraMap (FractionRing R) F (a i) :=
    ((GlobalTheory.ZH.SecComb.lin_comb_value_act R A F k).1 s x' fr' hfr').unique hval hval'
  rw [hv, funext hcoef]
  exact comb

end GlobalTheory.Poinc.Tors.LiesOverExt
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BrPairF

theorem funEquiv_symm_mapVV {K ι : Type} [Field K] [CharZero K] [Fintype ι] {n : ℕ} (φ : K →+* ℂ)
    (σ : ι → DomWeight n) (v : VV K fun τ => (σ τ).dual) :
    (GlobalTheory.FunObj.funEquiv σ).symm (GlobalTheory.CoefModel.mapVV φ (fun τ => (σ τ).dual) v) =
      GlobalTheory.CoefModel.mapVV φ σ ((GlobalTheory.FunObj.funEquiv σ).symm v) := by
  have h1 : IsFunForm σ ((funEquiv σ).symm v) v := by
    have := isFunForm_funEquiv σ ((funEquiv σ).symm v)
    rwa [LinearEquiv.apply_symm_apply] at this
  have h2 := GlobalTheory.BrRat.isFunForm_map φ σ h1
  have h3 := (isFunForm_iff_eq σ _ _).1 h2
  rw [LinearEquiv.symm_apply_eq]
  exact h3

theorem brPair_mapVV : ∀ {K ι : Type} [Field K] [CharZero K] [Fintype ι] {n N : ℕ} (φ : K →+* ℂ) (σ : ι → DomWeight n) (hN : N = n + 1)
    (Λ : ι → DomWeight N) (u : VV K Λ) (v : VV K fun τ => (σ τ).dual),
    GlobalTheory.FunObj.brPair σ hN Λ (GlobalTheory.CoefModel.mapVV φ Λ u) (GlobalTheory.CoefModel.mapVV φ (fun τ => (σ τ).dual) v) =
      φ (GlobalTheory.BrPairF.brPairF σ hN Λ u v) := by
  intro K ι _ _ _ n N φ σ hN Λ u v
  rw [brPair, LinearMap.compl₁₂_apply, pairBK_apply, pairB_apply, brPairF_apply, pairBK_apply, pairB_apply,
    GlobalTheory.BrRat.covOf_eq, funEquiv_symm_mapVV, GlobalTheory.CoefModel.mapVV_coe, Formalism.L2.Col.Br.brStd, LinearMap.comp_apply,
    Submodule.subtype_apply, Formalism.L2.Col.Br.brStd, LinearMap.comp_apply, Submodule.subtype_apply, GlobalTheory.CoefModel.mapVV_coe,
    GlobalTheory.Proof.TensorMapDescent.branchingProjection_map, GlobalTheory.Proof.TensorMapDescent.fockB_map, map_mul, map_inv₀]
  congr 2
  unfold extNormB
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← GlobalTheory.Proof.TensorMapDescent.fockB_map, Formalism.L2.DIV.map_extremal]

end GlobalTheory.BrPairF

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem funEquiv_symm_mapVV {K ι : Type} [Field K] [CharZero K] [Fintype ι] {n : ℕ} (φ : K →+* ℂ)
    (σ : ι → DomWeight n) (v : VV K fun τ => (σ τ).dual) :
    (GlobalTheory.FunObj.funEquiv σ).symm (GlobalTheory.CoefModel.mapVV φ (fun τ => (σ τ).dual) v) =
      GlobalTheory.CoefModel.mapVV φ σ ((GlobalTheory.FunObj.funEquiv σ).symm v) := by
  have h1 : IsFunForm σ ((funEquiv σ).symm v) v := by
    have := isFunForm_funEquiv σ ((funEquiv σ).symm v)
    rwa [LinearEquiv.apply_symm_apply] at this
  have h2 := GlobalTheory.BrRat.isFunForm_map φ σ h1
  have h3 := (isFunForm_iff_eq σ _ _).1 h2
  rw [LinearEquiv.symm_apply_eq]
  exact h3

theorem _root_.GlobalTheory.T.branchingPairing_extendScalars : ∀ {K ι : Type} [Field K] [CharZero K] [Fintype ι] {n N : ℕ} (φ : K →+* ℂ) (σ : ι → DomWeight n) (hN : N = n + 1)
    (Λ : ι → DomWeight N) (u : VV K Λ) (v : VV K fun τ => (σ τ).dual),
    GlobalTheory.FunObj.brPair σ hN Λ (GlobalTheory.CoefModel.mapVV φ Λ u) (GlobalTheory.CoefModel.mapVV φ (fun τ => (σ τ).dual) v) =
      φ (GlobalTheory.BrPairF.brPairF σ hN Λ u v) := by
  intro K ι _ _ _ n N φ σ hN Λ u v
  rw [brPair, LinearMap.compl₁₂_apply, pairBK_apply, pairB_apply, GlobalTheory.BrPairF.brPairF_apply, pairBK_apply, pairB_apply,
    GlobalTheory.BrRat.covOf_eq, funEquiv_symm_mapVV, GlobalTheory.CoefModel.mapVV_coe, Formalism.L2.Col.Br.brStd, LinearMap.comp_apply,
    Submodule.subtype_apply, Formalism.L2.Col.Br.brStd, LinearMap.comp_apply, Submodule.subtype_apply, GlobalTheory.CoefModel.mapVV_coe,
    GlobalTheory.Proof.TensorMapDescent.branchingProjection_map, GlobalTheory.Proof.TensorMapDescent.fockB_map, map_mul, map_inv₀]
  congr 2
  unfold extNormB
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← GlobalTheory.Proof.TensorMapDescent.fockB_map, Formalism.L2.DIV.map_extremal]
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.isOrientedVacuum_isometry_moved_lattices : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (ε : Bool) {S S' T T' : HSp D} (IS : GlobalTheory.Mem.Isom.IsoMat S S') (IT : GlobalTheory.Mem.Isom.IsoMat T T') (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f : WO S T → ℂ),
  IsVacO ψ θ (GlobalTheory.Grid.sgn ε S) T (fun τ => GlobalTheory.Grid.sgnM ε (sS τ)) sT LS LT f →
  IsVacO ψ θ (GlobalTheory.Grid.sgn ε S') T' (fun τ => GlobalTheory.Grid.sgnM ε (GlobalTheory.TriMove.cartMove (S' := S') IS τ (sS τ))) (fun τ => GlobalTheory.TriMove.cartMove (S' := T') IT τ (sT τ)) (GlobalTheory.TriMove.latMove (S' := S') IS LS) (GlobalTheory.TriMove.latMove (S' := T') IT LT) (GlobalTheory.TriMove.trH (S := S) (S' := S') (T := T) (T' := T') IS IT f) := by
  first | exact @GlobalTheory.VacMove.isVacO_move | exact GlobalTheory.VacMove.isVacO_move | (intros; apply GlobalTheory.VacMove.isVacO_move <;> assumption)
end
