module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2123
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle431
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2130
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1926
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny


open GlobalTheory.SympChange in
theorem GlobalTheory.WeylFour.weyl_hasOp : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    (∀ᶠ v in cofinite, PsiUnr ψ v) → (∀ v : Pl (F := F), ∃ x, psiLoc ψ v x ≠ 1) → ∀ (κ : Type) [Fintype κ] [DecidableEq κ],
    GlobalTheory.SympChange.HasOp ψ (GlobalTheory.SympChange.weylM (F := F) (κ := κ)) := by
  intro F _ _ ψ hψ hunr hnt κ _ _
  classical

  have hsp : ∀ {R : Type} [CommRing R] [Algebra F R] (w : (κ → R) × (κ → R)),
      spAct (weylM (F := F) (κ := κ)) w = (w.2, -w.1) := by
    intro R _ _ w
    ext k
    · simp [spAct, weylM, Matrix.fromBlocks_map, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Matrix.one_apply]
    · simp [spAct, weylM, Matrix.fromBlocks_map, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Matrix.one_apply]

  have hSB := fun v => GlobalTheory.T.local_fourier_schwartz_stable F ψ hψ v (hnt v) κ
  have hInv := fun v => GlobalTheory.T.local_fourier_double_reflection F ψ hψ v (hnt v) κ
  have hLaw := GlobalTheory.T.local_fourier_schrodinger_intertwine F ψ hψ
  have hInd := fun v => GlobalTheory.T.local_lattice_indicator_fourier F ψ hψ v κ
  have hsmV : ∀ v (c : ℂ) (φ : (κ → Fv F v) → ℂ), fourV ψ v (c • φ) = c • fourV ψ v φ := by
    intro v c φ; funext y
    simp only [fourV, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul c _
  have h0V : ∀ v, fourV ψ v (0 : (κ → Fv F v) → ℂ) = 0 := by
    intro v; funext y; simp [fourV]
  choose C hC using fun v : Pl F => Submodule.exists_isCompl (SB (κ → Fv F v))
  let P : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ) := fun v =>
    (SB (κ → Fv F v)).subtype ∘ₗ Submodule.linearProjOfIsCompl _ (C v) (hC v)
  have hPmem : ∀ v φ, P v φ ∈ SB (κ → Fv F v) := fun v φ => (Submodule.linearProjOfIsCompl _ (C v) (hC v) φ).2
  have hPid : ∀ v, ∀ φ ∈ SB (κ → Fv F v), P v φ = φ := fun v φ hφ =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left (hC v) ⟨φ, hφ⟩)
  let ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ) := fun v =>
    { toFun := fun φ => fourV ψ v (P v φ)
      map_add' := fun φ χ => by
        rw [map_add (f := _)]; exact (hSB v).2.1 _ (hPmem v φ) _ (hPmem v χ)
      map_smul' := fun c φ => by
        rw [map_smul, RingHom.id_apply]; exact hsmV v c _ }
  have hev : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ = fourV ψ v φ := fun v φ hφ => by
    show fourV ψ v (P v φ) = _
    rw [hPid v φ hφ]
  have hneg : ∀ v, ∀ φ ∈ SB (κ → Fv F v), (fun x => φ (-x)) ∈ SB (κ → Fv F v) := fun v φ hφ =>
    ⟨hφ.1.comp_continuous continuous_neg, hφ.2.comp_homeomorph (Homeomorph.neg _)⟩
  have hmap : ∀ v, (SB (κ → Fv F v)).map (ev v) = SB _ := by
    intro v
    apply le_antisymm
    · rintro _ ⟨φ, hφ, rfl⟩
      rw [hev v φ hφ]; exact (hSB v).1 φ hφ
    · intro φ hφ
      have h1 := hneg v φ hφ
      refine ⟨fourV ψ v (fun x => φ (-x)), (hSB v).1 _ h1, ?_⟩
      rw [hev v _ ((hSB v).1 _ h1), hInv v _ h1]
      simp
  have hinj : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ = 0 → φ = 0 := by
    intro v φ hφ h
    rw [hev v φ hφ] at h
    have h2 := hInv v φ hφ
    rw [h, h0V] at h2
    funext x
    have h3 := congrFun h2 (-x)
    simp only [Pi.zero_apply, neg_neg] at h3
    exact h3.symm

  obtain ⟨ei, hsurj, hei, hcont⟩ := GlobalTheory.T.finite_fourier_transform_surjective_integral F κ
  obtain ⟨μ, hμ, hprod⟩ := GlobalTheory.T.exists_haar_adelic_integral_formula F ψ hψ hunr hnt κ
  haveI := hμ
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  have hspan := GlobalTheory.T.schwartz_adelic_eq_span_pure F κ
  let fA : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ := fun Φ y => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ
  have hpure : ∀ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) →
      (∀ᶠ v in cofinite, φ v = indO v) → ∀ y, Integrable (fun x => pure f φ x * ψ (x ⬝ᵥ y)) μ ∧
        fA (pure f φ) y = pure (ei f) (fun v => fourV ψ v (φ v)) y := by
    intro f φ hφ hae y
    obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.schwartz_bruhat_restricted_product_char F ψ hψ hunr κ f φ y hφ hae
    have e : (fun x => pure f φ x * ψ (x ⬝ᵥ y)) = fun x =>
        (fun z => f z * eInf z (fun i => evI F (y i))) (fun i => evI F (x i)) *
          ∏ᶠ v, (fun z => φ v z * GlobalTheory.LatVac.psiAt ψ v (z ⬝ᵥ fun i => evFin F v (y i))) (fun i => evFin F v (x i)) :=
      funext h3
    obtain ⟨hc, hi⟩ := hcont f (fun i => evI F (y i))
    obtain ⟨j1, j2⟩ := hprod _ _ hc hi h1 h2
    refine ⟨e ▸ j1, ?_⟩
    show (∫ x, pure f φ x * ψ (x ⬝ᵥ y) ∂μ) = _
    rw [e, j2, ← hei]
    rfl
  have hint : ∀ Φ ∈ schA F κ, ∀ y, Integrable (fun x => Φ x * ψ (x ⬝ᵥ y)) μ := by
    intro Φ hΦ y
    rw [hspan] at hΦ
    induction hΦ using Submodule.span_induction with
    | mem Φ h =>
      obtain ⟨f, φ, hφ, hae, rfl⟩ := h
      exact (hpure f φ hφ hae y).1
    | zero => simp
    | add Φ Ψ _ _ h1 h2 =>
      refine (h1.add h2).congr (Filter.Eventually.of_forall fun x => ?_)
      simp [add_mul]
    | smul c Φ _ h => simpa [mul_assoc] using h.const_mul c
  have hadd : ∀ Φ ∈ schA F κ, ∀ Ψ ∈ schA F κ, fA (Φ + Ψ) = fA Φ + fA Ψ := by
    intro Φ hΦ Ψ hΨ; funext y
    simp only [fA, Pi.add_apply, add_mul]
    exact integral_add (hint Φ hΦ y) (hint Ψ hΨ y)
  have hsmul : ∀ (c : ℂ) (Φ : (κ → AF F) → ℂ), fA (c • Φ) = c • fA Φ := by
    intro c Φ; funext y
    simp only [fA, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul c _
  have hkeep : ∀ Φ ∈ schA F κ, fA Φ ∈ schA F κ := by
    intro Φ hΦ
    rw [hspan] at hΦ ⊢
    induction hΦ using Submodule.span_induction with
    | mem Φ h =>
      obtain ⟨f, φ, hφ, hae, rfl⟩ := h
      have e : fA (pure f φ) = pure (ei f) (fun v => fourV ψ v (φ v)) := funext fun y => (hpure f φ hφ hae y).2
      rw [e]
      refine Submodule.subset_span ⟨ei f, fun v => fourV ψ v (φ v), fun v => (hSB v).1 _ (hφ v), ?_, rfl⟩
      filter_upwards [hae, hunr] with v h1 h2
      rw [h1, (hInd v).2 h2]
    | zero =>
      have : fA 0 = 0 := by funext y; simp [fA]
      rw [this]; exact zero_mem _
    | add Φ Ψ hΦ hΨ h1 h2 =>
      rw [hadd Φ (hspan ▸ hΦ) Ψ (hspan ▸ hΨ)]; exact add_mem h1 h2
    | smul c Φ _ h =>
      rw [hsmul]; exact Submodule.smul_mem _ c h
  have hlawA : ∀ w Φ, fA (schr ψ w Φ) = schr ψ (w.2, -w.1) (fA Φ) := by
    intro w Φ; funext y
    simp only [fA, schr]
    have h1 := integral_add_right_eq_self (μ := μ) (fun z => ψ ((z - w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) *
      Φ z * ψ ((z - w.1) ⬝ᵥ y)) w.1
    simp only [add_sub_cancel_right] at h1
    rw [h1, ← integral_const_mul]
    congr 1; funext z
    have h2 : (⅟(2 : AF F)) + ⅟2 = 1 := invOf_two_add_invOf_two
    have key : ((z - w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) + (z - w.1) ⬝ᵥ y =
        (y ⬝ᵥ -w.1 + ⅟2 * (w.2 ⬝ᵥ -w.1)) + z ⬝ᵥ (y + w.2) := by
      simp only [sub_dotProduct, dotProduct_add, dotProduct_neg]
      rw [dotProduct_comm w.2 w.1, dotProduct_comm y w.1]
      linear_combination (w.1 ⬝ᵥ w.2) * h2
    calc ψ ((z - w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) * Φ z * ψ ((z - w.1) ⬝ᵥ y)
        = Φ z * ψ (((z - w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) + (z - w.1) ⬝ᵥ y) := by
          rw [AddChar.map_add_eq_mul ψ ((z - w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) ((z - w.1) ⬝ᵥ y)]; ring
      _ = _ := by
          rw [key, AddChar.map_add_eq_mul ψ (y ⬝ᵥ -w.1 + ⅟2 * (w.2 ⬝ᵥ -w.1)) (z ⬝ᵥ (y + w.2))]; ring
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl (schA F κ)
  let Q : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) := (schA F κ).subtype ∘ₗ Submodule.linearProjOfIsCompl _ D hD
  have hQmem : ∀ Φ, Q Φ ∈ schA F κ := fun Φ => (Submodule.linearProjOfIsCompl _ D hD Φ).2
  have hQid : ∀ Φ ∈ schA F κ, Q Φ = Φ := fun Φ hΦ =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hD ⟨Φ, hΦ⟩)
  let e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ :=
    { toFun := fun Φ => fA (Q Φ)
      map_add' := fun Φ Ψ => by rw [map_add (f := _)]; exact hadd _ (hQmem Φ) _ (hQmem Ψ)
      map_smul' := fun c Φ => by rw [map_smul, RingHom.id_apply]; exact hsmul c _ }
  have he : ∀ Φ ∈ schA F κ, e Φ = fA Φ := fun Φ hΦ => by
    show fA (Q Φ) = _
    rw [hQid Φ hΦ]
  refine ⟨e, ei, ev, hsurj, fun Φ hΦ => ?_, fun w Φ hΦ => ?_, hmap, hinj, fun v w φ hφ => ?_, ?_, ?_⟩
  · rw [he Φ hΦ]; exact hkeep Φ hΦ
  · rw [he _ (GlobalTheory.T.schrodinger_preserves_schwartz F ψ hψ κ w Φ hΦ), he Φ hΦ, hlawA, hsp]
  · rw [hsp, hev v _ ((hSB v).2.2 w φ hφ), hev v φ hφ, hLaw v κ w φ]
  · filter_upwards [hunr] with v hv
    rw [hev v _ (hInd v).1, (hInd v).2 hv]
  · intro f φ hφ hae
    have hm : pure f φ ∈ schA F κ := by
      rw [hspan]; exact Submodule.subset_span ⟨f, φ, hφ, hae, rfl⟩
    have e2 : (fun v => ev v (φ v)) = fun v => fourV ψ v (φ v) := funext fun v => hev v _ (hφ v)
    rw [he _ hm, e2]
    exact funext fun y => (hpure f φ hφ hae y).2
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.standardChar_halfSymplectic_movedFinitePoint_trivial : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∀ z : Matrix (Fin d) (Fin a) D.host.E,
  ∃ n : ℕ, 0 < n ∧ ∀ z', Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' →
    ψ (symplOH S T (finPt hS hT r z') (actO S T g h (finPt hS hT r z) - finPt hS hT r z')) = 1 := by
  first | exact @GlobalTheory.MovedTrChar.psi_sympl_moved_eq_one | exact GlobalTheory.MovedTrChar.psi_sympl_moved_eq_one | (intros; apply GlobalTheory.MovedTrChar.psi_sympl_moved_eq_one <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise


theorem _root_.GlobalTheory.T.unitaryChar_finiteIdele_eq_heckeChar_value : ∀ {D : D7} (c : (Formalism.L2.Theta.AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ →
    ∀ x y, IsFinIdl x y → ((c x : Circle) : ℂ) = ((χ.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.BotPointDict.chr_at_finIdl | exact GlobalTheory.BotPointDict.chr_at_finIdl | (intros; apply GlobalTheory.BotPointDict.chr_at_finIdl <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

noncomputable section

namespace GlobalTheory.PureMatch.Transport
open GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport
open scoped Pointwise

section General
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'}
  {A A' D A₂ A₂' D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
  [Fintype A₂] [DecidableEq A₂] [Fintype A₂'] [DecidableEq A₂'] [Fintype D₂] [DecidableEq D₂]

theorem corr_smul_of (hj : IsLocIso j) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}
    (h : LatCorr j cD Λ Λ₂) (c : kˣ) (c₂ : k'ˣ) (hc : valuation k' (j c) = valuation k' (c₂ : k')) :
    LatCorr j cD (c • Λ) (c₂ • Λ₂) := latCorr_smul hj cD h c c₂ hc

theorem corr_dual_of (hj : IsLocIso j) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}
    (h : LatCorr j cD Λ Λ₂) : LatCorr j cD (dualLat Λ) (dualLat Λ₂) := GlobalTheory.T.dualLattice_correspondingLattices hj cD h

theorem primFrame_corr (hj : IsLocIso j) (rA : A₂ ≃ A) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)}
    {Λ₂ : Submodule 𝒪[k'] (D₂ → k')} (h : LatCorr j cD Λ Λ₂) (Z : Matrix A D k) :
    IsPrimFrame Λ₂ (trM j rA cD Z) ↔ IsPrimFrame Λ Z := GlobalTheory.T.isPrimitiveFrame_matrixTransport_iff hj rA cD h Z

theorem corr_blockLat_of (hj : IsLocIso j) (cD : D₂ ≃ D) {ϖ : kˣ} {ϖ₂ : k'ˣ} (hϖ : IsUnif ϖ) (hϖ₂ : IsUnif ϖ₂)
    (e : ℕ) (P : Finset D) (P₂ : Finset D₂) (hP : ∀ c, c ∈ P₂ ↔ cD c ∈ P) :
    LatCorr j cD (blockLat ϖ e P) (blockLat ϖ₂ e P₂) := GlobalTheory.T.correspondingLattices_blockLattice hj cD hϖ hϖ₂ e P P₂ hP

variable [MeasurableSpace k] [BorelSpace k] [MeasurableSpace k'] [BorelSpace k']

theorem fFun_corr (hj : IsLocIso j) (rA : A₂ ≃ A) (rA' : A₂' ≃ A') (cD : D₂ ≃ D)
    (μ₂ : MeasureTheory.Measure (GL A₂' k')) [μ₂.IsHaarMeasure] (σ₂ : A₂ ⊕ A₂' ≃ D₂) (σ : A ⊕ A' ≃ D)
    (hσ : ∀ s, cD (σ₂ s) = σ (Sum.map rA rA' s)) (ν₂ : k'ˣ →* ℂˣ) (ν : kˣ →* ℂˣ)
    (hν : ∀ x, ν x = ν₂ (Units.map (j : k →* k') x)) (Ψ : Matrix A₂' D₂ k' → ℂ) (Z : Matrix A D k) :
    fFun μ₂ σ₂ ν₂ Ψ (trM j rA cD Z) = fFun (pullMeas hj rA' μ₂) σ ν (fun Y => Ψ (trM j rA' cD Y)) Z :=
  GlobalTheory.T.zetaFunction_transport_localFieldIso hj rA rA' cD μ₂ σ₂ σ hσ ν₂ ν hν Ψ Z

end General
end GlobalTheory.PureMatch.Transport

namespace GlobalTheory.PureMatch.Transport
open GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport
open scoped Pointwise

section General
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'}
  {A A' D A₂ A₂' D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
  [Fintype A₂] [DecidableEq A₂] [Fintype A₂'] [DecidableEq A₂'] [Fintype D₂] [DecidableEq D₂]

theorem latCorr_latA (hj : IsLocIso j) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}
    (h : LatCorr j cD Λ Λ₂) {ϖ : kˣ} {ϖ₂ : k'ˣ} (hϖ : IsUnif ϖ) (hϖ₂ : IsUnif ϖ₂) (e : ℕ) :
    LatCorr j cD (latA ϖ e Λ) (latA ϖ₂ e Λ₂) := by
  refine corr_smul_of hj cD (corr_dual_of hj cD h) _ _ ?_
  have h1 : valuation k' (j ϖ) = valuation k' (ϖ₂ : k') := (isUnif_map hj hϖ).trans hϖ₂.symm
  simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀, map_pow, h1]

theorem trM_mem_matLat (rA : A₂ ≃ A) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}
    (h : LatCorr j cD Λ Λ₂) (Z : Matrix A D k) : trM j rA cD Z ∈ matLat A₂ Λ₂ ↔ Z ∈ matLat A Λ := by
  rw [mem_matLat, mem_matLat]
  refine ⟨fun H a => ?_, fun H r => (h (Z.row (rA r))).2 (H _)⟩
  obtain ⟨r, rfl⟩ := rA.surjective a
  exact (h (Z.row (rA r))).1 (H r)

theorem hasDepth_trM (hj : IsLocIso j) (rA : A₂ ≃ A) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)}
    {Λ₂ : Submodule 𝒪[k'] (D₂ → k')} (h : LatCorr j cD Λ Λ₂) {ϖ : kˣ} {ϖ₂ : k'ˣ} (hϖ : IsUnif ϖ)
    (hϖ₂ : IsUnif ϖ₂) (e : ℕ) (Ξ : Matrix A D k → ℂ) (hΞ : HasDepth ϖ e Λ Ξ) :
    HasDepth ϖ₂ e Λ₂ (fun Y => Ξ (trM j.symm rA.symm cD.symm Y)) := by
  have h1 : valuation k' (j ϖ) = valuation k' (ϖ₂ : k') := (isUnif_map hj hϖ).trans hϖ₂.symm
  have hs : LatCorr j cD (ϖ ^ e • Λ) (ϖ₂ ^ e • Λ₂) := corr_smul_of hj cD h _ _ (by
    simp only [Units.val_pow_eq_pow_val, map_pow]; rw [h1])
  refine ⟨fun Y hY => hΞ.1 _ fun hZ => hY ?_, fun Y W hW => ?_⟩
  · rw [← trM_trM_symm j rA cD Y]; exact (trM_mem_matLat rA cD h _).2 hZ
  · have hW' : trM j.symm rA.symm cD.symm W ∈ matLat A (ϖ ^ e • Λ) := by
      rw [← trM_mem_matLat rA cD hs, trM_trM_symm]; exact hW
    show Ξ (trM j.symm rA.symm cD.symm (Y + W)) = Ξ (trM j.symm rA.symm cD.symm Y)
    rw [show trM j.symm rA.symm cD.symm (Y + W) = trM j.symm rA.symm cD.symm Y + trM j.symm rA.symm cD.symm W by
      ext r c; simp]
    exact hΞ.2 _ _ hW'

variable [MeasurableSpace k] [BorelSpace k] [MeasurableSpace k'] [BorelSpace k']

theorem phiA_trM (hj : IsLocIso j) (rA : A₂ ≃ A) (rA' : A₂' ≃ A') (cD : D₂ ≃ D)
    (μ₂ : MeasureTheory.Measure (GL A₂' k')) [μ₂.IsHaarMeasure] (σ₂ : A₂ ⊕ A₂' ≃ D₂) (σ : A ⊕ A' ≃ D)
    (hσ : ∀ s, cD (σ₂ s) = σ (Sum.map rA rA' s)) (ν₂ : k'ˣ →* ℂˣ) (ν : kˣ →* ℂˣ)
    (hν : ∀ x, ν x = ν₂ (Units.map (j : k →* k') x)) {ϖ : kˣ} {ϖ₂ : k'ˣ} (hϖ : IsUnif ϖ) (hϖ₂ : IsUnif ϖ₂) (e : ℕ)
    {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')} (h : LatCorr j cD Λ Λ₂)
    (Ψ : Matrix A₂' D₂ k' → ℂ) (Z : Matrix A D k) :
    phiA μ₂ σ₂ ν₂ ϖ₂ e Λ₂ Ψ (trM j rA cD Z) =
      phiA (pullMeas hj rA' μ₂) σ ν ϖ e Λ (fun Y => Ψ (trM j rA' cD Y)) Z := by
  classical
  unfold phiA
  rw [primFrame_corr hj rA cD (latCorr_latA hj cD h hϖ hϖ₂ e), fFun_corr hj rA rA' cD μ₂ σ₂ σ hσ ν₂ ν hν]

end General
end GlobalTheory.PureMatch.Transport

namespace GlobalTheory.PureMatch
open GlobalTheory.PureMatch.Transport GlobalTheory.FlipMatch

theorem mem_one_block_iff {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T)
    (w : Pl D.host.E) {i j : Fin D.R.m} (e : Num G i j) (c : (locGrid G t w).Cols i j) :
    c ∈ Assignment.one.block _ _ ↔ GlobalTheory.SquareFlipReach.colE t w e c ∈ blockV e := by
  rcases c with c | c
  · simp [Assignment.block, blockV, GlobalTheory.SquareFlipReach.colE]
  · simp [Assignment.block, blockV, GlobalTheory.SquareFlipReach.colE]

theorem phiA_transport_split_place : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (e : Num G i j) (w : Pl D.host.E) (hw : w ∈ locPl G t) (v : Pl D.host.F) (hv : w.under (𝓞 D.host.F) = v)
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), splitPrime τ = w → ∀ n : ℕ,
    ∃ (μ : @Measure (GL (Fin (spW₁ G i j).rank) (Fv D.host.F v)) Units.instMeasurableSpace)
      (_ : @Measure.IsHaarMeasure _ _ _ Units.instMeasurableSpace μ)
      (σ' : Fin (spW G i j).rank ⊕ Fin (spW₁ G i j).rank ≃ Fin ((spW G i j).rank + (spW₁ G i j).rank)),
      (∀ (Ψ : Matrix (Fin ((locGrid G t w).rank ((i : ℕ), (j : ℕ)))) ((locGrid G t w).Cols i j) (Kw w) → ℂ) Z,
        phiA (haarVol ((givenLevel G t w ((i : ℕ), (j : ℕ))).map invT)) (stdSplit ((locGrid G t w).rank_square i j))
          ((locGrid G t w).nu i j) (unifAt w) n (blockLat (unifAt w) n (Assignment.one.block _ _)) Ψ (trA t hv e Z) =
        phiA μ σ' (((locGrid G t w).nu i j).comp (Units.map (GlobalTheory.LFun.complMap hv).toMonoidHom)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n
          (blockLat (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n (blockV e)) (fun Y => Ψ (trB t hv e Y)) Z) ∧
      ∀ Ξ, HasDepth (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n (blockLat (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n (blockV e)) Ξ →
        ∃ Ξ', HasDepth (unifAt w) n (blockLat (unifAt w) n (Assignment.one.block _ _)) Ξ' ∧ ∀ Y, Ξ' (trB t hv e Y) = Ξ Y := by
  intro D T L sc G μ₀ hL t i j e w hw v hv τ hτ n
  subst hτ
  have hjj := isLocIso_complEquiv τ hv
  have hO := GivenAdm.givenLevel_open (G := G) hL hw ((i : ℕ), (j : ℕ))
  have hO' := isOpen_map_invT hO.1 hO.2
  let J := (givenLevel G t (splitPrime τ) ((i : ℕ), (j : ℕ))).map invT
  have hHaar : @Measure.IsHaarMeasure _ _ _ Units.instMeasurableSpace (haarVol J) :=
    isHaarMeasure_haarVol hO'.1 hO'.2
  have hϖv : IsUnif (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv D.host.F v)).choose_spec
  have hc := corr_blockLat_of hjj (GlobalTheory.SquareFlipReach.colE t (splitPrime τ) e) hϖv (isUnif_unifAt _) n (blockV e)
      (Assignment.one.block _ _) (mem_one_block_iff t _ e)
  refine ⟨pullMeas hjj (rowB t (splitPrime τ) i j) (haarVol J), ?_,
    (Equiv.sumCongr (GlobalTheory.SquareFlipReach.rowE t (splitPrime τ) i j).symm (rowB t (splitPrime τ) i j).symm).trans
      ((stdSplit ((locGrid G t (splitPrime τ)).rank_square i j)).trans (GlobalTheory.SquareFlipReach.colE t (splitPrime τ) e)),
    fun Ψ Z => ?_, fun Ξ hΞ => ?_⟩
  · exact @isHaar_pullMeas _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      hjj (rowB t (splitPrime τ) i j) (haarVol J) hHaar
  · exact @phiA_trM
      _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _
      hjj (GlobalTheory.SquareFlipReach.rowE t (splitPrime τ) i j) (rowB t (splitPrime τ) i j)
      (GlobalTheory.SquareFlipReach.colE t (splitPrime τ) e) (haarVol J) hHaar
      _ _ (fun s => by simp) _ _ (fun x => rfl) _ _ hϖv
      (isUnif_unifAt _) n _ _ hc Ψ Z
  · exact ⟨_, hasDepth_trM hjj (rowB t (splitPrime τ) i j) (GlobalTheory.SquareFlipReach.colE t (splitPrime τ) e) hc hϖv
      (isUnif_unifAt _) n Ξ hΞ, fun Y => by
        show Ξ (trM _ _ _ (trM (GlobalTheory.LFun.SplitTie.complEquiv τ hv) (rowB t (splitPrime τ) i j)
          (GlobalTheory.SquareFlipReach.colE t (splitPrime τ) e) Y)) = Ξ Y
        rw [trM_symm_trM]⟩

end GlobalTheory.PureMatch
end
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


theorem _root_.GlobalTheory.T.definiteBottom_stage_transport_same_constants : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} (W : G.Weil) (i j : Fin D.R.m) {A A' WW B B' WW₁ : HSp D} (X : Tri T A A' WW) (Y : Tri T B B' WW₁),
  IsBottomTri W i j X → GlobalTheory.SqTower.IsStageC W i j 0 0 Y →
  ∃ Y' : Tri T A A' WW, GlobalTheory.SqTower.IsStageC W i j 0 0 Y' ∧ ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → Y'.IsConst W.ψ W.θ c := by
  first | exact @GlobalTheory.TriMove.transport_bottom | exact GlobalTheory.TriMove.transport_bottom | (intros; apply GlobalTheory.TriMove.transport_bottom <;> assumption)
end

section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead


theorem _root_.GlobalTheory.T.weilAction_integralPoint_cosetVector_eq : ∀ {D : D7}, GlobalTheory.NormSum.Inp D → ∀ {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) {𝔪 : Ideal (𝓞 D.host.E)}, 𝔪 ≠ ⊥ →
  ∀ (o : ℕ) (k : Formalism.MainNotions.StandardLatticesGL3.GA D P.a), k ∈ intG D P.a → ∀ c : ℂ, P.W.Om k 1 P.e0 = c • P.e0 →
  ∀ z : Matrix (Fin P.d) (Fin P.a) D.host.E, IsIntE z → Approx 𝔪 o k z →
  P.W.Om k 1 (cosetVec P 𝔪 o) = c • cosV δ 𝔪 z P.e0 := by
  first | exact @GlobalTheory.StdRead.Move.om_cosetVec | exact GlobalTheory.StdRead.Move.om_cosetVec | (intros; apply GlobalTheory.StdRead.Move.om_cosetVec <;> assumption)
end

section


theorem _root_.GlobalTheory.T.toricPeriodZeta_of_latticeValue_statements : GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.LatVal.LatIntRam → GlobalTheory.LatVal.LatIntUnr → GlobalTheory.LatVal.LatAlg → GlobalTheory.LatVal.LatConj → GlobalTheory.Mem.LiteralAutomorphy.JoinOut := by
  first | exact @GlobalTheory.JoinFun.joinOut_of_lat | exact GlobalTheory.JoinFun.joinOut_of_lat | (intros; apply GlobalTheory.JoinFun.joinOut_of_lat <;> assumption)
end
