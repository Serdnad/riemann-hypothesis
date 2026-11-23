module

public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1203
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1433
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportOfTwist
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
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
import Mathlib.Tactic.Basify
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

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical



namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

section AlgExPf

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem keepQ {Q : Submodule ℂ H} {Γ : Type} {op : Γ → (H →L[ℂ] H)} {v : Γ → ℂ}
    (hQ : ∀ x, ∀ f ∈ Q, op x f ∈ Q ∧ star (op x) f ∈ Q) {y : (H →L[ℂ] H) × ℂ}
    (hy : y ∈ StarAlgebra.adjoin ℂ (Set.range fun x => (op x, v x))) :
    (∀ f ∈ Q, y.1 f ∈ Q) ∧ ∀ f ∈ Q, (star y.1) f ∈ Q := by
  induction hy using StarAlgebra.adjoin_induction with
  | mem x h =>
    obtain ⟨a, rfl⟩ := h
    exact ⟨fun f hf => (hQ a f hf).1, fun f hf => (hQ a f hf).2⟩
  | algebraMap r =>
    have h1 : (algebraMap ℂ ((H →L[ℂ] H) × ℂ) r).1 = r • (1 : H →L[ℂ] H) := by
      rw [Prod.algebraMap_apply, Algebra.algebraMap_eq_smul_one]
    rw [h1]
    refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · simpa using Q.smul_mem r hf
    · simpa [star_smul] using Q.smul_mem (star r) hf
  | add x y _ _ hx hy =>
    refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · exact Q.add_mem (hx.1 f hf) (hy.1 f hf)
    · rw [Prod.fst_add, star_add]
      exact Q.add_mem (hx.2 f hf) (hy.2 f hf)
  | mul x y _ _ hx hy =>
    refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · exact hx.1 _ (hy.1 f hf)
    · rw [Prod.fst_mul, star_mul]
      exact hy.2 _ (hx.2 f hf)
  | star x _ hx =>
    refine ⟨fun f hf => hx.2 f hf, fun f hf => ?_⟩
    have : (star (star x).1) = x.1 := by rw [Prod.fst_star, star_star]
    rw [this]
    exact hx.1 f hf

end AlgExPf

end UpperTheory.Zero.ConvolutionTheory.EB

theorem UpperTheory.Zero.ConvolutionTheory.EB.algEx :
    UpperTheory.Zero.ConvolutionTheory.EB.AlgEx := by
  intro H _ _ _ Q _ Γ op v hc hs hQ
  let s : Set ((H →L[ℂ] H) × ℂ) := Set.range fun x => (op x, v x)
  have hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact Prod.ext (hc x y).eq (mul_comm _ _)
  have hcs : ∀ a ∈ s, ∀ b ∈ s, a * star b = star b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact Prod.ext (hs x y).eq (mul_comm _ _)
  letI : IsMulCommutative (StarAlgebra.adjoin ℂ s) :=
    StarAlgebra.isMulCommutative_adjoin ℂ
      (fun x hx => ⟨(hcs x hx x hx).symm⟩)
      (fun x hx y hy _ => hcomm x hx y hy)
      (fun x hx y hy _ => hcs x hx y hy)
  letI : CommRing (StarAlgebra.adjoin ℂ s) := { (inferInstance : Ring _) with
    mul_comm := fun a b => mul_comm' a b }
  have keep : ∀ y : StarAlgebra.adjoin ℂ s, (∀ f ∈ Q, y.1.1 f ∈ Q) ∧ ∀ f ∈ Q, (star y.1.1) f ∈ Q :=
    fun y => UpperTheory.Zero.ConvolutionTheory.EB.keepQ hQ y.2
  let res : StarAlgebra.adjoin ℂ s → (Q →L[ℂ] Q) := fun y =>
    (y.1.1 ∘L Q.subtypeL).codRestrict Q fun q => (keep y).1 q q.2
  let R : StarAlgebra.adjoin ℂ s →⋆ₐ[ℂ] (Q →L[ℂ] Q) :=
    { toFun := res
      map_one' := by ext q; rfl
      map_mul' := fun a b => by ext q; rfl
      map_zero' := by ext q; rfl
      map_add' := fun a b => by ext q; rfl
      commutes' := fun r => by
        ext q
        have h1 : ((algebraMap ℂ (StarAlgebra.adjoin ℂ s) r).1).1 = r • (1 : H →L[ℂ] H) := by
          show (algebraMap ℂ ((H →L[ℂ] H) × ℂ) r).1 = _
          rw [Prod.algebraMap_apply, Algebra.algebraMap_eq_smul_one]
        have h2 : algebraMap ℂ (Q →L[ℂ] Q) r = r • (1 : Q →L[ℂ] Q) :=
          Algebra.algebraMap_eq_smul_one r
        show ((algebraMap ℂ (StarAlgebra.adjoin ℂ s) r).1).1 (q : H) = _
        rw [h1, h2]
        simp
      map_star' := fun y => by
        show res (star y) = star (res y)
        rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
        intro p q
        show inner ℂ (star y.1.1 (p : H)) (q : H) = inner ℂ (p : H) (y.1.1 (q : H))
        rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left] }
  let ι : Γ → StarAlgebra.adjoin ℂ s := fun x => ⟨(op x, v x), StarAlgebra.subset_adjoin ℂ s ⟨x, rfl⟩⟩
  have all : ∀ y : StarAlgebra.adjoin ℂ s, y ∈ StarAlgebra.adjoin ℂ (Set.range ι) := by
    intro y
    induction y using StarAlgebra.adjoin_induction_subtype with
    | mem x h =>
      obtain ⟨a, rfl⟩ := h
      exact StarAlgebra.subset_adjoin ℂ _ ⟨a, rfl⟩
    | algebraMap r => exact algebraMap_mem _ r
    | add x y hx hy => exact add_mem hx hy
    | mul x y hx hy => exact mul_mem hx hy
    | star x hx => exact star_mem hx
  have top : StarAlgebra.adjoin ℂ (Set.range ι) = ⊤ := eq_top_iff.2 fun y _ => all y
  exact ⟨{ B := StarAlgebra.adjoin ℂ s
           R := R
           P := (StarAlgHom.snd ℂ (H →L[ℂ] H) ℂ).comp (StarSubalgebra.subtype _)
           F := (StarAlgHom.fst ℂ (H →L[ℂ] H) ℂ).comp (StarSubalgebra.subtype _)
           ι := ι
           hF := fun _ => rfl
           hP := fun _ => rfl
           hR := fun _ _ => rfl
           top := top }⟩
end
end

section

theorem UpperTheory.Zero.ConvolutionTheory.EB.powNorm :
    UpperTheory.Zero.ConvolutionTheory.EB.PowNorm := by
  intro H _ _ Q U ρ hQ hU k
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans hU
  have hb : ∀ f ∈ Q, ‖U f‖ ≤ ρ * ‖f‖ := by
    intro f hf
    exact (U ∘L Q.subtypeL).le_of_opNorm_le hU ⟨f, hf⟩
  have key : ∀ k : ℕ, ∀ f ∈ Q, (U ^ k) f ∈ Q ∧ ‖(U ^ k) f‖ ≤ ρ ^ k * ‖f‖ := by
    intro k
    induction k with
    | zero =>
      intro f hf
      simp [hf]
    | succ k ih =>
      intro f hf
      obtain ⟨h1, h2⟩ := ih f hf
      have e : (U ^ (k + 1)) f = U ((U ^ k) f) := by
        rw [pow_succ']
        rfl
      rw [e]
      refine ⟨hQ _ h1, (hb _ h1).trans ?_⟩
      rw [pow_succ', mul_assoc]
      exact mul_le_mul_of_nonneg_left h2 hρ
  refine ⟨fun f hf => (key k f hf).1, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (pow_nonneg hρ k) fun q => ?_
  exact (key k q q.2).2
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical



attribute [local instance] borelG borelF borelA borelH

theorem UpperTheory.Zero.ConvolutionTheory.EB.satCard :
    UpperTheory.Zero.ConvolutionTheory.EB.SatCard := by
  intro E _ _ _ n D w B h
  obtain ⟨b, hb, rfl⟩ := h
  rw [Multiset.card_sum]
  exact (Finset.sum_congr rfl fun i _ => (hb i).card).trans D.sum
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical



namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

private theorem ev_tendsto {ι : Type} (e : Ex ι) {x : ℕ → ι → ℂ} {y : ι → ℂ}
    (h : ∀ i, Tendsto (fun k => x k i) atTop (𝓝 (y i))) :
    Tendsto (fun k => e.ev (x k)) atTop (𝓝 (e.ev y)) := by
  induction e with
  | one => exact tendsto_const_nhds
  | gen i => exact h i
  | smul c a ih => exact ih.const_mul c
  | add a b iha ihb => exact iha.add ihb
  | mul a b iha ihb => exact iha.mul ihb

private theorem satEig_top_ne_zero (q n : ℕ) {C : Multiset ℂˣ} (hC : C.card = n) : satEig q n C n ≠ 0 := by
  intro h0
  have h := GlobalTheory.LFun.ConjPlace.satEig_inv_mul (q := q) hC (le_refl n)
  rw [h0, mul_zero, Nat.sub_self, GlobalTheory.LFun.ConjPlace.satEig_zero] at h
  exact zero_ne_one h

private theorem satEig_inv_eq (q n : ℕ) {B : Multiset ℂˣ} (hB : B.card = n) {i : ℕ} (hi : i ≤ n) :
    satEig q n (inv B) i = satEig q n B (n - i) / satEig q n B n := by
  rw [eq_div_iff (satEig_top_ne_zero q n hB)]
  exact GlobalTheory.LFun.ConjPlace.satEig_inv_mul hB hi

private theorem satEig_inv_tendsto (q n : ℕ) {B : ℕ → Multiset ℂˣ} {C : Multiset ℂˣ} (hB : ∀ k, (B k).card = n)
    (hC : C.card = n) (h : ∀ i : ℕ, Tendsto (fun k => satEig q n (B k) i) atTop (𝓝 (satEig q n C i)))
    {i : ℕ} (hi : i ≤ n) :
    Tendsto (fun k => satEig q n (inv (B k)) i) atTop (𝓝 (satEig q n (inv C) i)) := by
  rw [satEig_inv_eq q n hC hi]
  simp only [fun k => satEig_inv_eq q n (hB k) hi]
  exact (h (n - i)).div (h n) (satEig_top_ne_zero q n hC)

private theorem qV_cPl {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) :
    Formalism.UG.qV E (cPl w) = Formalism.UG.qV E w :=
  GlobalTheory.UnrEuler.ConjFac.absNorm_conjSrc _ w

theorem valLim : ValLim := by
  intro E _ _ _ a b T e₁ e₂ B₁ B₂ C₁ C₂ h
  unfold UpperTheory.V.Z.Tf.GlobalTraceComparison.val
  refine tendsto_finsetProd _ fun w hw => Tendsto.mul ?_ ?_
  · obtain ⟨-, -, -, h₁, h₂⟩ := h w (Or.inl hw)
    exact ev_tendsto _ fun p => (h₁ p.1).mul (h₂ p.2)
  · have hcc : cPl (cPl w) = w := ((UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.places E).2.1 w).1
    obtain ⟨c₁, c₂, hk, h₁, h₂⟩ := h (cPl w) (Or.inr (hcc.symm ▸ hw))
    rw [qV_cPl] at h₁ h₂
    refine ev_tendsto _ fun p => Tendsto.mul ?_ ?_
    · exact satEig_inv_tendsto _ a (fun k => (hk k).1) c₁ h₁ (Nat.lt_succ_iff.1 p.1.2)
    · exact satEig_inv_tendsto _ b (fun k => (hk k).2) c₂ h₂ (Nat.lt_succ_iff.1 p.2.2)

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical



namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

open PositivityTheory.Rg.Tf.Loc (twConj)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem transl_eq {u : GL (Fin n) E} (hu : IsTransl u) (d : GL (Fin n) E) (x : GA E n) :
    gFin (twConj (thetaA E n) x (ratGL E n d)) * (ratF E n u)⁻¹ =
      (GeneralLinearGroup.map (pFin E) x)⁻¹ * ratF E n (d * u⁻¹) * thF E n (GeneralLinearGroup.map (pFin E) x) := by
  have h := congrArg (GeneralLinearGroup.map (pFin E)) (adeleqof_twist translAd_holds hu d x)
  simp only [map_mul, map_inv, adeleqof_pFin_thetaGL, adeleqof_pFin_ratGL] at h
  rw [map_mul (ratF E n), map_inv]
  exact h

private theorem transl_norm {u : GL (Fin n) E} (hu : IsTransl u) (d : GL (Fin n) E) (x : GA E n) :
    (gFin (twConj (thetaA E n) x (ratGL E n d)) * (ratF E n u)⁻¹) *
        thF E n (gFin (twConj (thetaA E n) x (ratGL E n d)) * (ratF E n u)⁻¹) =
      (GeneralLinearGroup.map (pFin E) x)⁻¹ * ratF E n (nrm d) * GeneralLinearGroup.map (pFin E) x := by
  rw [transl_eq hu]
  set c := GeneralLinearGroup.map (pFin E) x
  set r := ratF E n (d * u⁻¹) with hr0
  set s := ratF E n (thE E n (d * u⁻¹)) with hs0
  have hr : thF E n r = s := by
    rw [hr0, hs0, GlobalTheory.EulerTw.Comm.thF_ratF]
  rw [← poleq_norm E n u hu d, map_mul (ratF E n), ← hr0, ← hs0, map_mul, map_mul, map_inv,
    GlobalTheory.EulerTw.Comm.thF_thF, hr]
  group

private theorem transl_charpoly (w : Pl E) {u : GL (Fin n) E} (hu : IsTransl u) (d : GL (Fin n) E) (x : GA E n) :
    (GeneralLinearGroup.map (pLoc E w) ((gFin (twConj (thetaA E n) x (ratGL E n d)) * (ratF E n u)⁻¹) *
        thF E n (gFin (twConj (thetaA E n) x (ratGL E n d)) * (ratF E n u)⁻¹))).val.charpoly =
      (nrm d).val.charpoly.map (algebraMap E (w.adicCompletion E)) := by
  rw [transl_norm hu, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
    Matrix.charpoly_units_conj']
  rw [← Matrix.charpoly_map]
  rfl

private theorem sep_of {a b : ℕ} {S : Set (Pl E)} {φ₁ φ₂ : ∀ w : Pl E, LF a b w} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂)
    {w : Pl E} (hwS : w ∈ S) (hsp : IsSplitAt w)
    (hreg : ∀ y z, φ₁ w y ≠ 0 → φ₂ w z ≠ 0 → ((y * z).1.val.charpoly * (y * z).2.val.charpoly).Separable)
    (y : Gf E a b) (hne : finFn S φ₁ φ₂ y ≠ 0) :
    (GeneralLinearGroup.map (pLoc E w) (y.1 * thF E a y.1)).val.charpoly.Separable ∧
      (GeneralLinearGroup.map (pLoc E w) (y.2 * thF E b y.2)).val.charpoly.Separable := by
  have hf := GlobalTheory.CompanionTheory.SuppFinTw.factors_ne h₁ h₂ y hne w hwS
  have hs := hreg (atW w y) (atW w (thP E a b y)) hf.1 (hf.2 hsp)
  have e₁ : (atW w y * atW w (thP E a b y)).1 = GeneralLinearGroup.map (pLoc E w) (y.1 * thF E a y.1) :=
    (map_mul _ _ _).symm
  have e₂ : (atW w y * atW w (thP E a b y)).2 = GeneralLinearGroup.map (pLoc E w) (y.2 * thF E b y.2) :=
    (map_mul _ _ _).symm
  rw [e₁, e₂] at hs
  exact ⟨Polynomial.Separable.of_mul_left hs, Polynomial.Separable.of_mul_right hs⟩

theorem _root_.UpperTheory.Zero.ConvolutionTheory.EB.regS : RegS := by
  intro E _ _ _ a b S u₁ u₂ hu₁ hu₂ φ₁ φ₂ h₁ h₂ hw
  obtain ⟨w, hwS, hsp, hreg⟩ := hw
  refine ⟨fun d x h₂' hne => ?_, fun d x h₁' hne => ?_⟩
  · have hs := (sep_of h₁ h₂ hwS hsp hreg _ hne).1
    simp only [Prod.fst_mul, Prod.fst_inv] at hs
    rw [transl_charpoly w hu₁] at hs
    exact (Polynomial.separable_map _).1 hs
  · have hs := (sep_of h₁ h₂ hwS hsp hreg _ hne).2
    simp only [Prod.snd_mul, Prod.snd_inv] at hs
    rw [transl_charpoly w hu₂] at hs
    exact (Polynomial.separable_map _).1 hs

end UpperTheory.Zero.ConvolutionTheory.EB

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical



attribute [local instance] borelG borelF borelA borelH

theorem UpperTheory.Zero.ConvolutionTheory.EB.lvEx :
    UpperTheory.Zero.ConvolutionTheory.EB.LvEx := by
  intro E _ _ _ a b Z φ h
  have key : ∀ w : Pl E, ∃ (A : Subgroup (GLw a w)) (B : Subgroup (GLw b w)),
      IsOpen (A : Set (GLw a w)) ∧ IsOpen (B : Set (GLw b w)) ∧ A ≤ KGL w (n := a) ∧ B ≤ KGL w (n := b) ∧
      (w ∉ Z → A = KGL w (n := a) ∧ B = KGL w (n := b)) ∧ (w ∈ Z → IsHecke (A.prod B) (φ w)) := by
    intro w
    by_cases hw : w ∈ Z
    · obtain ⟨K', ho, hle, hH⟩ := h w hw
      refine ⟨K'.comap (MonoidHom.inl _ _), K'.comap (MonoidHom.inr _ _), ?_, ?_, ?_, ?_,
        fun h' => absurd hw h', fun _ => ⟨hH.1, ?_⟩⟩
      · exact ho.preimage (continuous_id.prodMk continuous_const)
      · exact ho.preimage (continuous_const.prodMk continuous_id)
      · intro x hx
        exact (hle hx).1
      · intro y hy
        exact (hle hy).2
      · rintro ⟨x, y⟩ ⟨hx, hy⟩ g
        have hxy : ((x, y) : GLw a w × GLw b w) ∈ K' := by
          have := K'.mul_mem hx hy
          simpa using this
        exact hH.2 _ hxy g
    · exact ⟨KGL w (n := a), KGL w (n := b), (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1,
        (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1, le_rfl, le_rfl,
        fun _ => ⟨rfl, rfl⟩, fun h' => absurd h' hw⟩
  choose A B hA hB hA' hB' hoff hfix using key
  exact ⟨⟨A, B, hA, hB, hA', hB', hoff⟩, hfix⟩
end
end
