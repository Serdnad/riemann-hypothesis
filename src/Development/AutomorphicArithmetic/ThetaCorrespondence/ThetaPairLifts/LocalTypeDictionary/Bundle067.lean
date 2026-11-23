module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle627
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle655
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.EndomorphismLawFromFirstRowTwist
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle004
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle361
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle425
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle586
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle338
public import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.HoweDualityUnramifiedAllPlaces
import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.Imports
import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.Bundle003
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle020
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle048
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle407
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle177

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.FirstRowTermLaw
end GlobalTheory.FirstRowTermLaw
namespace GlobalTheory.FirstRowTermLaw

theorem lift_splits_locally : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ →
    ∀ (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
    ∀ (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J) (c : ℂ),
      ch.W.om (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1) (ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) = c • ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) →
    ∀ (xs : ∀ j : Fin D.R.m, WO (ch.G.pS (.top t j)) (ch.G.pT (.top t j)))
      (ys : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))),
      (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) * c *
        (τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) *
          ∏ i, Function.update (fun i => (d.2 i).fn) (GlobalTheory.FirstRowVertex.firstIx D)
            (fun y => (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).fn (actO (ch.G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ y)) i (ys i)) =
      τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) * ∏ i, (d.2 i).fn (ys i) := by
  intro hP hS
  obtain ⟨a₁, h₁⟩ := _root_.GlobalTheory.T.endomorphism_law_from_first_row_twist hP hS
  refine ⟨a₁, fun ε CF hC => ?_⟩
  obtain ⟨x₁, hc₁⟩ := h₁ ε CF hC
  refine ⟨x₁, ?_⟩
  intro D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi hsc t a β hβ τ hτ k hkl hk c hc xs ys
  obtain ⟨lam, hlam, hscal⟩ := hc₁ D large₂ e hx Γ Pl0 T A Ks R F s ch hi hsc t a k hkl hk c hc
  have hL : (τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) *
      ∏ i, Function.update (fun i => (d.2 i).fn) (GlobalTheory.FirstRowVertex.firstIx D) (fun y => (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).fn ((actO (ch.G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) y)) i (ys i)) =
      τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) * ∏ i, (d.2 i).fn (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) ((actO (ch.G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) (ys (GlobalTheory.FirstRowVertex.firstIx D))) i) :=
    sum_update_comp τ (fun d j => (d.1 j).fn) (fun d i => (d.2 i).fn) (GlobalTheory.FirstRowVertex.firstIx D) (actO (ch.G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) xs ys
  rw [hL]
  exact law_gen ch.S.toGridChoice (Set.mem_univ t) hτ k lam hlam _ hscal xs ys
end GlobalTheory.FirstRowTermLaw
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.leading_coefficient_term_law_theta : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ →
    ∀ (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
    ∀ (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J) (c : ℂ),
      ch.W.om (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1) (ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) = c • ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) →
    ∀ (xs : ∀ j : Fin D.R.m, WO (ch.G.pS (.top t j)) (ch.G.pT (.top t j)))
      (ys : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))),
      (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) * c *
        (τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) *
          ∏ i, Function.update (fun i => (d.2 i).fn) (GlobalTheory.FirstRowVertex.firstIx D)
            (fun y => (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).fn (actO (ch.G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ y)) i (ys i)) =
      τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) * ∏ i, (d.2 i).fn (ys i) := by
  first | exact @_root_.GlobalTheory.FirstRowTermLaw.lift_splits_locally | exact _root_.GlobalTheory.FirstRowTermLaw.lift_splits_locally | (intros; apply _root_.GlobalTheory.FirstRowTermLaw.lift_splits_locally <;> assumption)
end
end

section

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix
noncomputable section
namespace UpperTheory.Lit.HoweDuality
open GlobalTheory.HoweGlobalPair
theorem stageV_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om N →
        N ≠ G.M.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p f = 0) →
    ∀ N, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb) N →
      ∀ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), Xc.T ⊆ T →
        GlobalTheory.HoweGlobal.algAt G.M Bs.ψ Bs.emb T ≤ N ∨
          ∀ Φ ∈ N, Φ ∈ GlobalTheory.HoweGlobal.algAt G.M Bs.ψ Bs.emb T → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf Φ 0 := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM hreal N hN T hT
  classical
  obtain ⟨L, hL, hrange⟩ := GlobalTheory.T.exists_linear_tensor_polyVacuum_pureTensors G.M Bs.ψ Bs.emb hM.triple.geo.hM.std T
  have hloc := _root_.GlobalTheory.T.global_howe_transfer_real_place hP F E σ Bs a a' G Xc om om' R Rf hM hreal
  have hfl := fun v => locV hM v
  obtain ⟨h1, h2, h3, h4⟩ := _root_.GlobalTheory.T.global_howe_tensor_product_transfer hP F E σ Bs a a' G Xc om om' R Rf hM N hN T L hL
  have key := tens (ι := T) (M₀ := ↥(G.M.Pol Bs.ψ Bs.emb))
    (M := fun v : T => ↥(SB (Fin a × Fin (a + a') → Fv F v.1)))
    (GlobalTheory.HoweGlobal.opInf Bs G om) (fun v => GlobalTheory.HoweGlobal.opFin G om v.1)
    (GlobalTheory.HoweGlobal.relInf Bs G om) (fun v => GlobalTheory.HoweGlobal.relFin G om v.1)
    (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype) (fun v => Rf.p v.1 ∘ₗ (SB _).subtype)
    hloc.1 (fun v => GlobalTheory.TripleAssembly.rank_SB_adicCompletion_le F _ v.1) hloc.2.1 hloc.2.2.1 hloc.2.2.2.1 hloc.2.2.2.2
    (fun v => (hfl v.1).1) (fun v => (kerV hM v.1).2.1) (fun v => (hfl v.1).2) (fun v => (kerV hM v.1).2.2.2)
    (N.comap L) h1 h2 h3 h4
  rcases key with htop | hker
  · left
    intro Φ hΦ
    obtain ⟨t, rfl⟩ := hrange hΦ
    have ht : t ∈ N.comap L := by rw [htop]; exact Submodule.mem_top
    exact ht
  · right
    intro Φ hΦN hΦT
    obtain ⟨t, rfl⟩ := hrange hΦT
    have ht0 := hker (show t ∈ N.comap L from hΦN)
    obtain ⟨m, f, φ, rfl⟩ := GlobalTheory.HoweGlobal.decomp t
    refine ⟨T, hT, m, 0, fun j => ((f j : ↥(G.M.Pol Bs.ψ Bs.emb)) : SInf F (Fin a × Fin (a + a'))),
      fun j v => if h : v ∈ T then ((φ j ⟨v, h⟩ : ↥(SB _)) : (Fin a × Fin (a + a') → Fv F v) → ℂ) else G.M.vac v,
      Fin.elim0, Fin.elim0, fun j => ⟨(f j).2, fun v => ?_, fun v hv => by simp only [dif_neg hv]⟩, fun j => Fin.elim0 j, ?_, ?_, ?_⟩
    · by_cases h : v ∈ T
      · simp only [dif_pos h]; exact (φ j ⟨v, h⟩).2
      · simp only [dif_neg h]; exact (hM.triple.geo.hM.vac v).1

    · rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => hL _ _ _ (fun v h => by simp only [dif_pos h]) (fun v h => by simp only [dif_neg h])
    · simp

    · rw [LinearMap.mem_ker, map_sum] at ht0
      rw [Fin.sum_univ_zero, ← ht0]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [TensorProduct.map_tmul, PiTensorProduct.map_tprod]
      simp
theorem allV_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om N →
        N ≠ G.M.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p f = 0) →
    ∀ N, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb) N →
      N ≠ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb →
      ∀ ΦD ∈ N, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf ΦD 0 := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM hreal N hN hne ΦD hΦ
  by_contra hc
  obtain ⟨T, hT, hΦT⟩ := GlobalTheory.HoweGlobal.exists_algAt G.M Bs.ψ Bs.emb (hN.1.1 hΦ) Xc.T
  apply hne
  refine le_antisymm hN.1.1 fun Ψ hΨ => ?_
  obtain ⟨T', hT', hΨT'⟩ := GlobalTheory.HoweGlobal.exists_algAt G.M Bs.ψ Bs.emb hΨ T
  rcases _root_.UpperTheory.Lit.HoweDuality.stageV_alt hP F E σ Bs a a' G Xc om om' R Rf hM hreal N hN T' (hT.trans hT') with h | h
  · exact h hΨT'
  · exact absurd (h ΦD hΦ (GlobalTheory.HoweGlobal.algAt_mono G.M Bs.ψ Bs.emb hT' hΦT)) hc
theorem twisted_theta_kernel_condition : _root_.GlobalTheory.T.TwistedThetaKernelCondition := fun hR hP F E _ _ _ _ _ σ Bs a a' G Xc om om' _ R Rf hM N hN hne =>
  _root_.UpperTheory.Lit.HoweDuality.allV_alt hP F E σ Bs a a' G Xc om om' R Rf hM (GlobalTheory.T.howeDuality_realPlaces_trivialChar_fockLift hR F E σ Bs a a' G Xc om om' R Rf hM) N hN hne
theorem twisted_theta_jet_condition : _root_.GlobalTheory.T.TwistedThetaJetCondition := fun hR _ F E _ _ _ _ _ σ a a' Bs G Xc om om' R Rf hM N hN hne =>
  allVp F E σ Bs a a' G Xc om om' R Rf hM (GlobalTheory.T.howeDuality_realPlaces_trivialChar_fockLift_smallPair hR F E σ Bs a a' G Xc om om' R Rf hM) N hN hne
end UpperTheory.Lit.HoweDuality
end
end
end
