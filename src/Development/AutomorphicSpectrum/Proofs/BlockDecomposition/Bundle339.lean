module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle317
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle302
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle323
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle316
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle319
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.EcSmooth

theorem continuous_glEmb (k : Type) [Field k] [TopologicalSpace k] [IsTopologicalRing k] (n : ℕ) :
    Continuous (glEmb k n) := by
  have hm : Continuous (glEmbMat k n) := by
    refine continuous_matrix fun a b => ?_
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => simpa [glEmbMat] using continuous_const
      | cast b => simpa [glEmbMat] using continuous_const
    | cast a =>
      induction b using Fin.lastCases with
      | last => simpa [glEmbMat] using continuous_const
      | cast b =>
        simpa [glEmbMat] using (continuous_id.matrix_elem a b)
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact hm.comp Units.continuous_val
  · exact hm.comp (Units.continuous_coe_inv)

theorem continuous_sEmb (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) : Continuous (sEmb k n) :=
  Continuous.subtype_mk ((continuous_glEmb k (n + 1)).comp continuous_subtype_val) _

theorem isOpen_rightInv {M X : Type} [Group M] [TopologicalSpace M] [IsTopologicalGroup M] (e : M → X) (A : Set M)
    (hA : IsOpen A) (h1 : (1 : M) ∈ A) (h : ∀ g ∈ A, ∀ m, e (m * g) = e m) :
    IsOpen {g : M | ∀ m, e (m * g) = e m} := by
  let T : Subgroup M :=
    { carrier := {g | ∀ m, e (m * g) = e m}
      mul_mem' := by
        intro a b ha hb m
        rw [← mul_assoc, hb, ha]
      one_mem' := by
        intro m
        rw [mul_one]
      inv_mem' := by
        intro a ha m
        have := ha (m * a⁻¹)
        rw [inv_mul_cancel_right] at this
        exact this.symm }
  exact T.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (hA.mem_nhds h1) h)

section Fix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ}
  {τ : MRep k (i + 1)} {σ : GRep k (t + 1)}

def fixX (f : XS τ σ) : Set (Mir k ((i + 1) + (t + 1))) :=
  {x | ind (HPG k (i + 1) (t + 1)) (sigX τ σ) x (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))).1 =
    (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))).1}

theorem isOpen_fixX (f : XS τ σ) : IsOpen (fixX f) :=
  (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))).2

theorem one_mem_fixX (f : XS τ σ) : (1 : Mir k ((i + 1) + (t + 1))) ∈ fixX f := by
  show ind (HPG k (i + 1) (t + 1)) (sigX τ σ) 1 _ = _
  rw [map_one]
  rfl

theorem evX_mul_of_mem (f : XS τ σ) {x : Mir k ((i + 1) + (t + 1))} (hx : x ∈ fixX f)
    (p : Mir k ((i + 1) + (t + 1))) : evX f (p * x) = evX f p :=
  congrArg (fun w : indSpace (HPG k (i + 1) (t + 1)) (sigX τ σ) => w.1 p) hx

theorem intC_mul (ψ : AddChar k Circle) (f : XS τ σ) (m g : Mir k ((i + 1) + t))
    (h : sEmb k ((i + 1) + t) g ∈ fixX f) :
    intC ψ f (sEmb k ((i + 1) + t) (m * g)) = intC ψ f (sEmb k ((i + 1) + t) m) := by
  unfold intC
  congr 1
  funext d
  have h2 : dEmb k i t d * sEmb k ((i + 1) + t) (m * g) =
      (dEmb k i t d * sEmb k ((i + 1) + t) m) * sEmb k ((i + 1) + t) g := by
    rw [MonoidHom.map_mul, mul_assoc]
  rw [h2]
  exact congrArg (fun v => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • v)
    (evX_mul_of_mem f h (dEmb k i t d * sEmb k ((i + 1) + t) m))

theorem eC_mul (ψ : AddChar k Circle) (f : XS τ σ) (m g : Mir k ((i + 1) + t))
    (h : sEmb k ((i + 1) + t) g ∈ fixX f) (h2 : dpowM (k := k) ((i + 1) + t) (-1 / 2) g = 1) :
    eC ψ f (m * g) = eC ψ f m := by
  have h5 : dpowM (k := k) ((i + 1) + t) (-1 / 2) (m * g) = dpowM ((i + 1) + t) (-1 / 2) m :=
    ((dpowM (k := k) ((i + 1) + t) (-1 / 2)).map_mul m g).trans (by rw [h2, mul_one])
  unfold eC
  exact congrArg₂ (fun (c : ℂˣ) v => (c : ℂ) • qC τ σ v) h5 (intC_mul ψ f m g h)

end Fix

theorem isOpen_eC_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1))
    (σ : GRep k (t + 1)) (f : XS τ σ),
    IsOpen {g : Mir k ((i + 1) + t) | ∀ m, eC ψ f (m * g) = eC ψ f m} := by
  intro k _ _ _ _ i t ψ τ σ f
  have hA : IsOpen ((sEmb k ((i + 1) + t)) ⁻¹' fixX f) := (isOpen_fixX f).preimage (continuous_sEmb k _)
  have hB : IsOpen {g : Mir k ((i + 1) + t) | dpowM (k := k) ((i + 1) + t) (-1 / 2) g = 1} :=
    (GlobalTheory.CompanionTheory.LeibPhi.isOpen_ker_dpow k ((i + 1) + t + 1) (-1 / 2)).preimage continuous_subtype_val
  refine isOpen_rightInv (eC ψ f) _ (hA.inter hB) ⟨?_, ?_⟩ fun g hg m => eC_mul ψ f m g hg.1 hg.2
  · show sEmb k ((i + 1) + t) 1 ∈ fixX f
    rw [MonoidHom.map_one]
    exact one_mem_fixX f
  · exact (dpowM (k := k) ((i + 1) + t) (-1 / 2)).map_one

end GlobalTheory.CompanionTheory.BZPhiPG.EcSmooth
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb

theorem ePG_false_castSucc (i t : ℕ) (a : Fin (i + 1)) :
    ePG (i + 1) (t + 1) ⟨false, Fin.castSucc a⟩ =
      (Fin.castSucc (eGP (i + 1) t ⟨false, a⟩) : Fin ((i + 1) + t + 1 + 1)) := by
  apply Fin.ext
  rw [Fin.val_castSucc, GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val]
  first
  | (simp [GlobalTheory.BZMir.Leib.ePG, finSumFinEquiv_symm_apply_castSucc]; done)
  | (have h1 : (finSumFinEquiv.symm (Fin.castSucc a) : Fin (i + 1) ⊕ Fin 1) = Sum.inl a :=
        finSumFinEquiv_symm_apply_castSucc a
     have h2 : GlobalTheory.BZMir.Leib.ePG (i + 1) (t + 1) ⟨false, Fin.castSucc a⟩ =
        finSumFinEquiv (Sum.map finSumFinEquiv (Equiv.refl (Fin 1))
          ((Equiv.sumAssoc (Fin (i + 1)) (Fin (t + 1)) (Fin 1)).symm
            (Sum.map (Equiv.refl (Fin (i + 1))) (Equiv.sumComm (Fin 1) (Fin (t + 1)))
              (Equiv.sumAssoc (Fin (i + 1)) (Fin 1) (Fin (t + 1))
                (Sum.inl (finSumFinEquiv.symm (Fin.castSucc a) : Fin (i + 1) ⊕ Fin 1)))))) := rfl
     rw [h2, h1]
     simp)

theorem ePG_true_eq (i t : ℕ) (b : Fin (t + 1)) :
    ePG (i + 1) (t + 1) ⟨true, b⟩ =
      (Fin.castSucc (eGP (i + 1) t ⟨true, b⟩) : Fin ((i + 1) + t + 1 + 1)) := by
  apply Fin.ext
  rw [Fin.val_castSucc, GlobalTheory.CompanionTheory.LeibPhi.blockIndex_true_val]
  all_goals first | rfl | simp [GlobalTheory.BZMir.Leib.ePG]

section Ent

variable (k : Type) [Field k]

theorem glEmbMat_cc (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (a b : Fin n) :
    glEmbMat k n A (Fin.castSucc a) (Fin.castSucc b) = A a b := by
  first
  | (simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_castSucc]; done)
  | simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_lc (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (b : Fin n) :
    glEmbMat k n A (Fin.last n) (Fin.castSucc b) = 0 := by
  first
  | (simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_last, Fin.lastCases_castSucc]; done)
  | simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_cl (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (a : Fin n) :
    glEmbMat k n A (Fin.castSucc a) (Fin.last n) = 0 := by
  first
  | (simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_last, Fin.lastCases_castSucc]; done)
  | simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_ll (n : ℕ) (A : Matrix (Fin n) (Fin n) k) :
    glEmbMat k n A (Fin.last n) (Fin.last n) = 1 := by
  first
  | (simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_last]; done)
  | simp [GlobalTheory.BZMir.glEmbMat]

end Ent

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sEmb_mem_HPG (i t : ℕ) (h : MirabolicParabolic k (i + 1) t) :
    sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) ∈ HPG k (i + 1) (t + 1) := by
  have hh : ∀ (b : Fin (t + 1)) (a : Fin (i + 1)),
      (((h : Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) :
        Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k)
        (eGP (i + 1) t ⟨true, b⟩) (eGP (i + 1) t ⟨false, a⟩) = 0 := by
    have hp : ((h : Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) ∈
        parab k (eGP (i + 1) t) := h.2
    rw [mem_parab_iff] at hp
    intro b a
    exact hp true false b a (by decide)
  have hentry : ∀ p q : Fin ((i + 1) + t + 1 + 1),
      (((GlobalTheory.CompanionTheory.BZPhiPG.sEmb k ((i + 1) + t) (h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) :
          GlobalTheory.BZMir.Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 1 + 1)) k) :
          Matrix (Fin ((i + 1) + t + 1 + 1)) (Fin ((i + 1) + t + 1 + 1)) k) p q =
        GlobalTheory.BZMir.glEmbMat k ((i + 1) + t + 1)
          (((h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) :
            Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) p q := fun _ _ => rfl
  have hlast : GlobalTheory.BZMir.Leib.ePG (i + 1) (t + 1) ⟨false, Fin.last (i + 1)⟩ =
      Fin.last ((i + 1) + t + 1) := GlobalTheory.BZMir.Leib.ePG_false_last (i + 1) (t + 1)
  show ((GlobalTheory.CompanionTheory.BZPhiPG.sEmb k ((i + 1) + t) (h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) :
      GlobalTheory.BZMir.Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + (t + 1) + 1)) k) ∈
    GlobalTheory.SmGL.parab k (GlobalTheory.BZMir.Leib.ePG (i + 1) (t + 1))
  rw [GlobalTheory.SmGL.mem_parab_iff]
  intro a b x y hba
  cases a <;> cases b
  all_goals first | exact absurd hba (by decide) | skip
  refine (hentry _ _).trans ?_
  obtain ⟨c, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last (y : Fin (i + 1 + 1))
  · rw [GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_true_eq,
      GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_false_castSucc,
      GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_cc]
    exact hh x c
  · rw [GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_true_eq, hlast, GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_cl]

theorem sEmb_HGP_mem_HPG : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (h : MirabolicParabolic k (i + 1) t), ∃ η : HPG k (i + 1) (t + 1), (η : Mir k ((i + 1) + t + 1)) = sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) ∧ pgProj k (i + 1) (t + 1) η = (levi k (i + 1) (gpProj k (i + 1) t h).1, (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)) := by
  intro k _ _ _ _ i t h
  let η : GlobalTheory.BZMir.Leib.HPG k (i + 1) (t + 1) :=
    ⟨GlobalTheory.CompanionTheory.BZPhiPG.sEmb k ((i + 1) + t) (h : GlobalTheory.BZMir.Mir k ((i + 1) + t)),
      GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.sEmb_mem_HPG k i t h⟩
  have hη : ∀ p q : Fin ((i + 1) + (t + 1) + 1),
      ((GlobalTheory.BZMir.Leib.hpgIncl k (i + 1) (t + 1) η : GL (Fin ((i + 1) + (t + 1) + 1)) k) :
          Matrix (Fin ((i + 1) + (t + 1) + 1)) (Fin ((i + 1) + (t + 1) + 1)) k) p q =
        GlobalTheory.BZMir.glEmbMat k ((i + 1) + t + 1)
          (((h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) :
            Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) p q := fun _ _ => rfl
  have hlast : GlobalTheory.BZMir.Leib.ePG (i + 1) (t + 1) ⟨false, Fin.last (i + 1)⟩ =
      Fin.last ((i + 1) + t + 1) := GlobalTheory.BZMir.Leib.ePG_false_last (i + 1) (t + 1)
  refine ⟨η, rfl, ?_⟩
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    apply Units.ext
    ext p q
    refine (GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.ePG (i + 1) (t + 1))
      (GlobalTheory.BZMir.Leib.hpgIncl k (i + 1) (t + 1) η) false p q).trans ?_
    refine (hη _ _).trans ?_
    have hX : ∀ a b : Fin (i + 1),
        (((GlobalTheory.BZMir.Leib.gpProj k (i + 1) t h).1 : GL (Fin (i + 1)) k) :
            Matrix (Fin (i + 1)) (Fin (i + 1)) k) a b =
          ((h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k)
            (GlobalTheory.BZMir.Leib.eGP (i + 1) t ⟨false, a⟩) (GlobalTheory.BZMir.Leib.eGP (i + 1) t ⟨false, b⟩) :=
      fun a b => GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP (i + 1) t)
        (GlobalTheory.BZMir.Leib.hgpIncl k (i + 1) t h) false a b
    have hL : ∀ a b : Fin (i + 1 + 1),
        (((GlobalTheory.BZMir.levi k (i + 1) (GlobalTheory.BZMir.Leib.gpProj k (i + 1) t h).1 :
            GlobalTheory.BZMir.Mir k (i + 1)) : GL (Fin (i + 1 + 1)) k) : Matrix (Fin (i + 1 + 1)) (Fin (i + 1 + 1)) k) a b =
          GlobalTheory.BZMir.glEmbMat k (i + 1)
            (((GlobalTheory.BZMir.Leib.gpProj k (i + 1) t h).1 : GL (Fin (i + 1)) k) :
              Matrix (Fin (i + 1)) (Fin (i + 1)) k) a b := fun _ _ => rfl
    refine Eq.trans ?_ (hL _ _).symm
    obtain ⟨a, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last (p : Fin (i + 1 + 1)) <;>
    obtain ⟨b, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last (q : Fin (i + 1 + 1))
    · rw [GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_false_castSucc,
        GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_false_castSucc,
        GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_cc, GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_cc]
      exact (hX a b).symm
    · rw [GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_false_castSucc, hlast,
        GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_cl, GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_cl]
    · rw [GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_false_castSucc, hlast,
        GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_lc, GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_lc]
    · rw [hlast, GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_ll, GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_ll]
  · apply Units.ext
    ext p q
    refine (GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.ePG (i + 1) (t + 1))
      (GlobalTheory.BZMir.Leib.hpgIncl k (i + 1) (t + 1) η) true p q).trans ?_
    refine (hη _ _).trans ?_
    refine Eq.trans ?_ (GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP (i + 1) t)
      (GlobalTheory.BZMir.Leib.hgpIncl k (i + 1) t h) true p q).symm
    rw [GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_true_eq, GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_true_eq,
      GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_cc]
    rfl

end GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.OpenSmooth

theorem isOpen_rightPeriods {G Z : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (F : G → Z)
    (N : Set G) (hN : N ∈ nhds (1 : G)) (h : ∀ g ∈ N, ∀ m, F (m * g) = F m) :
    IsOpen {g : G | ∀ m, F (m * g) = F m} := by
  let T : Subgroup G :=
    { carrier := {g : G | ∀ m, F (m * g) = F m}
      mul_mem' := by
        intro a b ha hb m
        rw [← mul_assoc, hb, ha]
      one_mem' := by intro m; rw [mul_one]
      inv_mem' := by
        intro a ha m
        have := ha (m * a⁻¹)
        rw [inv_mul_cancel_right] at this
        exact this.symm }
  refine T.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset hN ?_)
  intro g hg
  exact h g hg

theorem isOpen_stab_ind {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (σ : Representation ℂ H W) (v : smoothPart (ind H σ)) :
    IsOpen {x : G | ∀ y, v.1.1 (y * x) = v.1.1 y} := by
  have h : IsOpen {g : G | ind H σ g v.1 = v.1} := v.2
  convert h using 1
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hx
    exact Subtype.ext (funext hx)
  · intro hx y
    exact congrFun (congrArg Subtype.val hx) y

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_castM {a b : ℕ} (h : a = b) : Continuous (castM k h) := by
  subst h
  exact continuous_id

theorem continuous_sEmb (n : ℕ) : Continuous (sEmb k n) :=
  GlobalTheory.CompanionTheory.LeibPhi.continuous_iotaM k n

theorem isOpen_dpowM_eq_one (n : ℕ) (s : ℝ) : IsOpen {g : Mir k n | dpowM n s g = 1} :=
  (GlobalTheory.CompanionTheory.LeibPhi.isOpen_ker_dpow k (n + 1) s).preimage continuous_subtype_val

variable {i t : ℕ} {τ : MRep k (i + 1)} {σ : GRep k (t + 1)}

theorem intO_mul_of_stab (f : XS τ σ) (κ : Mir k ((i + 1) + t + 1))
    (hκ : ∀ x : Mir k ((i + 1) + (t + 1)), evX f (x * κ) = evX f x) (y : Mir k ((i + 1) + t + 1)) :
    intO f (y * κ) = intO f y := by
  unfold intO
  congr 1
  funext d
  rw [← mul_assoc]
  exact hκ _

theorem eO_mul_of_stab (ψ : AddChar k Circle) (f : XS τ σ) (m g : Mir k (i + (t + 1)))
    (hd : dpowM (i + (t + 1)) (-1 / 2) g = 1)
    (hκ : ∀ x : Mir k ((i + 1) + (t + 1)),
      evX f (x * sEmb k _ (castM k (by omega : i + (t + 1) = (i + 1) + t) g)) = evX f x) :
    eO ψ f (m * g) = eO ψ f m := by
  unfold eO
  rw [map_mul, hd, mul_one, map_mul, map_mul, ← mul_assoc, intO_mul_of_stab f _ hκ]

theorem isOpen_evX_stab (f : XS τ σ) :
    IsOpen {x : Mir k ((i + 1) + (t + 1)) | ∀ y : Mir k ((i + 1) + (t + 1)), evX f (y * x) = evX f y} :=
  isOpen_stab_ind _ _ (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ)))

end GlobalTheory.CompanionTheory.BZPhiPG.OpenSmooth

namespace GlobalTheory.CompanionTheory.BZPhiPG


open GlobalTheory.CompanionTheory.BZPhiPG.OpenSmooth in
theorem isOpen_eO_rightPeriods : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ),
    IsOpen {g : Mir k (i + (t + 1)) | ∀ m, eO ψ f (m * g) = eO ψ f m} := by
  intro k _ _ _ _ i t ψ τ σ f
  have hs : i + (t + 1) = (i + 1) + t := by omega
  have hφ : Continuous fun g : Mir k (i + (t + 1)) => sEmb k _ (castM k hs g) :=
    (continuous_sEmb _).comp (continuous_castM hs)
  have hU : IsOpen ({g : Mir k (i + (t + 1)) | dpowM (i + (t + 1)) (-1 / 2) g = 1} ∩
      (fun g : Mir k (i + (t + 1)) => sEmb k _ (castM k hs g)) ⁻¹'
        {x : Mir k ((i + 1) + (t + 1)) | ∀ y : Mir k ((i + 1) + (t + 1)), evX f (y * x) = evX f y}) :=
    (isOpen_dpowM_eq_one _ _).inter ((isOpen_evX_stab f).preimage hφ)
  refine isOpen_rightPeriods (eO ψ f) _ (hU.mem_nhds ⟨map_one _, ?_⟩) ?_
  · intro y
    simp
  · rintro g ⟨hd, hst⟩ m
    exact eO_mul_of_stab ψ f m g hd hst

end GlobalTheory.CompanionTheory.BZPhiPG

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG

theorem qC_sigX_unip : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (u : HPG k (i + 1) (t + 1)) (h1 : (pgProj k (i + 1) (t + 1) u).1 ∈ MirUin k (i + 1)) (h2 : (pgProj k (i + 1) (t + 1) u).2 = 1) (w : τ.V ⊗[ℂ] σ.V), qC τ σ (sigX τ σ u w) = qC τ σ w := by
  intro k _ _ _ _ i t τ σ u h1 h2 w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a b =>
    have hd : ((dpowM (i + 1) (((t + 1 : ℕ) : ℝ) / 2) (pgProj k (i + 1) (t + 1) u).1 : ℂˣ) : ℂ) = 1 := by
      have := GlobalTheory.CompanionTheory.LeibPhiTw.dpowM_unip (k := k) (i + 1) (((t + 1 : ℕ) : ℝ) / 2) ⟨_, h1⟩
      simpa using congrArg Units.val this
    have ha : (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (pgProj k (i + 1) (t + 1) u).1 a = τ.ρ (pgProj k (i + 1) (t + 1) u).1 a := by
      refine (twist_apply τ.ρ (dpowM (i + 1) (((t + 1 : ℕ) : ℝ) / 2)) _ a).trans ?_
      rw [hd, one_smul]
    have hρ : (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ (pgProj k (i + 1) (t + 1) u).2 = 1 := by
      rw [h2, map_one]
    have hb : (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ (pgProj k (i + 1) (t + 1) u).2 b = b :=
      LinearMap.congr_fun hρ b
    have e : sigX τ σ u (a ⊗ₜ[ℂ] b) = (τ.ρ (pgProj k (i + 1) (t + 1) u).1 a) ⊗ₜ[ℂ] b :=
      (extTensor_tmul (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ
        (pgProj k (i + 1) (t + 1) u) a b).trans (congrArg₂ (fun x y => TensorProduct.tmul ℂ x y) ha hb)
    have hq : (twKer τ.ρ (MirUin k (i + 1)) 1).mkQ (τ.ρ (pgProj k (i + 1) (t + 1) u).1 a) =
        (twKer τ.ρ (MirUin k (i + 1)) 1).mkQ a := by
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      unfold twKer
      apply Submodule.subset_span
      exact ⟨⟨_, h1⟩, a, by simp⟩
    rw [e]
    exact congrArg (fun x => TensorProduct.tmul ℂ x b) hq

end GlobalTheory.CompanionTheory.BZPhiPG
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfectAlg

theorem exists_theta_mod {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) :
    ∃ θ : A.Acr n →+* A.Un n, (∀ x : A.W, θ (A.toAcr n x) = Ideal.Quotient.mk _ (A.th x)) ∧
      RingHom.ker θ = A.Fil n 1 := by
  obtain ⟨hsurj, hker, -, -⟩ := GlobalTheory.T.quotient_maps_surjective_with_kernels A n
  refine ⟨((Ideal.quotEquivOfEq hker).toRingHom.comp
      (RingHom.quotientKerEquivOfSurjective hsurj).symm.toRingHom).comp
      (Ideal.Quotient.mk (A.Fil n 1)), fun x => ?_, ?_⟩
  · have h1 : A.uToQ n (A.th x) = Ideal.Quotient.mk (A.Fil n 1) (A.toAcr n x) := by rfl
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [← h1, ← RingHom.quotientKerEquivOfSurjective_apply_mk hsurj, RingEquiv.symm_apply_apply,
      Ideal.quotEquivOfEq_mk]
  · ext y
    simp only [RingHom.mem_ker, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [map_eq_zero_iff _ (RingEquiv.injective _), map_eq_zero_iff _ (RingEquiv.injective _),
      Ideal.Quotient.eq_zero_iff_mem]

end GlobalTheory.CompanionTheory.PerfectAlg
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib
open scoped TensorProduct

theorem _root_.GlobalTheory.T.whittaker_heredity_generic_product : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], WhitHeredity k → GenericProdIff k := by
  first | exact @GlobalTheory.CompanionTheory.Leib.genericProdIff_of_whitHeredity | exact GlobalTheory.CompanionTheory.Leib.genericProdIff_of_whitHeredity | (intros; apply GlobalTheory.CompanionTheory.Leib.genericProdIff_of_whitHeredity <;> assumption)
end
