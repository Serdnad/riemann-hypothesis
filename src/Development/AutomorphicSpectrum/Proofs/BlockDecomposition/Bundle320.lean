module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle302
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle149
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import GroundTheory.AutomorphicForms.GLnLocal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle292
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractingDoubleCosetVolumeBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasureImageDoubleCoset
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle278
public import GroundTheory.AutomorphicForms.InductionParabolic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle303
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle293
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq

@[expose] public section

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibPhi

private theorem one_add_colMat_apply_eq_zero_of_ne_last (k : Type) [Field k] (n : ℕ) (v : Fin n → k)
    {r c : Fin (n + 1)} (hc : c ≠ Fin.last n) (hrc : r ≠ c) :
    (1 + GlobalTheory.BZMir.colMat k n v) r c = 0 := by
  simp only [Matrix.add_apply, Matrix.one_apply, GlobalTheory.BZMir.colMat, ite_eq_right hc,
    ite_eq_right hrc, add_zero]

theorem mirUin_le_HGP (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ) :
    MirUin k (m + j) ≤ GlobalTheory.BZMir.Leib.MirabolicParabolic k m j := by
  intro g hg
  unfold GlobalTheory.BZMir.MirUin at hg
  rw [Subgroup.mem_subgroupOf] at hg
  obtain ⟨v, hv⟩ := hg
  change (g : GL (Fin (m + j + 1)) k) ∈ parab k (eGP m j)
  rw [GlobalTheory.SmGL.mem_parab_iff]
  intro x y b a hxy
  obtain ⟨rfl, rfl⟩ := Bool.lt_iff.mp hxy
  have hmat : ((g : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) =
      1 + GlobalTheory.BZMir.colMat k (m + j) (Multiplicative.toAdd v) := by
    rw [← hv]
    rfl
  rw [hmat]
  apply one_add_colMat_apply_eq_zero_of_ne_last k (m + j) _
    (GlobalTheory.BZMir.Leib.blockIndex_false_ne_last m j a)
  intro h
  have h' := congrArg Fin.val h
  rw [GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val,
    GlobalTheory.CompanionTheory.LeibPhi.blockIndex_true_val] at h'
  have ha := a.isLt
  omega

end GlobalTheory.CompanionTheory.LeibPhi
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mirabolic_unipotent_le_parabolic :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
      [IsNonarchimedeanLocalField k] (m j : ℕ),
      MirUin k (m + j) ≤ GlobalTheory.BZMir.Leib.MirabolicParabolic k m j := by
  intro k _ _ _ _ m j g hg
  unfold GlobalTheory.BZMir.MirUin at hg
  rw [Subgroup.mem_subgroupOf] at hg
  obtain ⟨v, hv⟩ := hg
  change (g : GL (Fin (m + j + 1)) k) ∈ parab k (eGP m j)
  rw [GlobalTheory.SmGL.mem_parab_iff]
  intro x y b a hxy
  obtain ⟨rfl, rfl⟩ := Bool.lt_iff.mp hxy
  have hmat : ((g : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) =
      1 + GlobalTheory.BZMir.colMat k (m + j) (Multiplicative.toAdd v) := by
    rw [← hv]
    rfl
  have hne : eGP m j ⟨true, b⟩ ≠ eGP m j ⟨false, a⟩ := by
    intro h
    have hval := congrArg Fin.val h
    rw [GlobalTheory.CompanionTheory.LeibPhi.blockIndex_true_val,
      GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val] at hval
    have ha := a.isLt
    omega
  rw [hmat]
  simp only [Matrix.add_apply, Matrix.one_apply, GlobalTheory.BZMir.colMat,
    ite_eq_right (GlobalTheory.BZMir.Leib.blockIndex_false_ne_last m j a), ite_eq_right hne,
    add_zero]
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

theorem gpProj_mirUin_char : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (m j : ℕ) (u : MirUin k (m + (j + 1)))
    (hh : (u : Mir k (m + (j + 1))) ∈ MirabolicParabolic k m (j + 1)),
    (gpProj k m (j + 1) ⟨u, hh⟩).1 = 1 ∧ ∃ hv : (gpProj k m (j + 1) ⟨u, hh⟩).2 ∈ MirUin k (j + 1),
      mirChar k ψ j ⟨_, hv⟩ = mirChar k ψ (m + j) u := by
  intro k _ _ _ _ ψ m j u hh
  obtain ⟨h1, hv⟩ := GlobalTheory.CompanionTheory.GpUnip.gpProj_unip k m (j + 1) ⟨u, hh⟩ u.2
  refine ⟨h1, hv, ?_⟩
  obtain ⟨w', hw'⟩ := id (id hv : (((gpProj k m (j + 1) ⟨u, hh⟩).2 : Mir k (j + 1)) : GL (Fin (j + 1 + 1)) k) ∈ MirU k (j + 1))
  obtain ⟨w, hw⟩ := (u.2 : ((u : Mir k (m + j + 1)) : GL (Fin (m + j + 1 + 1)) k) ∈ MirU k (m + j + 1))
  rw [mirChar_eq k ψ j ⟨_, hv⟩ w' hw'.symm, mirChar_eq k ψ (m + j) u w hw.symm]
  have hent : ((((gpProj k m (j + 1) ⟨u, hh⟩).2 : Mir k (j + 1)) : GL (Fin (j + 1 + 1)) k) : Matrix _ _ k)
      (Fin.castSucc (Fin.last j)) (Fin.last (j + 1)) =
      (((u : Mir k (m + (j + 1))) : GL (Fin (m + (j + 1) + 1)) k) : Matrix _ _ k)
        (eGP m (j + 1) ⟨true, Fin.castSucc (Fin.last j)⟩) (eGP m (j + 1) ⟨true, Fin.last (j + 1)⟩) := by
    show (leviProj k (eGP m (j + 1)) (hgpIncl k m (j + 1) ⟨u, hh⟩) true).val _ _ = _
    rw [leviProj_apply]
    rfl
  have e : eGP m (j + 1) ⟨true, Fin.castSucc (Fin.last j)⟩ = Fin.castSucc (Fin.last (m + j)) :=
    Fin.ext (by rw [blockIndex_true_val]; simp)
  rw [blockIndex_true_last, e, ← hw'] at hent
  have a1 := unip_apply_castSucc_last k (j + 1) w' (Fin.last j)
  have a2 := unip_apply_castSucc_last k (m + j + 1) w (Fin.last (m + j))
  have : w'.toAdd (Fin.last j) = w.toAdd (Fin.last (m + j)) := by
    rw [← a1, ← a2]
    refine hent.trans ?_
    exact congrArg (fun g : GL (Fin (m + j + 1 + 1)) k => (g : Matrix (Fin (m + j + 1 + 1)) (Fin (m + j + 1 + 1)) k)
      (Fin.castSucc (Fin.last (m + j))) (Fin.last (m + j + 1))) hw.symm
  rw [this]

end GlobalTheory.CompanionTheory.LeibPhi

end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.DerWhit

private theorem twKer_congr' {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) {H H' : Subgroup G} (h : H = H') (θ : H →* ℂˣ) (θ' : H' →* ℂˣ)
    (hθ : ∀ (x : G) (hx : x ∈ H), θ' ⟨x, h ▸ hx⟩ = θ ⟨x, hx⟩) :
    GlobalTheory.PRep.twKer ρ H θ = GlobalTheory.PRep.twKer ρ H' θ' := by
  subst h
  obtain rfl : θ' = θ := MonoidHom.ext fun x => hθ x x.2
  rfl

theorem colFix_zero (k : Type) [Field k] (N : ℕ) : colFix k N 0 = ⊤ := by
  ext g
  simp only [Subgroup.mem_top, iff_true]
  exact fun i hi => absurd hi (Nat.not_lt_zero _)

theorem mem_derUnip_zero (k : Type) [Field k] (N : ℕ) {g : GL (Fin N) k} (hg : g ∈ unipB k (Fin N)) :
    g ∈ derUnip k N 0 := by
  unfold GlobalTheory.BZMir.derUnip
  exact Subgroup.mem_inf.2 ⟨hg, GlobalTheory.CompanionTheory.DerWhit.colFix_zero k N ▸ Subgroup.mem_top g⟩

theorem whitCharFrom_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (N : ℕ) (u : unipB k (Fin N)) :
    whitCharFrom k ψ N 0 u = whitChar ψ N u := by
  first
  | rfl
  | simp [GlobalTheory.BZMir.whitCharFrom, GlobalTheory.LocGL.whitChar]
  | (simp only [GlobalTheory.BZMir.whitCharFrom, GlobalTheory.LocGL.whitChar, MonoidHom.coe_mk,
        OneHom.coe_mk]
     congr 2
     exact Finset.sum_congr (by ext p; simp) fun _ _ => rfl)

theorem twKer_derUnip_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (N : ℕ) (V : Type) [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) :
    twKer π (derUnip k N 0) (derChar k ψ N 0) = twKer π (unipB k (Fin N)) (whitChar ψ N) := by
  have hU : GlobalTheory.BZMir.derUnip k N 0 = GlobalTheory.SmGL.unipB k (Fin N) :=
    le_antisymm (GlobalTheory.BZMir.derUnip_le_unipB k N 0)
      fun g hg => GlobalTheory.CompanionTheory.DerWhit.mem_derUnip_zero k N hg
  refine twKer_congr' π hU _ _ fun x hx => ?_
  exact (GlobalTheory.CompanionTheory.DerWhit.whitCharFrom_zero ψ N ⟨x, hU ▸ hx⟩).symm

end GlobalTheory.CompanionTheory.DerWhit
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

noncomputable section

namespace GlobalTheory.CompanionTheory.BZMir

theorem mem_MirUin_iff_mem_derUnipM (k : Type) [Field k] (n : ℕ) (g : Mir k n) :
    g ∈ MirUin k n ↔ g ∈ derUnipM k n n := by
  rw [MirUin, derUnipM, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, derUnip, Subgroup.mem_inf]
  constructor
  · rintro ⟨v, hv⟩
    rw [← hv]
    refine ⟨(mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩, fun i hi => ?_⟩
    · have hj : j ≠ Fin.last n := fun h => by
        subst h; exact absurd hji (not_lt.2 (Fin.le_last i))
      have hij : i ≠ j := (ne_of_lt hji).symm
      simp [unip, colMat, Matrix.one_apply, hj, hij]
    · by_cases hi : i = Fin.last n
      · subst hi; simp [unip, colMat]
      · simp [unip, colMat, hi]
    · have hi' : i ≠ Fin.last n := fun h => by subst h; simp at hi
      ext l
      simp [unip, colMat, hi', Matrix.col, Matrix.one_apply, Pi.single_apply, eq_comm]
  · rintro ⟨hB, hC⟩
    refine ⟨Multiplicative.ofAdd (fun i => (g : GL (Fin (n + 1)) k).val (Fin.castSucc i) (Fin.last n)), ?_⟩
    ext i j
    show (1 + colMat k n _) i j = _
    induction j using Fin.lastCases with
    | last =>
      induction i using Fin.lastCases with
      | last => simp [colMat, ((mem_unipB k).1 hB).2]
      | cast i => simp [colMat, Matrix.one_apply, Fin.castSucc_ne_last]
    | cast j =>
      have h := congrFun (hC (Fin.castSucc j) (by simp)) i
      rw [mulVec_single_one] at h
      simp only [Matrix.col_apply] at h
      rw [h]
      simp [colMat, Fin.castSucc_ne_last, Matrix.one_apply, Pi.single_apply]

theorem derCharM_self_apply {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (n : ℕ) (x : derUnipM k n n) : derCharM k ψ n n x = 1 := by
  change Circle.toUnits (ψ (∑ p ∈ Finset.univ.filter
    (fun p : Fin (n + 1) × Fin (n + 1) => (p.2 : ℕ) = p.1 + 1 ∧ n ≤ (p.1 : ℕ)), _)) = 1
  rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one, map_one]
  intro p hp
  have h := (Finset.mem_filter.1 hp).2
  have := p.2.isLt
  omega

theorem twKer_MirUin_eq_derUnipM (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k n) V) :
    twKer τ (MirUin k n) 1 = twKer τ (derUnipM k n n) (derCharM k ψ n n) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro w ⟨u, v, rfl⟩
    refine Submodule.subset_span ⟨⟨u, (mem_MirUin_iff_mem_derUnipM k n u).1 u.2⟩, v, ?_⟩
    simp [derCharM_self_apply]
  · refine Submodule.span_le.2 ?_
    rintro w ⟨u, v, rfl⟩
    refine Submodule.subset_span ⟨⟨u, (mem_MirUin_iff_mem_derUnipM k n u).2 u.2⟩, v, ?_⟩
    simp [derCharM_self_apply]

end GlobalTheory.CompanionTheory.BZMir
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.BZMirDer

theorem twKer_resM_derUnipM : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (m n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (m + 1)) k) V),
    twKer (resM k π).ρ (derUnipM k m n) (derCharM k ψ m n) = twKer π (derUnip k (m + 1) n) (derChar k ψ (m + 1) n) := by
  intro k _ _ _ _ ψ m n V _ _ π
  unfold twKer
  congr 1
  ext w
  constructor
  · rintro ⟨u, v, rfl⟩
    exact ⟨Subgroup.subgroupOfEquivOfLe (derUnip_le_Mir k m n) u, v, rfl⟩
  · rintro ⟨u, v, rfl⟩
    refine ⟨(Subgroup.subgroupOfEquivOfLe (derUnip_le_Mir k m n)).symm u, v, ?_⟩
    simp [derCharM, resM]
    rfl

end GlobalTheory.CompanionTheory.BZMirDer
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
open ValuativeRel Matrix MeasureTheory GroundTheory.Automorphic.GLnLocal
open GlobalTheory.CompanionTheory.ContractVolume

private theorem leviEmbZjDiagonal {k : Type} [Field k] {h N : ℕ}
    (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h) :
    leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) =
      diagT k (Fin N) (fun i => if Zl.JC.blockIdx d hd i ≤ j then t else 1) := by
  apply Units.ext
  rw [val_diagT]
  ext i l
  obtain ⟨⟨a, x⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, y⟩, rfl⟩ := (stdBlocks d hd).surjective l
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    by_cases hxy : x = y
    · subst hxy
      by_cases ha : a ≤ j <;> simp [Zl.JC.zj, Zl.JC.blockIdx, ha, Matrix.GeneralLinearGroup.scalar]
    · have hne : stdBlocks d hd ⟨a, x⟩ ≠ stdBlocks d hd ⟨a, y⟩ := fun e => hxy (by
        have := (stdBlocks d hd).injective e
        simpa using this)
      rw [Matrix.diagonal_apply_ne _ hne]
      by_cases ha : a ≤ j <;> simp [Zl.JC.zj, ha, Matrix.GeneralLinearGroup.scalar, hxy]
  · have hne : stdBlocks d hd ⟨a, x⟩ ≠ stdBlocks d hd ⟨b, y⟩ := fun e => hab (by
      have := (stdBlocks d hd).injective e
      exact congrArg Sigma.fst this)
    rw [Matrix.diagonal_apply_ne _ hne, leviEmb_apply_ne k _ _ hab]

theorem _root_.GlobalTheory.T.contracting_double_coset_volume_bound :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ a, 0 < d a) →
        ∀ (t : kˣ), valuation k (t : k) < 1 → ∀ (j : Fin h), j.val + 1 < h →
          ∀ (m : ℕ), 1 ≤ m → ∀ [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)]
            (μ : Measure (AdGL k N)), μ.IsHaarMeasure →
              ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ,
                ENNReal.ofReal (c * (modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j))⁻¹ ^ r) ≤
                  μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) ''
                    {g | ∃ x ∈ congruenceSubgroup k N m, ∃ y ∈ congruenceSubgroup k N m,
                      g = x * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r * y}) := by
  intro k _ _ _ _ h N d hd _ t ht j _ m hm _ _ μ hμ
  have := hμ
  obtain ⟨n, p, u, hp, hu, htu⟩ := exists_decomp t ht
  have hK := coe_congruenceSubgroup k N m hm
  rw [← hp] at hK
  have hϖ1 : valuation k (p : k) < 1 := hp ▸ valuation_uniformizer_lt_one k
  have hunif : ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k (p : k) := fun x hx =>
    hp ▸ le_valuation_uniformizer k x hx
  obtain ⟨hpos, hfin⟩ := GlobalTheory.CompanionTheory.PrincipalCongruence.measure_image_principal_pos_lt_top k N (p : k) m
    p.ne_zero hϖ1 hunif hm μ hμ
  rw [← hK] at hpos hfin
  let a : Fin N → ℤ := fun i => if Zl.JC.blockIdx d hd i ≤ j then (n : ℤ) else 0
  have ha : Antitone a := by
    intro x y hxy
    have hmono := GlobalTheory.CompanionTheory.BlockIndex.blockIdx_monotone h N d hd hxy
    show (if _ then _ else _) ≤ (if _ then _ else _)
    by_cases hy : Zl.JC.blockIdx d hd y ≤ j
    · simp [hy, hmono.trans hy]
    · simp [hy]
      split_ifs <;> simp
  let D : GL (Fin N) k := diagT k (Fin N) (fun i => p ^ a i)
  have hD : (D : Matrix (Fin N) (Fin N) k) = Matrix.diagonal (fun i => (p : k) ^ a i) := by
    simp [D, val_diagT]
  let w : GL (Fin N) k := diagT k (Fin N) (fun i => if Zl.JC.blockIdx d hd i ≤ j then u else 1)
  have hw : w ∈ integralGL k N := by
    refine diagT_mem_integralGL _ fun i => ?_
    split_ifs
    · exact hu
    · simp
  have hfac : leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) = D * w := by
    rw [leviEmbZjDiagonal, ← map_mul]
    congr 1
    funext i
    by_cases hi : Zl.JC.blockIdx d hd i ≤ j
    · simp [a, hi, htu]
    · simp [a, hi]
  have hcomm : Commute D w := by
    show D * w = w * D
    rw [← map_mul, ← map_mul, mul_comm]
  have hmod : (modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j))⁻¹ =
      (resCard k : ℝ) ^ (n * ((∑ a, if a ≤ j then d a else 0) * ∑ b, if j < b then d b else 0)) := by
    have h1 : nabs k t = ((resCard k : ℝ)⁻¹) ^ n := by
      have h2 := nabs_uniformiser (irreducible_uniformizer k) hp
      have h3 := nabs_eq_one_of_valuation_eq_one hu
      rw [htu, show nabs k (p ^ n * u) = nabs k (p ^ n) * nabs k u from nabs_mul k _ _, nabs_pow', h2, h3,
        mul_one]
    have h4 : (∑ a, if a ≤ j then (d a : ℤ) else 0) * (∑ b, if j < b then (d b : ℤ) else 0) =
        (((∑ a, if a ≤ j then d a else 0) * ∑ b, if j < b then d b else 0 : ℕ) : ℤ) := by
      push_cast
      rfl
    rw [modulus_zj, sum_modExp, h4, h1, zpow_natCast, ← pow_mul, inv_pow, inv_inv]
  refine ⟨(μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) ''
    (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m : Set (GL (Fin N) k)))).toReal,
    ENNReal.toReal_pos hpos.ne' hfin.ne, fun r => ?_⟩
  have hvol := GlobalTheory.CompanionTheory.DoubleCosetVolume.measure_image_doubleCoset k N (p : k) m a p.ne_zero hϖ1 hunif
    hm ha D hD μ hμ r
  rw [← hK, sum_toNat d hd j n] at hvol
  have hle := measure_le_translate μ (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m) (D ^ r) (w ^ r)
    (hcomm.pow_pow r r) (fun x hx => conj_mem_congruenceSubgroup k N ((integralGL k N).pow_mem hw r) hx)
  rw [hfac, hcomm.mul_pow, hmod]
  refine le_trans (le_of_eq ?_) hle
  simp only [SetLike.mem_coe] at hvol
  rw [hvol, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin.ne, mul_comm,
    ← pow_mul, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast, mul_comm _ r]
  rfl
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

theorem _root_.GlobalTheory.T.jacquet_module_equiv_foundation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), ∃ e : Jacquet π (unipRad k (stdBlocks d hd)) ≃ₗ[ℂ] GroundTheory.Automorphic.Parabolic.JacquetModule k N (Zl.JC.blockIdx d hd) π, (∀ v : V, e (Submodule.Quotient.mk v) = Representation.Coinvariants.mk _ v) ∧ ∀ (g : Levi k (fun a => Fin (d a))) (hg : leviEmb k (stdBlocks d hd) g ∈ GroundTheory.Automorphic.Parabolic.levi k N (Zl.JC.blockIdx d hd)) (x : Jacquet π (unipRad k (stdBlocks d hd))), e (jacU (stdBlocks d hd) π g x) = GroundTheory.Automorphic.Parabolic.jacquetAction k N (Zl.JC.blockIdx d hd) π ⟨_, hg⟩ (e x) := by
  intro k _ _ _ _ N V _ _ π h d hd
  have hPQ := GlobalTheory.CompanionTheory.ParabolicCompare.unipRad_stdBlocks_eq_unipotentRadical k h N d hd
  have hK : twKer π (unipRad k (stdBlocks d hd)) 1 =
      Representation.Coinvariants.ker
        (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N (Zl.JC.blockIdx d hd)).subtype) := by
    rw [hPQ]
    exact GlobalTheory.CompanionTheory.JacquetDict.twKer_one_eq_coinvariantsKer π _
  refine ⟨Submodule.quotEquivOfEq _ _ hK, ?_, ?_⟩
  · intro v
    rfl
  · intro g hg x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.JmSub

theorem exists_subQuot_of_jm_ne_zero :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin N) k) V), Zc.jm x hd π ≠ 0 →
      ∃ S T : Subrepresentation (_root_.GlobalTheory.SmGL.jac (stdBlocks (fun a => (x a).1) hd) π),
        Nonempty ((subQuot S T).Equiv (piTensor fun a => (x a).rep)) := by
  intro k _ _ _ _ h N x hd V _ _ π hjm
  obtain ⟨r, hr, hpos⟩ : ∃ r, GlobalTheory.SmGL.OccursTimes (GlobalTheory.SmGL.piTensor fun a => (x a).rep)
      (GlobalTheory.SmGL.jac (GlobalTheory.SmGL.stdBlocks (fun a => (x a).1) hd) π) r ∧ 0 < r := by
    by_contra hcon
    apply hjm
    unfold Zc.jm GlobalTheory.SmGL.jhMult
    refine le_antisymm (iSup_le fun r => iSup_le fun hr' => ?_) zero_le
    have hr0 : r = 0 := by
      by_contra hne
      exact hcon ⟨r, hr', Nat.pos_of_ne_zero hne⟩
    simp [hr0]
  obtain ⟨S, T, -, -, hST⟩ := hr
  exact ⟨S ⟨0, hpos⟩, T ⟨0, hpos⟩, hST ⟨0, hpos⟩⟩

end GlobalTheory.CompanionTheory.JmSub
end
end
