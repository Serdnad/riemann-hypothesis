module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle091
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle101
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle097
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyLocalDensityStandardLatticeBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Real
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

@[expose] public section

section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

theorem _root_.GlobalTheory.T.isPolynomialRepGLComplex_algebraicWeight_evalPoint : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → ∀ τ : L →+* ℂ, IsPolyRep (fun B => evM P (evPt τ B)) := by
  first | exact @GlobalTheory.AlgWtHW.isPolyRep_evPt | exact GlobalTheory.AlgWtHW.isPolyRep_evPt | (intros; apply GlobalTheory.AlgWtHW.isPolyRep_evPt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup

theorem _root_.GlobalTheory.T.exists_sections_generate_ideal_projective : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProjOver s → ∀ J : X.IdealSheafData, ∃ (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec), Generates J σ := by
  first | exact @GlobalTheory.ProjBlowup.exists_generates | exact GlobalTheory.ProjBlowup.exists_generates | (intros; apply GlobalTheory.ProjBlowup.exists_generates <;> assumption)
end

section

open CategoryTheory Polynomial

namespace GlobalTheory.SerCmp

open Formalism.IrreducibleCountingLemmas.TYPES

theorem hasLabel_of_hasLabelO : ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod g)} (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) C), (∀ (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → CategoryTheory.Simple V → Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V → GlobalTheory.GLq.IsCuspOf L (O.lab d V) (fun x => V.character x)) → (∀ (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b → ∀ x : GL (Fin r) (ZMod g), LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x) = GlobalTheory.GLq.hcL (GlobalTheory.SerCmp.canonList b lam) r x) → (∀ (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))) (τ : FDRep ℂ (GL (Fin r) (ZMod g))), CategoryTheory.Simple τ → (Formalism.IrreducibleCountingLemmas.TYPES.IsConstituent τ (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam) ↔ GlobalTheory.GLq.ip (fun x => τ.character x) (fun x => LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x)) ≠ 0)) → ∀ (r : ℕ) (τ : FDRep ℂ (GL (Fin r) (ZMod g))) (f : (ZMod g)[X]), CategoryTheory.Simple τ → Formalism.IrreducibleCountingLemmas.TYPES.HasLabelO O τ f → GlobalTheory.GLq.HasLabel L (fun x => τ.character x) f := by
  intro g _ L C O h1 h2 h3 r τ f hτ hL
  obtain ⟨s, b, lam, hb, hl, hcon, rfl⟩ := hL
  have hc : ∀ c, 1 ≤ Fintype.card {i // b i = c} := fun c => by
    obtain ⟨i, hi⟩ := hb c
    exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  let Q : List ((ZMod g)[X] × GlobalTheory.GLq.Pc g) := (List.finRange s).map fun c =>
    (labO O (lam c), ⟨Fintype.card {i // b i = c},
      fun x => (transp (Fintype.equivFin {i // b i = c}) (lam c)).character x⟩)
  have hQ : Q.map Prod.snd = canonList b lam := by
    simp only [Q, canonList, List.map_map]
    rfl
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [Q, List.mem_map] at hp
    obtain ⟨c, -, rfl⟩ := hp
    exact h1 _ _ (hc c) (Formalism.L2.PT.simple_transp _ (hl c).1) (Formalism.L2.PT.isCuspidal_transp _ (hl c).2)
  · rw [hQ]
    unfold GlobalTheory.GLq.degL canonList
    rw [List.map_map]
    have e : ((List.finRange s).map ((fun p : GlobalTheory.GLq.Pc g => p.1) ∘ fun c : Fin s =>
        (⟨Fintype.card {i // b i = c},
          fun x => (transp (Fintype.equivFin {i // b i = c}) (lam c)).character x⟩ : GlobalTheory.GLq.Pc g))).sum =
        ∑ c : Fin s, Fintype.card {i // b i = c} := by
      rw [Fin.sum_univ_def]
      rfl
    rw [e, ← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv b), Fintype.card_fin]
  · simp only [Q, List.map_map]
    rw [Fin.prod_univ_def]
    rfl
  · rw [hQ]
    have ht : (fun x => LinearMap.trace ℂ (hcSpace (ZMod g) b lam) (hcRep (ZMod g) b lam x)) =
        GlobalTheory.GLq.hcL (canonList b lam) r := funext (h2 r s b lam hb)
    have := (h3 r s b lam τ hτ).1 hcon
    rw [ht] at this
    exact this

end GlobalTheory.SerCmp
end

section

open CategoryTheory Polynomial

noncomputable section

namespace GlobalTheory.SerCmp.ListBlocks

open Formalism.IrreducibleCountingLemmas.TYPES

theorem glEquiv_transp_cancel {g : ℕ} [Fact g.Prime] {F : Type} [Fintype F] [DecidableEq F] {n : ℕ}
    (E : F ≃ Fin n) (x : GL (Fin n) (ZMod g)) :
    (glEquiv (ZMod g) E.symm).symm ((glEquiv (ZMod g) E).symm x) = x := by
  ext i j
  rw [Formalism.L2.PT.coe_glEquiv_symm, Formalism.L2.PT.coe_glEquiv_symm]
  simp

theorem entry_eq {g : ℕ} [Fact g.Prime] {F : Type} [Fintype F] [DecidableEq F] {d : ℕ}
    (h : Fintype.card F = d) (V : FDRep ℂ (GL (Fin d) (ZMod g))) :
    (⟨Fintype.card F, fun x => (transp (Fintype.equivFin F)
      (transp ((finCongr h.symm).trans (Fintype.equivFin F).symm) V)).character x⟩ : GlobalTheory.GLq.Pc g) =
      ⟨d, fun x => V.character x⟩ := by
  generalize Fintype.equivFin F = E
  subst h
  refine Sigma.ext rfl (heq_of_eq (funext fun x => ?_))
  dsimp only
  rw [Formalism.L2.PT.character_transp, Formalism.L2.PT.character_transp]
  congr 1
  have : (finCongr (rfl : Fintype.card F = Fintype.card F)).trans E.symm = E.symm := by ext; simp
  rw [this, glEquiv_transp_cancel]

theorem exists_blocks (s : ℕ) (d : Fin s → ℕ) (r : ℕ) (hr : ∑ c, d c = r) :
    ∃ b : Fin r → Fin s, ∀ c, Fintype.card {i // b i = c} = d c := by
  subst hr
  refine ⟨fun i => (finSigmaFinEquiv.symm i).1, fun c => ?_⟩
  rw [Fintype.card_congr ((finSigmaFinEquiv.symm.subtypeEquiv (fun _ => Iff.rfl)).trans (Equiv.sigmaSubtype c))]
  simp

end GlobalTheory.SerCmp.ListBlocks

open Formalism.IrreducibleCountingLemmas.TYPES in
theorem GlobalTheory.SerCmp.canonList_of_cuspidal_list : ∀ (g : ℕ) [Fact g.Prime] (Q : List (GlobalTheory.GLq.Pc g)), (∀ p ∈ Q, 1 ≤ p.1 ∧ ∃ V : FDRep ℂ (GL (Fin p.1) (ZMod g)), CategoryTheory.Simple V ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V ∧ ∀ x, V.character x = p.2 x) → ∃ (b : Fin (GlobalTheory.GLq.degL Q) → Fin Q.length) (lam : ∀ c : Fin Q.length, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b ∧ (∀ c, CategoryTheory.Simple (lam c) ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) (lam c)) ∧ GlobalTheory.SerCmp.canonList b lam = Q := by
  intro g _ Q hQ
  have H : ∀ c : Fin Q.length, ∃ V : FDRep ℂ (GL (Fin (Q.get c).1) (ZMod g)), 1 ≤ (Q.get c).1 ∧
      CategoryTheory.Simple V ∧ IsCuspidal (ZMod g) V ∧ ∀ x, V.character x = (Q.get c).2 x := by
    intro c
    obtain ⟨h1, V, h2⟩ := hQ _ (List.get_mem Q c)
    exact ⟨V, h1, h2⟩
  choose V hd hVs hVc hVch using H
  have hsum : ∑ c : Fin Q.length, (Q.get c).1 = GlobalTheory.GLq.degL Q := by
    rw [GlobalTheory.GLq.degL]
    rw [← Fin.sum_univ_getElem]
    exact Fintype.sum_equiv (finCongr (List.length_map _).symm) _ _ (fun c => by simp)
  obtain ⟨b, hcard⟩ := GlobalTheory.SerCmp.ListBlocks.exists_blocks Q.length (fun c => (Q.get c).1) _ hsum
  refine ⟨b, fun c => transp ((finCongr (hcard c).symm).trans (Fintype.equivFin _).symm) (V c), ?_, ?_, ?_⟩
  · intro c
    have : 0 < Fintype.card {i // b i = c} := by rw [hcard c]; exact hd c
    obtain ⟨⟨i, hi⟩⟩ := Fintype.card_pos_iff.1 this
    exact ⟨i, hi⟩
  · intro c
    exact ⟨Formalism.L2.PT.simple_transp _ (hVs c), Formalism.L2.PT.isCuspidal_transp _ (hVc c)⟩
  · apply List.ext_get (GlobalTheory.SerCmp.canonList_length _ _)
    intro n h1 h2
    simp only [GlobalTheory.SerCmp.canonList, List.get_eq_getElem, List.getElem_map, List.getElem_finRange]
    rw [GlobalTheory.SerCmp.ListBlocks.entry_eq (hcard _) (V _)]
    have key : ∀ c, (⟨(Q.get c).1, fun x => (V c).character x⟩ : GlobalTheory.GLq.Pc g) = Q.get c := fun c =>
      Sigma.ext rfl (heq_of_eq (_root_.funext fun x => hVch c x))
    rw [key]
    simp
end
end

section

open CategoryTheory Polynomial

namespace GlobalTheory.SerCmp

theorem getElem_of_canonList_eq {g : ℕ} [Fact g.Prime] {r s : ℕ} (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))) (Q : List (GlobalTheory.GLq.Pc g))
    (h : canonList b lam = Q) (c : Fin s) (hc : (c : ℕ) < Q.length) :
    Q[(c : ℕ)] = ⟨Fintype.card {i // b i = c},
      fun x => (Formalism.IrreducibleCountingLemmas.TYPES.transp (Fintype.equivFin {i // b i = c}) (lam c)).character x⟩ := by
  subst h
  have e : (List.finRange s)[(c : ℕ)]'(by simp) = c := by simp
  simp only [canonList, List.getElem_map]
  rw [e]

theorem hasLabelO_of_hasLabel : ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod g)} (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) C), (∀ (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))) (P : (ZMod g)[X]), 1 ≤ d → CategoryTheory.Simple V → Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V → GlobalTheory.GLq.IsCuspOf L P (fun x => V.character x) → P = O.lab d V) → (∀ (d : ℕ) (χ : GlobalTheory.GLq.Gn g d → ℂ), GlobalTheory.GLq.IsCusp χ → ∃ V : FDRep ℂ (GL (Fin d) (ZMod g)), CategoryTheory.Simple V ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V ∧ ∀ x, V.character x = χ x) → (∀ (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b → ∀ x : GL (Fin r) (ZMod g), LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x) = GlobalTheory.GLq.hcL (GlobalTheory.SerCmp.canonList b lam) r x) → (∀ (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))) (τ : FDRep ℂ (GL (Fin r) (ZMod g))), CategoryTheory.Simple τ → (Formalism.IrreducibleCountingLemmas.TYPES.IsConstituent τ (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam) ↔ GlobalTheory.GLq.ip (fun x => τ.character x) (fun x => LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x)) ≠ 0)) → (∀ (Q : List (GlobalTheory.GLq.Pc g)), (∀ p ∈ Q, 1 ≤ p.1 ∧ ∃ V : FDRep ℂ (GL (Fin p.1) (ZMod g)), CategoryTheory.Simple V ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V ∧ ∀ x, V.character x = p.2 x) → ∃ (b : Fin (GlobalTheory.GLq.degL Q) → Fin Q.length) (lam : ∀ c : Fin Q.length, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b ∧ (∀ c, CategoryTheory.Simple (lam c) ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) (lam c)) ∧ GlobalTheory.SerCmp.canonList b lam = Q) → ∀ (r : ℕ) (τ : FDRep ℂ (GL (Fin r) (ZMod g))) (f : (ZMod g)[X]), CategoryTheory.Simple τ → GlobalTheory.GLq.HasLabel L (fun x => τ.character x) f → Formalism.IrreducibleCountingLemmas.TYPES.HasLabelO O τ f := by
  intro g _ L C O hU hReal hTr hCon hSurj r τ f hτ hL
  obtain ⟨Q, hQ, hdeg, hf, hip⟩ := hL
  subst hdeg
  have hQScusp : ∀ p ∈ (Q.map Prod.snd), 1 ≤ p.1 ∧ ∃ V : FDRep ℂ (GL (Fin p.1) (ZMod g)), CategoryTheory.Simple V ∧
      Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V ∧ ∀ x, V.character x = p.2 x := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    have hc : GlobalTheory.GLq.IsCusp q.2.2 := (hQ q hq).2.1
    exact ⟨hc.1, hReal _ _ hc⟩
  obtain ⟨b, lam, hb, hlam, hcan⟩ := hSurj (Q.map Prod.snd) hQScusp
  have key : ∀ c : Fin (Q.map Prod.snd).length, ∀ hcQ : (c : ℕ) < Q.length,
      Formalism.IrreducibleCountingLemmas.TYPES.labO O (lam c) = (Q[(c : ℕ)]'hcQ).1 := by
    intro c hcQ
    have hcusp := hQ _ (List.getElem_mem hcQ)
    have h2 : (Q[(c : ℕ)]'hcQ).2 = (Q.map Prod.snd)[(c : ℕ)] := by simp
    rw [h2, getElem_of_canonList_eq b lam (Q.map Prod.snd) hcan c c.2] at hcusp
    exact (hU _ _ _ hcusp.2.1.1 (Formalism.L2.PT.simple_transp _ (hlam c).1)
      (Formalism.L2.PT.isCuspidal_transp _ (hlam c).2) hcusp).symm
  refine ⟨(Q.map Prod.snd).length, b, lam, hb, hlam, ?_, ?_⟩
  · rw [hCon _ _ b lam τ hτ]
    have htr : (fun x => LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam)
        (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x)) = GlobalTheory.GLq.hcL (Q.map Prod.snd) (GlobalTheory.GLq.degL (Q.map Prod.snd)) := by
      funext x
      rw [hTr _ _ b lam hb x, hcan]
    rw [htr]
    exact hip
  · have hlen : (Q.map Prod.fst).length = (Q.map Prod.snd).length := by simp
    rw [hf, ← Fin.prod_univ_getElem (Q.map Prod.fst)]
    refine Fintype.prod_equiv (finCongr hlen) _ _ (fun c => ?_)
    have hcQ : (c : ℕ) < Q.length := by simpa using c.2
    rw [key _ hcQ]
    simp

end GlobalTheory.SerCmp
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.ProjBlowup

variable {R : Type} [CommRing R] {N : ℕ} {X : Scheme.{0}}

theorem val_res_pullO_g (φ : X ⟶ PSpace R N) (e : ℕ) (i j : (pullO φ e).ι)
    {V : X.Opens} (h : V ≤ (pullO φ e).U i ⊓ (pullO φ e).U j) :
    ((res h ((pullO φ e).g i j) : Γ(X, V)ˣ) : Γ(X, V)) = pullRatio φ V i (h.trans inf_le_left) j ^ e := by
  have : (((pullO φ e).g i j : Γ(X, (pullO φ e).U i ⊓ (pullO φ e).U j)ˣ) :
      Γ(X, (pullO φ e).U i ⊓ (pullO φ e).U j)) = pullRatio φ _ i inf_le_left j ^ e :=
    Units.val_pow_eq_pow_val _ _
  rw [res, Units.coe_map, MonoidHom.coe_coe, this]
  exact (map_pow _ _ e).trans (congrArg (· ^ e) (resG_pullRatio h))

theorem isLB_pullO (φ : X ⟶ PSpace R N) (e : ℕ) : (pullO φ e).IsLB := {
  cover := (isCoordFamily_pullRatio φ).cover
  g_self i := by
    ext
    rw [val_res_pullO_g, Units.val_one]
    exact (congrArg (· ^ e) pullRatio_self).trans (one_pow e)
  cocycle i j k := by
    ext
    rw [Units.val_mul, val_res_pullO_g, val_res_pullO_g, val_res_pullO_g]
    exact (mul_pow _ _ e).symm.trans (congrArg (· ^ e) pullRatio_mul_pullRatio) }

theorem exists_generates_isLB (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R)
    (J : X.IdealSheafData) (hs : IsProjOver s) :
    ∃ (L₀ : LB X) (m : ℕ) (σ : Fin (m + 1) → L₀.Sec), L₀.IsLB ∧ Generates J σ := by
  classical
  obtain ⟨N, φ, _, -⟩ := hs
  have fg : ∀ a, (J.ideal (affChart φ a)).FG := fun a => by
    have : IsNoetherianRing Γ(PSpace R N, chart R N a) :=
      isNoetherianRing_of_ringEquiv _ (chartAlgEquiv R N a).toRingEquiv
    have : IsNoetherianRing Γ(X, (affChart φ a).1) :=
      isNoetherianRing_of_surjective _ _ _ (φ.app_surjective _ (isAffineOpen_chart R N a))
    exact IsNoetherian.noetherian _
  change ∀ a, ∃ S : Finset Γ(X, (affChart φ a).1),
    Ideal.span (S : Set _) = J.ideal (affChart φ a) at fg
  choose S hS using fg
  choose e₀ he₀ using fun p : Σ a, S a =>
    exists_form_of_mem φ J p.1 p.2.1 (hS p.1 ▸ Ideal.subset_span p.2.2)
  choose F hF hFa hFb using fun p => he₀ p (Finset.univ.sup e₀) (Finset.le_sup (Finset.mem_univ p))
  let q := (Fintype.equivFinOfCardEq (Fintype.card_option (α := Σ a, S a))).symm
  let τ : Option (Σ a, S a) → (pullO φ (Finset.univ.sup e₀)).Sec := fun o =>
    o.elim (pullFormSec φ 0 (isHomogeneous_zero _ R _)) fun p => pullFormSec φ (F p) (hF p)
  refine ⟨_, _, fun j => τ (q j), isLB_pullO φ _, (isCoordFamily_pullRatio φ).cover, fun k V h => ?_⟩
  have key : J.ideal (affChart φ k) = Ideal.span (Set.range fun j => (τ (q j)).f k) := by
    refine le_antisymm ?_ (Ideal.span_le.2 ?_)
    · rw [← hS k]
      refine Ideal.span_mono fun g hg => ⟨q.symm (some ⟨k, g, hg⟩), ?_⟩
      simp only [q.apply_symm_apply]
      exact hFa ⟨k, g, hg⟩
    · rintro _ ⟨j, rfl⟩
      dsimp only
      cases q j with
      | none =>
        exact (congrArg (· ∈ J.ideal (affChart φ k)) (pullForm_zero (φ := φ) (hi := le_rfl))).mpr (zero_mem _)
      | some p => exact hFb p k
  rw [← J.map_ideal (V := affChart φ k) h, key]
  erw [Ideal.map_span, ← Set.range_comp]
  rfl

end GlobalTheory.ProjBlowup
end
end

section

set_option autoImplicit false

noncomputable section

open Topology

namespace GlobalTheory.ShFam.Hor.LogCh

open Topology in
set_option autoImplicit false in
private theorem exists_pos_int_combination_eq_zero_near_of_linearIndependent {g r : ℕ} {l₁ : Fin r → Fin g → ℂ}
    (hl : LinearIndependent ℝ l₁) :
    ∃ δ > 0, ∀ l : Fin r → Fin g → ℂ, ‖l - l₁‖ < δ → ∀ c : Fin r → ℤ,
      ‖∑ j, c j • l j‖ < δ → c = 0 := by
  set L : (Fin r → ℝ) →ₗ[ℝ] (Fin g → ℂ) := Fintype.linearCombination ℝ l₁ with hL
  have hLapp : ∀ x, L x = ∑ j, x j • l₁ j := fun x => by
    simp [hL, Fintype.linearCombination_apply]
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    exact funext (Fintype.linearIndependent_iff.1 hl x (by rw [← hLapp]; exact hx))
  obtain ⟨K, -, hK⟩ := L.exists_antilipschitzWith hker
  set k : ℝ := (K : ℝ) + 1 with hk
  have hk0 : 0 < k := by positivity
  have hbound : ∀ x, ‖x‖ ≤ k * ‖L x‖ := fun x => by
    have h := hK.le_mul_dist x 0
    simp only [map_zero, dist_zero_right] at h
    nlinarith [norm_nonneg (L x)]
  refine ⟨1 / (2 * k * ((r : ℝ) + 1)), by positivity, fun l hl c hc => ?_⟩
  set δ : ℝ := 1 / (2 * k * ((r : ℝ) + 1)) with hδ
  set x : Fin r → ℝ := fun j => (c j : ℝ) with hx
  have hcx : ∑ j, c j • l j = ∑ j, x j • l j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hx, Int.cast_smul_eq_zsmul]
  have hsplit : L x = ∑ j, x j • l j - ∑ j, x j • (l j - l₁ j) := by
    rw [hLapp]
    simp [smul_sub, Finset.sum_sub_distrib]
  have hsum : ‖∑ j, x j • (l j - l₁ j)‖ ≤ r * (‖x‖ * ‖l - l₁‖) := by
    calc ‖∑ j, x j • (l j - l₁ j)‖ ≤ ∑ j, ‖x j • (l j - l₁ j)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin r, ‖x‖ * ‖l - l₁‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_smul]
        exact mul_le_mul (norm_le_pi_norm x j) (by simpa using norm_le_pi_norm (l - l₁) j)
          (norm_nonneg _) (norm_nonneg _)
      _ = r * (‖x‖ * ‖l - l₁‖) := by simp
  have hLx : ‖L x‖ < δ + r * (‖x‖ * δ) := by
    rw [hsplit]
    calc ‖∑ j, x j • l j - ∑ j, x j • (l j - l₁ j)‖
        ≤ ‖∑ j, x j • l j‖ + ‖∑ j, x j • (l j - l₁ j)‖ := norm_sub_le _ _
      _ < δ + r * (‖x‖ * δ) := by
        have h1 : ‖∑ j, x j • l j‖ < δ := by rw [← hcx]; exact hc
        have h2 : r * (‖x‖ * ‖l - l₁‖) ≤ r * (‖x‖ * δ) := by
          gcongr
        linarith
  have hkδ : k * δ * ((r : ℝ) + 1) = 1 / 2 := by
    rw [hδ]; field_simp
  have hxlt : ‖x‖ < 1 := by
    have hb := hbound x
    have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hxn := norm_nonneg x
    have hδ0 : 0 < δ := by positivity
    have : ‖x‖ < k * δ + k * δ * r * ‖x‖ := by
      calc ‖x‖ ≤ k * ‖L x‖ := hb
        _ < k * (δ + r * (‖x‖ * δ)) := mul_lt_mul_of_pos_left hLx hk0
        _ = k * δ + k * δ * r * ‖x‖ := by ring
    have hkδ0 : 0 < k * δ := mul_pos hk0 hδ0
    have hkδ' : k * δ * r + k * δ = 1 / 2 := by rw [← hkδ]; ring
    have ha : k * δ * r ≤ 1 / 2 := by linarith
    have ha2 : k * δ ≤ 1 / 2 := by nlinarith
    have hm : k * δ * r * ‖x‖ ≤ 1 / 2 * ‖x‖ := mul_le_mul_of_nonneg_right ha hxn
    linarith
  funext j
  have hj : ‖x j‖ < 1 := lt_of_le_of_lt (norm_le_pi_norm x j) hxlt
  have hj' : |(c j : ℝ)| < 1 := by simpa [hx] using hj
  have : |c j| < 1 := by exact_mod_cast hj'
  simpa using Int.abs_lt_one_iff.1 this


open Topology in
set_option autoImplicit false in
theorem _root_.GlobalTheory.ShFam.Hor.LogCh.exists_const_coords (n g r : ℕ) (B : Set (Fin n → ℂ))
    (K : (Fin n → ℂ) → Set (Fin g → ℂ))
    (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (ζ : (Fin n → ℂ) → Fin g → ℂ) (b₀ : Fin n → ℂ)
    (hB : IsPreconnected B) (hlam : ContinuousOn lam B) (hζ : ContinuousOn ζ B)
    (hbas : ∀ b ∈ B, _root_.GlobalTheory.ShFam.Hor.LogCh.IsLatBasis (K b) (lam b)) (hmem : ∀ b ∈ B, ζ b ∈ K b)
    (hb₀ : b₀ ∈ B) :
    ∃ m : Fin r → ℤ, ∀ b ∈ B, ζ b = ∑ j, m j • lam b j := by
  classical
  have hex : ∀ b ∈ B, ∃ m : Fin r → ℤ, ζ b = ∑ j, m j • lam b j :=
    fun b hb => ((hbas b hb).2 (ζ b)).1 (hmem b hb)
  let F : (Fin n → ℂ) → Fin r → ℤ := fun b => if hb : b ∈ B then (hex b hb).choose else 0
  have hF : ∀ b ∈ B, ζ b = ∑ j, F b j • lam b j := by
    intro b hb
    simp only [F, dite_eq_left hb]
    exact (hex b hb).choose_spec
  have hloc : ∀ b₁ ∈ B, ∀ᶠ b in 𝓝[B] b₁, F b = F b₁ := by
    intro b₁ hb₁
    obtain ⟨δ, hδ, hkey⟩ := exists_pos_int_combination_eq_zero_near_of_linearIndependent (hbas b₁ hb₁).1
    have h1 : ∀ᶠ b in 𝓝[B] b₁, ‖lam b - lam b₁‖ < δ := by
      have hc : ContinuousWithinAt (fun b => ‖lam b - lam b₁‖) B b₁ :=
        ((hlam b₁ hb₁).sub continuousWithinAt_const).norm
      exact hc.eventually (eventually_lt_nhds (by simpa using hδ))
    have hcomb : Continuous (fun l : Fin r → Fin g → ℂ => ∑ j, F b₁ j • l j) :=
      continuous_finsetSum _ fun j _ => (continuous_apply j).const_smul (F b₁ j)
    have h2 : ∀ᶠ b in 𝓝[B] b₁, ‖ζ b - ∑ j, F b₁ j • lam b j‖ < δ := by
      have hc : ContinuousWithinAt (fun b => ‖ζ b - ∑ j, F b₁ j • lam b j‖) B b₁ :=
        ((hζ b₁ hb₁).sub (hcomb.continuousAt.comp_continuousWithinAt (hlam b₁ hb₁))).norm
      refine hc.eventually (eventually_lt_nhds ?_)
      show ‖ζ b₁ - ∑ j, F b₁ j • lam b₁ j‖ < δ
      rw [← hF b₁ hb₁, sub_self, norm_zero]
      exact hδ
    filter_upwards [h1, h2, self_mem_nhdsWithin] with b hb1 hb2 hbB
    have hdiff : ∑ j, (F b - F b₁) j • lam b j = ζ b - ∑ j, F b₁ j • lam b j := by
      rw [hF b hbB]
      simp [sub_smul, Finset.sum_sub_distrib]
    exact sub_eq_zero.1 (hkey (lam b) hb1 (F b - F b₁) (by rw [hdiff]; exact hb2))
  have hcont : ContinuousOn F B := fun b₁ hb₁ =>
    continuousWithinAt_const.congr_of_eventuallyEq (hloc b₁ hb₁) rfl
  refine ⟨F b₀, fun b hb => ?_⟩
  rw [← hB.constant hcont hb hb₀]
  exact hF b hb

end GlobalTheory.ShFam.Hor.LogCh
end
end

section

set_option autoImplicit false

namespace GlobalTheory.LatticeBasisClosedBall

theorem exists_real_coords {g : ℕ} (lam : Fin (2 * g) → Fin g → ℂ) (hli : LinearIndependent ℝ lam)
    (w : Fin g → ℂ) : ∃ c : Fin (2 * g) → ℝ, ∑ j, c j • lam j = w := by
  have hdim : Fintype.card (Fin (2 * g)) = Module.finrank ℝ (Fin g → ℂ) := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  have hspan : Submodule.span ℝ (Set.range lam) = ⊤ := hli.span_eq_top_of_card_eq_finrank' hdim
  have hw : w ∈ Submodule.span ℝ (Set.range lam) := hspan ▸ Submodule.mem_top
  exact (Submodule.mem_span_range_iff_exists_fun ℝ).1 hw

theorem isLatBasis_of_closedBall : ∀ {g : ℕ} (H : AddSubgroup (Fin g → ℂ)) (lam : Fin (2 * g) → Fin g → ℂ)
    (R : ℝ), LinearIndependent ℝ lam → (∀ j : Fin (2 * g), lam j ∈ H) → ∑ j : Fin (2 * g), ‖lam j‖ ≤ R →
    (∀ w ∈ Metric.closedBall (0 : Fin g → ℂ) R, w ∈ H →
      ∃ m : Fin (2 * g) → ℤ, w = ∑ j : Fin (2 * g), m j • lam j) →
    GlobalTheory.ShFam.Hor.LogCh.IsLatBasis (↑H : Set (Fin g → ℂ)) lam := by
  intro g H lam R hli hmem hR hball
  have hint : ∀ m : Fin (2 * g) → ℤ, ∑ j, m j • lam j ∈ H := fun m =>
    H.sum_mem fun j _ => H.zsmul_mem (hmem j) (m j)
  refine ⟨hli, fun w => ⟨fun hw => ?_, ?_⟩⟩
  · obtain ⟨c, hc⟩ := exists_real_coords lam hli w
    have hsplit : w - ∑ j, ⌊c j⌋ • lam j = ∑ j, Int.fract (c j) • lam j := by
      rw [← hc, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Int.fract, sub_smul, Int.cast_smul_eq_zsmul]
    have hH : w - ∑ j, ⌊c j⌋ • lam j ∈ H := H.sub_mem hw (hint _)
    have hnorm : w - ∑ j, ⌊c j⌋ • lam j ∈ Metric.closedBall (0 : Fin g → ℂ) R := by
      rw [mem_closedBall_zero_iff, hsplit]
      refine (norm_sum_le _ _).trans (le_trans (Finset.sum_le_sum fun j _ => ?_) hR)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one _).le
    obtain ⟨m, hm⟩ := hball _ hnorm hH
    refine ⟨fun j => m j + ⌊c j⌋, ?_⟩
    simp only [add_smul, Finset.sum_add_distrib]
    rw [← hm, sub_add_cancel]
  · rintro ⟨m, rfl⟩
    exact hint m

end GlobalTheory.LatticeBasisClosedBall
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.eventually_localDensity_standardLattice_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (β : F), 1 ≤ M → IsHermND σ J → β ≠ 0 → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ m, FibAt (Fv F v) σ J (tupMeas (s.lamV v) 1 M) (s.nuV v) (algebraMap F (Fv F v) β) m → |(m (latV b v)).toReal - 1| * (Ideal.absNorm v.asIdeal : ℝ) ^ M ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
  first | exact @GlobalTheory.GaugeDensity.local_density_bound | exact GlobalTheory.GaugeDensity.local_density_bound | (intros; apply GlobalTheory.GaugeDensity.local_density_bound <;> assumption)
end
