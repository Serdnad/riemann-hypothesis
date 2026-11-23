module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle131
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle066
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalOfIsSupercuspidal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle320
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle314
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelDecomposition
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepFormulaF
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle321
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Geometry.Euclidean.Projection
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegCoarse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def topCut (Δ : Segment k) {s : ℕ} (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) : Fin s → Segment k := fun a =>
  Segment.ofFirst (Δ.first.nu ((∑ b ∈ Finset.univ.filter (fun b => a < b), c b : ℕ) : ℂ)) (Δ.isCusp_first.nu _)
    (c a) (hc a)

theorem isTopCut_topCut (Δ : Segment k) {s : ℕ} (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (h : ∑ a, c a = Δ.len) :
    IsTopCut Δ (topCut Δ c hc) :=
  ⟨h, fun _ => rfl⟩

theorem eq_topCut {Δ : Segment k} {s : ℕ} {Γ : Fin s → Segment k} (h : IsTopCut Δ Γ) :
    Γ = topCut Δ (fun a => (Γ a).len) (fun a => (Γ a).len_pos) :=
  funext fun a => Segment.ext_first (by rw [h.2 a]; rfl) rfl

theorem sum_split {s : ℕ} (c : Fin s → ℕ) (a : Fin s) :
    ∑ b, c b = (∑ t : Fin a, c (Fin.castLE a.2.le t)) + c a + ∑ b ∈ Finset.univ.filter (fun b => a < b), c b := by
  have h1 : ∑ t : Fin a, c (Fin.castLE a.2.le t) = ∑ b ∈ Finset.univ.filter (fun b : Fin s => b < a), c b := by
    refine Finset.sum_bij (fun t _ => Fin.castLE a.2.le t)
      (fun t _ => Finset.mem_filter.2 ⟨Finset.mem_univ _, Fin.lt_def.2 t.2⟩)
      (fun t _ u _ h => Fin.castLE_injective _ h) (fun b hb => ?_) (fun _ _ => rfl)
    have hb' : (b : ℕ) < a := Fin.lt_def.1 (Finset.mem_filter.1 hb).2
    exact ⟨⟨b, hb'⟩, Finset.mem_univ _, rfl⟩
  rw [h1]
  have h2 : ∑ b, c b = ∑ b, ((if b < a then c b else 0) + (if b = a then c b else 0) + (if a < b then c b else 0)) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    rcases lt_trichotomy b a with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.2 h.le]
  rw [h2, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
    ← Finset.sum_filter, Finset.filter_eq', if_pos (Finset.mem_univ _), Finset.sum_singleton]

theorem concat_dec_topCut (Δ : Segment k) {s : ℕ} (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (h : ∑ a, c a = Δ.len)
    (i : Fin (∑ a, c a)) : concat c (fun a => dec (topCut Δ c hc a)) i = dec Δ (Fin.cast h i) := by
  show dec (topCut Δ c hc (finSigmaFinEquiv.symm i).1) (finSigmaFinEquiv.symm i).2 = dec Δ (Fin.cast h i)
  rcases hq : finSigmaFinEquiv.symm i with ⟨a, j⟩
  have hi : (i : ℕ) = (∑ t : Fin a, c (Fin.castLE a.2.le t)) + j := by
    rw [← Equiv.apply_symm_apply finSigmaFinEquiv i, hq, finSigmaFinEquiv_apply]
  have hs := sum_split c a
  have hj : (j : ℕ) < c a := j.2
  simp only [dec, Segment.term, topCut, Segment.first_ofFirst, IrrGL.nu_nu]
  congr 1
  simp only [Fin.val_rev, Fin.val_cast, Segment.len_ofFirst]
  have key : Δ.len - (i + 1) = (∑ b ∈ Finset.univ.filter (fun b => a < b), c b) + (c a - (j + 1)) := by
    rw [← h]; omega
  rw [key]
  push_cast
  congr 1

theorem concat_injective {s : ℕ} {c : Fin s → ℕ} {x x' : ∀ a, Fin (c a) → IrrGL (k := k)} (h : concat c x = concat c x') :
    x = x' := by
  funext a j
  have := congrFun h (finSigmaFinEquiv ⟨a, j⟩)
  change (fun p : (b : Fin s) × Fin (c b) => x p.1 p.2) (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨a, j⟩)) =
    (fun p : (b : Fin s) × Fin (c b) => x' p.1 p.2) (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨a, j⟩)) at this
  rw [Equiv.symm_apply_apply] at this
  exact this

theorem concat_apply_equiv {s : ℕ} (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL (k := k)) (p : (a : Fin s) × Fin (c a)) :
    concat c x (finSigmaFinEquiv p) = x p.1 p.2 := by
  change (fun q : (b : Fin s) × Fin (c b) => x q.1 q.2) (finSigmaFinEquiv.symm (finSigmaFinEquiv p)) = _
  rw [Equiv.symm_apply_apply]

theorem sum_concat {s : ℕ} (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL (k := k)) :
    ∑ i, (concat c x i).1 = ∑ a, ∑ j, (x a j).1 := by
  rw [← Equiv.sum_comp finSigmaFinEquiv, Fintype.sum_sigma]
  simp only [concat_apply_equiv]

theorem sum_dec (Δ : Segment k) : ∑ a, (dec Δ a).1 = Δ.deg := by
  rw [← Segment.sum_term_fst]
  exact Equiv.sum_comp Fin.revPerm (fun a => (Δ.term a).1)

theorem deg_topCut (Δ : Segment k) {s : ℕ} (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (a : Fin s) :
    (topCut Δ c hc a).deg = c a * Δ.d := rfl

theorem jm_reindex {n m N : ℕ} (h : n = m) (x : Fin n → IrrGL (k := k)) (x' : Fin m → IrrGL (k := k))
    (hx : ∀ i, x i = x' (Fin.cast h i)) (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x' a).1 = N) {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) : jm x hd π = jm x' hd' π := by
  subst h
  obtain rfl : x = x' := funext fun i => by simpa using hx i
  rfl

theorem eq_of_isLSeg {Γ : Segment k} {x x' : IrrGL (k := k)} (h : IsLSeg Γ x.rep) (h' : IsLSeg Γ x'.rep) : x = x' := by
  obtain ⟨n, c⟩ := x
  obtain ⟨n', c'⟩ := x'
  have e1 := h.deg_eq
  have e2 := h'.deg_eq
  obtain rfl : n = n' := e1.symm.trans e2
  obtain ⟨φ⟩ := h.unique h'
  have := (IrrGL.of_eq_of (π := IrrGL.rep (k := k) ⟨n, c'⟩) (σ := IrrGL.rep (k := k) ⟨n, c⟩)
    (hs := c'.rep.smooth) (hi := c'.rep.irr) (hs' := c.rep.smooth) (hi' := c.rep.irr)).2 ⟨φ⟩
  rw [IrrGL.of_rep, IrrGL.of_rep] at this
  exact this.symm

end GlobalTheory.CompanionTheory.SegCoarse

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
open GlobalTheory.Parabolic (isIrreducible_of_equiv)

namespace GlobalTheory.CompanionTheory.SegFine

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V X : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X] {n : ℕ}

abbrev ev (k : Type) [Field k] (n : ℕ) : (∀ _ : Fin 1, GL (Fin n) k) →* GL (Fin n) k :=
  Pi.evalMonoidHom (fun _ : Fin 1 => GL (Fin n) k) 0

abbrev lv (τ : Representation ℂ (GL (Fin n) k) X) : Representation ℂ (∀ _ : Fin 1, GL (Fin n) k) X := τ.comp (ev k n)

theorem stdBlocks_one (h : ∑ _ : Fin 1, n = n) (a : Fin 1) (i : Fin n) :
    stdBlocks (fun _ : Fin 1 => n) h ⟨a, i⟩ = i :=
  Fin.ext (by rw [stdBlocks_val, Subsingleton.elim a 0]; simp)

theorem leviEmb_one (h : ∑ _ : Fin 1, n = n) (g : ∀ _ : Fin 1, GL (Fin n) k) :
    leviEmb k (stdBlocks (fun _ : Fin 1 => n) h) g = g 0 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have := leviEmb_apply_same k (stdBlocks (fun _ : Fin 1 => n) h) g 0 i j
  rwa [stdBlocks_one, stdBlocks_one] at this

theorem unipRad_one (h : ∑ _ : Fin 1, n = n) : unipRad k (stdBlocks (fun _ : Fin 1 => n) h) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => Units.ext (Matrix.ext fun i j => ?_)
  have := (mem_unipRad.1 hu).2 0 i j
  rwa [stdBlocks_one, stdBlocks_one] at this

def jacEquiv (h : ∑ _ : Fin 1, n = n) (π : Representation ℂ (GL (Fin n) k) V) :
    (lv π).Equiv (_root_.GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin 1 => n) h) π) := by
  have hK : twKer π (unipRad k (stdBlocks (fun _ : Fin 1 => n) h)) 1 = ⊥ := by
    rw [unipRad_one]
    refine Submodule.span_eq_bot.2 ?_
    rintro _ ⟨u, v, rfl⟩
    obtain rfl : u = 1 := Subsingleton.elim _ _
    simp
  have hd : ∀ g, deltaHalf k (fun _ : Fin 1 => Fin n) g = 1 := fun g => by
    simp [deltaHalf_apply, modExp, Finset.filter_singleton]
  let f : (lv π).IntertwiningMap (_root_.GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin 1 => n) h) π) :=
    ⟨(twKer π (unipRad k (stdBlocks (fun _ : Fin 1 => n) h)) 1).mkQ, fun g => LinearMap.ext fun v => by
      show Submodule.Quotient.mk (π (g 0) v) = _root_.GlobalTheory.SmGL.jac _ π g (Submodule.Quotient.mk v)
      rw [_root_.GlobalTheory.SmGL.jac_mk, hd, leviEmb_one]
      simp⟩
  refine equivOfBijective f ⟨(injective_iff_map_eq_zero _).2 fun v hv => ?_, Submodule.Quotient.mk_surjective _⟩
  have : v ∈ twKer π (unipRad k (stdBlocks (fun _ : Fin 1 => n) h)) 1 := (Submodule.Quotient.mk_eq_zero _).1 hv
  rw [hK] at this
  exact this

def piTensorEquiv (τ : Representation ℂ (GL (Fin n) k) X) :
    (lv τ).Equiv (piTensor fun _ : Fin 1 => τ) := by
  let L := (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 => X) 0).symm
  have hL : ∀ v, L v = PiTensorProduct.tprod ℂ fun _ => v := fun v => by
    rw [LinearEquiv.symm_apply_eq]
    simp
  let f : (lv τ).IntertwiningMap (piTensor fun _ : Fin 1 => τ) :=
    ⟨L.toLinearMap, fun g => LinearMap.ext fun v => by
      show L (τ (g 0) v) = piTensor (fun _ : Fin 1 => τ) g (L v)
      rw [hL, hL, piTensor_tprod]
      exact congrArg _ (funext fun a => by rw [Subsingleton.elim a 0])⟩
  exact equivOfBijective f L.bijective

def subrepComp (τ : Representation ℂ (GL (Fin n) k) X) :
    Subrepresentation (lv τ) ≃o Subrepresentation τ where
  toFun S := ⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (fun _ => g) hv⟩
  invFun S := ⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (g 0) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_comp {τ : Representation ℂ (GL (Fin n) k) X} (h : τ.IsIrreducible) :
    (lv τ).IsIrreducible := (subrepComp τ).isSimpleOrder_iff.2 h

theorem jhMult_one (h : ∑ _ : Fin 1, n = n) (τ : Representation ℂ (GL (Fin n) k) X)
    (π : Representation ℂ (GL (Fin n) k) V) :
    jhMult (piTensor fun _ : Fin 1 => τ) (_root_.GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin 1 => n) h) π) =
      jhMult (lv τ) (lv π) := by
  rw [← jhMult_congr_left (piTensorEquiv τ), ← jhMult_congr_right _ (jacEquiv h π)]

theorem jm_eq_one (x : IrrGL (k := k)) (π : Representation ℂ (GL (Fin x.1) k) V) (φ : π.Equiv x.rep)
    (y : Fin 1 → IrrGL (k := k)) (hy : ∑ a, (y a).1 = x.1) (hyx : y = fun _ => x) : jm y hy π = 1 := by
  subst hyx
  refine (jhMult_one hy x.rep π).trans ?_
  rw [jhMult_congr_right _ (compEquiv φ (ev k x.1))]
  exact jhMult_self (isIrreducible_comp x.2.rep.irr)

theorem eq_of_one_le_jm (x : IrrGL (k := k)) (π : Representation ℂ (GL (Fin x.1) k) V) (φ : π.Equiv x.rep)
    (y : Fin 1 → IrrGL (k := k)) (hy : ∑ a, (y a).1 = x.1) (h : 1 ≤ jm y hy π) : y 0 = x := by
  obtain ⟨z, rfl⟩ : ∃ z, y = fun _ => z := ⟨y 0, funext fun a => by rw [Subsingleton.elim a 0]⟩
  obtain ⟨d, c⟩ := z
  obtain ⟨m, b⟩ := x
  obtain rfl : d = m := by simpa using hy
  have h0 : jhMult (lv c.rep.ρ) (lv π) ≠ 0 := by
    rw [← jhMult_one hy]
    exact ENat.one_le_iff_ne_zero.1 h
  have hπ : π.IsIrreducible := isIrreducible_of_equiv φ.symm b.rep.irr
  obtain ⟨E⟩ := (jhMult_ne_zero_iff.1 h0).nonempty_equiv (isIrreducible_comp c.rep.irr) (isIrreducible_comp hπ)
  let f : π.IntertwiningMap c.rep.ρ := ⟨E.toLinearEquiv.toLinearMap, fun g => LinearMap.ext fun v =>
    E.toIntertwiningMap.isIntertwining _ _ (fun _ => g) v⟩
  have E' : c.rep.ρ.Equiv b.rep.ρ := (equivOfBijective f E.toLinearEquiv.bijective).symm.trans φ
  exact congrArg (Sigma.mk d) (irrCl_eq_iff.2 ⟨E'⟩)

theorem dec_single (ρ : IrrGL (k := k)) (hρ : ρ.IsCusp) : dec (Segment.single ρ hρ) = fun _ => ρ := funext fun a => by
  show ρ.nu (((Fin.rev (a : Fin 1) : Fin 1) : ℕ) : ℂ) = ρ
  simp [Fin.val_eq_zero]

theorem not_one_le_jm {N c : ℕ} {π : Representation ℂ (GL (Fin N) k) V} (hπ : IsCuspidal π)
    (y : Fin (c + 2) → IrrGL (k := k)) (hy : ∑ a, (y a).1 = N) (hc : ∀ a, (y a).IsCusp) : ¬ 1 ≤ jm y hy π := by
  intro h
  have hne : unipRad k (stdBlocks (fun a => (y a).1) hy) ≠ ⊥ := CuspMax.unipRad_ne_bot_iff.2
    ⟨stdBlocks (fun a => (y a).1) hy ⟨0, ⟨0, (hc 0).1⟩⟩, stdBlocks (fun a => (y a).1) hy ⟨1, ⟨0, (hc 1).1⟩⟩, by simp⟩
  have := hπ.2 _ _ _ hne
  have hn : Nontrivial (PiTensorProduct ℂ fun a => (y a).2.rep.V) :=
    GlobalTheory.ProdSupport.nontrivial_piTensor _ fun a => Model.nontrivial_of_isIrreducible (y a).2.rep.irr
  obtain ⟨S, f, hf⟩ := jhMult_ne_zero_iff.1 (ENat.one_le_iff_ne_zero.1 h)
  exact not_subsingleton _ hf.subsingleton

theorem fineJac_one (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (h : Δ.len = 1) : FineJac Δ := by
  obtain ⟨ρ, hρ, rfl⟩ : ∃ ρ hρ, Δ = Segment.single ρ hρ :=
    ⟨Δ.first, Δ.isCusp_first, Segment.ext_first rfl h⟩
  intro N V _ _ π hπ
  obtain rfl : ρ.1 = N := by
    have := hπ.deg_eq
    simpa [Segment.deg, Segment.single, Segment.ofFirst] using this
  obtain ⟨φ⟩ := (single_spec hρ).2.1.unique hπ
  refine ⟨fun hd => jm_eq_one ρ π φ _ hd (dec_single ρ hρ), fun c y hy hc h1 => ?_⟩
  rcases c with _ | _ | c
  · exact absurd hy (by simpa using hρ.1.ne)
  · have key : ∀ (z : Fin 1 → IrrGL (k := k)) (hz : ∑ a, (z a).1 = ρ.1), 1 ≤ jm z hz π →
        ∀ a, z a = ρ := fun z hz h1 a => by
      rw [Subsingleton.elim a 0]
      exact eq_of_one_le_jm ρ π φ z hz h1
    exact ⟨rfl, fun a => (key y hy h1 a).trans (congrFun (dec_single ρ hρ) _).symm⟩
  · exact absurd h1 (not_one_le_jm (isCuspidal_of_equiv φ.symm hρ.2) y hy hc)

end GlobalTheory.CompanionTheory.SegFine

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.DualCusp

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]

theorem isSupercuspidal_contra
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    {π : Representation ℂ G V} (hπ : IsAdmissible π) (hs : IsSupercuspidal π) :
    IsSupercuspidal (contra π) := by
  refine ⟨isSmooth_contra π, fun l Λ hΛ => ?_⟩
  obtain ⟨u, hu⟩ := (GlobalTheory.ContraRefl.evMap_bijective hG hπ).2 ⟨Λ, hΛ⟩
  have hev : ∀ m : smoothPart π.dual, Λ m = (m : Module.Dual ℂ V) u := fun m =>
    (LinearMap.congr_fun (congrArg Subtype.val hu) m).symm
  obtain ⟨C, hC, hsupp⟩ := hs.2 u l l.2
  open scoped Pointwise in
    refine ⟨C⁻¹, hC.inv, fun g hg => ?_⟩
    rw [hev, contra_apply] at hg
    obtain ⟨z, hz, c, hc, e⟩ := hsupp g⁻¹ hg
    refine ⟨z⁻¹, inv_mem hz, c⁻¹, Set.inv_mem_inv.2 hc, ?_⟩
    have h1 : g = (z * c)⁻¹ := by rw [← e, inv_inv]
    rw [h1, mul_inv_rev]
    exact (Subgroup.mem_center_iff.1 (inv_mem hz) c⁻¹)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dualCl_isCusp (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) (hx : x.IsCusp) :
    (dualCl x).IsCusp ∧ (dualCl x).1 = x.1 := by
  have hadm : IsAdmissible x.rep := hA k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr
  have hG := GlobalTheory.SqIntUnit.compactOpen_basis k x.1
  have hirr : (contra x.rep).IsIrreducible := GlobalTheory.ContraRefl.contra_isIrreducible hG hadm x.2.rep.irr
  have hd : dualCl x = IrrGL.of (contra x.rep) (isSmooth_smoothRep _) hirr := dif_pos hirr
  rw [hd]
  refine ⟨IrrGL.isCusp_of.2 ⟨hx.1, ?_⟩, rfl⟩
  exact GlobalTheory.SuperCusp.isCuspidal_of_isSupercuspidal k x.1 _ _
    (isSupercuspidal_contra hG hadm (GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal k x.1 _ _ hx.2))

end GlobalTheory.CompanionTheory.DualCusp

end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

theorem _root_.GlobalTheory.T.jacquet_multiplicity_ne_zero_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), Zc.jm x hd π ≠ 0 → ∃ S T : Subrepresentation (_root_.GlobalTheory.SmGL.jac (stdBlocks (fun a => (x a).1) hd) π), Nonempty ((subQuot S T).Equiv (piTensor fun a => (x a).rep)) := by
  first | exact @GlobalTheory.CompanionTheory.JmSub.exists_subQuot_of_jm_ne_zero | exact GlobalTheory.CompanionTheory.JmSub.exists_subQuot_of_jm_ne_zero | (intros; apply GlobalTheory.CompanionTheory.JmSub.exists_subQuot_of_jm_ne_zero <;> assumption)
end

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

theorem _root_.GlobalTheory.T.segment_jacquet_two_factor_split : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k) (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), Zc.LSegJacquet k → IsLSeg Δ π → ∀ (x : Fin 2 → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), (∀ a, 0 < (x a).1) → Zc.jm x hd π ≠ 0 → ∃ Γ : Fin 2 → Segment k, Zc.IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (x a).rep := by
  first | exact @GlobalTheory.CompanionTheory.SegJacquet.exists_isTopCut_two_of_jhMult_ne_zero | exact GlobalTheory.CompanionTheory.SegJacquet.exists_isTopCut_two_of_jhMult_ne_zero | (intros; apply GlobalTheory.CompanionTheory.SegJacquet.exists_isTopCut_two_of_jhMult_ne_zero <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.LUniq

theorem isL_unique : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    LOrderFree k → ∀ (𝔭 : Multiset (Segment k)) {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W),
    IsL 𝔭 π → IsL 𝔭 σ → Nonempty (π.Equiv σ) := by
  intro k _ _ _ _ hLO 𝔭 N V W _ _ _ _ π σ hπ hσ
  obtain ⟨h, x, hd, hx, hπc⟩ := hπ
  have hσc : IsCosocle σ (prodIrr x hd) := hLO 𝔭 h N x hd hx σ hσ
  exact hσc.unique hπc

end GlobalTheory.CompanionTheory.LUniq
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.Canon

theorem isRevOrdered_of_isCanon {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h : ℕ} (Γ : Fin h → Segment k) : IsCanon Γ → IsRevOrdered Γ :=
  fun hc i j hij hp => (hc.1 i j hij).1 hp.2

end GlobalTheory.CompanionTheory.Canon
end

section


theorem _root_.GlobalTheory.T.finite_propagation_speed_holds : PositivityTheory.RgBcC.AsmSpeed := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.asmSpeed | exact GlobalTheory.CompanionTheory.WaveSpd.asmSpeed | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.asmSpeed <;> assumption)
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.wave_kernel_decomposition : LgFacts → Unimod → RCalc → WaveSpeed → WaveEx → KerUniq → KerOne → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (w : List (Bool × ℕ)) (g : ℝ → ℝ) (T : ℝ) (k : Mat n → (E.V →L[ℂ] E.V)), IsBump g T → IsKer μ E w g k → ∃ (N : ℕ) (c : Fin N → ℂ) (w₁ : Fin N → List (Bool × ℕ)) (K : Fin N → Mat n → (E.V →L[ℂ] E.V)), (∀ i, IsKer μ E (w₁ i) g (K i)) ∧ (haveI := FiniteDimensional.complete ℂ E.V; ∀ y ∈ GLs n, ContinuousLinearMap.adjoint (k y⁻¹) = ∑ i, c i • K i y) ∧ ∀ χ : Inf n, IsHerm χ → conj (zVal w χ) = ∑ i, c i * zVal (w₁ i) χ := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.KerAdj.kernel_adjoint | exact GlobalTheory.CompanionTheory.WaveMult.KerAdj.kernel_adjoint | (intros; apply GlobalTheory.CompanionTheory.WaveMult.KerAdj.kernel_adjoint <;> assumption)
end

section


theorem _root_.GlobalTheory.T.irreducible_of_discrete_series_datum : PositivityTheory.RgDs.Hilb.StepDatum → PositivityTheory.RgDs.Hilb.StepIrred := by
  first | exact @GlobalTheory.CompanionTheory.RgDsHilb.stepIrred_of_stepDatum | exact GlobalTheory.CompanionTheory.RgDsHilb.stepIrred_of_stepDatum | (intros; apply GlobalTheory.CompanionTheory.RgDsHilb.stepIrred_of_stepDatum <;> assumption)
end

section


theorem _root_.GlobalTheory.T.vogan_minimal_type_statement : PositivityTheory.RgDs.Hilb.StepVogan := by
  first | exact @GlobalTheory.CompanionTheory.DiscreteSeries.stepVogan | exact GlobalTheory.CompanionTheory.DiscreteSeries.stepVogan | (intros; apply GlobalTheory.CompanionTheory.DiscreteSeries.stepVogan <;> assumption)
end

section


theorem _root_.GlobalTheory.T.weight_vectors_span_dense : PositivityTheory.RgDs.Hilb.StepWtSpan := by
  first | exact @GlobalTheory.CompanionTheory.RgDsHilb.stepWtSpan | exact GlobalTheory.CompanionTheory.RgDsHilb.stepWtSpan | (intros; apply GlobalTheory.CompanionTheory.RgDsHilb.stepWtSpan <;> assumption)
end
