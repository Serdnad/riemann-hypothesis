module

import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle081
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle350
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle026
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle124
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle356
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle317
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle349
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle351
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.MoyPrasadJacquetIsoTrivial
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle248
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle209
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle215
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle230
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle358
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc GlobalTheory.SplitWeil

namespace GlobalTheory.CompanionTheory.HalfModCompact

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_nabs_le_of_isCompact {C : Set k} (hC : IsCompact C) :
    ∃ B : ℝ, ∀ u : kˣ, (u : k) ∈ C → nabs k u ≤ B := by
  apply GlobalTheory.ZetaConvergence.exists_nabs_le <;> assumption

theorem nabs_pow_eq (y : kˣ) (n : ℕ) : nabs k (y ^ n) = nabs k y ^ n := by
  unfold nabs
  rw [map_pow, NNReal.coe_pow]

theorem nabs_inv_eq (y : kˣ) : nabs k y⁻¹ = (nabs k y)⁻¹ := by
  unfold nabs
  rw [map_inv, NNReal.coe_inv]

theorem nabs_eq_one_of_pow_le (y : kˣ) (B : ℝ) (h₁ : ∀ n : ℕ, nabs k (y ^ n) ≤ B)
    (h₂ : ∀ n : ℕ, nabs k (y⁻¹ ^ n) ≤ B) : nabs k y = 1 := by
  have hpos : 0 < nabs k y := (nabs_properties k).2.1 y
  rcases lt_trichotomy (nabs k y) 1 with hlt | heq | hgt
  · exfalso
    have hinv : 1 < (nabs k y)⁻¹ := (one_lt_inv₀ hpos).2 hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B hinv
    have h3 := h₂ n
    rw [nabs_pow_eq, nabs_inv_eq] at h3
    linarith
  · exact heq
  · exfalso
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B hgt
    have h3 := h₁ n
    rw [nabs_pow_eq] at h3
    linarith

def blockDet {N h : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (a : Fin h) (g : GL (Fin N) k) : k :=
  Matrix.det (Matrix.of fun i j : Fin (d a) =>
    (g : Matrix (Fin N) (Fin N) k) (stdBlocks d hd ⟨a, i⟩) (stdBlocks d hd ⟨a, j⟩))

theorem continuous_blockDet {N h : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (a : Fin h) :
    Continuous (blockDet (k := k) d hd a) := by
  unfold blockDet
  first
    | fun_prop
    | exact Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j =>
        (Units.continuous_val.matrix_elem _ _))

theorem blockDet_leviEmb {N h : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (a : Fin h)
    (x : Levi k (Bl d)) :
    blockDet d hd a (leviEmb k (stdBlocks d hd) x) =
      ((Matrix.GeneralLinearGroup.det (x a) : kˣ) : k) := by
  unfold blockDet
  have hm : (Matrix.of fun i j : Fin (d a) =>
      ((leviEmb k (stdBlocks d hd) x : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)
        (stdBlocks d hd ⟨a, i⟩) (stdBlocks d hd ⟨a, j⟩)) =
      ((x a : GL (Bl d a) k) : Matrix (Bl d a) (Bl d a) k) := by
    ext i j
    simp [leviEmb, Matrix.blockDiagonal'_apply_eq]
  rw [hm, Matrix.GeneralLinearGroup.val_det_apply]

theorem nabs_det_eq_one_of_mem_KM {N h : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)
    {J : Subgroup (GL (Fin N) k)} (hJ : IsCompact (J : Set (GL (Fin N) k)))
    {x : Levi k (Bl d)} (hx : x ∈ KM k N J d hd) (a : Fin h) :
    nabs k (Matrix.GeneralLinearGroup.det (x a)) = 1 := by
  have hmem : ∀ z ∈ KM k N J d hd, blockDet d hd a (leviEmb k (stdBlocks d hd) z) ∈
      blockDet (k := k) d hd a '' (J : Set (GL (Fin N) k)) :=
    fun z hz => ⟨_, hz, rfl⟩
  obtain ⟨B, hB⟩ := exists_nabs_le_of_isCompact (hJ.image (continuous_blockDet d hd a))
  apply nabs_eq_one_of_pow_le _ B
  · intro n
    apply hB
    have h1 := hmem _ ((KM k N J d hd).pow_mem hx n)
    have e : (x ^ n) a = x a ^ n := rfl
    rw [blockDet_leviEmb, e, map_pow] at h1
    exact h1
  · intro n
    apply hB
    have h1 := hmem _ ((KM k N J d hd).pow_mem ((KM k N J d hd).inv_mem hx) n)
    have e : (x⁻¹ ^ n) a = (x a)⁻¹ ^ n := rfl
    rw [blockDet_leviEmb, e, map_pow, map_inv] at h1
    exact h1

theorem deltaHalf_eq_one_of_mem_KM :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)),
      IsCompact (J : Set (GL (Fin N) k)) → ∀ x ∈ KM k N J d hd, deltaHalf k (Bl d) x = 1 := by
  intro k _ _ _ _ N h d hd J hJ x hx
  unfold deltaHalf
  rw [MonoidHom.finsetProd_apply]
  apply Finset.prod_eq_one
  intro a _
  rw [MonoidHom.comp_apply, Pi.evalMonoidHom_apply]
  unfold detChar
  rw [MonoidHom.comp_apply]
  apply Units.ext
  simp [absPow, nabs_det_eq_one_of_mem_KM d hd hJ hx a]

end GlobalTheory.CompanionTheory.HalfModCompact
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos Matrix

namespace GlobalTheory.CompanionTheory.FineProd.JmDrop

section Blocks

variable {R : Type} [Field R] {r r' : ℕ} {d : Fin r → ℕ} {o : Fin r' → Fin r}

theorem dropHom_surjective (ho : Function.Injective o) :
    Function.Surjective (GlobalTheory.CompanionTheory.FineProd.dropHom (k := R) d o) := by
  classical
  intro x
  have key : ∀ (j : Fin r) (b : Fin r') (hb : o b = j) (a : Fin r') (ha : o a = j),
      (hb ▸ x b : GL (Fin (d j)) R) = ha ▸ x a := by
    intro j b hb a ha
    obtain rfl : b = a := ho (hb.trans ha.symm)
    rfl
  refine ⟨(fun j => if hj : ∃ a, o a = j then hj.choose_spec ▸ x hj.choose else 1 :
    ∀ j, GL (Fin (d j)) R), ?_⟩
  funext a
  have hj : ∃ b, o b = o a := ⟨a, rfl⟩
  show (if hj : ∃ b, o b = o a then (hj.choose_spec ▸ x hj.choose : GL (Fin (d (o a))) R) else 1) = x a
  rw [dite_eq_left hj]
  exact key (o a) _ hj.choose_spec a rfl

variable {n : Type} [Fintype n] [DecidableEq n]
  {e : (Σ j, Fin (d j)) ≃ n} {e' : (Σ a, Fin (d (o a))) ≃ n}

theorem unipRad_eq (hm : StrictMono o) (hne : ∀ j, d j ≠ 0 → j ∈ Set.range o)
    (he : ∀ a t, e' ⟨a, t⟩ = e ⟨o a, t⟩) : unipRad R e = unipRad R e' := by
  ext g
  rw [GlobalTheory.SmGL.mem_unipRad, GlobalTheory.SmGL.mem_unipRad,
    GlobalTheory.SmGL.mem_parab_iff, GlobalTheory.SmGL.mem_parab_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun a b i j hab => ?_, fun a i j => ?_⟩
    · rw [he, he]
      exact h1 _ _ i j (hm hab)
    · rw [he, he]
      exact h2 _ i j
  · rintro ⟨h1, h2⟩
    refine ⟨fun A B i j hBA => ?_, fun A i j => ?_⟩
    · obtain ⟨a, rfl⟩ := hne A (Fin.pos i).ne'
      obtain ⟨b, rfl⟩ := hne B (Fin.pos j).ne'
      rw [← he, ← he]
      exact h1 a b i j (hm.lt_iff_lt.1 hBA)
    · obtain ⟨a, rfl⟩ := hne A (Fin.pos i).ne'
      rw [← he, ← he]
      exact h2 a i j

theorem leviEmb_eq (hm : StrictMono o) (he : ∀ a t, e' ⟨a, t⟩ = e ⟨o a, t⟩)
    (g : Levi R fun j => Fin (d j)) :
    leviEmb R e g = leviEmb R e' (GlobalTheory.CompanionTheory.FineProd.dropHom (k := R) d o g) := by
  apply Units.ext
  ext p q
  obtain ⟨⟨a, i⟩, rfl⟩ := e'.surjective p
  obtain ⟨⟨b, j⟩, rfl⟩ := e'.surjective q
  by_cases hab : a = b
  · subst hab
    have h1 := GlobalTheory.SmGL.leviEmb_apply_same R e g (o a) i j
    have h2 := GlobalTheory.SmGL.leviEmb_apply_same R e'
      (GlobalTheory.CompanionTheory.FineProd.dropHom (k := R) d o g) a i j
    rw [← he, ← he] at h1
    exact h1.trans h2.symm
  · have h1 := GlobalTheory.SmGL.leviEmb_apply_ne R e g (hm.injective.ne hab) i j
    have h2 := GlobalTheory.SmGL.leviEmb_apply_ne R e'
      (GlobalTheory.CompanionTheory.FineProd.dropHom (k := R) d o g) hab i j
    rw [← he, ← he] at h1
    exact h1.trans h2.symm


omit [Fintype n] [DecidableEq n] in
theorem modExp_drop (hm : StrictMono o) (hne : ∀ j, d j ≠ 0 → j ∈ Set.range o) (a : Fin r') :
    modExp (fun b => Fin (d (o b))) a = modExp (fun j => Fin (d j)) (o a) := by
  unfold GlobalTheory.SmGL.modExp
  congr 1
  all_goals
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Fintype.sum_of_injective o hm.injective _ _ (fun j hj => ?_) (fun b => ?_)
    · by_cases hd : d j = 0
      · simp [hd]
      · exact absurd (hne j hd) hj
    · simp [hm.lt_iff_lt]

end Blocks

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r r' : ℕ} {d : Fin r → ℕ} {o : Fin r' → Fin r}

theorem deltaHalf_drop (hm : StrictMono o) (hne : ∀ j, d j ≠ 0 → j ∈ Set.range o)
    (g : Levi k fun j => Fin (d j)) :
    deltaHalf k (fun j => Fin (d j)) g =
      deltaHalf k (fun a => Fin (d (o a))) (GlobalTheory.CompanionTheory.FineProd.dropHom (k := k) d o g) := by
  apply GlobalTheory.CompanionTheory.FineProd.ProdDrop.deltaHalf_drop <;> assumption

variable {n : Type} [Fintype n] [DecidableEq n]
  {e : (Σ j, Fin (d j)) ≃ n} {e' : (Σ a, Fin (d (o a))) ≃ n}
  {V : Type} [AddCommGroup V] [Module ℂ V]

def jacDrop (hm : StrictMono o) (hne : ∀ j, d j ≠ 0 → j ∈ Set.range o)
    (he : ∀ a t, e' ⟨a, t⟩ = e ⟨o a, t⟩) (π : Representation ℂ (GL n k) V) :
    (_root_.GlobalTheory.SmGL.jac e π).Equiv
      ((_root_.GlobalTheory.SmGL.jac e' π).comp (GlobalTheory.CompanionTheory.FineProd.dropHom (k := k) d o) :
        Representation ℂ (Levi k fun j => Fin (d j)) _) :=
  have h3 : twKer π (unipRad k e) 1 = twKer π (unipRad k e') 1 := by rw [unipRad_eq hm hne he]
  .mk (Submodule.quotEquivOfEq _ _ h3) fun g => by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
    show Submodule.quotEquivOfEq _ _ h3 (_root_.GlobalTheory.SmGL.jac e π g (Submodule.Quotient.mk v)) =
      _root_.GlobalTheory.SmGL.jac e' π (GlobalTheory.CompanionTheory.FineProd.dropHom (k := k) d o g) (Submodule.Quotient.mk v)
    rw [_root_.GlobalTheory.SmGL.jac_mk, _root_.GlobalTheory.SmGL.jac_mk, map_smul, deltaHalf_drop hm hne, leviEmb_eq hm he]
    rfl

end Local

theorem jm_drop : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r r' N : ℕ} (y : Fin r → IrrGL (k := k)) (hd : ∑ a, (y a).1 = N) (o : Fin r' → Fin r), StrictMono o → (∀ j, (y j).1 ≠ 0 → j ∈ Set.range o) → ∀ (hd' : ∑ a, (y (o a)).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), jm y hd π = jm (fun a => y (o a)) hd' π := by
  intro k _ _ _ _ r r' N y hd o hm hne hd' V _ _ π
  have he := GlobalTheory.T.standard_blocks_reindex_strictMono (fun j => (y j).1) hd o hm hne hd'
  obtain ⟨φ⟩ := GlobalTheory.T.tensor_product_drop_zero_factors y o hm hne
  unfold Zc.jm
  rw [GlobalTheory.SmGL.jhMult_congr_left φ,
    GlobalTheory.SmGL.jhMult_congr_right _
      (GlobalTheory.CompanionTheory.FineProd.JmDrop.jacDrop (d := fun j => (y j).1) (o := o) hm hne he π),
    GlobalTheory.SmGL.EmptyBlocks.jhMult_comp_surjective _
      (GlobalTheory.CompanionTheory.FineProd.JmDrop.dropHom_surjective (R := k) (d := fun j => (y j).1) hm.injective)]

end GlobalTheory.CompanionTheory.FineProd.JmDrop

end
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Fib

section Abstract

variable {G D W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddGroup D] [TopologicalSpace D] [IsTopologicalAddGroup D]
  [AddCommGroup W] [Module ℂ W]

theorem isLocallyConstant_translate (H : Subgroup G) (σ : Representation ℂ H W)
    (f : smoothPart (ind H σ)) (e : D → G) (he : Continuous e) (h0 : e 0 = 1)
    (hadd : ∀ a b, e (a + b) = e a * e b) (y : G) :
    IsLocallyConstant (fun d => f.1.1 (e d * y)) := by
  have hK : IsOpen {g : G | ind H σ g f.1 = f.1} := f.2
  let c : D → G := fun a => y⁻¹ * e a * y
  have hc : Continuous c := by fun_prop
  have hU : IsOpen (c ⁻¹' {g : G | ind H σ g f.1 = f.1}) := hK.preimage hc
  rw [IsLocallyConstant.iff_exists_open]
  intro d
  refine ⟨(fun x => -d + x) ⁻¹' (c ⁻¹' {g : G | ind H σ g f.1 = f.1}), hU.preimage (by fun_prop), ?_, ?_⟩
  · show ind H σ (c (-d + d)) f.1 = f.1
    simp [c, h0]
  · intro x hx
    have hx' : ind H σ (c (-d + x)) f.1 = f.1 := hx
    have h1 : e x = e d * e (-d + x) := by rw [← hadd, add_neg_cancel_left]
    have h2 := congrArg (fun v : indSpace H σ => v.1 (e d * y)) hx'
    have h3 : (ind H σ (c (-d + x)) f.1).1 (e d * y) = f.1.1 (e d * y * c (-d + x)) := rfl
    simp only [h3] at h2
    have h4 : e d * y * c (-d + x) = e x * y := by
      simp only [c, h1]; group
    simpa [h4] using h2

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ePG_true_val (i t : ℕ) (b : Fin t) : ((ePG i t ⟨true, b⟩ : Fin (i + t + 1)) : ℕ) = i + b := by
  simp [ePG]

theorem dEmb_zero (i t : ℕ) : dEmb k i t 0 = 1 := by
  apply Subtype.ext
  have : Fin.append (0 : Fin (i + 1) → k) (0 : Fin (t + 1) → k) = 0 := by
    funext x; refine Fin.addCases ?_ ?_ x <;> simp
  simp [dEmb, this]

theorem dEmb_add (i t : ℕ) (a b : Fin (t + 1) → k) : dEmb k i t (a + b) = dEmb k i t a * dEmb k i t b := by
  apply Subtype.ext
  have : Fin.append (0 : Fin (i + 1) → k) (a + b) = Fin.append (0 : Fin (i + 1) → k) a + Fin.append (0 : Fin (i + 1) → k) b := by
    funext x; refine Fin.addCases ?_ ?_ x <;> simp
  simp only [dEmb, Subgroup.coe_mul, this, ofAdd_add, map_mul]

theorem continuous_dEmb (i t : ℕ) : Continuous (dEmb k i t) := by
  apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Small.continuous_dEmb <;> assumption

theorem dEmb_mul_entry (i t : ℕ) (d : Fin (t + 1) → k) (g : Mir k ((i + 1) + t + 1)) (b : Fin (t + 1)) :
    (((dEmb k i t d * g : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
        Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc (Fin.natAdd (i + 1) b)) (Fin.last _) =
    ((g : GL (Fin ((i + 1) + t + 2)) k) : Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc (Fin.natAdd (i + 1) b)) (Fin.last _) + d b := by
  have hg : ((g : GL (Fin ((i + 1) + t + 2)) k) : Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.last _) (Fin.last _) = 1 := by
    have := congrFun ((mem_Mir_iff k _).1 g.2) (Fin.last _)
    simpa [eLast] using this
  have hv : ((dEmb k i t d : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k).val =
      1 + colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d) := rfl
  have hc : colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d)
      (Fin.castSucc (Fin.natAdd (i + 1) b)) (Fin.last _) = d b := by
    simp only [colMat, if_true, Fin.lastCases_castSucc, Fin.append_right]
  rw [Subgroup.coe_mul, Units.val_mul, hv, add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply,
    Finset.sum_eq_single (Fin.last _)]
  · rw [hc]
    exact congrArg (_ + ·) ((congrArg (d b * ·) hg).trans (mul_one _))
  · intro l _ hl
    simp [colMat, hl]
  · simp

theorem hpg_entry_eq_zero (i t : ℕ) (h : Mir k ((i + 1) + t + 1)) (hh : h ∈ HPG k (i + 1) (t + 1)) (b : Fin (t + 1)) :
    ((h : GL (Fin ((i + 1) + t + 2)) k) : Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc (Fin.natAdd (i + 1) b)) (Fin.last _) = 0 := by
  have h1 := mem_parab_iff.1 (show ((h : GL (Fin ((i + 1) + (t + 1) + 1)) k)) ∈ parab k (ePG (i + 1) (t + 1)) from hh)
    true false b (Fin.last (i + 1)) (by decide)
  rw [ePG_false_last] at h1
  have h2 : ePG (i + 1) (t + 1) ⟨true, b⟩ = Fin.castSucc (Fin.natAdd (i + 1) b) := by
    apply Fin.ext
    rw [ePG_true_val]
    simp
  rw [h2] at h1
  exact h1

theorem fibre_isLocallyConstant_hasCompactSupport (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (y : Mir k ((i + 1) + t + 1)) :
    IsLocallyConstant (fun d : Fin (t + 1) → k => evX f (dEmb k i t d * y)) ∧
      HasCompactSupport (fun d : Fin (t + 1) → k => evX f (dEmb k i t d * y)) := by
  refine ⟨isLocallyConstant_translate (HPG k (i + 1) (t + 1)) (sigX τ σ) f.1 (dEmb k i t) (continuous_dEmb i t)
    (dEmb_zero i t) (dEmb_add i t) y, ?_⟩
  obtain ⟨C, hC, hf⟩ := f.2
  let φ : Mir k ((i + 1) + t + 1) → Fin (t + 1) → k := fun c b =>
    -(((y * c⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
        Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc (Fin.natAdd (i + 1) b)) (Fin.last _)
  have hφ : Continuous φ := by
    refine continuous_pi fun b => Continuous.neg ?_
    have h1 : Continuous fun c : Mir k ((i + 1) + t + 1) =>
        (((y * c⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
          Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k) :=
      Units.continuous_val.comp (continuous_subtype_val.comp (continuous_const.mul continuous_inv))
    exact (continuous_apply_apply _ _).comp h1
  refine HasCompactSupport.intro (hC.image hφ) fun x hx => ?_
  by_contra hne
  obtain ⟨h, hh, c, hc, e⟩ := hf (dEmb k i t x * y) hne
  refine hx ⟨c, hc, ?_⟩
  have e1 : h = dEmb k i t x * (y * c⁻¹) := by
    rw [← mul_assoc]
    exact eq_mul_inv_of_mul_eq e.symm
  funext b
  have h0 := hpg_entry_eq_zero i t h hh b
  rw [e1, dEmb_mul_entry] at h0
  exact neg_eq_of_add_eq_zero_right h0

end GlobalTheory.CompanionTheory.BZPhiPG.Fib
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

theorem _root_.GlobalTheory.T.cuspidal_support_realised_by_product : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (s : Multiset (IrrGL (k := k))), HasSupport π s → ∃ (h : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), Finset.univ.val.map x = s ∧ (∀ a, (x a).IsCusp) ∧ IsSubquotient π (prodIrr x hd) := by
  first | exact @GlobalTheory.CompanionTheory.GenSupp.hasSupport_std | exact GlobalTheory.CompanionTheory.GenSupp.hasSupport_std | (intros; apply GlobalTheory.CompanionTheory.GenSupp.hasSupport_std <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

theorem _root_.GlobalTheory.T.nonempty_equiv_subQuot_of_not_le_sup : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (T : Submodule ℂ V), Module.rank ℂ (V ⧸ T) ≤ 1 → (∀ X Y : Subrepresentation ρ, (X ⊔ Y).toSubmodule ⊓ T ≤ X.toSubmodule ⊓ T ⊔ Y.toSubmodule ⊓ T) → ∀ A B C D : Subrepresentation ρ, B ≤ A → D ≤ C → (subQuot A B).IsIrreducible → (subQuot C D).IsIrreducible → ¬ A.toSubmodule ≤ B.toSubmodule ⊔ T → ¬ C.toSubmodule ≤ D.toSubmodule ⊔ T → Nonempty ((subQuot A B).Equiv (subQuot C D)) := by
  first | exact @GlobalTheory.CompanionTheory.GenCoreMain.nonempty_equiv_of_generic | exact GlobalTheory.CompanionTheory.GenCoreMain.nonempty_equiv_of_generic | (intros; apply GlobalTheory.CompanionTheory.GenCoreMain.nonempty_equiv_of_generic <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.MoyPrasadTop

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

theorem moyPrasadJacquetIso : GlobalTheory.Published.MoyPrasadJacquetIso := by
  intro k _ _ _ _ n s d e V _ _ π hπ
  refine ⟨mapsTo_fixed_jacU e π _, ?_, ?_⟩
  · intro v hv w hw h
    have h0 : (Submodule.Quotient.mk (v - w) : Jacquet π (unipRad k e)) = 0 := by
      rw [Submodule.Quotient.mk_sub]
      exact sub_eq_zero.2 h
    exact sub_eq_zero.1 (GlobalTheory.CompanionTheory.DepthZeroJac.fixed_inj_smooth k n s d e V π hπ.1 (v - w) (sub_mem hv hw) h0)
  · intro y hy
    obtain ⟨v, hv, hvy⟩ := GlobalTheory.CompanionTheory.JacquetCentral.exists_fixed_mk_eq_of_commute π hπ (Gx k e) (unipRad k e) (GlobalTheory.CompanionTheory.MoyPrasad.isOpen_Gx k n s d e)
      (GlobalTheory.T.isCompact_parahoric_subgroup k n s d e) (leviEmb k e) (leviEmb_mem_normalizer k e) ((Gx k e).comap (leviEmb k e))
      (fun _ hm => hm) (lowC k e) (GlobalTheory.T.parahoric_levi_unipotent_lower k n s d e)
      (fun U hU => by
        refine (GlobalTheory.T.central_torus_contracts_lower k n s d e U hU).imp ?_
        intro t ht
        exact ⟨fun m _ => ht.1 m, ht.2⟩) y hy
    exact ⟨v, hv, hvy⟩

end GlobalTheory.CompanionTheory.MoyPrasadTop

end
end
