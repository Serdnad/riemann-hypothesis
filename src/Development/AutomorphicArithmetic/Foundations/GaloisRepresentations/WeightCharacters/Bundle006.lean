module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BlockCharacterApproximation.NeatOfPlace
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundTheorem
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.neatLev_of :
    UpperTheory.Gal.Wt.NeatLev := by
  intro E _ _ _ l hl a ha w₀ hmem hs v' hv' hap K hK hint Kv hKv W f hf
  obtain ⟨N, hN, hNf⟩ := UpperTheory.Gal.Gen.smoothAt_holds E a w₀ hs W f
  obtain ⟨J, hJ, hJN, hJt, -⟩ := UpperTheory.Gal.Gen.tower_holds E w₀ a l hl hmem ha N hN
  obtain ⟨hLev, hmemC, hcJ, -, -, -⟩ :=
    UpperTheory.Gal.Gen.levFacts_holds E a w₀ hs K hK (J 0) (hJ.isOpen 0) (hJ.compact 0)
  have hKC : K ≤ UpperTheory.Gal.Gen.lev K w₀ (J 0) := le_sup_left
  refine ⟨UpperTheory.Gal.Gen.lev K w₀ (J 0), hLev, hKC, ?_, ?_, ?_⟩
  · intro g γ hγ c hc x hx h
    have hT : UpperTheory.Gal.CharacterCongruences.TorsFreeAt (UpperTheory.Gal.Gen.lev K w₀ (J 0)) w₀ :=
      fun k hk ho => hJt _ (hcJ k hk) ho
    exact UpperTheory.Gal.CharacterCongruences.neatOfPlace_holds E a _ ⟨hLev.fin, hLev.compact, hLev.isOpen⟩ w₀ hT
      g γ hγ c hc x hx h
  · have hKGL : GlobalTheory.LFun.KGL v' (n := a) ≤ (UpperTheory.Gal.Gen.lev K w₀ (J 0)).map (cLoc v') := by
      intro y hy
      obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a v' hv'
      have hy' : cLoc v' (e.symm y : UA E a) = y := by rw [← he]; simp
      exact ⟨(e.symm y : UA E a), hKC (hint _ (e.symm y).2 (hy'.symm ▸ hy)), hy'⟩
    have hmax := UpperTheory.Gal.Gen.maxCpt_holds E v' a ((UpperTheory.Gal.Gen.lev K w₀ (J 0)).map (cLoc v'))
      (cLoc v' '' (UpperTheory.Gal.Gen.lev K w₀ (J 0) : Set (UA E a)))
      (hLev.compact.image (GlobalTheory.BCT.GlobLev.continuous_cLoc v'))
      (fun _ h => h) hKGL
    intro c hc
    exact hmax ⟨c, hc, rfl⟩
  · intro c hc v g
    obtain ⟨hcC, hcv⟩ := hc
    obtain ⟨k, hk, x, hx, hxJ, rfl⟩ := (hmemC _).1 hcC
    have hx1 : cLoc v' x = 1 :=
      MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.2 v') hap)
    have hkv : k ∈ K ⊓ Kv.comap (cLoc v') := by
      refine ⟨hk, ?_⟩
      have h2 : cLoc v' (k * x) ∈ Kv := hcv
      rw [map_mul, hx1, mul_one] at h2
      exact h2
    rw [← mul_assoc, hNf x hx (hJN hxJ) v (g * k)]
    exact hf k hkv v g
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)

namespace UpperTheory.Gal.Wt

private theorem isOpen_subgroupOf {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}
    {C C₀ : Subgroup (UA E a)} (hC : IsLevel C) (hC₀ : IsLevel C₀) :
    IsOpen ((C₀.subgroupOf C : Subgroup C) : Set C) := by
  obtain ⟨N, hNo, h1N, hNC⟩ := hC₀.isOpen
  refine Subgroup.isOpen_of_mem_nhds (g := 1) _ ?_
  refine Filter.mem_of_superset
    ((hNo.preimage continuous_subtype_val).mem_nhds (show ((1 : C) : UA E a) ∈ N from h1N)) ?_
  intro x hx
  exact Subgroup.mem_subgroupOf.2 (hNC ⟨hx, hC.fin x.2⟩)

theorem twistBd_of : Twist → TwistBd := by
  intro hT E _ _ _ l _ ι a C hC ℓ hℓ W f X b hb
  classical
  obtain ⟨C₀, hC₀, hf⟩ := UpperTheory.Gal.Gen.levelEx_holds E a W f
  have hHo := isOpen_subgroupOf hC hC₀
  haveI : CompactSpace C := isCompact_iff_compactSpace.1 hC.compact
  haveI : Finite (C ⧸ C₀.subgroupOf C) := Subgroup.quotient_finite_of_isOpen _ hHo
  letI := Fintype.ofFinite (C ⧸ C₀.subgroupOf C)
  have hq : ∀ q : C ⧸ C₀.subgroupOf C, ∃ R : ℝ, ∀ g i,
      ‖ι.symm (f.1 (b g i) (g * ((ℓ g)⁻¹ * q.out : C)))‖ ≤ R := by
    intro q
    obtain ⟨F, -, hF⟩ := hT E a C hC ℓ hℓ W f q.out
    obtain ⟨R, hR⟩ := hb F
    exact ⟨R, fun g i => by rw [← hF]; exact hR g i⟩
  choose R hR using hq
  refine ⟨1 + ∑ q, |R q|, by positivity, fun c g i => ?_⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (C₀.subgroupOf C) c
  have hhC : ((h : C) : UA E a) ∈ C₀ := Subgroup.mem_subgroupOf.1 h.2
  have e : f.1 (b g i) (g * ((ℓ g)⁻¹ * (QuotientGroup.mk c : C ⧸ C₀.subgroupOf C).out : C)) =
      f.1 (b g i) (g * ((ℓ g)⁻¹ * c : C)) := by
    rw [hh]
    have : (((ℓ g)⁻¹ * (c * (h : C)) : C) : UA E a) = (((ℓ g)⁻¹ * c : C) : UA E a) * ((h : C) : UA E a) := by
      simp [mul_assoc]
    rw [this, ← mul_assoc]
    exact hf _ hhC _ _
  rw [← e]
  refine (hR _ g i).trans ((le_abs_self _).trans ?_)
  have := Finset.single_le_sum (f := fun q => |R q|) (fun q _ => abs_nonneg _)
    (Finset.mem_univ (QuotientGroup.mk c : C ⧸ C₀.subgroupOf C))
  linarith

end UpperTheory.Gal.Wt

end
end
