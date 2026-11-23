module

public import Formalism.WeaklyAdmissibleFiltrations.Bundle001
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle074
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle050
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.RingTheory.Filtration
public import Mathlib.Algebra.Module.CharacterModule

@[expose] public section

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace GlobalTheory.CompanionTheory.FinCoc

section Generic

variable {G LL O V : Type} [Group G] [Field LL] [CommRing O] [Algebra O LL] [AddCommGroup V] [Module LL V]
  [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}

theorem actQ_one' (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I) (m : ↥L.T ⧸ I) :
    actQ L I hI 1 m = m := by
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  change Submodule.Quotient.mk (actT L 1 t) = Submodule.Quotient.mk t
  congr 1
  exact Subtype.ext (by simp [actT])

theorem actQ_mul' (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I) (g h : G)
    (m : ↥L.T ⧸ I) : actQ L I hI (g * h) m = actQ L I hI g (actQ L I hI h m) := by
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  change Submodule.Quotient.mk (actT L (g * h) t) = Submodule.Quotient.mk (actT L g (actT L h t))
  congr 1
  refine Subtype.ext ?_
  change ρ (g * h) (t : V) = ρ g (ρ h (t : V))
  simp

theorem pow_nsmul_quot (L : Lattice (O := O) ρ) {ϖ : O} {n : ℕ} (hn : (n : O) ∈ Ideal.span {ϖ}) (r : ℕ)
    (m : ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) : n ^ r • m = 0 := by
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 hn
  rw [← Nat.cast_smul_eq_nsmul O, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  have hc : ((n ^ r : ℕ) : O) = ϖ ^ r * u ^ r := by
    rw [Nat.cast_pow, ← hu, mul_pow, mul_comm]
  rw [hc, mul_smul]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

variable [TopologicalSpace V] [ContinuousAdd V]

theorem mk_isLocallyConstant (L : Lattice (O := O) ρ) {ϖ : O} {r : ℕ}
    (hW : (fun x => ϖ ^ r • x) '' (L.T : Set V) ∈ nhds (0 : V)) :
    IsLocallyConstant (fun x : ↥L.T =>
      (Submodule.Quotient.mk x : ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T))) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hc : Continuous fun y : ↥L.T => (y : V) + -(x : V) :=
    continuous_subtype_val.add continuous_const
  have hev := hc.continuousAt.eventually_mem (x := x)
    (s := (fun x => ϖ ^ r • x) '' (L.T : Set V)) (by simpa using hW)
  filter_upwards [hev] with y hy
  obtain ⟨t, ht, h⟩ := hy
  rw [Submodule.Quotient.eq]
  have hxy : y - x = ϖ ^ r • (⟨t, ht⟩ : ↥L.T) :=
    Subtype.ext (by simpa [sub_eq_add_neg] using h.symm)
  rw [hxy]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

theorem finite_quot (L : Lattice (O := O) ρ) {ϖ : O} {r : ℕ} (hC : IsCompact (L.T : Set V))
    (hW : (fun x => ϖ ^ r • x) '' (L.T : Set V) ∈ nhds (0 : V)) :
    Finite (↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) := by
  have hcs : CompactSpace ↥L.T := isCompact_iff_compactSpace.1 hC
  refine Set.finite_univ_iff.1 ?_
  rw [← (Submodule.Quotient.mk_surjective _).range_eq]
  exact (mk_isLocallyConstant L hW).range_finite

theorem actQ_isLocallyConstant [TopologicalSpace G] (L : Lattice (O := O) ρ) {ϖ : O} {r : ℕ}
    (hW : (fun x => ϖ ^ r • x) '' (L.T : Set V) ∈ nhds (0 : V))
    (hcont : ∀ x, Continuous fun g => ρ g x)
    (hI : StableSub L (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T))
    (m : ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) :
    IsLocallyConstant fun g => actQ L _ hI g m := by
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  have hc : Continuous fun g : G => actT L g t := (hcont (t : V)).subtype_mk _
  exact (mk_isLocallyConstant L hW).comp_continuous hc

end Generic

end GlobalTheory.CompanionTheory.FinCoc
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.LocDual.FinT

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {LL O V : Type} [Field LL] [CommRing O] [Algebra O LL]
    [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

theorem mem_smulTop (L : Lattice (O := O) ρ) (ϖ : O) (x : ↥L.T) :
    x ∈ (Ideal.span {ϖ ^ 1} • ⊤ : Submodule O ↥L.T) ↔ ∃ y : ↥L.T, ϖ • y = x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp

theorem fg_Z1T [TopologicalSpace LL] [ContinuousSMul LL V] [IsTopologicalAddGroup V] [T2Space V] (L : Lattice (O := O) ρ) {ϖ : O}
    (h0 : algebraMap O LL ϖ ≠ 0)
    (hB : (nhds (0 : V)).HasBasis (fun _ : ℕ => True) (fun n => (fun x => ϖ ^ n • x) '' (L.T : Set V)))
    (hK : IsCompact (Set.range (algebraMap O LL)))
    (hI : StableSub L (Ideal.span {ϖ ^ 1} • ⊤ : Submodule O ↥L.T)) (hfin : Finite ↥(quotientCocycles L _ hI)) :
    (latticeCocycles L).FG :=
  _root_.UpperTheory.Reformulated.B.Gub2.fg_Z1T L h0 hB hK hI hfin

theorem t2Space_of_lattice_nhds_basis [IsTopologicalAddGroup V] [IsNoetherianRing O] [IsLocalRing O] (L : Lattice (O := O) ρ) {ϖ : O}
    (hϖ : ¬ IsUnit ϖ)
    (hB : (nhds (0 : V)).HasBasis (fun _ : ℕ => True) (fun n => (fun x => ϖ ^ n • x) '' (L.T : Set V))) :
    T2Space V := by
  refine IsTopologicalAddGroup.t2Space_of_zero_sep fun x hx => ?_
  by_contra hcon
  push_neg at hcon
  have hin : ∀ n : ℕ, ∃ t ∈ L.T, ϖ ^ n • t = x := fun n => hcon _ (hB.mem_of_mem (i := n) trivial)
  haveI : Module.Finite O ↥L.T := Module.Finite.iff_fg.2 L.fg
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := ↥L.T) (Ideal.span {ϖ})
    (fun h => hϖ (Ideal.span_singleton_eq_top.1 h))
  obtain ⟨t₀, ht₀, he₀⟩ := hin 0
  have hxT : x ∈ L.T := by
    rw [pow_zero, one_smul] at he₀
    exact he₀ ▸ ht₀
  have hmem : (⟨x, hxT⟩ : ↥L.T) ∈ (⨅ i : ℕ, (Ideal.span {ϖ}) ^ i • (⊤ : Submodule O ↥L.T)) := by
    rw [Submodule.mem_iInf]
    intro n
    obtain ⟨t, ht, he⟩ := hin n
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨⟨t, ht⟩, trivial, Subtype.ext he⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact hx (congrArg Subtype.val hmem)

def toV (L : Lattice (O := O) ρ) : LatticeCohomology L →ₗ[O] H1V ρ :=
  Submodule.liftQ _
    (((Submodule.mkQ ((B1 ρ).comap (continuousCocycles ρ).subtype)).restrictScalars O) ∘ₗ
      { toFun := fun c => ⟨(c : G → V), c.2.1⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl })
    (by
      rintro c ⟨x, _, hx⟩
      refine (Submodule.Quotient.mk_eq_zero _).2 ?_
      exact ⟨x, hx⟩)

theorem toV_mk (L : Lattice (O := O) ρ) (c : ↥(latticeCocycles L)) :
    toV L (Submodule.Quotient.mk c) = Submodule.Quotient.mk ⟨(c : G → V), c.2.1⟩ := rfl

theorem isLocalized_toV [IsDomain O] [IsFractionRing O LL] (L : Lattice (O := O) ρ) {ϖ : O} (h0 : ϖ ≠ 0)
    (hInt : ∀ c : G → V, Continuous c → ∃ n : ℕ, ∀ g, ϖ ^ n • c g ∈ L.T) :
    IsLocalizedModule (nonZeroDivisors O) (toV L) := by
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · intro s
    have hs : algebraMap O LL (s : O) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
    rw [Module.End.isUnit_iff]
    constructor
    · intro x y hxy
      have hxy' : (s : O) • x = (s : O) • y := hxy
      rw [← algebraMap_smul LL (s : O) x, ← algebraMap_smul LL (s : O) y] at hxy'
      exact smul_right_injective _ hs hxy'
    · intro y
      refine ⟨(algebraMap O LL (s : O))⁻¹ • y, ?_⟩
      change (s : O) • ((algebraMap O LL (s : O))⁻¹ • y) = y
      rw [← algebraMap_smul LL (s : O), smul_smul, mul_inv_cancel₀ hs, one_smul]
  · intro y
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨n, hn⟩ := hInt (c : G → V) c.2.1
    have hz : ϖ ^ n • (c : G → V) ∈ latticeCocycles L :=
      ⟨(continuousCocycles ρ).restrictScalars O |>.smul_mem _ c.2, fun g _ => hn g⟩
    refine ⟨⟨Submodule.Quotient.mk ⟨_, hz⟩, ⟨ϖ ^ n, pow_mem (mem_nonZeroDivisors_of_ne_zero h0) n⟩⟩, ?_⟩
    rfl
  · intro x₁ x₂ h
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x₁
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x₂
    rw [toV_mk, toV_mk, Submodule.Quotient.eq] at h
    obtain ⟨v, hv⟩ := h
    obtain ⟨n, hn⟩ := hInt (fun _ => v) continuous_const
    refine ⟨⟨ϖ ^ n, pow_mem (mem_nonZeroDivisors_of_ne_zero h0) n⟩, ?_⟩
    rw [Submonoid.mk_smul, Submonoid.mk_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    refine ⟨ϖ ^ n • v, hn 1, ?_⟩
    funext g
    have hvg : ρ g v - v = (a : G → V) g - (b : G → V) g := congrFun hv g
    change ρ g (ϖ ^ n • v) - ϖ ^ n • v = ϖ ^ n • (a : G → V) g - ϖ ^ n • (b : G → V) g
    rw [← smul_sub, ← hvg, ← algebraMap_smul LL (ϖ ^ n) v, map_smul, ← smul_sub, algebraMap_smul]

end Gen

end GlobalTheory.CompanionTheory.LocDual.FinT
end
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

theorem GlobalTheory.CompanionTheory.LocDual.cup_flip_cob {G W W' R : Type} [Group G] [TopologicalSpace G] [AddCommGroup W]
    [AddCommGroup W'] [CommRing R] (χ : G → R) (a : G → W →+ W) (a' : G → W' →+ W') (P : W →+ W' →+ R)
    (hP : ∀ g x y, P (a g x) (a' g y) = χ g * P x y) (y : G → W) (x : G → W')
    (hy : IsLocallyConstant y ∧ ∀ g h, y (g * h) = y g + a g (y h))
    (hx : IsLocallyConstant x ∧ ∀ g h, x (g * h) = x g + a' g (x h)) (z z' : G × G → R)
    (hz : (z = (fun p => P (y p.1) (a' p.1 (x p.2))) ∧ z' = (fun p => P (a p.1 (y p.2)) (x p.1))) ∨
      (z' = (fun p => P (y p.1) (a' p.1 (x p.2))) ∧ z = (fun p => P (a p.1 (y p.2)) (x p.1))))
    (h : ∃ f : G → R, IsLocallyConstant f ∧ ∀ g h, χ g * f h - f (g * h) + f g = z (g, h)) :
    ∃ f : G → R, IsLocallyConstant f ∧ ∀ g h, χ g * f h - f (g * h) + f g = z' (g, h) := by
  obtain ⟨f, hf, hfd⟩ := h
  have hlc : IsLocallyConstant fun g => P (y g) (x g) :=
    IsLocallyConstant.comp₂ hy.1 hx.1 fun u v => P u v
  have hid : ∀ g h, χ g * P (y h) (x h) - P (y (g * h)) (x (g * h)) + P (y g) (x g) =
      -P (y g) (a' g (x h)) - P (a g (y h)) (x g) := by
    intro g h
    rw [hy.2, hx.2, ← hP]
    simp only [map_add (f := _), AddMonoidHom.add_apply]
    abel
  refine ⟨fun g => -P (y g) (x g) - f g, (hlc.neg).sub hf, fun g h => ?_⟩
  have h1 := hid g h
  have h2 := hfd g h
  rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only at h2 ⊢ <;> linear_combination -h1 - h2
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace GlobalTheory.CompanionTheory.LocDual.Kernels

theorem mem_of_forall_pow {O M : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [AddCommGroup M] [Module O M] (Λ E : Submodule O M) (hΛ : Λ.FG) (ϖ : O) (hϖ : ¬ IsUnit ϖ)
    (w : M) (h : ∀ n : ℕ, ∃ e ∈ E, ∃ t ∈ Λ, w = e + ϖ ^ n • t) : w ∈ E := by
  classical
  set N : Submodule O (M ⧸ E) := Λ.map E.mkQ with hNdef
  have hNfg : N.FG := hΛ.map _
  haveI : Module.Finite O N := Module.Finite.iff_fg.2 hNfg
  have hE : ∀ e ∈ E, E.mkQ e = 0 := fun e he => (Submodule.Quotient.mk_eq_zero E).2 he
  obtain ⟨e₀, he₀, t₀, ht₀, hw₀⟩ := h 0
  have hwN : E.mkQ w ∈ N := ⟨t₀, ht₀, by rw [hw₀, pow_zero, one_smul, map_add (f := _), hE e₀ he₀, zero_add]⟩
  have hI : Ideal.span {ϖ} ≠ ⊤ := fun h' => hϖ (Ideal.span_singleton_eq_top.1 h')
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := N) (Ideal.span {ϖ}) hI
  have hmem : (⟨E.mkQ w, hwN⟩ : N) ∈ (⨅ i : ℕ, Ideal.span {ϖ} ^ i • ⊤ : Submodule O N) := by
    refine Submodule.mem_iInf _ |>.2 fun i => ?_
    obtain ⟨e, he, t, ht, hw⟩ := h i
    have htN : E.mkQ t ∈ N := ⟨t, ht, rfl⟩
    have heq : (⟨E.mkQ w, hwN⟩ : N) = ϖ ^ i • (⟨E.mkQ t, htN⟩ : N) := by
      apply Subtype.ext
      rw [Submodule.coe_smul]
      show E.mkQ w = ϖ ^ i • E.mkQ t
      rw [hw, map_add (f := _), map_smul, hE e he, zero_add]
    rw [heq]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self ϖ) i) Submodule.mem_top
  rw [hbot, Submodule.mem_bot] at hmem
  have h0 : E.mkQ w = 0 := congrArg Subtype.val hmem
  exact (Submodule.Quotient.mk_eq_zero E).1 h0

theorem exists_finset_sep {k U G X : Type} [Field k] [AddCommGroup U] [Module k U]
    [FiniteDimensional k U] [AddCommGroup X] [Module k X] (φ : U →ₗ[k] G → X) :
    ∃ F : Finset G, ∀ u, (∀ g ∈ F, φ u g = 0) → φ u = 0 := by
  classical
  let Kf : Finset G → Submodule k U := fun F => ⨅ g ∈ F, LinearMap.ker ((LinearMap.proj g).comp φ)
  obtain ⟨_, ⟨F, rfl⟩, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Submodule k U)) (Set.range Kf)
    ⟨Kf ∅, Set.mem_range_self _⟩
  have hall : ∀ g, Kf F ≤ LinearMap.ker ((LinearMap.proj g).comp φ) := by
    intro g
    have hle : Kf (insert g F) ≤ Kf F := by
      refine le_iInf₂ fun g' hg' => iInf₂_le g' (Finset.mem_insert_of_mem hg')
    have heq : Kf (insert g F) = Kf F := by
      by_contra hne
      exact hmin _ (Set.mem_range_self _) (lt_of_le_of_ne hle hne)
    rw [← heq]
    exact iInf₂_le g (Finset.mem_insert_self g F)
  refine ⟨F, fun u hu => funext fun g => ?_⟩
  have huF : u ∈ Kf F := by
    simp only [Kf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval]
    exact hu
  have := hall g huF
  simpa using this

end GlobalTheory.CompanionTheory.LocDual.Kernels
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace GlobalTheory.CompanionTheory.LocDual.GenChar

theorem exists_addHom_zmod_ne_zero {N : ℕ} [NeZero N] {A : Type} [AddCommGroup A]
    (hA : ∀ a : A, N • a = 0) {q : A} (hq : q ≠ 0) : ∃ f : A →+ ZMod N, f q ≠ 0 := by
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hq
  let c' : A →+ AddCircle (1 : ℚ) := c
  have hc' : c' q ≠ 0 := hc
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  let g : ℤ →+ AddCircle (1 : ℚ) :=
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))).comp
      ((AddMonoidHom.mulRight ((N : ℚ)⁻¹)).comp (Int.castAddHom ℚ))
  have hg : ∀ z : ℤ, g z = QuotientAddGroup.mk ((z : ℚ) * (N : ℚ)⁻¹) := fun z => rfl
  have hgN : g N = 0 := by
    rw [hg, Int.cast_natCast, mul_inv_cancel₀ hN]
    exact (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_zmultiples _)
  let ι : ZMod N →+ AddCircle (1 : ℚ) := ZMod.lift N ⟨g, hgN⟩
  have hι : ∀ z : ℤ, ι z = g z := fun z => ZMod.lift_coe N ⟨g, hgN⟩ z
  have hinj : Function.Injective ι := by
    refine (injective_iff_map_eq_zero ι).2 fun m hm => ?_
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective m
    rw [hι, hg] at hm
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 ((QuotientAddGroup.eq_zero_iff _).1 hm)
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine ⟨k, ?_⟩
    rw [zsmul_eq_mul, mul_one] at hk
    have h2 : (z : ℚ) = (N : ℚ) * k := by
      field_simp at hk
      linarith
    exact_mod_cast h2
  have hmem : ∀ a : A, c' a ∈ ι.range := by
    intro a
    obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective (c' a)
    have h1 : N • c' a = 0 := by rw [← map_nsmul, hA, map_zero]
    have h0 : (N • r : ℚ) ∈ AddSubgroup.zmultiples (1 : ℚ) := by
      rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul, hr]
      exact h1
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 h0
    refine AddMonoidHom.mem_range.2 ⟨(k : ZMod N), ?_⟩
    rw [hι, hg, ← hr]
    congr 1
    rw [zsmul_eq_mul, mul_one, nsmul_eq_mul] at hk
    rw [hk]
    field_simp
  refine ⟨(AddMonoidHom.ofInjective hinj).symm.toAddMonoidHom.comp
    (AddMonoidHom.codRestrict c' ι.range hmem), ?_⟩
  intro h0
  apply hc'
  have h1 : AddMonoidHom.codRestrict c' ι.range hmem q = 0 := by
    have h3 := congrArg (AddMonoidHom.ofInjective hinj) h0
    simpa using h3
  have h2 := congrArg Subtype.val h1
  simpa using h2

theorem exists_mul_eq_socle {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) (s : ℕ) {x : O ⧸ Ideal.span {ϖ ^ (s + 1)}} (hx : x ≠ 0) :
    ∃ o, o * x = Ideal.Quotient.mk (Ideal.span {ϖ ^ (s + 1)}) (ϖ ^ s) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hy : y ≠ 0 := by
    rintro rfl
    exact hx (map_zero _)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  have hn : n ≤ s := by
    by_contra hlt
    apply hx
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, hu]
    exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (Nat.succ_le_of_lt (not_le.1 hlt))) _
  refine ⟨Ideal.Quotient.mk _ (↑u⁻¹ * ϖ ^ (s - n)), ?_⟩
  rw [← map_mul, hu]
  congr 1
  calc ↑u⁻¹ * ϖ ^ (s - n) * (↑u * ϖ ^ n) = (↑u⁻¹ * ↑u) * (ϖ ^ (s - n) * ϖ ^ n) := by ring
    _ = ϖ ^ s := by rw [Units.inv_mul, one_mul, ← pow_add, Nat.sub_add_cancel hn]

theorem socle_ne_zero {O : Type} [CommRing O] [IsDomain O] {ϖ : O} (hϖ : Irreducible ϖ) (s : ℕ) :
    Ideal.Quotient.mk (Ideal.span {ϖ ^ (s + 1)}) (ϖ ^ s) ≠ 0 := by
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
    pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit]
  omega

theorem exists_generating_character : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (r N : ℕ), 0 < N → Finite (O ⧸ Ideal.span {ϖ ^ r}) → ((N : O) ∈ Ideal.span {ϖ ^ r}) → ∃ ψ₀ : (O ⧸ Ideal.span {ϖ ^ r}) →+ ZMod N, (∀ x, (∀ o, ψ₀ (o * x) = 0) → x = 0) ∧ ∀ ψ : (O ⧸ Ideal.span {ϖ ^ r}) →+ ZMod N, ∃ o, ∀ x, ψ x = ψ₀ (o * x) := by
  intro O _ _ _ ϖ hϖ r N hN hfin hNmem
  haveI : NeZero N := ⟨by omega⟩
  have htors : ∀ a : O ⧸ Ideal.span {ϖ ^ r}, N • a = 0 := by
    intro a
    have hN0 : ((N : O ⧸ Ideal.span {ϖ ^ r})) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {ϖ ^ r}))]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hNmem
    rw [nsmul_eq_mul, hN0, zero_mul]
  have key : ∃ ψ₀ : (O ⧸ Ideal.span {ϖ ^ r}) →+ ZMod N,
      ∀ x, (∀ o, ψ₀ (o * x) = 0) → x = 0 := by
    cases r with
    | zero =>
      refine ⟨0, fun x _ => ?_⟩
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Ideal.Quotient.eq_zero_iff_mem, pow_zero, Ideal.span_singleton_one]
      exact Submodule.mem_top
    | succ s =>
      obtain ⟨ψ₀, hψ₀⟩ := exists_addHom_zmod_ne_zero htors (socle_ne_zero hϖ s)
      refine ⟨ψ₀, fun x hx => ?_⟩
      by_contra hne
      obtain ⟨o, ho⟩ := exists_mul_eq_socle hϖ s hne
      have h5 := hx o
      rw [ho] at h5
      exact hψ₀ h5
  obtain ⟨ψ₀, hψ₀⟩ := key
  refine ⟨ψ₀, hψ₀, ?_⟩
  let Φ : (O ⧸ Ideal.span {ϖ ^ r}) → ((O ⧸ Ideal.span {ϖ ^ r}) →+ ZMod N) :=
    fun o => ψ₀.comp (AddMonoidHom.mulLeft o)
  have hinj : Function.Injective Φ := by
    intro a b hab
    have h0 : ∀ x, ψ₀ ((a - b) * x) = 0 := by
      intro x
      have h6 : ψ₀ (a * x) = ψ₀ (b * x) := DFunLike.congr_fun hab x
      rw [sub_mul, map_sub, h6, sub_self]
    have h7 : a - b = 0 := hψ₀ (a - b) (fun o => by rw [mul_comm]; exact h0 o)
    exact sub_eq_zero.1 h7
  haveI : Finite ((O ⧸ Ideal.span {ϖ ^ r}) →+ ZMod N) :=
    Finite.of_injective (fun f : (O ⧸ Ideal.span {ϖ ^ r}) →+ ZMod N =>
      (f : (O ⧸ Ideal.span {ϖ ^ r}) → ZMod N)) DFunLike.coe_injective
  have hbij := hinj.bijective_of_nat_card_le (GlobalTheory.natCard_addMonoidHom_zmod_le N _)
  intro ψ
  obtain ⟨o, ho⟩ := hbij.2 ψ
  exact ⟨o, fun x => by rw [← ho]; rfl⟩

end GlobalTheory.CompanionTheory.LocDual.GenChar
end
