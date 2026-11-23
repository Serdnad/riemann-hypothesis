module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle084
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepFormulaF
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterFormulaOfDiscreteSeriesDatum
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigLamLeOfKTypes
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActionEquivarianceStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Fin.Tuple.Sort
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.ArbitraryA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.ArbitraryB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle005

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.JmMono

section General

variable {F G U V W : Type} [Field F] [Group G] [AddCommGroup U] [Module F U] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

theorem occursTimes_of_isSubquotient {σ : Representation F G U} {π : Representation F G V}
    {P : Representation F G W} (h : IsSubquotient π P) {r : ℕ} (ho : OccursTimes σ π r) :
    OccursTimes σ P r := by
  obtain ⟨S, f, hf⟩ := h
  unfold GlobalTheory.SmGL.OccursTimes at ho ⊢
  obtain ⟨A, B, hBA, hAB, hiso⟩ := ho
  let ι : Representation.IntertwiningMap S.toRepresentation P :=
    ⟨S.toSubmodule.subtype, fun _ => LinearMap.ext fun _ => rfl⟩
  have hι : Function.Injective ι := fun a b hab => Subtype.val_injective hab
  refine ⟨fun i => GlobalTheory.JHMult.subMap ι (GlobalTheory.JHMult.subComap f (A i)),
    fun i => GlobalTheory.JHMult.subMap ι (GlobalTheory.JHMult.subComap f (B i)),
    fun i => GlobalTheory.JHMult.subMap_mono ι (GlobalTheory.JHMult.subComap_mono f (hBA i)),
    fun i j hij => GlobalTheory.JHMult.subMap_mono ι (GlobalTheory.JHMult.subComap_mono f (hAB i j hij)),
    fun i => ?_⟩
  exact GlobalTheory.JHMult.step_iff.mpr
    (GlobalTheory.JHMult.step_map ι hι
      (GlobalTheory.JHMult.step_comap f hf
        (GlobalTheory.JHMult.step_iff.mp (hiso i))))

theorem jhMult_le_of_isSubquotient (σ : Representation F G U) {π : Representation F G V}
    {P : Representation F G W} (h : IsSubquotient π P) : jhMult σ π ≤ jhMult σ P := by
  unfold GlobalTheory.SmGL.jhMult
  exact iSup₂_le fun r hr => le_iSup₂_of_le r (GlobalTheory.CompanionTheory.JmMono.occursTimes_of_isSubquotient h hr) le_rfl

end General

theorem jm_le_of_isSubquotient {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h N : ℕ} (y : Fin h → IrrGL (k := k)) (hy : ∑ a, (y a).1 = N) {V W : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V)
    (P : Representation ℂ (GL (Fin N) k) W) (hP : IsSmooth P) (h : IsSubquotient π P) :
    jm y hy π ≤ jm y hy P := by
  unfold Zc.jm
  exact GlobalTheory.CompanionTheory.JmMono.jhMult_le_of_isSubquotient _
    (GlobalTheory.JacquetExact.isSubquotient_jac _ hP h)

end GlobalTheory.CompanionTheory.JmMono

end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

noncomputable section

namespace GlobalTheory.CompanionTheory.ZcDual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isIrreducible_contra (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible) : (contra π).IsIrreducible := by
  exact GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis k n) (hA k n V π hs hi) hi

theorem dualCl_eq (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) :
    dualCl x = IrrGL.of (contra x.rep) (isSmooth_contra _) (isIrreducible_contra hA _ x.2.rep.smooth x.2.rep.irr) := by
  unfold dualCl
  rw [dite_eq_left (isIrreducible_contra hA _ x.2.rep.smooth x.2.rep.irr)]

theorem nonempty_equiv_contra_twist (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {n : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible)
    {χ χ' : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) (hχ' : IsSmoothChar χ') (h : χ * χ' = 1) :
    Nonempty ((twist (contra π) (detChar (Fin n) χ')).Equiv (contra (twist π (detChar (Fin n) χ)))) := by
  have hψ : IsSmoothChar (detChar (Fin n) χ) := hχ.detChar
  have hinv : ∀ g : GL (Fin n) k,
      ((detChar (Fin n) χ' g : ℂˣ) : ℂ) = ((detChar (Fin n) χ g⁻¹ : ℂˣ) : ℂ) := by
    intro g
    have h1 : χ (Matrix.GeneralLinearGroup.det g) * χ' (Matrix.GeneralLinearGroup.det g) = 1 := by
      rw [← MonoidHom.mul_apply, h, MonoidHom.one_apply]
    have h2 : χ' (Matrix.GeneralLinearGroup.det g) = (χ (Matrix.GeneralLinearGroup.det g))⁻¹ :=
      eq_inv_of_mul_eq_one_right h1
    show ((χ' (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) =
      ((χ (Matrix.GeneralLinearGroup.det g⁻¹) : ℂˣ) : ℂ)
    rw [h2, map_inv, map_inv]
  have hdual : ∀ (g : GL (Fin n) k) (l : Module.Dual ℂ V),
      (twist π (detChar (Fin n) χ)).dual g l = ((detChar (Fin n) χ g⁻¹ : ℂˣ) : ℂ) • π.dual g l := by
    intro g l
    apply LinearMap.ext
    intro v
    show l (((detChar (Fin n) χ g⁻¹ : ℂˣ) : ℂ) • π g⁻¹ v) = ((detChar (Fin n) χ g⁻¹ : ℂˣ) : ℂ) • l (π g⁻¹ v)
    exact map_smul l _ _
  have hker : ∀ g : GL (Fin n) k, g ∈ (detChar (Fin n) χ).ker →
      ((detChar (Fin n) χ g⁻¹ : ℂˣ) : ℂ) = 1 := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    rw [map_inv, hg, inv_one, Units.val_one]
  have hkn : ((detChar (Fin n) χ).ker : Set (GL (Fin n) k)) ∈ nhds (1 : GL (Fin n) k) :=
    IsOpen.mem_nhds hψ (Subgroup.one_mem _)
  have heq : smoothPart π.dual = smoothPart (twist π (detChar (Fin n) χ)).dual := by
    ext l
    constructor
    · intro hl
      apply mem_smoothPart_of_nhds
      refine Filter.mem_of_superset (Filter.inter_mem (IsOpen.mem_nhds hl (by
        show π.dual 1 l = l
        rw [map_one]
        rfl)) hkn) ?_
      rintro g ⟨hg1, hg2⟩
      have h3 : π.dual g l = l := hg1
      show (twist π (detChar (Fin n) χ)).dual g l = l
      rw [hdual, hker g hg2, one_smul]
      exact h3
    · intro hl
      apply mem_smoothPart_of_nhds
      refine Filter.mem_of_superset (Filter.inter_mem (IsOpen.mem_nhds hl (by
        show (twist π (detChar (Fin n) χ)).dual 1 l = l
        rw [map_one]
        rfl)) hkn) ?_
      rintro g ⟨hg1, hg2⟩
      have h3 : (twist π (detChar (Fin n) χ)).dual g l = l := hg1
      rw [hdual, hker g hg2, one_smul] at h3
      show π.dual g l = l
      exact h3
  have htw : ∀ (g : GL (Fin n) k) (l : smoothPart π.dual),
      ((twist (contra π) (detChar (Fin n) χ') g l : smoothPart π.dual) : Module.Dual ℂ V) =
        ((detChar (Fin n) χ' g : ℂˣ) : ℂ) • ((contra π g l : smoothPart π.dual) : Module.Dual ℂ V) :=
    fun _ _ => rfl
  have htw2 : ∀ (g : GL (Fin n) k) (v : V),
      (twist π (detChar (Fin n) χ)) g v = ((detChar (Fin n) χ g : ℂˣ) : ℂ) • π g v :=
    fun _ _ => rfl
  exact ⟨{ toLinearEquiv := LinearEquiv.ofEq _ _ heq
           isIntertwining' := fun g => by
             apply LinearMap.ext
             intro l
             apply Subtype.ext
             apply LinearMap.ext
             intro v
             simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_ofEq_apply, htw,
               LinearMap.smul_apply, contra_apply, htw2, map_smul, smul_eq_mul, hinv] }⟩

private theorem comp_intertwiningMap_mem_smoothPart_dual {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (f : ρ.IntertwiningMap σ)
    (l : Module.Dual ℂ W) (hl : l ∈ smoothPart σ.dual) : l ∘ₗ f.toLinearMap ∈ smoothPart ρ.dual := by
  apply mem_smoothPart_of_nhds
  refine Filter.mem_of_superset (IsOpen.mem_nhds hl (by
    show σ.dual 1 l = l
    rw [map_one]
    rfl)) ?_
  intro g hg
  have h : σ.dual g l = l := hg
  show ρ.dual g (l ∘ₗ f.toLinearMap) = l ∘ₗ f.toLinearMap
  refine LinearMap.ext fun v => ?_
  calc (ρ.dual g (l ∘ₗ f.toLinearMap)) v = l (f.toLinearMap (ρ g⁻¹ v)) := rfl
    _ = l (σ g⁻¹ (f v)) := by
      rw [Representation.IntertwiningMap.toLinearMap_apply, Representation.IntertwiningMap.isIntertwining]
    _ = σ.dual g l (f v) := rfl
    _ = (l ∘ₗ f.toLinearMap) v := by
      rw [h, LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply]

private theorem nonempty_contra_equiv_of_equiv {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) :
    Nonempty ((contra σ).Equiv (contra ρ)) := by
  refine ⟨{ toFun := fun l => ⟨l.1 ∘ₗ e.toIntertwiningMap.toLinearMap,
              comp_intertwiningMap_mem_smoothPart_dual e.toIntertwiningMap l.1 l.2⟩
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl
            invFun := fun l => ⟨l.1 ∘ₗ e.symm.toIntertwiningMap.toLinearMap,
              comp_intertwiningMap_mem_smoothPart_dual e.symm.toIntertwiningMap l.1 l.2⟩
            left_inv := fun l => Subtype.ext (LinearMap.ext fun w => by
              show l.1 (e.toIntertwiningMap.toLinearMap (e.symm.toIntertwiningMap.toLinearMap w)) = l.1 w
              simp only [Representation.IntertwiningMap.toLinearMap_apply,
                Representation.Equiv.coe_toIntertwiningMap, Representation.Equiv.apply_symm_apply])
            right_inv := fun l => Subtype.ext (LinearMap.ext fun v => by
              show l.1 (e.symm.toIntertwiningMap.toLinearMap (e.toIntertwiningMap.toLinearMap v)) = l.1 v
              simp only [Representation.IntertwiningMap.toLinearMap_apply,
                Representation.Equiv.coe_toIntertwiningMap, Representation.Equiv.symm_apply_apply])
            isIntertwining' := fun g => by
              apply LinearMap.ext
              intro l
              apply Subtype.ext
              apply LinearMap.ext
              intro v
              simp only [LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, contra_apply,
                Representation.IntertwiningMap.toLinearMap_apply,
                Representation.IntertwiningMap.isIntertwining] }⟩

theorem dualCl_nu : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) (s : ℂ), dualCl (x.nu s) = (dualCl x).nu (-s) := by
  intro k _ _ _ _ hA x s
  have hs' : IsSmoothChar (absPow k s) := isSmoothChar_of_isUnram (isUnram_absPow k s)
  have hn' : IsSmoothChar (absPow k (-s)) := isSmoothChar_of_isUnram (isUnram_absPow k (-s))
  have hmul : absPow k s * absPow k (-s) = 1 := by
    rw [absPow_neg, mul_inv_cancel]
  have hψ : IsSmoothChar (detChar (Fin x.fst) (absPow k s)) := hs'.detChar
  have hψn : IsSmoothChar (detChar (Fin x.fst) (absPow k (-s))) := hn'.detChar
  obtain ⟨e1⟩ : Nonempty ((x.nu s).rep.Equiv (twist x.rep (detChar (Fin x.fst) (absPow k s)))) :=
    IrrRep.nonempty_equiv_rep (irrTwist x.snd.rep (detChar (Fin x.fst) (absPow k s)) hψ)
  obtain ⟨e2⟩ := nonempty_contra_equiv_of_equiv e1
  obtain ⟨e3⟩ := nonempty_equiv_contra_twist hA x.rep x.2.rep.smooth x.2.rep.irr hs' hn' hmul
  have hc := isIrreducible_contra hA _ x.2.rep.smooth x.2.rep.irr
  obtain ⟨e4⟩ := IrrRep.nonempty_equiv_rep
    (⟨_, contra x.rep, isSmooth_contra _, hc⟩ : IrrRep (GL (Fin x.fst) k))
  have e5 := twistEquiv e4 (detChar (Fin x.fst) (absPow k (-s)))
  rw [dualCl_eq hA, dualCl_eq hA]
  refine Sigma.ext ?_ ?_
  · rfl
  apply heq_of_eq
  exact IrrRep.cl_eq_iff.mpr ⟨(e2.symm.trans e3.symm).trans e5.symm⟩

end GlobalTheory.CompanionTheory.ZcDual

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.CanonOrder

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in
def lineSetoid : Setoid (IrrGL (k := k)) where
  r x y := ∃ m : ℤ, y = x.nu m
  iseqv :=
    { refl := fun x => ⟨0, by simp⟩
      symm := by
        rintro x _ ⟨m, rfl⟩
        exact ⟨-m, by simp⟩
      trans := by
        rintro x _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
        exact ⟨m + n, by simp⟩ }

variable (k) in
def Line : Type 1 := Quotient (lineSetoid k)

instance lineLinearOrder : LinearOrder (Line k) := (exists_wellFoundedLT (Line k)).choose

def lineOf (x : IrrGL (k := k)) : Line k := Quotient.mk (lineSetoid k) x

def lineRep (x : IrrGL (k := k)) : IrrGL (k := k) := Quotient.out (s := lineSetoid k) (Quotient.mk (lineSetoid k) x)

theorem exists_height (x : IrrGL (k := k)) : ∃ m : ℤ, x = (lineRep x).nu m := by
  exact @Quotient.mk_out _ (lineSetoid k) x

def height (x : IrrGL (k := k)) : ℤ := (exists_height x).choose

theorem nu_height (x : IrrGL (k := k)) : (lineRep x).nu (height x) = x := by
  exact (exists_height x).choose_spec.symm

theorem lineRep_eq {x y : IrrGL (k := k)} (h : lineOf x = lineOf y) : lineRep x = lineRep y := by
  unfold lineRep
  unfold lineOf at h
  rw [h]

def key (Δ : Segment k) : Line k ×ₗ ℤ ×ₗ ℕ :=
  toLex (lineOf Δ.first, toLex (height Δ.first, Δ.len))

theorem key_injective : Function.Injective (key (k := k)) := by
  intro Δ Δ' h
  simp only [key, toLex_inj, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine Segment.ext_first ?_ h3
  rw [← nu_height Δ.first, ← nu_height Δ'.first, lineRep_eq h1, h2]

private theorem lineOf_eq_height_eq_add_of_eq_nu {x y : IrrGL (k := k)} (hy : 0 < y.fst) {n : ℤ} (h : x = y.nu n) :
    lineOf x = lineOf y ∧ height x = height y + n := by
  have hl : lineOf x = lineOf y := by
    unfold lineOf
    refine Quotient.sound (s := lineSetoid k) ⟨-n, ?_⟩
    rw [h, IrrGL.nu_nu, Int.cast_neg, add_neg_cancel, IrrGL.nu_zero]
  refine ⟨hl, ?_⟩
  have hR := lineRep_eq hl
  have hRpos : 0 < (lineRep y).fst := by
    have h2 := congrArg Sigma.fst (nu_height y)
    rw [IrrGL.nu_fst] at h2
    rw [h2]
    exact hy
  apply (IrrGL.nu_intCast_inj hRpos).1
  calc (lineRep y).nu (height x) = (lineRep x).nu (height x) := by rw [hR]
    _ = x := nu_height x
    _ = y.nu n := h
    _ = ((lineRep y).nu (height y)).nu n := by rw [nu_height]
    _ = (lineRep y).nu ((height y + n : ℤ) : ℂ) := by rw [IrrGL.nu_nu, Int.cast_add]

theorem key_le {Δ Δ' : Segment k} (h : key Δ ≤ key Δ') :
    (¬ ∃ n : ℕ, 0 < n ∧ Δ.first = Δ'.first.nu (n : ℂ)) ∧ (Δ.first = Δ'.first → Δ.len ≤ Δ'.len) := by
  have hpos : 0 < Δ'.first.fst := Δ'.d_pos
  have hle := h
  simp only [key, Prod.Lex.toLex_le_toLex] at hle
  constructor
  · rintro ⟨n, hn, heq⟩
    have heq' : Δ.first = Δ'.first.nu ((n : ℤ) : ℂ) := by
      rw [Int.cast_natCast]
      exact heq
    obtain ⟨hl, hh⟩ := lineOf_eq_height_eq_add_of_eq_nu hpos heq'
    rcases hle with hlt | ⟨_, hlt | ⟨heq2, _⟩⟩
    · rw [hl] at hlt
      exact lt_irrefl _ hlt
    · omega
    · omega
  · intro hf
    rw [hf] at hle
    rcases hle with hlt | ⟨_, hlt | ⟨_, hlen⟩⟩
    · exact absurd hlt (lt_irrefl _)
    · exact absurd hlt (lt_irrefl _)
    · exact hlen

theorem exists_isCanon {h : ℕ} (Γ : Fin h → Segment k) : ∃ σ : Equiv.Perm (Fin h), IsCanon (Γ ∘ σ) := by
  refine ⟨Tuple.sort (key ∘ Γ), ?_⟩
  have hmono : Monotone ((key ∘ Γ) ∘ Tuple.sort (key ∘ Γ)) := Tuple.monotone_sort _
  unfold IsCanon
  refine ⟨fun i j hij => key_le (hmono hij.le), fun i j l hij hjl hil => ?_⟩
  apply key_injective
  apply le_antisymm
  · calc key ((Γ ∘ Tuple.sort (key ∘ Γ)) j) ≤ key ((Γ ∘ Tuple.sort (key ∘ Γ)) l) := hmono hjl.le
      _ = key ((Γ ∘ Tuple.sort (key ∘ Γ)) i) := by rw [hil]
  · exact hmono hij.le

end GlobalTheory.CompanionTheory.CanonOrder

end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.ZcWords

theorem wtW_isCusp {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h : ℕ} (Δ : Fin h → Segment k) :
    ∀ c ∈ wtW Δ, c.IsCusp := by
  intro c hc
  obtain ⟨l, hl, hcl⟩ := List.mem_flatten.1 hc
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hl
  obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hcl
  exact Segment.isCusp_term _ _

end GlobalTheory.CompanionTheory.ZcWords
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.Words

theorem wd_of_isSubquotient {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W)
    (hπ : IsSmooth π) (h : IsSubquotient σ π) (w : List (IrrGL (k := k))) (hw : Wd σ w) : Wd π w := by
  obtain ⟨hd, hne⟩ := hw
  refine ⟨hd, ?_⟩
  exact jhMult_ne_zero_iff.2
    ((jhMult_ne_zero_iff.1 hne).trans (GlobalTheory.JacquetExact.isSubquotient_jac _ hπ h))

end GlobalTheory.CompanionTheory.Words
end

section


theorem _root_.GlobalTheory.T.character_formula_of_discrete_series_datum : PositivityTheory.RgDs.Hilb.StepDatum → PositivityTheory.RgDs.Hilb.StepFormulaF := by
  first | exact @GlobalTheory.CompanionTheory.Hilb.stepFormulaF | exact GlobalTheory.CompanionTheory.Hilb.stepFormulaF | (intros; apply GlobalTheory.CompanionTheory.Hilb.stepFormulaF <;> assumption)
end

section

noncomputable section

open MeasureTheory ReciprocityTheory.ChartRestriction.DS

namespace GlobalTheory.CompanionTheory.HilbMoll

variable {n : ℕ}

theorem opConv_mem_of_isClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (α : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (W : Submodule ℂ H) (hWc : IsClosed (W : Set H)) (hWs : ∀ g ∈ UJset ε, ∀ x ∈ W, σ g x ∈ W)
    {x : H} (hx : x ∈ W) : opConv ε σ α x ∈ W := by
  have : CompleteSpace W := hWc.completeSpace_coe
  unfold opConv
  by_cases hint : Integrable (fun g : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat g) • σ (Formalism.MainNotions.S.umat g) x)
      (Formalism.REAL.muG ε)
  · have hfix : ∀ g : Formalism.REAL.UJ ε, W.starProjection (α (Formalism.MainNotions.S.umat g) • σ (Formalism.MainNotions.S.umat g) x) =
        α (Formalism.MainNotions.S.umat g) • σ (Formalism.MainNotions.S.umat g) x := fun g =>
      Submodule.starProjection_eq_self_iff.2 (W.smul_mem _ (hWs _ (arb_umat_mem g) x hx))
    have h := W.starProjection.integral_comp_comm hint
    simp only [hfix] at h
    rw [h]
    exact W.starProjection_apply_mem _
  · rw [integral_undef hint]
    exact W.zero_mem

theorem stepMoll : PositivityTheory.RgDs.Hilb.StepMoll := by
  intro n ε W S hWc hWs hSf hSW _
  have := hSf
  obtain ⟨α, hadd, hsmul, hαK, hαsm, hαS⟩ := exists_moll_data (rreg_isURepOn ε) S
  let A : L2 ε →ₗ[ℂ] L2 ε := { toFun := opConv ε (rreg ε) α, map_add' := hadd, map_smul' := hsmul }
  have hAv : ∀ v, A v = opConv ε (rreg ε) α v := fun v => rfl
  refine ⟨A, fun k hk x => (hαK k hk x).symm, ?_, ?_, ?_⟩
  · intro w hw h0
    have h1 := hαS w hw
    rw [← hAv, h0, zero_sub, norm_neg] at h1
    have h2 : ‖w‖ ≤ 0 := by linarith
    exact norm_le_zero_iff.1 h2
  · rintro _ ⟨w, _, rfl⟩
    exact (mem_smD_iff ε (rreg ε) _).2 (hαsm w)
  · rintro _ ⟨w, hw, rfl⟩
    exact opConv_mem_of_isClosed ε (rreg ε) α W hWc hWs (hSW hw)

end GlobalTheory.CompanionTheory.HilbMoll
end
end

section


theorem _root_.GlobalTheory.T.action_equivariance_statement : PositivityTheory.RgDs.K.ActEquiv := by
  first | exact @GlobalTheory.CompanionTheory.ActEquivK.actEquiv | exact GlobalTheory.CompanionTheory.ActEquivK.actEquiv | (intros; apply GlobalTheory.CompanionTheory.ActEquivK.actEquiv <;> assumption)
end
