module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle028
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle022
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle033
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle038
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.WeilBound.CoreStatements.HodgeTatePoints.CbAlpha
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle040
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle017
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ReBase
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HasLenOfSurj
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RangeSubtypeEq
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle006
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle013

@[expose] public section

section

open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] {n : ℕ}
  {Sg : Type} {r s : Sg → ℕ}

theorem mem_stepGraph_iff (D : LieLatticeData Ω F n Sg r s) (τ : Sg) (χ : F → Ω) (i : Fin n) (c : Ω)
    (m : Fin (r τ) → Ω) :
    (c, m) ∈ D.stepGraph τ χ i ↔
      ∃ g u, (g, m) ∈ D.Th τ ∧ u ∈ vanSub Ω F n ((i : ℕ) + 1) ∧
        c • (fun x : Fin n → F => χ (x i)) = g + u := by
  unfold LieLatticeData.stepGraph
  rw [AddSubgroup.mem_comap, AddSubgroup.mem_sup]
  constructor
  · rintro ⟨⟨g, m'⟩, hy, ⟨u, m''⟩, hz, he⟩
    obtain ⟨hu, hm⟩ := AddSubgroup.mem_prod.1 hz
    have hm0 : m'' = 0 := hm
    subst hm0
    have h1 : g + u = c • (fun x : Fin n → F => χ (x i)) := congrArg Prod.fst he
    have h2 : m' + 0 = m := congrArg Prod.snd he
    rw [add_zero] at h2
    subst h2
    exact ⟨g, u, hy, hu, h1.symm⟩
  · rintro ⟨g, u, hg, hu, he⟩
    refine ⟨(g, m), hg, (u, 0), AddSubgroup.mem_prod.2 ⟨hu, rfl⟩, ?_⟩
    exact Prod.ext he.symm (add_zero m)

theorem vanSub_apply_zero {i : ℕ} {u : (Fin n → F) → Ω} (hu : u ∈ vanSub Ω F n i) : u 0 = 0 := by
  have h := (Submodule.mem_pi.1 hu) (0 : Fin n → F) (fun _ _ => rfl)
  simpa using h

theorem stepGraph_stable [Fintype F] (D : LieLatticeData Ω F n Sg r s) {R : Subalgebra o Ω} {p : ℕ} {w : Ω}
    (hB : D.Base R p w) (τ : Sg) (χ : F → Ω) (i : Fin n) :
    ∀ a ∈ R, ∀ v ∈ D.stepGraph τ χ i, a • v ∈ D.stepGraph τ χ i := by
  rintro a ha ⟨c, m⟩ h
  obtain ⟨g, u, hg, hu, he⟩ := (mem_stepGraph_iff D τ χ i c m).1 h
  refine (mem_stepGraph_iff D τ χ i (a • c) (a • m)).2
    ⟨a • g, a • u, (hB.stable τ a ha).2.2 (g, m) hg, Submodule.smul_mem _ _ hu, ?_⟩
  rw [smul_assoc, he, smul_add]

theorem fst_mem_xId_of_mem_stepGraph [Fintype F] (D : LieLatticeData Ω F n Sg r s) {R : Subalgebra o Ω}
    {p : ℕ} {w : Ω} (hB : D.Base R p w) (τ : Sg) (χ : F → Ω) (i : Fin n) {c : Ω}
    {m : Fin (r τ) → Ω} (h : (c, m) ∈ D.stepGraph τ χ i) : c ∈ D.xId χ i := by
  obtain ⟨g, u, hg, hu, he⟩ := (mem_stepGraph_iff D τ χ i c m).1 h
  have hgM : g ∈ D.M := (((hB.th τ).1 g).1 ⟨m, hg⟩).1
  refine AddSubgroup.mem_comap.2 (AddSubgroup.mem_sup.2 ⟨g, hgM, u, hu, ?_⟩)
  exact he.symm

theorem exists_mem_stepGraph_of_mem_xId [Fintype F] (D : LieLatticeData Ω F n Sg r s) {R : Subalgebra o Ω}
    {p : ℕ} {w : Ω} (hB : D.Base R p w) (τ : Sg) (χ : F → Ω) (h0 : χ 0 = 0) (i : Fin n) {c : Ω}
    (h : c ∈ D.xId χ i) : ∃ m, (c, m) ∈ D.stepGraph τ χ i := by
  obtain ⟨g, hg, u, hu, he⟩ := AddSubgroup.mem_sup.1 (AddSubgroup.mem_comap.1 h)
  have he' : g + u = c • (fun x : Fin n → F => χ (x i)) := he
  have hu0 : u 0 = 0 := vanSub_apply_zero hu
  have hg0 : g 0 = 0 := by
    have := congrFun he' 0
    simpa [h0, hu0] using this
  obtain ⟨m, hm⟩ := ((hB.th τ).1 g).2 ⟨hg, hg0⟩
  exact ⟨m, (mem_stepGraph_iff D τ χ i c m).2 ⟨g, u, hm, hu, he'.symm⟩⟩

theorem zero_mem_stepGraph_iff (D : LieLatticeData Ω F n Sg r s) (τ : Sg) (χ : F → Ω) (i : Fin n)
    (m : Fin (r τ) → Ω) : (0, m) ∈ D.stepGraph τ χ i ↔ m ∈ D.kk τ ((i : ℕ) + 1) := by
  rw [mem_stepGraph_iff]
  constructor
  · rintro ⟨g, u, hg, hu, he⟩
    rw [zero_smul] at he
    have hgu : g = -u := eq_neg_of_add_eq_zero_left he.symm
    refine ⟨(g, m), ⟨hg, AddSubgroup.mem_prod.2 ⟨?_, trivial⟩⟩, rfl⟩
    rw [hgu]
    exact neg_mem hu
  · rintro ⟨⟨g, m'⟩, ⟨hg, hp⟩, rfl⟩
    have hv : g ∈ vanSub Ω F n ((i : ℕ) + 1) := (AddSubgroup.mem_prod.1 hp).1
    refine ⟨g, -g, hg, neg_mem hv, ?_⟩
    simp

theorem stepKer : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ i, LocFree R 1 ((D.stepGraph τ (χ τ) i).comap (AddMonoidHom.inl _ _))) ∧ ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ i, ((D.bc RC).stepGraph τ (fun a => algebraMap Ω C (χ τ a)) i).comap (AddMonoidHom.inl _ _) = spanOver RC (algebraMap Ω C '' (D.stepGraph τ (χ τ) i).comap (AddMonoidHom.inl _ _)) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hχ hB hG1 hG2
  refine ⟨fun τ i => ?_, fun C _ _ _ _ RC hRC τ i => ?_⟩
  · have h0 : χ τ 0 = 0 := (hχ.2.2.2.2 τ).1
    exact (LocFreeSchanuel.main R 1 (r τ) (D.xId (χ τ) i)
      ((D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _)) (D.kk τ ((i : ℕ) + 1))
      (D.stepGraph τ (χ τ) i) (((GlobalTheory.T.lattice_good_base_change D R p w χ hχ hB hG1).1 τ).2.2.2 i) (hG2.step τ i)
      (hG2.kk τ _) (stepGraph_stable D hB τ (χ τ) i)
      (fun c m h => ⟨fst_mem_xId_of_mem_stepGraph D hB τ (χ τ) i h, ⟨(c, m), h, rfl⟩⟩)
      (fun c h => exists_mem_stepGraph_of_mem_xId D hB τ (χ τ) h0 i h)
      (zero_mem_stepGraph_iff D τ (χ τ) i)
      (by
        rintro _ ⟨⟨c, m⟩, h, rfl⟩
        exact ⟨c, h⟩)).2
  · have hst := stepGraph_stable D hB τ (χ τ) i
    rw [(GlobalTheory.T.kernel_graph_base_change_holds D R p w χ hχ hB hG1 C RC hRC τ).2 i]
    let sw := (AddEquiv.prodComm (M := Ω) (N := Fin (r τ) → Ω)).toAddMonoidHom
    let Δ' : AddSubgroup ((Fin (r τ) → Ω) × Ω) := (D.stepGraph τ (χ τ) i).map sw
    have hst' : ∀ a ∈ R, ∀ v ∈ Δ', a • v ∈ Δ' := by
      rintro a ha _ ⟨x, hx, rfl⟩
      exact ⟨a • x, hst a ha x hx, rfl⟩
    have hfst : Δ'.map (AddMonoidHom.fst _ _) =
        (D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _) := by
      rw [AddSubgroup.map_map]
      rfl
    have key := (GlobalTheory.T.locally_free_base_change_quotient R RC hRC (bcMap Ω C (Fin (r τ))) (Algebra.linearMap Ω C)
      (isBaseChange_bcMap Ω C _) (IsBaseChange.linearMap Ω C) Δ' ⊥ (r τ) hst'
      (hfst ▸ hG2.step τ i) bot_le (by
        intro a _ v hv
        rw [AddSubgroup.mem_bot] at hv ⊢
        rw [hv, smul_zero])).2
    have hsw := spanOver_swap RC (bcMap Ω C (Fin (r τ))) (Algebra.linearMap Ω C)
      (D.stepGraph τ (χ τ) i)
    have e1 : Δ'.comap (AddMonoidHom.inr _ _) =
        (D.stepGraph τ (χ τ) i).comap (AddMonoidHom.inl _ _) := by
      ext c
      constructor
      · rintro ⟨⟨c', m⟩, h, he⟩
        have h1 : m = 0 := congrArg Prod.fst he
        have h2 : c' = c := congrArg Prod.snd he
        subst h1 h2
        exact h
      · intro h
        exact ⟨_, h, rfl⟩
    have e2 : ∀ X : AddSubgroup (C × (Fin (r τ) → C)),
        (X.map (AddEquiv.prodComm (M := C) (N := Fin (r τ) → C)).toAddMonoidHom).comap
          (AddMonoidHom.inr _ _) = X.comap (AddMonoidHom.inl _ _) := by
      intro X
      ext c
      constructor
      · rintro ⟨⟨c', m⟩, h, he⟩
        have h1 : m = 0 := congrArg Prod.fst he
        have h2 : c' = c := congrArg Prod.snd he
        subst h1 h2
        exact h
      · intro h
        exact ⟨_, h, rfl⟩
    rw [hsw, e2, e1] at key
    exact key

end GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness
end

section

open GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.hodge_annihilator_lattice_holds : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → p.Prime → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ φ : Equiv.Perm Sg, D.TestFacts R p w χ φ → D.Good₁ R p χ → ∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.hodge_annihilator_lattice | exact GlobalTheory.CompanionTheory.Ar.Num.hodge_annihilator_lattice | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.hodge_annihilator_lattice <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj.AlphaAct

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem alpha_comm_act : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (a : O) (u : Fin d → R), alpha B p (((rho B a).map (· ^ p)).mulVec u) = rhoH B a (alpha B p u) :=
  @PositivityTheory.HtPt.Cb.alpha_act

end GlobalTheory.CompanionTheory.Ar.Conj.AlphaAct
end
end

section

open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Flat.DegCurve

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegCurve

theorem subDeg_range_shortExact : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V'') (P : V →ₗ[K] V) (P' : V' →ₗ[K] V') (P'' : V'' →ₗ[K] V''), IsBun C L' → ShortExact C L L' L'' f g → (∀ x, P (P x) = P x) → (∀ x, P' (P' x) = P' x) → (∀ x, P'' (P'' x) = P'' x) → (∀ x, f (P x) = P' (f x)) → (∀ y, g (P' y) = P'' (g y)) → IsHom C L' L' P' → subDeg C L' (LinearMap.range P') = subDeg C L (LinearMap.range P) + subDeg C L'' (LinearMap.range P'') := by
  intro K _ C V _ _ _ V' _ _ _ V'' _ _ _ L L' L'' f g P P' P'' hB hSE hP hP' hP'' hfP hgP hHom
  obtain ⟨hinj, hex, hsurj, hL, hL''⟩ := hSE
  have mP : ∀ v ∈ LinearMap.range P, P v = v := by
    intro v hv
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hv
    exact hP u
  have mP' : ∀ v ∈ LinearMap.range P', P' v = v := by
    intro v hv
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hv
    exact hP' u
  have mP'' : ∀ v ∈ LinearMap.range P'', P'' v = v := by
    intro v hv
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hv
    exact hP'' u
  let f₀ : LinearMap.range P →ₗ[K] LinearMap.range P' :=
    LinearMap.codRestrict (LinearMap.range P') (f.domRestrict (LinearMap.range P)) (fun v =>
      LinearMap.mem_range.2 ⟨f v, by
        show P' (f v) = f v
        rw [← hfP, mP _ v.2]⟩)
  let g₀ : LinearMap.range P' →ₗ[K] LinearMap.range P'' :=
    LinearMap.codRestrict (LinearMap.range P'') (g.domRestrict (LinearMap.range P')) (fun v =>
      LinearMap.mem_range.2 ⟨g v, by
        show P'' (g v) = g v
        rw [← hgP, mP' _ v.2]⟩)
  have hSE0 : ShortExact C (sub C L (LinearMap.range P)) (sub C L' (LinearMap.range P'))
      (sub C L'' (LinearMap.range P'')) f₀ g₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x y h
      apply Subtype.ext
      apply hinj
      exact congrArg Subtype.val h
    · intro y
      constructor
      · intro hy
        have hy' : g (y : V') = 0 := congrArg Subtype.val hy
        obtain ⟨x, hx⟩ := (hex (y : V')).1 hy'
        refine ⟨⟨P x, LinearMap.mem_range_self P x⟩, ?_⟩
        apply Subtype.ext
        show f (P x) = (y : V')
        rw [hfP, hx, mP' _ y.2]
      · rintro ⟨x, rfl⟩
        apply Subtype.ext
        show g (f (x : V)) = 0
        exact (hex _).2 ⟨x, rfl⟩
    · intro z
      obtain ⟨y, hy⟩ := hsurj (z : V'')
      refine ⟨⟨P' y, LinearMap.mem_range_self P' y⟩, ?_⟩
      apply Subtype.ext
      show g (P' y) = (z : V'')
      rw [hgP, hy, mP'' _ z.2]
    · intro i x
      show (x : V) ∈ L i ↔ f (x : V) ∈ L' i
      exact hL i x
    · intro i z
      constructor
      · intro hz
        obtain ⟨y, hyL, hy⟩ := (hL'' i z).1 hz
        refine ⟨⟨P' y, LinearMap.mem_range_self P' y⟩, hHom i y hyL, ?_⟩
        apply Subtype.ext
        show g (P' y) = (z : V'')
        rw [hgP, hy, mP'' _ z.2]
      · rintro ⟨y, hyL, rfl⟩
        exact (hL'' i _).2 ⟨y, hyL, rfl⟩
  have hBW : IsBun C (sub C L' (LinearMap.range P')) :=
    (SubQuot.isBun_sub_quot K C V' L' (LinearMap.range P') hB).1
  exact (deg_shortExact K C (LinearMap.range P) (LinearMap.range P') (LinearMap.range P'')
    (sub C L (LinearMap.range P)) (sub C L' (LinearMap.range P')) (sub C L'' (LinearMap.range P''))
    f₀ g₀ hBW hSE0).2.2

end GlobalTheory.CompanionTheory.Ar.Flat.DegCurve
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.short_exact_first_term_bundle : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V''), IsBun C L' → ShortExact C L L' L'' f g → IsBun C L ∧ IsBun C L'' ∧ deg C L' = deg C L + deg C L'' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.deg_shortExact | exact GlobalTheory.CompanionTheory.Ar.Crv.deg_shortExact | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.deg_shortExact <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.augmentation_length_colength_bound : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card N * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card N * (p - 1)) = cN ^ 2 → GenAF p AA.carrier ⊥) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.augmentation_length_colength_bound | exact GlobalTheory.CompanionTheory.Relay.augmentation_length_colength_bound | (intros; apply GlobalTheory.CompanionTheory.Relay.augmentation_length_colength_bound <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem ret_hopf_factor : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'], ∀ (ι : N' →+ N) (π : N →+ N'), (∀ y, π (ι y) = y) → (∀ g ∈ AA.carrier, (fun x => g (ι (π x))) ∈ AA.carrier) → (∃ A' : HopfOrder (C := C) R N', A'.carrier = AA.carrier.map (LinearMap.funLeft R C (ι : N' → N))) ∧ (∀ h ∈ AA.carrier.map (LinearMap.funLeft R C (ι : N' → N)), (fun x => h (π x)) ∈ AA.carrier) ∧ ∀ K' : AddSubgroup N', GenAF p AA.carrier (K'.map ι) → GenAF p (AA.carrier.map (LinearMap.funLeft R C (ι : N' → N))) K' :=
  @PositivityTheory.HtPt.Re.ret_hopf

end GlobalTheory.CompanionTheory.Ar.GR
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.fundamental_ideal_frobenius_powers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ c : ℕ → R, (∀ n, xIdeal AA.carrier (σ ^ p ^ n) = Ideal.span {c n}) → (∀ n, v (p : C) ≤ v (algebraMap R C (c n)) ^ (p - 1)) ∧ ∀ d : Fin f → Fin p, (∃ n, (d n : ℕ) ≠ 0) → xIdeal AA.carrier (σ ^ (∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ))) = Ideal.span {∏ n : Fin f, c n ^ (d n : ℕ)} := by
  first | exact @GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_powers | exact GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_powers | (intros; apply GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_powers <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.stable_hopf_order_fundamental_lengths : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∃ d : Fin n → Fin f → R, (∀ (i : Fin n) (s : Fin f), idealD p AA.carrier (flagSub b i) (b i) (σ ^ p ^ (s : ℕ)) = Ideal.span {d i s}) ∧ HasLen v R (AFQuot p AA.carrier) (∏ i, ∏ s, v (algebraMap R C (d i s))) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.stable_hopf_order_fundamental_lengths | exact GlobalTheory.CompanionTheory.Relay.stable_hopf_order_fundamental_lengths | (intros; apply GlobalTheory.CompanionTheory.Relay.stable_hopf_order_fundamental_lengths <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.CompanionTheory.Relay.hopf_orders_of_zmod_p_extremes : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → (∃ AA : HopfOrder (C := C) R (ZMod p), AA.carrier = intFun R (ZMod p) ∧ FStable (ZMod p) AA.carrier ∧ IsTight v p AA.carrier ∧ ∀ K, GenAF p AA.carrier K) ∧ (∃ AA : HopfOrder (C := C) R (ZMod p), AA.carrier = Submodule.span R (Set.range fun (ψ : AddChar (ZMod p) C) (x : ZMod p) => ψ x) ∧ AA.carrier ≠ intFun R (ZMod p) ∧ FStable (ZMod p) AA.carrier ∧ IsTight v p AA.carrier ∧ ∀ K, GenAF p AA.carrier K) := by
  first | exact @PositivityTheory.HtPt.Ri.inh_af | exact PositivityTheory.HtPt.Ri.inh_af
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem subquoHopfOrder : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable (F := F) AA.carrier → ∀ (K : Submodule F N) [Fintype K] [DecidableEq K] [Fintype (N ⧸ K)] [DecidableEq (N ⧸ K)], (∃ AK : HopfOrder (C := C) R K, AK.carrier = (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) ∧ FStable (F := F) AK.carrier) ∧ (∃ AQ : HopfOrder (C := C) R (N ⧸ K), AQ.carrier = (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) ∧ FStable (F := F) AQ.carrier) ∧ invFun AA.carrier K.toAddSubgroup = (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))).map (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K)) ∧ ∀ c cQ cK, HasColen R v AA.carrier c → HasColen R v (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) cQ → HasColen R v (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) cK → c = cQ ^ Fintype.card K * cK ^ Fintype.card (N ⧸ K) :=
  by
    intro p _ C _ _ _ v R _ _ hv _ F _ _ _ _ f _ N _ _ _ _ AA hAA K _ _ _ _
    have hres : FStable (F := F)
        (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) := by
      rintro a _ ⟨g, hg, rfl⟩
      exact ⟨_, hAA a g hg, rfl⟩
    have hquo : FStable (F := F)
        (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) := by
      intro a g hg
      have h := hAA a _ hg
      show LinearMap.funLeft R C (K.mkQ : N → N ⧸ K) _ ∈ AA.carrier
      convert h using 1
      funext x
      show g (K.mkQ (a • x)) = g (a • K.mkQ x)
      rw [map_smul]
    have hrange : K.subtype.toAddMonoidHom.range = K.mkQ.toAddMonoidHom.ker := by
      ext x
      simp [AddMonoidHom.mem_range, AddMonoidHom.mem_ker]
    refine ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨AK, hAK⟩ := PositivityTheory.HtPt.Rc.exists_res hv AA
        K.subtype.toAddMonoidHom Subtype.val_injective
      exact ⟨AK, hAK, hAK ▸ hres⟩
    · obtain ⟨AQ, hAQ⟩ := PositivityTheory.HtPt.Rc.exists_quo hv AA
        K.mkQ.toAddMonoidHom K.mkQ_surjective
      exact ⟨AQ, hAQ, hAQ ▸ hquo⟩
    · exact PositivityTheory.HtPt.Rc.invFun_eq _ K.mkQ.toAddMonoidHom
        K.mkQ_surjective _ (fun x => by simp)
    · intro c cQ cK hc hQ hK
      exact PositivityTheory.HtPt.Rc.colen_ses hv AA K.subtype.toAddMonoidHom
        Subtype.val_injective K.mkQ.toAddMonoidHom K.mkQ_surjective hrange c cQ cK hc hQ hK

end GlobalTheory.CompanionTheory.Ar.GR
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.Sesq

theorem form_of_datum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), (∀ (a : 𝓞 E) x y, Algebra.trace ℚ E ((a : E) * sesq D x y) = (D.EF (a • x) y : ℚ)) ∧ (∀ x x' y, sesq D (x + x') y = sesq D x y + sesq D x' y) ∧ (∀ x y y', sesq D x (y + y') = sesq D x y + sesq D x y') ∧ (∀ (a : 𝓞 E) x y, sesq D (a • x) y = a * sesq D x y) ∧ (∀ (a : 𝓞 E) x y, sesq D x (a • y) = IsCMField.complexConj E (a : E) * sesq D x y) ∧ (∀ x y, sesq D y x = -IsCMField.complexConj E (sesq D x y)) ∧ ∀ δ ∈ differentIdeal ℤ (𝓞 E), ∀ x y, ∃ b : 𝓞 E, (δ : E) * sesq D x y = b := by
  intro E _ _ _ H D
  exact PositivityTheory.Xgf.sesq_sesquilinear_skew_hermitian E H D

end GlobalTheory.CompanionTheory.Ar.Fl.Sesq
end
