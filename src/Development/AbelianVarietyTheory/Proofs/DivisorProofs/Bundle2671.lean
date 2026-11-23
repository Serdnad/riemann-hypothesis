module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle111
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1253
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle012
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTorsionSectionsOfRoot
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle117
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle003
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegUniq

theorem eq_of_siegPB : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (S : Scheme.{0})
    (s' : S ⟶ Sp (cycAway n)) (c : SiegPre g n (zetaAway n) s') (f f' : S ⟶ F.X), f ≫ F.s = s' → f' ≫ F.s = s' →
    SiegPB c F.univ f → SiegPB c F.univ f' → f = f' := by
  intro g n _ _ _ F S s' c f f' hf hf' h₁ h₂
  refine GlobalTheory.hom_ext_of_fromSpecStalk fun x => ?_
  haveI : IsLocalRing (S.presheaf.stalk x) := inferInstance
  obtain ⟨c', hc'⟩ := (GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) S (Sp (S.presheaf.stalk x)) s'
    (S.fromSpecStalk x ≫ s') (S.fromSpecStalk x) c rfl).1
  have e : (S.fromSpecStalk x ≫ f) ≫ F.s = (S.fromSpecStalk x ≫ f') ≫ F.s := by
    simp only [Category.assoc, hf, hf']
  exact @SFam.inj g n _ _ _ F (S.presheaf.stalk x) _ this (S.fromSpecStalk x ≫ f) (S.fromSpecStalk x ≫ f') (S.fromSpecStalk x ≫ s') c' e
    (GlobalTheory.SiegelPullComp.pb_comp h₁ hc') (GlobalTheory.SiegelPullComp.pb_comp h₂ hc')

end GlobalTheory.SiegUniq
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM
open scoped CategoryTheory.Obj

namespace GlobalTheory.HodgePow

open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CechPic

theorem lbIso_hodge_of_iso {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (e : A ≅ B)
    (he : η[A] ≫ e.hom = η[B]) (r : ℕ) (hA : IsVB (omega A) r) :
    IsVB (omega B) r ∧ LBIso (GlobalTheory.SiegelTor.hodge A r) (GlobalTheory.SiegelTor.hodge B r) := by
  have he' : η[B] ≫ e.inv = η[A] := by rw [← he, Category.assoc, e.hom_inv_id, Category.comp_id]
  let φ : omega A ≅ omega B :=
    { hom := cotMap e.inv he'
      inv := cotMap e.hom he
      hom_inv_id := (cotMap_comp he' he e.hom_inv_id (Category.comp_id _)).trans (cotMap_id rfl _)
      inv_hom_id := (cotMap_comp he he' e.inv_hom_id (Category.comp_id _)).trans (cotMap_id rfl _) }
  exact ⟨hA.of_iso φ, hA.lbIso_det_of_iso φ⟩

def prodUnitIso {S : Scheme.{0}} (G : Over S) : G ⊗ 𝟙_ (Over S) ≅ G where
  hom := fst _ _
  inv := lift (𝟙 G) (toUnit G)
  hom_inv_id := by ext1 <;> simp <;> exact toUnit_unique _ _
  inv_hom_id := by simp

section Pow

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [QuasiSeparated G.hom] (g : ℕ)

theorem cls_hodge_powObj [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom]
    (hs : SmoothOfRelativeDimension g G.hom) (hG : IsVB (omega G) g) (n : ℕ) :
    ∃ h : IsVB (omega (powObj G (n + 1))) ((n + 1) * g),
      cls _ h.isLB_det = (n + 1) • cls _ hG.isLB_det := by
  have hV : ∀ m, IsVB (omega (powObj G m)) (m * g) := fun m => by
    haveI := (GlobalFunctionsDvrGeneric.powObj_props G m).2.1
    haveI := smoothOfRelativeDimension_powObj G g hs m
    exact isVB_omega _ _
  refine ⟨hV (n + 1), ?_⟩
  induction n with
  | zero =>
    have hE : η[G ⊗ 𝟙_ (Over S)] ≫ (prodUnitIso G).hom = η[G] := by simp [prodUnitIso]
    have h1 := hV 1
    rw [Nat.one_mul] at h1
    have := (lbIso_hodge_of_iso (prodUnitIso G) hE g h1).2
    rw [Nat.zero_add, one_smul]
    have hh : ∀ (r : ℕ) (hr : r = 1 * g) (h₁ : IsVB (omega (powObj G 1)) r),
        cls _ h₁.isLB_det = cls _ hG.isLB_det := by
      intro r hr h₁
      rw [Nat.one_mul] at hr
      subst hr
      exact (cls_eq_iff _ _).2 this
    exact hh _ rfl (hV 1)
  | succ n ih =>
    haveI := (GlobalFunctionsDvrGeneric.powObj_props G (n + 1)).2.1
    have key := GlobalTheory.HodgeProd.lbIso_det_conormal_prod G (powObj G (n + 1)) g ((n + 1) * g) hG (hV (n + 1))
      η[G ⊗ powObj G (n + 1)] (by ext1 <;> simp)
    have hT := isLB_tens hG.isLB_det (hV (n + 1)).isLB_det
    have hh : ∀ (r : ℕ) (hr : r = g + (n + 1) * g) (h₁ : IsVB (omega (powObj G (n + 1 + 1))) r),
        cls _ h₁.isLB_det = cls _ hG.isLB_det + cls _ (hV (n + 1)).isLB_det := by
      intro r hr h₁
      subst hr
      rw [← cls_tens _ _ hT]
      exact (cls_eq_iff _ _).2 key
    rw [hh _ (by ring) (hV _), ih, succ_nsmul' _ (n + 1)]

theorem one_powPr {n : ℕ} (i : Fin n) : η[powObj G n] ≫ powPr G i = η[G] := by
  haveI := powPr.isMonHom G i
  exact IsMonHom.one_hom _

end Pow

theorem hodge_eight_mul_iso_hodge_pow_eight : ∀ (S : Scheme.{0}) (G H : Over S) [GrpObj G] [GrpObj H] (g : ℕ) (pr : Fin 8 → (H ⟶ G)),
    (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ G)), ∃! x : T ⟶ H, ∀ u, x ≫ pr u = y u) →
    IsSemiAbelian G → SmoothOfRelativeDimension g G.hom →
    LBIso (GlobalTheory.SiegelTor.hodge H (8 * g)) (lbPow (GlobalTheory.SiegelTor.hodge G g) 8) := by
  intro S G H _ _ g pr hpr hU hG hs
  haveI := hG.smooth
  haveI := hG.separated
  haveI := hG.quasiCompact
  haveI : SmoothOfRelativeDimension g G.hom := hs
  have hVG : IsVB (omega G) g := isVB_omega G g
  obtain ⟨hP, hc⟩ := cls_hodge_powObj G g hs hVG 7
  let lim : IsLimit (Fan.mk H pr) := mkFanLimit _ (fun s => (hU s.pt s.proj).exists.choose)
    (fun s i => (hU s.pt s.proj).exists.choose_spec i)
    (fun s m hm => (hU s.pt s.proj).unique hm (hU s.pt s.proj).exists.choose_spec)
  let e : H ≅ powObj G 8 := lim.conePointUniqueUpToIso (powIsLimit G 8)
  have he : ∀ i, e.hom ≫ powPr G i = pr i := fun i =>
    lim.conePointUniqueUpToIso_hom_comp (powIsLimit G 8) ⟨i⟩
  have hη : η[powObj G 8] ≫ e.inv = η[H] := by
    refine lim.hom_ext fun ⟨i⟩ => ?_
    have h1 : e.inv ≫ pr i = powPr G i := by rw [← he, Iso.inv_hom_id_assoc]
    haveI := hpr i
    simp only [Fan.mk_π_app, Category.assoc, h1]
    exact (one_powPr G i).trans (IsMonHom.one_hom (pr i)).symm
  obtain ⟨hH, hiso⟩ := lbIso_hodge_of_iso e.symm hη (8 * g) hP
  have hL := hVG.isLB_det
  refine (cls_eq_iff hH.isLB_det (isLB_lbPow hL 8)).1 ?_
  rw [cls_lbPow hL, ← (cls_eq_iff hP.isLB_det hH.isLB_det).2 hiso]
  exact hc

end GlobalTheory.HodgePow
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.LevTrivOpen

variable {S : Scheme.{0}}

theorem range_subset_iff_mem {k : Type} [Field k] (x : Sp k ⟶ S) (U : Set S) (p : Sp k) :
    Set.range x.base ⊆ U ↔ x.base p ∈ U := by
  refine ⟨fun h => h ⟨p, rfl⟩, ?_⟩
  rintro h _ ⟨q, rfl⟩
  rwa [Subsingleton.elim q p]

theorem pow_nsmul {G : Over S} [GrpObj G] {h : ℕ} (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ G))
    (hadd : ∀ a b, lev (a + b) = lev a * lev b) (n : ℕ) (c : Fin h ⊕ Fin h → ℤ) : lev (n • c) = lev c ^ n := by
  have h0 : lev 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  induction n with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]

end GlobalTheory.LevTrivOpen

open GlobalTheory.LevCover GlobalTheory.LevTrivOpen in
theorem GlobalTheory.levTriv_locus_open : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (M : ℕ) (t : S ⟶ Sp (cycAway M)) (G : Over S) [GrpObj G] [IsCommMonObj G] (h : ℕ) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ G)), IsAbelianScheme G → 3 ≤ M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S), (∀ a, (toUnit (Over.mk x₀) ≫ lev a = 1 ↔ ∃ b, a = M • b)) → ∃ W : S.Opens, Set.range x₀.base ⊆ W ∧ ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ S), Set.range x.base ⊆ W → ∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = M • b) := by
  intro S _ M t G _ _ h lev hab hM hadd hpow k _ _ x₀ hx₀
  have hu : IsUnit (M : Γ(S, ⊤)) := by
    have := (GlobalTheory.SiegelTor.isUnit_natCast (n := M) (by omega)).map
      (t.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (GlobalTheory.SiegelTor.cycAway M))).inv.hom)
    rwa [map_natCast] at this
  obtain ⟨-, hfin, het⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion G (hG := hab) hu
  have hU : ∀ f : 𝟙_ (Over S) ⟶ G, ∃ U : S.Opens, IsClosed (U : Set S) ∧ (f ^ M = 1 → ∀ (k' : Type) [Field k']
      [IsAlgClosed k'] (x : Sp k' ⟶ S), (toUnit (Over.mk x) ≫ f = 1 ↔ Set.range x.base ⊆ U)) := fun f => by
    by_cases hf : f ^ M = 1
    · obtain ⟨U, hUc, HU⟩ := GlobalTheory.TorsionSections.clopenCond_torsion_eq (n := M) (T := 𝟙_ (Over S)) hf (one_pow M)
      refine ⟨U, hUc, fun _ k' _ _ x => ?_⟩
      have := HU (Over.mk x) (toUnit (Over.mk x))
      simp only [MonObj.comp_one] at this
      simpa using this
    · exact ⟨⊤, isClosed_univ, fun h => absurd h hf⟩
  choose Uf hUc HU using hU
  classical
  obtain ⟨κ, _, q, hq⟩ := exists_finite_mod (Fin h ⊕ Fin h → ℤ) (show 0 < M by omega)
  let P : (Fin h ⊕ Fin h → ℤ) → Prop := fun a => ∃ b, a = M • b
  let A : (Fin h ⊕ Fin h → ℤ) → Set S := fun a => {s | s ∈ (Uf (lev a) : Set S) ↔ P a}
  have hAo : ∀ a, IsOpen (A a) := fun a => by
    by_cases hp : P a
    · convert (Uf (lev a)).isOpen using 1
      ext s
      simp only [A, Set.mem_setOf_eq, hp, iff_true, SetLike.mem_coe]
    · convert (hUc (lev a)).isOpen_compl using 1
      ext s
      simp only [A, Set.mem_setOf_eq, hp, iff_false, Set.mem_compl_iff, SetLike.mem_coe]
  have hAq : ∀ a a', q a = q a' → A a = A a' := fun a a' e => by
    obtain ⟨c, rfl⟩ := hq a a' e
    have hl : lev (a + M • c) = lev a := by rw [hadd, pow_nsmul lev hadd, hpow, _root_.mul_one]
    have hP : P (a + M • c) ↔ P a :=
      ⟨fun ⟨b, hb⟩ => ⟨b - c, by rw [smul_sub, ← hb]; abel⟩, fun ⟨b, hb⟩ => ⟨b + c, by rw [hb, smul_add]⟩⟩
    ext s
    simp only [A, Set.mem_setOf_eq, hl, hP]
  let pick : κ → (Fin h ⊕ Fin h → ℤ) := fun c => if hc : ∃ a, q a = c then hc.choose else 0
  have hpick : ∀ a, A a = A (pick (q a)) := fun a => by
    have hc : ∃ a', q a' = q a := ⟨a, rfl⟩
    refine hAq _ _ ?_
    simp only [pick, dif_pos hc]
    exact hc.choose_spec.symm
  refine ⟨⟨⋂ c, A (pick c), isOpen_iInter_of_finite fun c => hAo _⟩, ?_, ?_⟩
  · rintro _ ⟨p, rfl⟩
    simp only [TopologicalSpace.Opens.coe_mk, Set.mem_iInter]
    intro c
    show x₀.base p ∈ (Uf (lev (pick c)) : Set S) ↔ P (pick c)
    rw [← range_subset_iff_mem, ← HU _ (hpow _) k x₀]
    exact hx₀ _
  · intro k' _ _ x hx a
    obtain ⟨p⟩ := (inferInstance : Nonempty (Sp k'))
    have h1 := hx ⟨p, rfl⟩
    simp only [TopologicalSpace.Opens.coe_mk, Set.mem_iInter] at h1
    have h2 : x.base p ∈ A a := by rw [hpick]; exact h1 _
    rw [HU _ (hpow a) k' x, range_subset_iff_mem _ _ p]
    exact h2
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.TorsEqOpen

theorem exists_open_eqLocus {S X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion (pullback.diagonal f)]
    (u v : S ⟶ X) (huv : u ≫ f = v ≫ f) :
    ∃ U : S.Opens, (∀ V : S.Opens, V ≤ U → V.ι ≫ u = V.ι ≫ v) ∧
      ∀ (T : Scheme.{0}) (g : T ⟶ S), g ≫ u = g ≫ v → Set.range g.base ⊆ (U : Set S) := by
  refine ⟨(pullback.lift u v huv) ⁻¹ᵁ (pullback.diagonal f).opensRange, ?_, ?_⟩
  · intro V hV
    have hr : Set.range (V.ι ≫ pullback.lift u v huv).base ⊆ Set.range (pullback.diagonal f).base := by
      rintro _ ⟨p, rfl⟩
      have hp : V.ι.base p ∈ V := by
        have h0 : V.ι.base p ∈ Set.range V.ι.base := ⟨p, rfl⟩
        rwa [Scheme.Opens.range_ι] at h0
      have := hV hp
      simpa using this
    have hl := IsOpenImmersion.lift_fac (pullback.diagonal f) (V.ι ≫ pullback.lift u v huv) hr
    have h1 := congrArg (· ≫ pullback.fst f f) hl
    have h2 := congrArg (· ≫ pullback.snd f f) hl
    simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, pullback.lift_fst,
      pullback.lift_snd, Category.comp_id] at h1 h2
    rw [← h1, ← h2]
  · intro T g hg
    rintro _ ⟨p, rfl⟩
    have e : g ≫ pullback.lift u v huv = g ≫ u ≫ pullback.diagonal f := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
      · simp only [Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, hg]
    have e2 := congrArg (fun h => h.base p) e
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at e2
    show (pullback.lift u v huv).base (g.base p) ∈ (pullback.diagonal f).opensRange
    rw [← SetLike.mem_coe, Scheme.Hom.coe_opensRange]
    exact ⟨_, e2.symm⟩

end GlobalTheory.TorsEqOpen

namespace GlobalTheory.TorsEqOpen

theorem comp_pow_pt {S : Scheme.{0}} {X Y G : Over S} [GrpObj G] (f : X ⟶ Y) (g : Y ⟶ G) (n : ℕ) :
    f ≫ g ^ n = (f ≫ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem eq_of_eq_single {S : Scheme.{0}} {κ : Type} [Fintype κ] [DecidableEq κ] {A Z W : Over S} [GrpObj A] [IsCommMonObj A]
    (x y : (κ → ℤ) → (W ⟶ A)) (hx : ∀ a b, x (a + b) = x a * x b) (hy : ∀ a b, y (a + b) = y a * y b)
    (φ : Z ⟶ W) (hφ : ∀ i, φ ≫ x (Pi.single i 1) = φ ≫ y (Pi.single i 1)) (a : κ → ℤ) :
    φ ≫ x a = φ ≫ y a := by
  let F : (κ → ℤ) →+ Additive (Z ⟶ A) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (φ ≫ x a)) (fun a b => by
      rw [hx, MonObj.comp_mul]; rfl)
  let G : (κ → ℤ) →+ Additive (Z ⟶ A) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (φ ≫ y a)) (fun a b => by
      rw [hy, MonObj.comp_mul]; rfl)
  have hFG : F = G := by
    refine AddMonoidHom.functions_ext _ F G fun i k => ?_
    have e : (Pi.single i k : κ → ℤ) = k • Pi.single i 1 := by
      ext j
      by_cases h : j = i
      · subst h; simp
      · simp [Pi.single_apply, h]
    rw [e, map_zsmul, map_zsmul]
    congr 1
    simpa [F, G] using congrArg Additive.ofMul (hφ i)
  exact congrArg Additive.toMul (DFunLike.congr_fun hFG a)

end GlobalTheory.TorsEqOpen

namespace GlobalTheory

theorem torsFamily_eq_isOpen : ∀ (m M : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (t : S' ⟶ Sp (cycAway M))
    (A : Over S') [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → 1 ≤ M →
    ∀ (x y : (Fin m ⊕ Fin m → ℤ) → (𝟙_ (Over S') ⟶ A)), (∀ a b, x (a + b) = x a * x b) →
    (∀ a b, y (a + b) = y a * y b) → (∀ a, x a ^ M = 1) → (∀ a, y a ^ M = 1) →
    ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → ∀ a, V.ι ≫ (x a).left = V.ι ≫ (y a).left) ∧
      ∀ (T : Scheme.{0}) (g : T ⟶ S'), (∀ a, g ≫ (x a).left = g ≫ (y a).left) →
        Set.range g.base ⊆ (U : Set S') := by
  intro m M S' _ t A _ _ hA hM x y hx hy hxM hyM
  have hu : IsUnit (M : Γ(S', ⊤)) := by
    have h1 : IsUnit (M : cycAway M) := isUnit_natCast (by omega)
    have h2 := h1.map (Scheme.ΓSpecIso (CommRingCat.of (cycAway M))).inv.hom
    have h3 := h2.map t.appTop.hom
    simpa using h3
  haveI := hA.smooth
  haveI : Etale (𝟙 A ^ M).left := GlobalTheory.GrpTangent.etale_id_pow A hu
  have hpow : ∀ z : 𝟙_ (Over S') ⟶ A, z ^ M = 1 →
      z.left ≫ (𝟙 A ^ M).left = (1 : 𝟙_ (Over S') ⟶ A).left := by
    intro z hz
    rw [← Over.comp_left, TorsEqOpen.comp_pow_pt, Category.comp_id, hz]
  choose U hU1 hU2 using fun i : Fin m ⊕ Fin m =>
    TorsEqOpen.exists_open_eqLocus (S := S') (𝟙 A ^ M).left (x (Pi.single i 1)).left (y (Pi.single i 1)).left
      ((hpow _ (hxM _)).trans (hpow _ (hyM _)).symm)
  refine ⟨⟨⋂ i, (U i : Set S'), isOpen_iInter_of_finite fun i => (U i).2⟩, ?_, ?_⟩
  · intro V hV a
    have hVi : ∀ i, V ≤ U i := fun i => (show (V : Set S') ⊆ U i from
      (show (V : Set S') ⊆ ⋂ i, (U i : Set S') from hV).trans (Set.iInter_subset _ i))
    have key := TorsEqOpen.eq_of_eq_single x y hx hy (toUnit (Over.mk V.ι)) (fun i =>
      Over.OverMorphism.ext (by
        rw [Over.comp_left, Over.comp_left, Over.toUnit_left]
        exact hU1 i V (hVi i))) a
    have := congrArg Over.Hom.left key
    rwa [Over.comp_left, Over.comp_left, Over.toUnit_left] at this
  · intro T g hg
    exact Set.subset_iInter fun i => hU2 i T g (hg _)

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

namespace GlobalTheory.CycAwayQProj

theorem finiteType_closure {K : Type} [CommRing K] {s : Set K} (hs : s.Finite) :
    (Int.castRingHom (Subring.closure s)).FiniteType := by
  have h : Algebra.FiniteType ℤ (Algebra.adjoin ℤ s) :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨s, hs, rfl⟩)
  have e : Algebra.adjoin ℤ s ≃+* Subring.closure s :=
    RingEquiv.subringCongr (s := (Algebra.adjoin ℤ s).toSubring) (by rw [Algebra.adjoin_int]; rfl)
  have h' : Algebra.FiniteType ℤ (Subring.closure s) := h.equiv (AlgEquiv.ofRingEquiv (f := e) fun x => by simp)
  have := RingHom.finiteType_algebraMap.2 h'
  rwa [RingHom.eq_intCast' (algebraMap ℤ (Subring.closure s))] at this

theorem finiteType_cycAway (M : ℕ) : (Int.castRingHom (cycAway M)).FiniteType :=
  finiteType_closure (Set.toFinite _)

theorem isQProjOver_comp_spMap {A B : Type} [CommRing A] [CommRing B] {f : A →+* B} (hf : f.FiniteType)
    {Y : Scheme.{0}} {s : Y ⟶ Sp B} (h : IsQProjOver s) : IsQProjOver (s ≫ spMap f) := by
  obtain ⟨_, hL⟩ := (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB s).1 h
  have : LocallyOfFiniteType (spMap f) := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 hf
  exact (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB _).2 ⟨inferInstance, hL⟩

theorem isQProjOver_of_isFinite_pullback : ∀ (M : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R], IsUnit ((M : ℕ) : R) → ∀ (Y : Scheme.{0}) (s : Y ⟶ Sp (cycAway M)), IsQProjOver s → ∀ (Z : Scheme.{0}) (π : Z ⟶ pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R))), IsFinite π → IsQProjOver (π ≫ pullback.snd _ _) :=
  fun M _ _ _ _ _ _ hs _ π _ =>
    isQProjOver_comp_of_isFinite π
      (isQProjOver_of_isPullback (IsPullback.of_hasPullback _ _) (isQProjOver_comp_spMap (finiteType_cycAway M) hs))

end GlobalTheory.CycAwayQProj
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BalProj

theorem chart_dense_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens), Dense ((chart U).base ⁻¹' (interior Y : Set Y.X)) := by
  intro E _ _ _ H Dw l Xo c Y U
  have hi := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have h : IsOpenMap (chart U).base := (Scheme.Hom.isOpenEmbedding (f := U.2.fromSpec)).isOpenMap
  exact (dense_interior Y).preimage h

end GlobalTheory.BalProj
end
