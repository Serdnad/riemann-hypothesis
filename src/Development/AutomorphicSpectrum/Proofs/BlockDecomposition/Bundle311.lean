module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrrParIffCuspidalProduct
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle132
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle297
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenCore

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem nonempty_equiv_quotient_of_eq {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ G W) (P Q : Submodule ℂ W)
    (hP : ∀ g, P ≤ P.comap (σ g)) (hQ : ∀ g, Q ≤ Q.comap (σ g)) (h : P = Q) :
    Nonempty ((σ.quotient P hP).Equiv (σ.quotient Q hQ)) := by
  subst h
  exact ⟨Representation.Equiv.mk' (Representation.IntertwiningMap.id _) id
    (fun _ => rfl) (fun _ => rfl)⟩

theorem eq_or_eq_top_of_isIrreducible_quotient {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ G W) (P : Submodule ℂ W) (hP : ∀ g, P ≤ P.comap (σ g))
    (hirr : (σ.quotient P hP).IsIrreducible) (M : Submodule ℂ W)
    (hM : ∀ g, M ≤ M.comap (σ g)) (hPM : P ≤ M) : M = P ∨ M = ⊤ := by
  haveI : IsSimpleOrder (Subrepresentation (σ.quotient P hP)) := hirr
  let N : Subrepresentation (σ.quotient P hP) :=
    ⟨M.map P.mkQ, by
      rintro g _ ⟨m, hm, rfl⟩
      exact ⟨σ g m, hM g hm, rfl⟩⟩
  let S₀ : Subrepresentation (σ.quotient P hP) :=
    ⟨⊥, by
      intro g v hv
      rw [Submodule.mem_bot] at hv ⊢
      rw [hv, map_zero]⟩
  let S₁ : Subrepresentation (σ.quotient P hP) :=
    ⟨⊤, by
      intro _ _ _
      exact Submodule.mem_top⟩
  have hcomap : (M.map P.mkQ).comap P.mkQ = M := by
    rw [Submodule.comap_map_eq, Submodule.ker_mkQ, sup_eq_left.mpr hPM]
  rcases IsSimpleOrder.eq_bot_or_eq_top N with hN | hN
  · left
    have h1 : N ⊓ S₀ = N := by rw [hN, bot_inf_eq]
    have h2 := congrArg Subrepresentation.toSubmodule h1
    rw [Subrepresentation.toSubmodule_inf] at h2
    have h3 : M.map P.mkQ = ⊥ := le_bot_iff.mp (inf_eq_left.mp h2)
    rw [← hcomap, h3, Submodule.comap_bot, Submodule.ker_mkQ]
  · right
    have h1 : N ⊔ S₁ = N := by rw [hN, top_sup_eq]
    have h2 := congrArg Subrepresentation.toSubmodule h1
    rw [Subrepresentation.toSubmodule_sup] at h2
    have h3 : M.map P.mkQ = ⊤ := top_le_iff.mp (sup_eq_left.mp h2)
    rw [← hcomap, h3, Submodule.comap_top]

theorem nonempty_equiv_subQuot (ρ : Representation ℂ G V) (E K L : Subrepresentation ρ)
    (hK : (subQuot E K).IsIrreducible) (hL : (subQuot E L).IsIrreducible)
    (hE : ¬ E ≤ E ⊓ K ⊔ E ⊓ L) : Nonempty ((subQuot E K).Equiv (subQuot E L)) := by
  have hPK : ∀ g, K.toSubmodule.comap E.toSubmodule.subtype ≤
      (K.toSubmodule.comap E.toSubmodule.subtype).comap (E.toRepresentation g) := by
    intro g x hx
    exact K.2 g hx
  have hPL : ∀ g, L.toSubmodule.comap E.toSubmodule.subtype ≤
      (L.toSubmodule.comap E.toSubmodule.subtype).comap (E.toRepresentation g) := by
    intro g x hx
    exact L.2 g hx
  have hK' : (E.toRepresentation.quotient _ hPK).IsIrreducible := hK
  have hL' : (E.toRepresentation.quotient _ hPL).IsIrreducible := hL
  have hsup : ∀ g, K.toSubmodule.comap E.toSubmodule.subtype ⊔ L.toSubmodule.comap E.toSubmodule.subtype ≤
      (K.toSubmodule.comap E.toSubmodule.subtype ⊔ L.toSubmodule.comap E.toSubmodule.subtype).comap
        (E.toRepresentation g) := by
    intro g
    exact sup_le ((hPK g).trans (Submodule.comap_mono le_sup_left))
      ((hPL g).trans (Submodule.comap_mono le_sup_right))
  have hsup' : ∀ g, L.toSubmodule.comap E.toSubmodule.subtype ⊔ K.toSubmodule.comap E.toSubmodule.subtype ≤
      (L.toSubmodule.comap E.toSubmodule.subtype ⊔ K.toSubmodule.comap E.toSubmodule.subtype).comap
        (E.toRepresentation g) := by
    intro g
    rw [sup_comm]
    exact hsup g
  have hne : K.toSubmodule.comap E.toSubmodule.subtype ⊔ L.toSubmodule.comap E.toSubmodule.subtype ≠ ⊤ := by
    intro htop
    apply hE
    have hle : E.toSubmodule ≤ E.toSubmodule ⊓ K.toSubmodule ⊔ E.toSubmodule ⊓ L.toSubmodule := by
      intro x hx
      have hmem : (⟨x, hx⟩ : E.toSubmodule) ∈
          K.toSubmodule.comap E.toSubmodule.subtype ⊔ L.toSubmodule.comap E.toSubmodule.subtype := by
        rw [htop]
        exact Submodule.mem_top
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
      exact Submodule.mem_sup.mpr ⟨y, ⟨y.2, hy⟩, z, ⟨z.2, hz⟩, congrArg Subtype.val hyz⟩
    rw [← inf_eq_left]
    apply Subrepresentation.toSubmodule_injective
    rw [Subrepresentation.toSubmodule_inf, Subrepresentation.toSubmodule_sup,
      Subrepresentation.toSubmodule_inf, Subrepresentation.toSubmodule_inf]
    exact inf_eq_left.mpr hle
  have hne' : L.toSubmodule.comap E.toSubmodule.subtype ⊔ K.toSubmodule.comap E.toSubmodule.subtype ≠ ⊤ := by
    rw [sup_comm]
    exact hne
  have h1 := (GlobalTheory.CompanionTheory.GenCore.eq_or_eq_top_of_isIrreducible_quotient _ _ hPK hK' _ hsup le_sup_left).resolve_right hne
  have h2 := (GlobalTheory.CompanionTheory.GenCore.eq_or_eq_top_of_isIrreducible_quotient _ _ hPL hL' _ hsup' le_sup_left).resolve_right hne'
  have hPQ : K.toSubmodule.comap E.toSubmodule.subtype = L.toSubmodule.comap E.toSubmodule.subtype :=
    le_antisymm (sup_eq_left.mp h2) (sup_eq_left.mp h1)
  exact GlobalTheory.CompanionTheory.GenCore.nonempty_equiv_quotient_of_eq E.toRepresentation _ _ hPK hPL hPQ

end GlobalTheory.CompanionTheory.GenCore
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SubquotPres

theorem exists_equiv_subQuot : ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (π : Representation ℂ G W),
    IsSubquotient π ρ → ∃ A B : Subrepresentation ρ, B ≤ A ∧ Nonempty (π.Equiv (subQuot A B)) := by
  intro G V W _ _ _ _ _ ρ π h
  obtain ⟨S, f, hf⟩ := h
  have hint : ∀ (g : G) (x : S.toSubmodule),
      f.toLinearMap (S.toRepresentation g x) = π g (f.toLinearMap x) := fun g x => by
    simpa only [Representation.IntertwiningMap.toLinearMap_apply] using
      Representation.IntertwiningMap.isIntertwining _ _ f g x
  let K : Submodule ℂ S.toSubmodule := LinearMap.ker f.toLinearMap
  let B : Subrepresentation ρ := ⟨K.map S.toSubmodule.subtype, by
    intro g v hv
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hv
    refine Submodule.mem_map.mpr ⟨S.toRepresentation g x, ?_, rfl⟩
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hint, hx, map_zero]⟩
  have hBS : B ≤ S := by
    show K.map S.toSubmodule.subtype ≤ S.toSubmodule
    exact Submodule.map_subtype_le _ _
  have hQ : Submodule.comap S.toSubmodule.subtype B.toSubmodule = K :=
    Submodule.comap_map_eq_of_injective Subtype.val_injective K
  let φ := Submodule.liftQ (Submodule.comap S.toSubmodule.subtype B.toSubmodule) f.toLinearMap hQ.le
  have hφ : ∀ x : S.toSubmodule, φ (Submodule.Quotient.mk x) = f.toLinearMap x := fun x => rfl
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hQ.ge
  have hsurj : Function.Surjective φ := by
    intro w
    obtain ⟨x, rfl⟩ := hf w
    exact ⟨Submodule.Quotient.mk x, by rw [hφ, Representation.IntertwiningMap.toLinearMap_apply]⟩
  let e := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have hφint : ∀ (g : G) q, φ (GlobalTheory.SmGL.subQuot S B g q) = π g (φ q) := by
    intro g q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact hint g x
  have hT : ∀ g : G, e.symm.toLinearMap ∘ₗ π g =
      GlobalTheory.SmGL.subQuot S B g ∘ₗ e.symm.toLinearMap := by
    intro g
    ext w
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.symm_apply_eq]
    obtain ⟨q, rfl⟩ := e.surjective w
    rw [LinearEquiv.symm_apply_apply]
    exact (hφint g q).symm
  let T : Representation.IntertwiningMap π (GlobalTheory.SmGL.subQuot S B) :=
    ⟨e.symm.toLinearMap, hT⟩
  exact ⟨S, B, hBS, ⟨Representation.Equiv.mk' T e (fun w => e.apply_symm_apply w)
    (fun q => e.symm_apply_apply q)⟩⟩

end GlobalTheory.CompanionTheory.SubquotPres
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.ContraSq

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isSmooth_sub {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (S : Subrepresentation ρ) :
    IsSmooth S.toRepresentation := fun s => by
  have e : {g : G | S.toRepresentation g s = s} = {g : G | ρ g (s : V) = s} := by
    ext g
    exact Subtype.ext_iff
  rw [e]
  exact hρ s

theorem exists_smooth_extension {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (S : Subrepresentation ρ)
    {K : Subgroup G} (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G))
    (l₀ : Module.Dual ℂ S.toSubmodule) (hl₀ : ∀ h ∈ K, ∀ s, l₀ (S.toRepresentation h s) = l₀ s) :
    ∃ l : smoothPart ρ.dual, (∀ h ∈ K, contra ρ h l = l) ∧
      ∀ s : S.toSubmodule, (l : Module.Dual ℂ V) s = l₀ s := by
  have hmem : ∀ x : fixed S.toRepresentation K,
      (S.toSubmodule.subtype ∘ₗ (fixed S.toRepresentation K).subtype) x ∈ fixed ρ K := by
    intro x
    refine GlobalTheory.ContraRefl.mem_fix.2 fun h hh => ?_
    exact congrArg Subtype.val (GlobalTheory.ContraRefl.mem_fix.1 x.2 h hh)
  let ι : fixed S.toRepresentation K →ₗ[ℂ] fixed ρ K := LinearMap.codRestrict _ _ hmem
  have hι : LinearMap.ker ι = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have h1 : ((x : S.toSubmodule) : V) = 0 := congrArg Subtype.val hx
    exact Subtype.ext (Subtype.ext h1)
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective ι hι
  obtain ⟨l, hl1, hl2⟩ := GlobalTheory.ContraRefl.exists_fixed_contra hρ ho hc
    ((l₀ ∘ₗ (fixed S.toRepresentation K).subtype) ∘ₗ r)
  refine ⟨l, hl1, fun s => ?_⟩
  have key : (l : Module.Dual ℂ V) ∘ₗ S.toSubmodule.subtype = l₀ := by
    refine GlobalTheory.ContraRefl.form_ext (isSmooth_sub hρ S) hc (fun h hh w => ?_) hl₀ fun w hw => ?_
    · have h1 := congrArg (fun x : smoothPart ρ.dual => (x : Module.Dual ℂ V) (w : V))
        (hl1 h⁻¹ (inv_mem hh))
      simp only [contra_apply, inv_inv] at h1
      exact h1
    · have h2 := hl2 (ι ⟨w, hw⟩)
      have h3 : r (ι ⟨w, hw⟩) = ⟨w, hw⟩ := LinearMap.congr_fun hr ⟨w, hw⟩
      simp only [LinearMap.comp_apply, h3] at h2
      exact h2
  exact LinearMap.congr_fun key s

def annih {ρ : Representation ℂ G V} {τ : Representation ℂ G W} (S : Subrepresentation ρ)
    (f : S.toRepresentation.IntertwiningMap τ) : Subrepresentation (contra ρ) :=
  ⟨{ carrier := {l | ∀ s : S.toSubmodule, f s = 0 → (l : Module.Dual ℂ V) s = 0}
     add_mem' := fun {a b} ha hb s hs => by simp [ha s hs, hb s hs]
     zero_mem' := fun s _ => by simp
     smul_mem' := fun c a ha s hs => by simp [ha s hs] }, by
    intro h l hl s hs
    have h0 : f (S.toRepresentation h⁻¹ s) = 0 := by
      rw [f.isIntertwining, hs, map_zero]
    exact hl _ h0⟩

theorem mem_annih {ρ : Representation ℂ G V} {τ : Representation ℂ G W} {S : Subrepresentation ρ}
    {f : S.toRepresentation.IntertwiningMap τ} {l : smoothPart ρ.dual} :
    l ∈ (annih S f).toSubmodule ↔ ∀ s : S.toSubmodule, f s = 0 → (l : Module.Dual ℂ V) s = 0 :=
  Iff.rfl

def pull {ρ : Representation ℂ G V} (S : Subrepresentation ρ) (g : W →ₗ[ℂ] S.toSubmodule) :
    Module.Dual ℂ V →ₗ[ℂ] Module.Dual ℂ W :=
  (S.toSubmodule.subtype ∘ₗ g).dualMap

theorem pull_apply_map {ρ : Representation ℂ G V} {τ : Representation ℂ G W} {S : Subrepresentation ρ}
    {f : S.toRepresentation.IntertwiningMap τ} {g : W →ₗ[ℂ] S.toSubmodule}
    (hg : ∀ w, f (g w) = w) {l : smoothPart ρ.dual} (hl : l ∈ (annih S f).toSubmodule)
    (s : S.toSubmodule) : pull S g (l : Module.Dual ℂ V) (f s) = (l : Module.Dual ℂ V) s := by
  have h0 : f (g (f s) - s) = 0 := by
    have : f (g (f s) - s) = f (g (f s)) - f s := map_sub f.toLinearMap _ _
    rw [this, hg, sub_self]
  have h1 := mem_annih.1 hl _ h0
  have h2 : (l : Module.Dual ℂ V) ((g (f s) : V) - s) = 0 := h1
  rw [map_sub, sub_eq_zero] at h2
  exact h2

def restrLin {ρ : Representation ℂ G V} {τ : Representation ℂ G W} {S : Subrepresentation ρ}
    {f : S.toRepresentation.IntertwiningMap τ} (hf : Function.Surjective f)
    {g : W →ₗ[ℂ] S.toSubmodule} (hg : ∀ w, f (g w) = w) :
    (annih S f).toSubmodule →ₗ[ℂ] smoothPart τ.dual where
  toFun l := ⟨pull S g ((l : smoothPart ρ.dual) : Module.Dual ℂ V),
    mem_smoothPart_of_nhds (Filter.mem_of_superset
      ((isSmooth_contra ρ (l : smoothPart ρ.dual)).mem_nhds (by simp)) fun h hh => by
        have hh' : contra ρ h (l : smoothPart ρ.dual) = l := hh
        refine LinearMap.ext fun w => ?_
        obtain ⟨s, rfl⟩ := hf w
        show pull S g _ (τ h⁻¹ (f s)) = pull S g _ (f s)
        rw [← f.isIntertwining, pull_apply_map hg l.2, pull_apply_map hg l.2]
        have h1 := congrArg (fun x : smoothPart ρ.dual => (x : Module.Dual ℂ V) (s : V)) hh'
        simp only [contra_apply] at h1
        exact h1)⟩
  map_add' a b := Subtype.ext (by simp)
  map_smul' c a := Subtype.ext (by simp)

theorem restrLin_apply_map {ρ : Representation ℂ G V} {τ : Representation ℂ G W}
    {S : Subrepresentation ρ} {f : S.toRepresentation.IntertwiningMap τ}
    (hf : Function.Surjective f) {g : W →ₗ[ℂ] S.toSubmodule} (hg : ∀ w, f (g w) = w)
    (l : (annih S f).toSubmodule) (s : S.toSubmodule) :
    (restrLin hf hg l : Module.Dual ℂ W) (f s) = ((l : smoothPart ρ.dual) : Module.Dual ℂ V) s :=
  pull_apply_map hg l.2 s

theorem restrLin_comm {ρ : Representation ℂ G V} {τ : Representation ℂ G W}
    {S : Subrepresentation ρ} {f : S.toRepresentation.IntertwiningMap τ}
    (hf : Function.Surjective f) {g : W →ₗ[ℂ] S.toSubmodule} (hg : ∀ w, f (g w) = w)
    (h : G) (l : (annih S f).toSubmodule) (w : W) :
    (restrLin hf hg ((annih S f).toRepresentation h l) : Module.Dual ℂ W) w =
      (restrLin hf hg l : Module.Dual ℂ W) (τ h⁻¹ w) := by
  have e : ∀ s : S.toSubmodule,
      (restrLin hf hg ((annih S f).toRepresentation h l) : Module.Dual ℂ W) (f s) =
        (restrLin hf hg l : Module.Dual ℂ W) (τ h⁻¹ (f s)) := fun s => by
    rw [← f.isIntertwining, restrLin_apply_map, restrLin_apply_map]
    rfl
  have := e (g w)
  rwa [hg w] at this

def restr {ρ : Representation ℂ G V} {τ : Representation ℂ G W} {S : Subrepresentation ρ}
    {f : S.toRepresentation.IntertwiningMap τ} (hf : Function.Surjective f)
    {g : W →ₗ[ℂ] S.toSubmodule} (hg : ∀ w, f (g w) = w) :
    (annih S f).toRepresentation.IntertwiningMap (contra τ) where
  toLinearMap := restrLin hf hg
  isIntertwining' h :=
    LinearMap.ext fun l => Subtype.ext (LinearMap.ext fun w => restrLin_comm hf hg h l w)

theorem contra_isSubquotient : ∀ {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W],
    (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) →
    ∀ (ρ : Representation ℂ G V) (τ : Representation ℂ G W),
      IsSmooth ρ → IsSubquotient τ ρ → IsSubquotient (contra τ) (contra ρ) := by
  intro G V W _ _ _ _ _ _ _ hG ρ τ hρ ⟨S, f, hf⟩
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective f.toLinearMap
    (LinearMap.range_eq_top.2 hf)
  have hg' : ∀ w, f (g w) = w := fun w => LinearMap.congr_fun hg w
  refine ⟨annih S f, restr hf hg', fun m => ?_⟩
  obtain ⟨K, ho, hc, hKs⟩ := hG _ ((isSmooth_contra τ m).mem_nhds (by simp))
  have hfix : ∀ h ∈ K, ∀ s, (m : Module.Dual ℂ W) (f (S.toRepresentation h s)) =
      (m : Module.Dual ℂ W) (f s) := by
    intro h hh s
    have h1 : contra τ h⁻¹ m = m := hKs (inv_mem hh)
    have h2 := congrArg (fun x : smoothPart τ.dual => (x : Module.Dual ℂ W) (f s)) h1
    simp only [contra_apply, inv_inv] at h2
    rw [f.isIntertwining]
    exact h2
  obtain ⟨l, -, hl⟩ := exists_smooth_extension hρ S ho hc
    ((m : Module.Dual ℂ W) ∘ₗ f.toLinearMap) hfix
  have hmem : l ∈ (annih S f).toSubmodule := fun s hs => by
    have h1 := hl s
    have h2 : ((m : Module.Dual ℂ W) ∘ₗ f.toLinearMap) s = (m : Module.Dual ℂ W) (f s) := rfl
    rw [h1, h2, hs, map_zero]
  refine ⟨⟨l, hmem⟩, Subtype.ext (LinearMap.ext fun w => ?_)⟩
  obtain ⟨s, rfl⟩ := hf w
  show pull S g (l : Module.Dual ℂ V) (f s) = _
  rw [pull_apply_map hg' hmem]
  exact hl s

end GlobalTheory.CompanionTheory.ContraSq

end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.FiniteLengthQuot

theorem exists_isCoatom_subrepresentation :
    ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
      HasFiniteLength ρ → Nontrivial V → ∃ S : Subrepresentation ρ, IsCoatom S := by
  intro G V _ _ _ ρ hfl hnt
  have : WellFoundedGT (Subrepresentation ρ) := ((hasFiniteLength_iff_wellFounded ρ).1 hfl).1
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hmem : x ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [← h] at hmem
    exact hx ((Submodule.mem_bot ℂ).1 hmem)
  obtain ⟨M, hM, -⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subrepresentation ρ)).resolve_left hbt
  exact ⟨M, hM⟩

end GlobalTheory.CompanionTheory.FiniteLengthQuot
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.CompanionTheory.IsoSub

theorem nonempty_equiv_of_isotypic {A M T Q S : Type*} [Ring A] [AddCommGroup M] [Module A M]
    [AddCommGroup T] [Module A T] [AddCommGroup Q] [Module A Q] [AddCommGroup S] [Module A S]
    [IsSimpleModule A S] (h : isotypicComponent A M S = ⊤) (j : T →ₗ[A] M)
    (hj : Function.Injective j) (f : T →ₗ[A] Q) (hf : Function.Surjective f) :
    IsSimpleModule A Q → Nonempty (Q ≃ₗ[A] S) := by
  intro hQ
  have hiso : IsIsotypicOfType A M S := IsIsotypicOfType.of_isotypicComponent_eq_top h
  have hss : IsSemisimpleModule A M := by
    refine IsSemisimpleModule.of_sSup_simples_eq_top (top_le_iff.1 ?_)
    rw [← h]
    exact sSup_le_sSup fun m (hm : Nonempty (m ≃ₗ[A] S)) => IsSimpleModule.congr hm.some
  have hT : IsSemisimpleModule A T := IsSemisimpleModule.of_injective j hj
  obtain ⟨C, hC⟩ := exists_isCompl (LinearMap.ker f)
  let e₁ : C ≃ₗ[A] Q :=
    (Submodule.quotientEquivOfIsCompl _ _ hC).symm.trans (f.quotKerEquivOfSurjective hf)
  have hC' : IsSimpleModule A C := IsSimpleModule.congr e₁
  let e₂ : C ≃ₗ[A] C.map j := Submodule.equivMapOfInjective j hj C
  have hCj : IsSimpleModule A (C.map j) := IsSimpleModule.congr e₂.symm
  obtain ⟨e₃⟩ := hiso (C.map j)
  exact ⟨e₁.symm.trans (e₂.trans e₃)⟩

def inclusion {G Y : Type} [Group G] [AddCommGroup Y] [Module ℂ Y] {R : Representation ℂ G Y}
    (S : Subrepresentation R) : S.toRepresentation.IntertwiningMap R :=
  ⟨S.toSubmodule.subtype, fun _ => rfl⟩

theorem equiv_of_isSubquotient (G : Type) [Group G] (V Y W : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup Y] [Module ℂ Y] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (R : Representation ℂ G Y) (σ : Representation ℂ G W)
    (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible)
    (hR : ⨆ f : ρ.IntertwiningMap R, LinearMap.range f.toLinearMap = ⊤)
    (hsq : IsSubquotient σ R) : Nonempty (σ.Equiv ρ) := by
  have hρs : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).1 hρ
  have hσs : IsSimpleModule (MonoidAlgebra ℂ G) σ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).1 hσ
  have htop : Subrepresentation.asSubmodule (GlobalTheory.CuspFactor.spanRep R ρ) = ⊤ := by
    have hX : (GlobalTheory.CuspFactor.spanRep R ρ).toSubmodule = ⊤ := hR
    apply SetLike.coe_injective
    show ((GlobalTheory.CuspFactor.spanRep R ρ).toSubmodule : Set Y) = Set.univ
    rw [hX]
    first
      | rfl
      | exact Submodule.top_coe
      | simp
  have h : isotypicComponent (MonoidAlgebra ℂ G) R.asModule ρ.asModule = ⊤ := by
    rw [← GlobalTheory.CuspFactor.spanRep_asSubmodule R ρ hρ]
    exact htop
  obtain ⟨S, f, hf⟩ := hsq
  let j := Representation.IntertwiningMap.equivLinearMapAsModule _ _
    (GlobalTheory.CompanionTheory.IsoSub.inclusion S)
  have hj : Function.Injective j := by
    first
      | exact Subtype.val_injective
      | (intro x y hxy; exact Subtype.val_injective hxy)
  let f' := Representation.IntertwiningMap.equivLinearMapAsModule _ _ f
  have hf' : Function.Surjective f' := by
    first
      | exact hf
      | (intro y; obtain ⟨x, hx⟩ := hf y; exact ⟨x, hx⟩)
  exact (GlobalTheory.CuspFactor.nonempty_equiv_iff σ ρ).2
    (GlobalTheory.CompanionTheory.IsoSub.nonempty_equiv_of_isotypic h j hj f' hf' hσs)

end GlobalTheory.CompanionTheory.IsoSub
end
end

section

open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho

theorem _root_.GlobalTheory.T.casimir_eq_of_singular_weight_vector : ∀ {n : ℕ} (μ : Fin n → ℤ) (x : U n), IsAdW μ x → (∀ a : Fin n × Fin n, IsUpper a → e a * x ∈ Jp n) → x ∉ Jp n → casC (fun k => rhoVec n k + (μ k : ℂ)) = casC (rhoVec n) := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.casC_rho_add_eq | exact GlobalTheory.CompanionTheory.PresRho.casC_rho_add_eq | (intros; apply GlobalTheory.CompanionTheory.PresRho.casC_rho_add_eq <;> assumption)
end
