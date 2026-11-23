module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle463
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle106
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle143
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle164
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle214
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle165
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle155
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle464
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle355
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

theorem _root_.GlobalTheory.T.speh_langlands_quotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
      IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) →
    ∀ (δ x : IrrGL (k := k)) (Δ : Segment k) (m : ℕ), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsSpeh δ m x.rep →
      ∀ s : ℝ, IsL ↑(List.ofFn fun i : Fin m => Δ.nu ((s + ((m : ℝ) - 1) / 2 - (i : ℕ) : ℝ) : ℂ)) (x.nu (s : ℂ)).rep := by
  first | exact @GlobalTheory.LocGL.isL_speh_nu | exact GlobalTheory.LocGL.isL_speh_nu | (intros; apply GlobalTheory.LocGL.isL_speh_nu <;> assumption)
end

section

noncomputable section

open ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Published

namespace GlobalTheory.LocGL

theorem hasSupport_msupp_of_isL (hZ : ZelevinskyPolynomialRing) (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (𝔪 : Multiset (Segment k)) (x : IrrGL (k := k))
    (h : IsL 𝔪 x.rep) : HasSupport x.rep (msupp 𝔪) := by

  obtain ⟨_, Ψ, -, hΨ, -⟩ := hZ k

  obtain ⟨c, y, hd, ⟨Δ, ⟨hΔ, -⟩, hy⟩, hx⟩ := h

  have key : HasSupport x.rep (∑ a, (Δ a).ms) :=
    SupportRing.hasSupport_of_isSubquotient_prodIrr hΨ (fun a => (hy a).hasSupport) hx.1 hx.isSubquotient

  have e : msupp 𝔪 = ∑ a, (Δ a).ms := by
    rw [← hΔ, msupp, Multiset.bind, Multiset.map_map, Finset.sum_eq_multiset_sum]
    rfl
  rw [e]
  exact key

end GlobalTheory.LocGL
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.ResDual

noncomputable section

namespace GlobalTheory.LocalH2Injective


open GlobalTheory.TateTop in
theorem cob_of_gen {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [ContinuousMul Γ] [CompactSpace Γ] {χ : Γ →* ℤ_[l]ˣ} (hχ : Continuous fun g => (χ g : ℤ_[l]))
    (hG : ∀ r, ∃ c, GlobalTheory.TateTop.Gen χ (r + 1) c)
    {B' B : Type} [AddCommGroup B'] [Module ℤ_[l] B'] [Finite B'] [AddCommGroup B] [Module ℤ_[l] B]
    (f : B' →ₗ[ℤ_[l]] B) (hf : Function.Injective f)
    (htor : ∀ b : B, ∃ n : ℕ, (l : ℤ_[l]) ^ n • b = 0) (z : Γ × Γ → B') (c : Γ → B)
    (hc : IsLocallyConstant c) (hz : ∀ p, f (z p) = cob χ c p) :
    ∃ c' : Γ → B', IsLocallyConstant c' ∧ ∀ p, z p = cob χ c' p := by
  classical
  have hfinS : (Set.range c ∪ Set.range f).Finite := hc.range_finite.union (Set.finite_range f)
  obtain ⟨r, hfin, hkill⟩ := finite_span (l := l) htor hfinS
  set M := Submodule.span ℤ_[l] (Set.range c ∪ Set.range f) with hMdef
  have : Finite M := hfin
  have hM : ∀ m : M, (l : ℤ_[l]) ^ (r + 1) • m = 0 := fun m => by
    rw [pow_succ', mul_smul, hkill m, smul_zero]
  let fM : B' →ₗ[ℤ_[l]] M :=
    f.codRestrict M (fun b => Submodule.subset_span (Or.inr ⟨b, rfl⟩))
  have hfM : Function.Injective fM := fun a b hab => hf (congrArg Subtype.val hab)
  let cM : Γ → M := fun g => ⟨c g, Submodule.subset_span (Or.inl ⟨g, rfl⟩)⟩
  have hcM : IsLocallyConstant cM := IsLocallyConstant.desc cM Subtype.val hc Subtype.val_injective
  have hB' : ∀ b : B', (l : ℤ_[l]) ^ (r + 1) • b = 0 := by
    intro b
    apply hfM
    rw [map_smul, map_zero, hM]
  have hfz : (fun p => fM (z p)) = cob χ cM := by
    funext p
    apply Subtype.ext
    simp [fM, cM, cob, hz p]
  have hcoc := isCoc_cob hχ hM hcM
  have hzc : IsCoc χ z := by
    refine ⟨IsLocallyConstant.desc z fM (by rw [show ⇑fM ∘ z = fun p => fM (z p) from rfl, hfz]; exact hcoc.1) hfM, ?_⟩
    intro g h k
    apply hfM
    have e := hcoc.2 g h k
    rw [← hfz] at e
    simpa only [map_sub, map_add (f := _), map_smul, map_zero] using e
  obtain ⟨g0, hg0⟩ := hG r
  obtain ⟨x, b, hb, hzb⟩ := (hg0 B' hB').2.1 z hzc
  have hx : fM x = 0 := by
    refine (hg0 M hM).2.2 (fM x) (fun g => cM g - fM (b g))
      (hcM.comp₂ (hb.comp fM) (· - ·)) ?_
    intro p
    have h2 : fM (z p) = cob χ cM p := congrFun hfz p
    calc g0 p • fM x = fM (z p) - fM (cob χ b p) := by
          rw [hzb p, map_add (f := _), map_smul, add_sub_cancel_right]
      _ = cob χ cM p - cob χ (fun g => fM (b g)) p := by
          rw [h2]; simp only [cob, map_add (f := _), map_sub, map_smul]
      _ = cob χ (fun g => cM g - fM (b g)) p := by
          simp only [cob, smul_sub]; abel
  have hx0 : x = 0 := hfM (by rw [hx, map_zero])
  exact ⟨b, hb, fun p => by rw [hzb p, hx0, smul_zero, zero_add]⟩

theorem h2_inj : LocalTateDuality → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] (B' B : Type) [AddCommGroup B'] [Module O B'] [Finite B'] [AddCommGroup B] [Module O B] (f : B' →ₗ[O] B), Function.Injective f → (∀ b : B, ∃ n : ℕ, l ^ n • b = 0) → ∀ (z : Dec (F := F) A → Dec (F := F) A → B') (c : Dec (F := F) A → B), IsLocallyConstant c → (∀ g h, f (z g h) = algebraMap ℤ_[l] O ((cycZ F Ω l g.1 : ℤ_[l]ˣ) : ℤ_[l]) • c h - c (g * h) + c g) → ∃ c' : Dec (F := F) A → B', IsLocallyConstant c' ∧ ∀ g h, z g h = algebraMap ℤ_[l] O ((cycZ F Ω l g.1 : ℤ_[l]ˣ) : ℤ_[l]) • c' h - c' (g * h) + c' g := by
  intro hT F Ω _ _ _ _ _ l _ A v hA O _ _ B' B _ _ _ _ _ f hf htor z c hc hzc
  have : CompactSpace (Dec (F := F) A) :=
    isCompact_iff_compactSpace.mp (isClosed_Dec (F := F) A).isCompact
  let : Module ℤ_[l] B' := Module.compHom B' (algebraMap ℤ_[l] O)
  let : Module ℤ_[l] B := Module.compHom B (algebraMap ℤ_[l] O)
  let fZ : B' →ₗ[ℤ_[l]] B :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun a x => f.map_smul (algebraMap ℤ_[l] O a) x }
  let χ : Dec (F := F) A →* ℤ_[l]ˣ := (cycZ F Ω l).comp (Dec (F := F) A).subtype
  have hχ : Continuous fun g => (χ g : ℤ_[l]) :=
    Units.continuous_val.comp ((continuous_cycZ F Ω l).comp continuous_subtype_val)
  have htorZ : ∀ b : B, ∃ n : ℕ, (l : ℤ_[l]) ^ n • b = 0 := by
    intro b
    obtain ⟨n, hn⟩ := htor b
    refine ⟨n, ?_⟩
    show algebraMap ℤ_[l] O ((l : ℤ_[l]) ^ n) • b = 0
    rw [map_pow, map_natCast, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hn]
  have hG : ∀ r, ∃ c, GlobalTheory.TateTop.Gen χ (r + 1) c := by
    intro r
    have : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    let : TopologicalSpace (ZMod (l ^ (r + 1))) := ⊥
    have : DiscreteTopology (ZMod (l ^ (r + 1))) := ⟨rfl⟩
    refine GlobalTheory.TateTop.exists_gen hχ
      ((hT F Ω l (r + 1) (ZMod (l ^ (r + 1))) A
        (Representation.trivial (ZMod (l ^ (r + 1))) (Dec (F := F) A) (ZMod (l ^ (r + 1)))) v
        (Nat.succ_pos r) hA ?_).1) ?_
    · have htr : (fun p : Dec (F := F) A × ZMod (l ^ (r + 1)) =>
          Representation.trivial (ZMod (l ^ (r + 1))) (Dec (F := F) A) (ZMod (l ^ (r + 1)))
            p.1 p.2) = Prod.snd := by
        funext p
        simp
      show Continuous _
      rw [htr]
      exact continuous_snd
    · intro M _ _ _ _ _ rho hrho
      exact (hT F Ω l (r + 1) M A rho v (Nat.succ_pos r) hA hrho).2.2.2.2
  obtain ⟨c', hc', hzc'⟩ := cob_of_gen hχ hG fZ hf htorZ (fun p => z p.1 p.2) c hc
    (fun p => hzc p.1 p.2)
  exact ⟨c', hc', fun g h => hzc' (g, h)⟩

end GlobalTheory.LocalH2Injective
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.GenSpan

open GlobalTheory.TateTop ReciprocityTheory.Gal

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]

theorem gen_zmod {χ : G →* ℤ_[l]ˣ} {r : ℕ} {c : G × G → ℤ_[l]} (h : Gen χ r c) :
    (IsLocallyConstant (fun p => PadicInt.toZModPow r (c p)) ∧
      ∀ g k m, PadicInt.toZModPow r (χ g : ℤ_[l]) * PadicInt.toZModPow r (c (k, m))
        - PadicInt.toZModPow r (c (g * k, m)) + PadicInt.toZModPow r (c (g, k * m))
        - PadicInt.toZModPow r (c (g, k)) = 0) ∧
    (∀ z : G × G → ZMod (l ^ r), IsLocallyConstant z →
      (∀ g k m, PadicInt.toZModPow r (χ g : ℤ_[l]) * z (k, m) - z (g * k, m) + z (g, k * m)
        - z (g, k) = 0) →
      ∃ (x : ZMod (l ^ r)) (b : G → ZMod (l ^ r)), IsLocallyConstant b ∧ ∀ p,
        z p = PadicInt.toZModPow r (c p) * x +
          (PadicInt.toZModPow r (χ p.1 : ℤ_[l]) * b p.2 - b (p.1 * p.2) + b p.1)) ∧
    (∀ (x : ZMod (l ^ r)) (b : G → ZMod (l ^ r)), IsLocallyConstant b →
      (∀ p, PadicInt.toZModPow r (c p) * x =
          PadicInt.toZModPow r (χ p.1 : ℤ_[l]) * b p.2 - b (p.1 * p.2) + b p.1) → x = 0) := by
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let : Module ℤ_[l] (ZMod (l ^ r)) := Module.compHom _ (PadicInt.toZModPow r)
  have hs : ∀ (a : ℤ_[l]) (m : ZMod (l ^ r)), a • m = PadicInt.toZModPow r a * m := fun _ _ => rfl
  have h0 : PadicInt.toZModPow r ((l : ℤ_[l]) ^ r) = 0 := (dvd_iff_toZModPow _).1 dvd_rfl
  have hM : ∀ m : ZMod (l ^ r), (l : ℤ_[l]) ^ r • m = 0 := fun m => by rw [hs, h0, zero_mul]
  obtain ⟨h1, h2, h3⟩ := h _ hM
  refine ⟨?_, fun z hz hz' => ?_, fun x b hb hx => h3 x b hb fun p => ?_⟩
  · obtain ⟨a1, a2⟩ := h1 1
    simp only [hs, mul_one] at a1 a2
    exact ⟨a1, a2⟩
  · obtain ⟨x, b, hb, e⟩ := h2 z ⟨hz, fun g k m => by simpa only [hs] using hz' g k m⟩
    exact ⟨x, b, hb, fun p => by simpa only [GlobalTheory.TateTop.cob, hs] using e p⟩
  · simpa only [GlobalTheory.TateTop.cob, hs] using hx p


open GlobalTheory.PadicH2Separated in
theorem span : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (χ : G →* ℤ_[l]ˣ) (c : G × G → ℤ_[l]), Continuous (fun g => (χ g : ℤ_[l])) → (∀ r, GlobalTheory.TateTop.Gen χ r c) → (∀ r : ℕ, 0 < r → Finite (ReciprocityTheory.Gal.H1 (ReciprocityTheory.Gal.charRep ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ)))) → (Continuous (fun p => (c p : ℚ_[l])) ∧ ∀ g h k, ((χ g : ℤ_[l]) : ℚ_[l]) * (c (h, k) : ℚ_[l]) - (c (g * h, k) : ℚ_[l]) + (c (g, h * k) : ℚ_[l]) - (c (g, h) : ℚ_[l]) = 0) ∧ ∀ z : G × G → ℚ_[l], Continuous z → (∀ g h k, ((χ g : ℤ_[l]) : ℚ_[l]) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → ∃ (x : ℚ_[l]) (f : G → ℚ_[l]), Continuous f ∧ ∀ g h, ((χ g : ℤ_[l]) : ℚ_[l]) * f h - f (g * h) + f g = z (g, h) - x * (c (g, h) : ℚ_[l]) := by
  intro l _ G _ _ _ _ χ c hχ hgen hfin
  have hl : l.Prime := Fact.out
  have hG := fun r => gen_zmod (hgen r)
  have hcc : Continuous c := GlobalTheory.PadicH2Separated.continuous_of_reductions c fun s =>
    (hG (s + 1)).1.1.continuous
  have hcoc : ∀ g h k, (χ g : ℤ_[l]) * c (h, k) - c (g * h, k) + c (g, h * k) - c (g, h) = 0 := by
    intro g h k
    rw [← PadicInt.ext_of_toZModPow]
    intro n
    simpa only [map_sub, map_add (f := _), map_mul, map_zero] using (hG n).1.2 g h k
  refine ⟨⟨continuous_subtype_val.comp hcc, fun g h k => ?_⟩, fun z hz hzc => ?_⟩
  · have e := congrArg (fun a : ℤ_[l] => (a : ℚ_[l])) (hcoc g h k)
    push_cast at e
    exact e
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hz.continuousOn
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt C (by exact_mod_cast hl.one_lt : (1 : ℝ) < l)
  have hnorm : ∀ p, ‖(l : ℚ_[l]) ^ m * z p‖ ≤ 1 := fun p => by
    rw [norm_mul, Padic.norm_p_pow, zpow_neg, zpow_natCast]
    have hp : (0 : ℝ) < (l : ℝ) ^ m := by have := hl.pos; positivity
    rw [inv_mul_le_iff₀ hp, mul_one]
    exact (hC p trivial).trans hm.le
  let w : G × G → ℤ_[l] := fun p => ⟨(l : ℚ_[l]) ^ m * z p, hnorm p⟩
  have hw : ∀ p, (w p : ℚ_[l]) = (l : ℚ_[l]) ^ m * z p := fun _ => rfl
  have hwc : Continuous w := (continuous_const.mul hz).subtype_mk _
  have hwcoc : ∀ g h k, (χ g : ℤ_[l]) * w (h, k) - w (g * h, k) + w (g, h * k) - w (g, h) = 0 := by
    intro g h k
    have e : (((χ g : ℤ_[l]) * w (h, k) - w (g * h, k) + w (g, h * k) - w (g, h) : ℤ_[l]) :
        ℚ_[l]) = 0 := by
      push_cast [hw]
      linear_combination (l : ℚ_[l]) ^ m * hzc g h k
    exact PadicInt.coe_eq_zero.1 e
  have hlev : ∀ r, ∃ (x : ZMod (l ^ r)) (b : G → ZMod (l ^ r)), IsLocallyConstant b ∧ ∀ p,
      PadicInt.toZModPow r (w p) = PadicInt.toZModPow r (c p) * x +
        (PadicInt.toZModPow r (χ p.1 : ℤ_[l]) * b p.2 - b (p.1 * p.2) + b p.1) := fun r =>
    (hG r).2.1 _ ((IsLocallyConstant.iff_continuous _).2
      ((GlobalTheory.PadicH2Separated.continuous_reduction r).comp hwc))
      fun g k m => by
        simpa only [map_sub, map_add (f := _), map_mul, map_zero] using
          congrArg (PadicInt.toZModPow r) (hwcoc g k m)
  choose X B hB hXB using hlev
  have hred : ∀ r, PadicInt.toZModPow r (((X r).val : ℕ) : ℤ_[l]) = X r := fun r => by
    have : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.ne_zero⟩
    rw [map_natCast, ZMod.natCast_zmod_val]
  have hcomp : ∀ r, ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)) (X (r + 1)) = X r := by
    intro r
    set ψ := ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))
    have hψ : ∀ a : ℤ_[l], ψ (PadicInt.toZModPow (r + 1) a) = PadicInt.toZModPow r a := fun a => by
      rw [ZMod.castHom_apply]
      exact PadicInt.cast_toZModPow r (r + 1) (Nat.le_succ r) a
    rw [← sub_eq_zero]
    refine (hG r).2.2 _ (fun g => B r g - ψ (B (r + 1) g)) ((hB r).sub ((hB (r + 1)).comp ψ))
      fun p => ?_
    have e1 : PadicInt.toZModPow r (w p) = PadicInt.toZModPow r (c p) * ψ (X (r + 1)) +
        (PadicInt.toZModPow r (χ p.1 : ℤ_[l]) * ψ (B (r + 1) p.2) - ψ (B (r + 1) (p.1 * p.2)) +
          ψ (B (r + 1) p.1)) := by
      have := congrArg ψ (hXB (r + 1) p)
      simpa only [map_add (f := _), map_sub, map_mul, hψ] using this
    have e2 := hXB r p
    show PadicInt.toZModPow r (c p) * (ψ (X (r + 1)) - X r) =
      PadicInt.toZModPow r (χ p.1 : ℤ_[l]) * (B r p.2 - ψ (B (r + 1) p.2)) -
        (B r (p.1 * p.2) - ψ (B (r + 1) (p.1 * p.2))) + (B r p.1 - ψ (B (r + 1) p.1))
    linear_combination e2 - e1
  obtain ⟨x, hx⟩ := exists_lim (fun r => (((X r).val : ℕ) : ℤ_[l])) fun r => by
    rw [dvd_iff_toZModPow, map_sub, hred, ← PadicInt.cast_toZModPow r (r + 1) (Nat.le_succ r),
      hred]
    exact sub_eq_zero.2 (hcomp r)
  have hxr : ∀ r, PadicInt.toZModPow r x = X r := fun r => by
    have := (dvd_iff_toZModPow _).1 (hx r)
    rwa [map_sub, hred, sub_eq_zero] at this
  have hcont : ContAction (charRep χ) := by
    show Continuous fun p : G × ℤ_[l] => charRep χ p.1 p.2
    simp only [charRep_apply]
    exact (hχ.comp continuous_fst).mul continuous_snd
  have hcompat : ∀ (r : ℕ) (g : G) (a : ℤ_[l]), PadicInt.toZModPow r (charRep χ g a) =
      charRep ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ) g
        (PadicInt.toZModPow r a) := fun r g a => by
    simp [charRep_apply]
  have hyZ : (fun p => w p - x * c p) ∈ Z2 (charRep χ) := by
    refine (mem_cocycles2 _ _).2 ⟨hwc.sub (continuous_const.mul hcc), fun g h k => ?_⟩
    simp only [charRep_apply]
    linear_combination hwcoc g h k - x * hcoc g h k
  have hyB : ∀ r, (fun p => PadicInt.toZModPow r (w p - x * c p)) ∈
      B2 (charRep ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ)) := by
    intro r
    refine (separated_dvr_second_cohomology_mem _ _).2 ⟨B r, (hB r).continuous, funext fun p => ?_⟩
    obtain ⟨g, h⟩ := p
    simp only [d1_apply, charRep_apply, MonoidHom.comp_apply, Units.coe_map, map_sub, map_mul, hxr]
    have e := hXB r (g, h)
    simp only at e
    simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    linear_combination -e
  have hker : ∀ r : ℕ, ∃ w' ∈ Z2 (charRep χ), (fun p => w p - x * c p) - (l : ℤ_[l]) ^ r • w' ∈
      B2 (charRep χ) := fun r =>
    GlobalTheory.padicInt_two_cocycle_eq_pow_smul_of_reduction_coboundary l G (charRep χ) hcont r _
      (hcompat r) _ hyZ (hyB r)
  obtain ⟨f, hf, hfd⟩ := (separated_dvr_second_cohomology_mem _ _).1
    (GlobalTheory.PadicH2Separated.mem_coboundaries_of_forall_pow l G (charRep χ) _ hcompat hfin _ hyZ hker)
  have hl0 : (l : ℚ_[l]) ^ m ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.ne_zero)
  refine ⟨(x : ℚ_[l]) / (l : ℚ_[l]) ^ m, fun g => (f g : ℚ_[l]) / (l : ℚ_[l]) ^ m,
    (continuous_subtype_val.comp hf).div_const _, fun g h => ?_⟩
  have e := congrFun hfd (g, h)
  simp only [d1_apply, charRep_apply] at e
  have e' := congrArg (fun a : ℤ_[l] => (a : ℚ_[l])) e
  push_cast [hw] at e'
  field_simp
  linear_combination e'

end GlobalTheory.GenSpan
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.TwistLift GlobalTheory.TateTop

namespace GlobalTheory.TateTop

theorem exists_fundamental_cocycle_loc (hT : Formalism.GaloisCohomology.LocalTateDualityK) :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), CompactSpace ↥(GK K) ∧
      ∃ (χ : ↥(GK K) →* ℤ_[l]ˣ) (c : ↥(GK K) × ↥(GK K) → ℤ_[l]),
        Continuous (fun g => (χ g : ℤ_[l])) ∧
        (∀ g, ((χ g : ℤ_[l]) : ℚ_[l]) = (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l])) ∧
        (∀ r, GlobalTheory.TateTop.Gen χ r c) ∧
        ∀ r : ℕ, 0 < r → Finite (ReciprocityTheory.Gal.H1 (ReciprocityTheory.Gal.charRep
          ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ))) := by
  intro l _ P K
  obtain ⟨hΦ1, hΦ2⟩ := continuous_fixingSubgroupEquiv K.1
  set Φ := K.1.fixingSubgroupEquiv with hΦ
  have hcyc : IsCyc P.χQ := P.χQ_cyc
  let χZ : Formalism.GaloisCohomology.GK l K.1 →* ℤ_[l]ˣ := (cyclotomicCharacter (PadicAlgCl l) l).comp
      (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK l K.1) (PadicAlgCl l))
  have hχZ : ∀ g, ((χZ g : ℤ_[l]) : ℚ_[l]) = (P.χQ (Φ.symm g : GQ l) : ℚ_[l]) := fun g => by
    rw [isCyc_unique hcyc (isCyc_cycChar l)]; rfl
  have hχc : Continuous fun g => (χZ g : ℤ_[l]) := by
    rw [continuous_iff_coe]
    simp only [hχZ]
    exact hcyc.continuous.comp (continuous_subtype_val.comp hΦ1)
  obtain ⟨c, hc⟩ := exists_gen_all hχc fun r => by
    have : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    exact exists_gen hχc
      (hT l K.1 K.2 (r + 1) (ZMod (l ^ (r + 1))) (ReciprocityTheory.Gal.charRep (redChar χZ (r + 1)))
        (Nat.succ_pos _) (contAction_charRep _ ((continuous_toZModPow _).comp hχc))).1
      fun M _ _ _ _ _ rho hrho => (hT l K.1 K.2 (r + 1) M rho (Nat.succ_pos _) hrho).2.2.2.2
  refine ⟨Φ.symm.surjective.compactSpace hΦ1, χZ.comp Φ.toMonoidHom, _, hχc.comp hΦ2,
    fun g => ?_, fun r => (hc r).transport Φ hΦ2 hΦ1, fun r hr => ?_⟩
  · have h1 := hχZ (Φ g)
    rw [show Φ.symm (Φ g) = g from Φ.symm_apply_apply g, ← P.PD_χ K g] at h1
    exact h1
  · have : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    have hfin := (GlobalTheory.T.finite_H1_H2_local hT l K.1 K.2 r (ZMod (l ^ r))
      (ReciprocityTheory.Gal.charRep (redChar χZ r)) hr
      (contAction_charRep _ ((continuous_toZModPow _).comp hχc))).1
    obtain ⟨e⟩ := (GlobalTheory.contCohomology_transport_mulEquiv (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK l K.1)
      ↥(GK K) (ZMod (l ^ r)) Φ hΦ2 hΦ1 (ReciprocityTheory.Gal.charRep (redChar χZ r))
      (ReciprocityTheory.Gal.charRep ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp
        (χZ.comp Φ.toMonoidHom))) (fun g m => rfl)).1
    exact Finite.of_equiv _ e

end GlobalTheory.TateTop
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

namespace GlobalTheory.TateNat

theorem free_inj : ∀ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] {G : Type} [Group G] [TopologicalSpace G] (χ : G →* ℤ_[p]ˣ) (c : G × G → ℤ_[p]), (∀ r, GlobalTheory.TateTop.Gen χ r c) → ∀ (φ : ℤ_[p] →+* O) (ε : G →* Oˣ), (∀ g, ((ε g : Oˣ) : O) = φ (χ g : ℤ_[p])) → ∀ (ϖ : O), Irreducible ϖ → (p : O) ∈ IsLocalRing.maximalIdeal O → (∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O)) → ∀ (a : O) (f : G → O), Continuous f → (∀ g h : G, d1 (twist ε O) f (g, h) = a * φ (c (g, h))) → a = 0 := by
  intro p _ O _ _ _ _ _ _ G _ _ χ c hgen φ ε hεφ ϖ hϖ hp hopen a f hf hd
  have key : ∀ n : ℕ, a ∈ (powSub (M := O) ϖ n : Submodule O O) := by
    intro n
    set N : Submodule O O := powSub (M := O) ϖ n with hN
    letI : Module ℤ_[p] (O ⧸ N) := Module.compHom (O ⧸ N) φ
    have hs : ∀ (t : ℤ_[p]) (x : O), t • (Submodule.Quotient.mk x : O ⧸ N) =
        Submodule.Quotient.mk (φ t * x) := fun t x => by
      show (φ t) • (Submodule.Quotient.mk x : O ⧸ N) = _
      rw [← Submodule.Quotient.mk_smul, smul_eq_mul]
    haveI : Finite (O ⧸ N) := AddSubgroup.quotient_finite_of_isOpen N.toAddSubgroup (hopen n)
    have hM : ∀ m : O ⧸ N, (p : ℤ_[p]) ^ n • m = 0 := by
      intro m
      induction m using Submodule.Quotient.induction_on with
      | H x =>
        rw [hs, Submodule.Quotient.mk_eq_zero, map_pow, map_natCast]
        rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hp
        obtain ⟨u, hu⟩ := hp
        refine mem_powSub.2 ⟨u ^ n * x, ?_⟩
        rw [hu, smul_eq_mul, mul_pow]
        ring
    have hlc : IsLocallyConstant (fun g => (Submodule.Quotient.mk (f g) : O ⧸ N)) := by
      intro s
      have ho : IsOpen ((Submodule.Quotient.mk : O → O ⧸ N) ⁻¹' s) := by
        rw [isOpen_iff_forall_mem_open]
        intro x hx
        refine ⟨(fun y => y - x) ⁻¹' (N : Set O), fun y hy => ?_,
          (hopen n).preimage (continuous_id.sub continuous_const), ?_⟩
        · have e : (Submodule.Quotient.mk y : O ⧸ N) = Submodule.Quotient.mk x :=
            (Submodule.Quotient.eq N).2 hy
          show (Submodule.Quotient.mk y : O ⧸ N) ∈ s
          rw [e]
          exact hx
        · show x - x ∈ N
          rw [sub_self]
          exact N.zero_mem
      exact ho.preimage hf
    have h3 := ((hgen n) (O ⧸ N) hM).2.2 (Submodule.Quotient.mk a)
      (fun g => Submodule.Quotient.mk (f g)) hlc fun q => by
        obtain ⟨g, h⟩ := q
        have e := hd g h
        simp only [d1_apply] at e
        change (ε g : O) • f h - f (g * h) + f g = a * φ (c (g, h)) at e
        rw [smul_eq_mul, hεφ] at e
        simp only [GlobalTheory.TateTop.cob, hs]
        rw [← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add]
        congr 1
        linear_combination -e
    exact (Submodule.Quotient.mk_eq_zero N).1 h3
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal O)
    (IsLocalRing.maximalIdeal.isMaximal O).ne_top
  have hmem : a ∈ ⨅ i, (IsLocalRing.maximalIdeal O) ^ i := by
    refine Submodule.mem_iInf _ |>.2 fun i => ?_
    obtain ⟨y, hy⟩ := mem_powSub.1 (key i)
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← hy, smul_eq_mul]
    exact dvd_mul_right _ _
  rw [hbot] at hmem
  exact (Submodule.mem_bot O).1 hmem

end GlobalTheory.TateNat
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

theorem _root_.GlobalTheory.T.jumps_dictionary_at_embedding_over_realPlace : ∀ D : D7, WeightParam D → BlockCharParam D → GlobalTheory.JumpDictionaryFoundation.AlgebraicCharacter_at D → GlobalTheory.TwSys.Cheb → ∀ (i : D.nd.Loc) (τ : D.host.E →+* Qbar (D.nd.l i)) (ρ : D.what₂.Tau) (b : Bool), (D.naut.iotaQC i).toRingHom.comp τ = embOver D ρ b → ∃ cτ : ℤ, (D.naut.locAutHodgeTateWeightsLevelZero i τ).map (fun n : ℤ => (n : ℚ)) = (PP D i ρ).map (fun p => sgnOf true b * p + cτ) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (chiGL D i 1)) w ∧ (D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (chiGL D i 1)) τ).map (fun n : ℤ => (n : ℚ)) = {sgnOf true b * (-(D.hc ρ).e (liftIdx D i)) - ((D.R.t : ℚ) - 1) / 2 + cτ} := by
  first | exact @GlobalTheory.JumpDictRec.main | exact GlobalTheory.JumpDictRec.main | (intros; apply GlobalTheory.JumpDictRec.main <;> assumption)
end
