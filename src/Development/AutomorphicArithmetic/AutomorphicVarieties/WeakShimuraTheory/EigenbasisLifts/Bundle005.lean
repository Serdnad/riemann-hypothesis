module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle028
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ArithmeticPointClassicality
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle031
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.Bundle004
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

@[expose] public section

local instance (priority := 2000) fieldIsTorsionFreeForEigenbasisLiftsBundle005
    (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] : Module.IsTorsionFree F Ω :=
  DivisionSemiring.to_moduleIsTorsionFree

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.Eb.psiInj :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 L)), IsPlaceOver A w → ((l : ℕ) : 𝓞 L) ∈ w.asIdeal →
        ∀ {n : ℕ} (κ : Fin n → Dec (F := L) A →* (PadicAlgCl l)ˣ) (m : Fin n → ℤ) (k : ℕ), Function.Injective m → 0 < k → (∀ i (g : Dec (F := L) A), (g : G L Ω) ∈ Ine (F := L) A → (κ i g * cycBar L Ω l g ^ (-m i)) ^ k = 1) → Function.Injective κ := by
  intro l _ L Ω _ _ _ _ _ A w hA hw n κ m k hm hk h i i' e
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  obtain ⟨j, rfl⟩ := (Loc.decEmb (F := L) (Ω := Ω) (v := l)).1 A w hA hw
  obtain ⟨-, φ, b1, -, -, b4, b5, -⟩ := (Loc.decEmb (F := L) (Ω := Ω) (v := l)).2 j
  obtain ⟨-, _, ⟨⟨g, rfl⟩, hg⟩, h2⟩ := (Loc.cycInertia l).2 φ.range b1.isOpen_range
  rw [b5] at h2
  have h3 : ¬ IsOfFinOrder (cycBar L Ω l (g : G L Ω)) := fun hf => by
    obtain ⟨N, hN, h1⟩ := isOfFinOrder_iff_pow_eq_one.1 hf
    refine h2 (isOfFinOrder_iff_pow_eq_one.2 ⟨N, hN, Units.ext (Subtype.ext
      ((algebraMap ℚ_[l] (PadicAlgCl l)).injective ?_))⟩)
    have h4 := congrArg Units.val h1
    simp [cycBar] at h4 ⊢
    exact h4
  have a1 := h i g ((b4 g).1 hg)
  have a2 := h i' g ((b4 g).1 hg)
  rw [← e] at a2
  have a3 := a1.trans a2.symm
  rw [mul_pow, mul_pow, mul_right_inj, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul] at a3
  have a4 := (injective_zpow_iff_not_isOfFinOrder.2 h3) a3
  have a5 : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
  exact hm (neg_injective (mul_right_cancel₀ a5 a4))
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

open scoped Pointwise in
private theorem bkAb_emb {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] (A : HeightOneSpectrum (𝓞 F) → ValuationSubring Ω) (hA : ∀ w, IsPlaceOver (A w) w)
    (τ : F →+* Formalism.BasicNotions.Loc.Om l) :
    ∃ (j : Ω →+* Formalism.BasicNotions.Loc.Om l) (w : HeightOneSpectrum (𝓞 F)), j.comp (algebraMap F Ω) = τ ∧
      ((l : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ Loc.placeJ j = A w := by
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  obtain ⟨j₀, hj₀⟩ : ∃ j : Ω →+* Formalism.BasicNotions.Loc.Om l, j.comp (algebraMap F Ω) = τ := by
    letI : Algebra F (Formalism.BasicNotions.Loc.Om l) := τ.toAlgebra
    exact ⟨(IsAlgClosed.lift (R := F) (S := Ω) (M := Formalism.BasicNotions.Loc.Om l)).toRingHom,
      (IsAlgClosed.lift (R := F) (S := Ω) (M := Formalism.BasicNotions.Loc.Om l)).comp_algebraMap⟩
  obtain ⟨w, hw, hl⟩ := ((Loc.decEmb (F := F) (Ω := Ω) (v := l)).2 j₀).1
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := F) (hA w) hw
  refine ⟨j₀.comp (g : Ω →+* Ω), w, hj₀ ▸ RingHom.ext fun x => congrArg j₀ (g.commutes x), hl, ?_⟩
  ext x
  change g • x ∈ Loc.placeJ j₀ ↔ _
  rw [← hg]
  exact ValuationSubring.smul_mem_pointwise_smul_iff

theorem UpperTheory.V.Ws.Eb.bkAb :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) {n : ℕ} (R : Representation (PadicAlgCl l) V.frame.Γ (Matrix (Fin n) (Fin n) (PadicAlgCl l))), ∀ z ∈ Z1 R,
        (∀ (v : V.frame.Vl) (φ : V.frame.Gv v →* Formalism.BasicNotions.Loc.GQ l), Topology.IsOpenEmbedding φ → (∀ g, φ g ∈ Loc.Iq l ↔ g ∈ V.frame.Iv v) → (∀ g, Loc.cycA l l (PadicAlgCl l) (φ g) = cycBar L Ω l (Subtype.val g)) →
          (fun g : V.frame.Gv v => z (V.frame.φ v g)) ∈ Loc.finiteCocycles φ (R.comp (V.frame.η.ker.subtype.comp (V.frame.φ v)) : Representation (PadicAlgCl l) (V.frame.Gv v) (Matrix (Fin n) (Fin n) (PadicAlgCl l)))) →
        (∀ w : HeightOneSpectrum (𝓞 (W.Lp L)), ((l : ℕ) : 𝓞 (W.Lp L)) ∉ w.asIdeal → ∃ X, ∀ g ∈ Ine (F := W.Lp L) (s.A w), z (toGS Ω V.S' g) = R (toGS Ω V.S' g) X - X) →
        Af.IsBK l (R.comp (toGS Ω V.S') : Representation (PadicAlgCl l) (G (W.Lp L) Ω) (Matrix (Fin n) (Fin n) (PadicAlgCl l))) (fun g => z (toGS Ω V.S' g)) := by
  intro l _ L Ω _ _ _ _ _ _ s V n R z hz h1 h2
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  refine ⟨fun w hw => ⟨s.A w, s.hA w, h2 w hw⟩, fun τ => ?_⟩
  obtain ⟨j, w, hj, hl, hA⟩ := bkAb_emb s.A s.hA τ
  refine ⟨j, hj, ?_⟩
  have key : ∃ φ : ↥(Dec (F := L) (s.A w)) →* Formalism.BasicNotions.Loc.GQ l, Topology.IsOpenEmbedding φ ∧
      (∀ g y, φ g (j y) = j ((g : G L Ω) y)) ∧ (∀ g, φ g ∈ Loc.Iq l ↔ (g : G L Ω) ∈ Ine (F := L) (s.A w)) ∧
      (∀ g, Loc.cyc l l (φ g) = cycZ L Ω l (g : G L Ω)) := by
    rw [← hA]
    obtain ⟨φ, a, b, -, c, d, -⟩ := ((Loc.decEmb (F := L) (Ω := Ω) (v := l)).2 j).2
    exact ⟨φ, a, b, c, d l⟩
  obtain ⟨φ, a, b, c, d⟩ := key
  have h3 := h1 ⟨w, hl⟩ φ a c fun g => congrArg (Units.map _) (d g)
  exact (Loc.bkAbove (F := W.Lp L) j φ ((W.resP L Ω).comp (Dec (F := L) (s.A w)).subtype) a b
    (R.comp (toGS Ω V.S')) (fun g => z (toGS Ω V.S' g))
    ⟨hz.1.comp (continuous_toGS Ω _), fun g h => (congrArg z (map_mul _ g h)).trans (hz.2 _ _)⟩).1 h3
end

section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.Eb.cocycle_vanishes_on_inertia_of_point_pseudodeformation :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L]
      [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev)
      {c : Coef l} {n : ℕ} {r : W.Resid (W.HidaSetting.Lev.frame V) c.O n}
      (B : W.UniversalOrdinaryDeterminantRing r) (x : B.Pt)
      (ρ : (W.HidaSetting.Lev.frame V).G₀ →* GL (Fin n) (PadicAlgCl l)),
      r.V0ok → B.u.D.map (x : B.B →+* PadicAlgCl l) = W.GDet.ofRep (W.mat ρ) →
      Continuous ρ → ∀ y ∈ Z1 (Loc.adGL ρ), ∀ g ∈ (W.HidaSetting.Lev.frame V).I0, y g = 0 := by
  intro l _ L Ω _ _ _ _ _ _ s V c n r B x ρ hok hB hρ y hy g hg
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact Subsingleton.elim _ _
  haveI : Fact s.p.Prime := ⟨s.p_prime⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  obtain ⟨hI0, hD0, g0, hg0D, hg0e⟩ := hok
  have hpv : ((s.p : ℕ) : 𝓞 (W.Lp L)) ∈ s.v0.asIdeal := by
    have h := Ideal.absNorm_mem s.v0.asIdeal
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← normV, s.norm_v0_eq_one] at h
  have hpw : ((s.p : ℕ) : 𝓞 L) ∈ (s.w s.v0).asIdeal := by
    rw [← s.hw s.v0]
    have h := (s.hA s.v0 _).mpr hpv
    simpa using h
  obtain ⟨j, hj⟩ := (Loc.decEmb (F := L) (Ω := Ω) (v := s.p)).1 (s.A s.v0) (s.w s.v0) (s.hw s.v0) hpw
  obtain ⟨-, φ, hφo, -, -, hφI, hφc, -⟩ := (Loc.decEmb (F := L) (Ω := Ω) (v := s.p)).2 j
  change g ∈ Subgroup.map V.pr (Ine (s.A s.v0)) at hg
  change ∀ i, Subgroup.map V.pr (Ine (s.A s.v0)) ≤ (r.chib i).ker at hI0
  change ∀ g ∈ Subgroup.map V.pr (Dec (s.A s.v0)), ∀ i j, (r.chib i) g = (r.chib j) g at hD0
  change g0 ∈ Subgroup.map V.pr (Dec (s.A s.v0)) at hg0D
  rw [← hj] at hg hI0 hD0 hg0D
  obtain ⟨ρ₂, hρ₂c, hρ₂p, hρ₂y⟩ := dblRep ρ hρ y hy
  let ψ : ↥(Dec (Loc.placeJ j)) →* V.frame.G₀ := V.pr.comp (Dec (Loc.placeJ j)).subtype
  have hψc : Continuous ψ := (V.pr_cont W.continuous_resP).comp continuous_subtype_val
  haveI : CompactSpace ↥(Dec (Loc.placeJ j)) := isCompact_iff_compactSpace.mp (isClosed_Dec (F := L) (Loc.placeJ j)).isCompact
  let κ : ↥(Dec (Loc.placeJ j)) →* (ResidueField c.O)ˣ := (r.chib ⟨0, hn⟩).comp ψ
  have main := inertia_trivial_of_charpoly_roots_near_character s.p_ne φ hφo c κ ?_ ?_ (ρ₂.comp ψ) (hρ₂c.comp hψc) ?_
  · obtain ⟨h, hh, rfl⟩ := hg
    apply hρ₂y
    exact main ⟨h, Ine_le_Dec _ hh⟩ ((hφI ⟨h, Ine_le_Dec _ hh⟩).2 hh)
  · intro h hh
    have hI : (h : G L Ω) ∈ Ine (Loc.placeJ j) := (hφI h).1 hh
    exact MonoidHom.mem_ker.mp (hI0 ⟨0, hn⟩ ⟨(h : G L Ω), hI, rfl⟩)
  · obtain ⟨h, hh, rfl⟩ := hg0D
    refine ⟨⟨h, hh⟩, fun heq => hg0e ?_⟩
    unfold Loc.cycA at heq
    rw [MonoidHom.comp_apply, hφc] at heq
    have e1 : V.frame.ε (V.frame.η.ker.subtype (V.pr h)) = cycZ L Ω l h := by
      change V.ε (toGS Ω V.S' (W.resP L Ω h)) = _
      rw [← MonoidHom.comp_apply, V.hε]
      rfl
    apply Units.ext
    unfold W.GFrame.eps W.pushCh
    change (algebraMap c.O (ResidueField c.O)) (algebraMap ℤ_[l] c.O
      ↑(V.frame.ε (V.frame.η.ker.subtype (V.pr h)))) = 1
    change (residue c.O) (algebraMap ℤ_[l] c.O ↑(cycZ L Ω l h)) = 1 at heq
    rw [e1, IsLocalRing.ResidueField.algebraMap_eq]
    exact heq
  · intro h a ha t ht
    change t ∈ (W.mat ρ₂ (ψ h)).charpoly.roots at ht
    rw [hρ₂p, Polynomial.roots_pow, Multiset.mem_nsmul] at ht
    refine rootsNear B x ρ hB (ψ h) a (fun i => ?_) t ht.2
    rw [ha]
    exact congrArg Units.val (hD0 (ψ h) ⟨h.1, h.2, rfl⟩ ⟨0, hn⟩ i)
end
