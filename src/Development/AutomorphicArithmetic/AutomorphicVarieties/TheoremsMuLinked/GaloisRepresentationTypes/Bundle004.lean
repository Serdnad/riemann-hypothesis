module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.PolNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.RelKill
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IrreducibleSpans.Burnside
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th

private theorem avg {Γ k M : Type} [Group Γ] [Field k] [CharZero k] [AddCommGroup M] [Module k M] (R : Representation k Γ M)
    (H : Subgroup Γ) [H.FiniteIndex] (c : Γ → M) (hc : ∀ g h, c (g * h) = c g + R g (c h)) (X : M)
    (hX : ∀ h ∈ H, c h = R h X - X) : ∃ Y, ∀ g, c g = R g Y - Y := by
  classical
  haveI : Fintype (Γ ⧸ H) := Fintype.ofFinite _
  let d : Γ → M := fun g => c g - (R g X - X)
  have hd : ∀ g h, d (g * h) = d g + R g (d h) := fun g h => by
    simp only [d, hc, map_mul, map_sub, Module.End.mul_apply]
    abel
  have hd0 : ∀ g, ∀ h ∈ H, d (g * h) = d g := fun g h hh => by
    have : d h = 0 := by simp only [d, hX h hh, sub_self]
    rw [hd, this, map_zero, add_zero]
  let e : Γ ⧸ H → M := fun q => d q.out
  have he : ∀ g : Γ, e (g : Γ ⧸ H) = d g := fun g => by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
    show d _ = d g
    rw [hh, hd0 _ _ h.2]
  have hs : ∀ g : Γ, ∑ q, e q = (Fintype.card (Γ ⧸ H) : k) • d g + R g (∑ q, e q) := fun g => by
    have h1 : ∀ q : Γ ⧸ H, e (g • q) = d g + R g (e q) := fun q => by
      induction q using QuotientGroup.induction_on with
      | H a => rw [MulAction.Quotient.smul_mk, he, he, smul_eq_mul, hd]
    conv_lhs => rw [← Equiv.sum_comp (MulAction.toPerm g) e]

    simp only [MulAction.toPerm_apply, h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, map_sum,
    Nat.cast_smul_eq_nsmul]
  have hn : (Fintype.card (Γ ⧸ H) : k) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨X - (Fintype.card (Γ ⧸ H) : k)⁻¹ • ∑ q, e q, fun g => ?_⟩
  have h2 : d g = (Fintype.card (Γ ⧸ H) : k)⁻¹ • (∑ q, e q - R g (∑ q, e q)) := by
    rw [sub_eq_of_eq_add (hs g), smul_smul, inv_mul_cancel₀ hn, one_smul]
  have h3 : c g = d g + (R g X - X) := by simp only [d, sub_add_cancel]
  rw [h3, h2, map_sub, map_smul, smul_sub]
  abel

private theorem cc_eq {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] (c : Ω → Ω) (j : Ω →+* ℂ)
    (h : ∀ x, j (c x) = starRingEnd ℂ (j x)) (x : K) :
    c (algebraMap K Ω x) = algebraMap K Ω (IsCMField.complexConj K x) := by
  apply j.injective
  rw [h]
  exact (IsCMField.complexEmbedding_complexConj K (j.comp (algebraMap K Ω)) x).symm

private theorem zero_NS {l : ℕ} [Fact l.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V] [T2Space V]
    {ρ : Representation C (G F Ω) V} {c : G F Ω → V} (hc : c ∈ Z1 ρ) (hb : Af.IsBK l ρ c)
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → w ∈ S)
    (hρ : ∀ s ∈ NS Ω S, ρ s = 1) : ∀ s ∈ NS Ω S, c s = 0 := by
  have c1 : c 1 = 0 := by
    have := hc.2 1 1
    simpa using this
  let N : Subgroup (G F Ω) :=
    { carrier := {s | s ∈ NS Ω S ∧ c s = 0}
      one_mem' := ⟨one_mem _, c1⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by rw [hc.2, ha.2, hb.2, map_zero, add_zero]⟩
      inv_mem' := fun {a} ha => by
        have h1 := hc.2 a a⁻¹
        rw [mul_inv_cancel, c1, hρ a ha.1, ha.2, zero_add] at h1
        exact ⟨inv_mem ha.1, h1.symm⟩ }
  haveI : N.Normal := ⟨fun a ha g => by
    refine ⟨(inferInstance : (NS Ω S).Normal).conj_mem a ha.1 g, ?_⟩
    have h1 := hc.2 g g⁻¹
    rw [mul_inv_cancel, c1] at h1
    rw [hc.2, hc.2, map_mul, hρ a ha.1, ha.2, mul_one, map_zero, add_zero, ← h1]⟩
  have hcl : IsClosed (N : Set (G F Ω)) := (isClosed_NS Ω S).inter (isClosed_eq hc.1 continuous_const)
  have hin : ∀ w, w ∉ S → ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ s ∈ Ine (F := F) A, s ∈ NS Ω S := by
    intro w hw A hA s hs
    refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
    simp only [Set.mem_iUnion]
    exact ⟨w, hw, A, hA, hs⟩
  have hN : NS Ω S ≤ N := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal fun s hs => ?_) hcl
    simp only [Set.mem_iUnion] at hs
    obtain ⟨w, hw, A, hA, hs⟩ := hs
    obtain ⟨A₀, hA₀, x, hx⟩ := hb.away w fun h => hw (hS w h)
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := F) hA₀ hA
    have hs' : s ∈ Ine (F := F) A := hs
    rw [← hg] at hs'
    have ht := GlobalTheory.Cut.ShaBound.conj_mem_Ine' hs'
    have hm := hin w hw A₀ hA₀ _ ht
    have h1 : g⁻¹ * s * g ∈ N := ⟨hm, by rw [hx _ ht, hρ _ hm, Module.End.one_apply, sub_self]⟩
    have h2 := (inferInstance : N.Normal).conj_mem _ h1 g
    have e : g * (g⁻¹ * s * g) * g⁻¹ = s := by group
    rwa [e] at h2
  exact fun s hs => (hN hs).2

theorem UpperTheory.V.Th.adDown :
    AdDown := by
  intro Ω _ _ _ l _ K L _ _ _ _ _ _ _ _ _ _ hLK s V n r μ R _ hR ρ ka h1 h2 hz c hc hb
  obtain ⟨c0, P, ⟨j, hj⟩, hP, hRK, hRc⟩ := hR
  obtain ⟨j', hj'⟩ := s.hc
  obtain ⟨hc', hb'⟩ := X.Kato.bkRes l (W.Lp L) Ω _ _ R c hc hb
  have he : ∀ g, V.frame.eps ℤ_[l] (Qbar l) (V.pr g) = cycBar L Ω l g := by
    intro g
    have : V.ε (toGS Ω V.S' (W.resP L Ω g)) = cycZ L Ω l g := DFunLike.congr_fun V.hε _
    ext
    show algebraMap ℤ_[l] (Qbar l) (V.ε (toGS Ω V.S' (W.resP L Ω g)) : ℤ_[l]) = _
    rw [this]
    rfl
  have hK : ∀ σ ∈ Base.galOf ℚ K Ω, ∃ t, Base.galEmb ℚ K Ω t = σ := fun σ h => by
    rwa [← Base.range_galEmb] at h
  have hc0 : ∀ x : K, c0⁻¹ (algebraMap K Ω x) = algebraMap K Ω (IsCMField.complexConj K x) := fun x => by
    refine c0.symm_apply_eq.2 ?_
    rw [cc_eq c0 j hj, IsCMField.complexConj_apply_apply]
  obtain ⟨w, hw⟩ := hK (Base.galEmb ℚ (W.Lp L) Ω s.c * c0⁻¹) fun x => by
    rw [AlgEquiv.mul_apply, hc0, Base.galEmb_apply, cc_eq s.c j' hj', IsCMField.complexConj_apply_apply]
  have hconj : ∀ t : G K Ω, ∃ t', Base.galEmb ℚ K Ω t' = c0 * Base.galEmb ℚ K Ω t * c0⁻¹ := fun t => hK _ fun x => by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hc0, Base.galEmb_apply, t.commutes, cc_eq c0 j hj,
      IsCMField.complexConj_apply_apply]
  have hT : ∀ g : G L Ω, ∃ t, Base.galEmb ℚ L Ω g = Base.galEmb ℚ K Ω t := fun g =>
    (hK _ (hLK (Base.galEmb_mem ℚ L Ω g))).imp fun _ h => h.symm
  have hpr : ∀ x : V.frame.G₀, ∃ g, V.pr g = x := by
    rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨g, rfl⟩ := (V.hη y).1 hx
    exact ⟨g, rfl⟩
  have had : ∀ (g : G L Ω) X, R (Base.galEmb ℚ L Ω g) X = Loc.adGL ρ (V.pr g) X := fun g X => by
    obtain ⟨t, ht⟩ := hT g
    have a1 : (ρ (V.pr g)).val = (ka g).val • (r t).val := h1 g t ht
    have a2 : (ρ (V.pr g)⁻¹).val = (ka g⁻¹).val • (r t⁻¹).val :=
      map_inv V.pr g ▸ h1 g⁻¹ t⁻¹ (by rw [map_inv, map_inv, ht])
    rw [map_inv ka, map_inv r, show ρ (V.pr g)⁻¹ = (ρ (V.pr g))⁻¹ from map_inv ρ (V.pr g)] at a2
    rw [ht]
    refine (hRK t X).trans ?_
    show _ = (ρ (V.pr g)).val * X * ((ρ (V.pr g))⁻¹).val
    rw [a1, a2, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.mul_inv, one_smul]
  have hN : ∀ x ∈ NS Ω V.S', R (Base.galEmb ℚ (W.Lp L) Ω x) = 1 := fun x hx => by
    have e : toGS Ω V.S' x = 1 := (QuotientGroup.eq_one_iff x).2 hx
    obtain ⟨g, rfl⟩ := (V.hη x).1 (by rw [e, map_one])
    have e' : V.pr g = 1 := Subtype.ext e
    refine LinearMap.ext fun X => (had g X).trans ?_
    rw [e']
    exact LinearMap.congr_fun (map_one (Loc.adGL ρ)) X
  have hN' := zero_NS hc' hb' V.S' (fun v hv => V.sub (Or.inl hv)) hN
  let R' : Representation (Qbar l) V.frame.Γ (Matrix (Fin n) (Fin n) (Qbar l)) :=
    QuotientGroup.lift (NS Ω V.S') (R.comp (Base.galEmb ℚ (W.Lp L) Ω)) hN
  let z : V.frame.Γ → Matrix (Fin n) (Fin n) (Qbar l) := fun q =>
    Quotient.liftOn' q (fun x => c (Base.galEmb ℚ (W.Lp L) Ω x)) fun a b hab => by
      have h := QuotientGroup.leftRel_apply.1 hab
      have h' := hc'.2 a (a⁻¹ * b)
      have h0 := hN' _ h
      beta_reduce at h' h0
      rw [mul_inv_cancel_left, h0, map_zero, add_zero] at h'
      exact h'.symm
  have hz1 : z ∈ Z1 R' := by
    refine (mem_Z1_iff_cocycle _ _).2 ⟨hc'.1.quotient_liftOn' _, fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact hc'.2 a b
  have hform : V.frame.IsForm ℤ_[l] n ρ (P * (r w)⁻¹) := by
    intro x
    obtain ⟨g, rfl⟩ := hpr x
    obtain ⟨g', hg'⟩ := (V.hη (s.c * W.resP L Ω g * s.c⁻¹)).1 (V.frame.conj (V.pr g)).2
    have e : V.frame.conj (V.pr g) = V.pr g' := Subtype.ext (by
      show _ = toGS Ω V.S' (W.resP L Ω g')
      rw [hg', map_mul, map_mul, map_inv]
      rfl)
    obtain ⟨t, ht⟩ := hT g
    obtain ⟨t', ht'⟩ := hconj t
    have e2 : Base.galEmb ℚ L Ω g' = Base.galEmb ℚ K Ω (w * t' * w⁻¹) := by
      show Base.galEmb ℚ (W.Lp L) Ω (W.resP L Ω g') = _
      rw [hg', map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hw, ht', ← ht]
      show _ * Base.galEmb ℚ L Ω g * _ = _
      group
    have e3 : (P * (r w)⁻¹).val * W.mat r (w * t' * w⁻¹) = P.val * (r t').val * ((r w)⁻¹).val := by
      show _ * (r (w * t' * w⁻¹)).val = _
      rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul, map_mul, map_mul, map_inv]
      congr 1
      group
    have e4 : (W.mat r t).transpose * P.val * (r t').val = (μ t).val • P.val := hP t t' ht'
    rw [e, h1 g t ht, h1 g' _ e2, he, ← h2 g g' t hg' ht, Matrix.transpose_smul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, e3, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e4, Matrix.smul_mul,
      smul_smul, smul_smul, Units.val_mul, Units.val_mul, Units.val_mul]
  have hext : Ws.Eb.IsAdExt V.frame ρ (P * (r w)⁻¹) R' := by
    refine ⟨fun x X => ?_, fun X => ?_⟩
    · obtain ⟨g, rfl⟩ := hpr x
      exact had g X
    · show R (Base.galEmb ℚ (W.Lp L) Ω s.c) X = _
      rw [mul_inv_eq_iff_eq_mul.1 hw.symm, map_mul, Module.End.mul_apply, hRc]
      refine (hRK w _).trans ?_
      simp only [mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  obtain ⟨X, hX⟩ := hz _ R' hform hext z hz1 hb'
  haveI : (Base.galOf ℚ (W.Lp L) Ω).FiniteIndex :=
    ⟨by rw [(Base.galEmbTop ℚ (W.Lp L) Ω).2.2]; exact Module.finrank_pos.ne'⟩
  refine (mem_coboundaries1 _ _).2 (avg R (Base.galOf ℚ (W.Lp L) Ω) c hc.2 X fun h hh => ?_)
  rw [← Base.range_galEmb] at hh
  obtain ⟨x, rfl⟩ := hh
  exact hX (toGS Ω V.S' x)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

private theorem ad_eq {H K : Type} [Group H] [CommRing K] {n : ℕ} (ρ : H →* GL (Fin n) K) (g : H) (X : Matrix (Fin n) (Fin n) K) :
    Loc.adGL ρ g X = W.mat ρ g * X * W.mat ρ g⁻¹ := by
  change _ = (ρ g : Matrix (Fin n) (Fin n) K) * X * (ρ g⁻¹ : GL (Fin n) K)
  rw [map_inv]
  rfl

private theorem cont_sub {H K : Type} [Group H] [TopologicalSpace H] [ContinuousInv H] [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] {n : ℕ} {a y : H → Matrix (Fin n) (Fin n) K} (ha : Continuous a) (hy : Continuous y)
    (X : Matrix (Fin n) (Fin n) K) : Continuous fun g => y g - (a g * X * a g⁻¹ - X) :=
  hy.sub (((ha.matrix_mul continuous_const).matrix_mul (ha.comp continuous_inv)).sub continuous_const)

theorem UpperTheory.V.Th.core_of :
    Th.OrdVan2 → W.PhiAll → Th.Core := by
  intro hO hΦ l _ L Ω _ _ _ _ _ _ s V hV _ c _ n h2 h4 r h0 B ι x ρ hN P R hP hR z hz hzo
  obtain ⟨h, hh⟩ := hN.arith
  obtain ⟨hD, -⟩ := Det.redB x ρ hN.rep
  have hfull : Submodule.span (Qbar l) (Set.range (W.mat ρ)) = ⊤ :=
    KStar.Schema.span_eq_top_of_irreducible _ fun N hs => hN.irr N fun g _ => hs g
  have hI := (Ws.Eb.relKill B x ρ hfull hD).2
  obtain ⟨X₀, hpol, hext⟩ := Det.polNorm V.frame ρ P R z hR hz.2
  have heps : ∃ g : V.frame.G₀, V.frame.ε g ≠ 1 := by
    obtain ⟨g, -, hg⟩ := h0.2.2
    refine ⟨g, fun e => hg ?_⟩
    have e' : (V.frame.ε.comp V.frame.η.ker.subtype) g = 1 := e
    rw [W.GFrame.eps, MonoidHom.comp_apply, e', map_one]
  have hdet := regDet V.frame c.O ρ P (by omega) (hΦ l L Ω s V).2.1 heps hN.cont hN.irr hN.n3
  have hno : ∀ (v : W.Vl l L) i j, x.psi v i ≠ x.psi v j * (cycBar L Ω l).comp (Dec (F := L) (s.A v)).subtype := by
    intro v i j e
    by_cases hij : i = j
    · subst hij
      have h1 := (s.hA v.1 ((l : ℕ) : 𝓞 (W.Lp L))).2 v.2
      exact Det.epsDec (l := l) (L := L) (Ω := Ω) (s.A v.1) (s.w v.1) (s.hw v.1) ((s.hw v.1 ((l : ℕ) : 𝓞 L)).1 (by simpa only [map_natCast] using h1)) (left_eq_mul.1 e)
    · obtain ⟨g, hg, hf⟩ := hN.free v
      refine hf i j hij 1 one_pos ?_
      have e1 : V.ε (toGS Ω V.S' (W.resP L Ω (Subtype.val g))) = cycZ (W.Lp L) Ω l (W.resP L Ω (Subtype.val g)) :=
        DFunLike.congr_fun V.hε _
      have e2 : cycZ L Ω l (Subtype.val g) = 1 := e1.symm.trans hg
      have e3 : cycBar L Ω l (Subtype.val g) = 1 := by rw [cycBar, MonoidHom.comp_apply, e2, map_one]
      have e4 : x.psi v i g = x.psi v j g * cycBar L Ω l (Subtype.val g) := DFunLike.congr_fun e g
      rw [e3, mul_one] at e4
      simp only [pow_one]
      exact e4
  have hc : Continuous fun g : V.frame.G₀ => W.mat ρ g := Units.continuous_val.comp hN.cont
  refine (hO l L Ω s V c n r B ι x h ρ P hV h2 h4 h0 hh hD hN.cont hN.aut hfull hP hN.unr0 hno hdet
    (fun g => z g - Pa.dY V.frame (W.mat ρ) X₀ g) ⟨?_, fun g g' => ?_, hpol, fun u g hg => ?_, fun v => ?_⟩).elim hext
  · exact cont_sub hc (hz.1.comp continuous_subtype_val) X₀
  · have e1 : z ((g * g' : V.frame.G₀) : V.frame.Γ) = z g + W.mat ρ g * z g' * W.mat ρ g⁻¹ := by
      rw [← ad_eq, ← hR.ad]
      exact hz.2 _ _
    have e2 : W.mat ρ g * W.mat ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    simp only [e1, Pa.dY, _root_.mul_inv_rev, map_mul]
    noncomm_ring
  · simp only [hzo.ine u g hg, Pa.dY, W.mat, MonoidHom.comp_apply, map_inv, hI u g hg]
    simp
  · obtain ⟨a, X, ha⟩ := hzo.ord v
    refine ⟨a⁻¹, X - X₀, fun g => ?_⟩
    obtain ⟨a1, a2, a3, a4⟩ := ha g
    have e : z (V.frame.φ v g) - Pa.dY V.frame (W.mat ρ) X₀ (V.frame.φ v g) - Pa.dY V.frame (W.mat ρ) (X - X₀) (V.frame.φ v g) =
        z (V.frame.φ v g) - (Loc.adGL (ρ.comp (V.frame.φ v)) g X - X) := by
      rw [ad_eq]
      have e1 : ∀ t, W.mat (ρ.comp (V.frame.φ v)) t = W.mat ρ (V.frame.φ v t) := fun _ => rfl
      simp only [Pa.dY, e1, map_inv]
      noncomm_ring
    rw [inv_inv, e]
    exact ⟨a1, a2, a3, a4⟩
end
