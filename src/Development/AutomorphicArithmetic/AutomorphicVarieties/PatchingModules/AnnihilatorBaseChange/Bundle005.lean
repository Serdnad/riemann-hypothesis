module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchedSupportCompletions
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle005
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

@[expose] public section

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem ker_open {l : ℕ} [Fact l.Prime] {Γ S : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CommRing S] (ε : Γ →* ℤ_[l]ˣ) (hε : Continuous ε) (φ : ℤ_[l] →+* S) (j : ℕ) (hφ : φ ((l : ℤ_[l]) ^ j) = 0) :
    IsOpen ((pushCh φ ε).ker : Set Γ) := by
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  have hc : Continuous fun g => ‖((ε g : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ :=
    ((Units.continuous_val.comp hε).sub continuous_const).norm
  have hp : (0 : ℝ) < (l : ℝ) ^ (-(j : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  have ho : IsOpen {g | ‖((ε g : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ < (l : ℝ) ^ (-(j : ℤ))} := isOpen_lt hc continuous_const
  refine Filter.mem_of_superset (ho.mem_nhds (by simpa using hp)) fun g hg => ?_
  have h1 := (PadicInt.norm_le_pow_iff_mem_span_pow _ j).1 (le_of_lt hg)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
  have h2 : φ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
    have := congrArg φ hc
    rw [map_mul, hφ, mul_zero, map_sub, map_one] at this
    exact (sub_eq_zero.1 this.symm)
  exact Units.ext h2

private theorem lam_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G)
    (i : ℕ) (h : H) (a : A) :
    (D.comap φ).lam i (MonoidAlgebra.single h a) = D.lam i (MonoidAlgebra.single (φ h) a) := by
  have : (D.comap φ).chi (MonoidAlgebra.single h a) = D.chi (MonoidAlgebra.single (φ h) a) := by
    change D.D _ (MonoidAlgebra.mapDomainRingHom _ φ _) = D.D _ _
    congr 1
    rw [map_sub]
    simp
  simp only [GDet.lam, this]

private theorem lam_map {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : GDet n A G) (f : A →+* B)
    (i : ℕ) (h : G) (a : A) :
    f (D.lam i (MonoidAlgebra.single h a)) = (D.map f).lam i (MonoidAlgebra.single h (f a)) := by
  rw [← ((UpperTheory.V.CA.d_gmap D).2.2.1 f (MonoidAlgebra.single h a)).2 i, MonoidAlgebra.mapRingHom_single]

theorem UpperTheory.V.Pa.Core.patched_lam_conj_twist_approx_annihilated :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Adapted T (r := r) → ∀ (i : ℕ) (g g' : Ph0 Λ), (g' : Λ.Ph) = Λ.ct * g * Λ.ct⁻¹ → ∀ j : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), ∃ a' : W.R, (W.t.D.lam i (MonoidAlgebra.single g'⁻¹ ((Λ.G.frame.eps O W.R (πo0 Λ g) ^ (1 - (n : ℤ)) : W.Rˣ) : W.R)) - W.t.D.lam i (MonoidAlgebra.single g 1)) - a' ∈ maximalIdeal W.R ^ j ∧ (m.ρ N a' = 0 ∨ ∀ x : (A.A N).M, (fEl (T.Nq N) (A.A N).U * m.ρ N a') ^ A.ex • x = 0) := by
  intro l _ L G0 T Λ n O _ _ _ hO _ r B _ _ _ u J D A W m _ i g g' hg j
  have hlO : (l : O) ∈ maximalIdeal O := by
    haveI := hO.char
    rw [← residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero _ l
  have hlR : (l : W.R) ∈ maximalIdeal W.R := by
    have := map_nonunit (algebraMap O W.R) _ hlO
    rwa [map_natCast] at this
  let q := Ideal.Quotient.mk (maximalIdeal W.R ^ j)
  let φ : ℤ_[l] →+* W.R ⧸ maximalIdeal W.R ^ j := q.comp ((algebraMap O W.R).comp (algebraMap ℤ_[l] O))
  have hφ : φ ((l : ℤ_[l]) ^ j) = 0 := by
    rw [map_pow, map_natCast, ← map_natCast q, ← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hlR j)
  let V : OpenNormalSubgroup G0.Γ :=
    { toSubgroup := (pushCh φ G0.ε).ker
      isOpen' := ker_open G0.ε G0.ε_cont φ j hφ
      isNormal' := MonoidHom.normal_ker _ }
  refine (Λ.p_lim V).mono fun N hN => ?_
  have h1 : pushCh φ G0.ε ((T.h N).p (Λ.π N g) * (Λ.h.p (Λ.πo g))⁻¹) = 1 := hN g
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  have h2 : Units.map (q : W.R →* W.R ⧸ maximalIdeal W.R ^ j) ((T.GN N).frame.eps O W.R (πN0 Λ N g)) =
      Units.map (q : W.R →* W.R ⧸ maximalIdeal W.R ^ j) (Λ.G.frame.eps O W.R (πo0 Λ g)) := by
    have h3 := congrArg Units.val h1
    change φ (G0.ε _ : ℤ_[l]ˣ) = φ (G0.ε _ : ℤ_[l]ˣ) at h3
    rw [(T.h N).ε, Λ.h.ε] at h3
    exact Units.ext h3
  refine ⟨W.t.D.lam i (MonoidAlgebra.single g'⁻¹
      (((T.GN N).frame.eps O W.R (πN0 Λ N g) ^ (1 - (n : ℤ)) : W.Rˣ) : W.R)) -
      W.t.D.lam i (MonoidAlgebra.single g 1), ?_, Or.inl ?_⟩
  · rw [sub_sub_sub_cancel_right, ← Ideal.Quotient.eq]
    change q _ = q _
    rw [lam_map, lam_map]
    have h4 := congrArg (fun z : (W.R ⧸ maximalIdeal W.R ^ j)ˣ => ((z ^ (1 - (n : ℤ)) : _ˣ) : W.R ⧸ maximalIdeal W.R ^ j)) h2
    simp only [← map_zpow (Units.map (q : W.R →* W.R ⧸ maximalIdeal W.R ^ j))] at h4
    exact congrArg (fun z => (W.t.D.map q).lam i (MonoidAlgebra.single g'⁻¹ z)) h4.symm
  · rw [map_sub, sub_eq_zero]
    change (m.ρ N).toRingHom _ = (m.ρ N).toRingHom _
    rw [lam_map, lam_map, (m.ρ_maps N).1, lam_comap, lam_comap, map_one, ← (A.A N).p.P i (πN0 Λ N g)]
    have e1 : πN0 Λ N g' = (T.GN N).frame.conj (πN0 Λ N g) := Subtype.ext (by
      change Λ.π N g' = (T.GN N).c * Λ.π N g * (T.GN N).c⁻¹
      rw [hg, map_mul, map_mul, map_inv, Λ.ct_N])
    have e2 : Units.map ((m.ρ N).toRingHom : W.R →* (A.A N).R) ((T.GN N).frame.eps O W.R (πN0 Λ N g)) =
        (T.GN N).frame.eps O (A.A N).R (πN0 Λ N g) := Units.ext ((m.ρ N).commutes _)
    have e3 : (m.ρ N).toRingHom (((T.GN N).frame.eps O W.R (πN0 Λ N g) ^ (1 - (n : ℤ)) : W.Rˣ) : W.R) =
        (((T.GN N).frame.eps O (A.A N).R (πN0 Λ N g) ^ (1 - (n : ℤ)) : (A.A N).Rˣ) : (A.A N).R) := by
      rw [← e2, ← map_zpow (Units.map ((m.ρ N).toRingHom : W.R →* (A.A N).R))]
      rfl
    rw [e3, map_inv, e1]
    congr 1
    simp [GFrame.star, GFrame.starOp]
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem mem_map {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') {y : R} (hy : y ∈ maximalIdeal R) :
    f y ∈ maximalIdeal R' := by
  rw [← res_eq_zero_iff O R'] at *
  rw [res_map]
  exact (res_eq_zero_iff O R y).mpr hy

private theorem adic_map {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') {Γ : Type} [TopologicalSpace Γ] {a : Γ → R}
    (ha : AdicCont (maximalIdeal R) a) : AdicCont (maximalIdeal R') fun g => f (a g) := by
  intro N
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap f.toRingHom := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    apply Ideal.pow_right_mono
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact mem_map f hx
  have key := (ha N).comp (Ideal.quotientMap (maximalIdeal R' ^ N) f.toRingHom hle)
  convert key using 1
  funext g
  simp [Ideal.quotientMap_mk]

theorem UpperTheory.V.Pa.Core.tupMap :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (R R' : Type) [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R'] (t : Tup Λ A R) (f : R →ₐ[O] R'), ∃ t' : Tup Λ A R', t.Maps f.toRingHom t'.D t'.ψ t'.s t'.U t'.y := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A R R' _ _ _ _ _ _ t f
  refine ⟨⟨t.D.map f.toRingHom, ?_, ?_, fun v i => pushCh f.toRingHom (t.ψ v i), ?_, f t.s, mem_map f t.s_mem,
    fun j i => f (t.U j i), ?_, fun j i => f (t.y j i), fun j i => mem_map f (t.y_mem j i)⟩,
    rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  · intro i
    have h := adic_map f (t.cont i)
    convert h using 2 with g
    have := ((UpperTheory.V.CA.d_gmap t.D).2.2.1 f.toRingHom (MonoidAlgebra.single g 1)).2 i
    simpa using this
  · rw [(UpperTheory.V.CA.d_gmap t.D).2.1]
    have : (res O R' : R' →+* ResidueField O).comp f.toRingHom = (res O R : R →+* ResidueField O) := by
      ext x
      exact res_map f x
    rw [this]
    exact t.red
  · intro v i
    have hp := t.psi v i
    refine ⟨?_, ?_, ?_⟩
    · exact adic_map f hp.cont
    · intro g
      simpa [res_map] using hp.red g
    · intro g
      simpa using congrArg f (hp.mu g)
  · intro j i
    have h := mem_map f (t.U_mem j i)
    simpa using h
end
