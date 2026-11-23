module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.MapAdjAlg
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem lifts_map {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ]
    [IsLocalRing Λ] {a : O →+* Λ} {c : PD Φ.ι Γ (ResidueField Λ)} {R R' : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R]
    [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] {P : PD Φ.ι Γ R} (h : Φ.Lifts a c P) (f : R →ₐ[Λ] R') :
    Φ.Lifts a c (P.map (f : R →+* R')) := by
  refine ⟨?_, ?_, ?_⟩
  · have hp := h.pair.map (f : R →+* R')
    rwa [← RingHom.comp_assoc, AlgHom.comp_algebraMap] at hp
  · exact h.cont.map _ (fun x hx =>
      (res_eq_zero_iff Λ R' _).mp ((res_map f x).trans ((res_eq_zero_iff Λ R x).mpr hx)))
  · rw [PD.map_map]
    convert h.red using 2
    exact RingHom.ext fun x => res_map f x

private theorem lifts_noMu {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ]
    [IsLocalRing Λ] {a : O →+* Λ} {c : PD Φ.ι Γ (ResidueField Λ)} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R]
    {P : PD Φ.ι Γ R} (h : Φ.Lifts a c P) : Φ.noMu.Lifts a c P :=
  ⟨⟨h.pair.mult, h.pair.kill, h.pair.nrm, h.pair.low, h.pair.flag, fun _ _ hs => hs.elim⟩, h.cont, h.red⟩

theorem UpperTheory.V.Ws.X1.muQuot :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ), Φ.Std l a → ∀ c : PD Φ.ι Γ (ResidueField Λ), Φ.IsRes ((residue Λ).comp a) c → ∀ ζ : Φ.ι → Γ, (∀ v, MuGen (Φ.Gv v) (Φ.Mu v) (ζ v)) → (∀ v, a (Φ.ν (ζ v)) = 1) → ∀ (R : Type) [CommRing R] [Algebra Λ R] [IsCO Λ R] (P : PD Φ.ι Γ R), Φ.IsDef a c P → ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (P' : PD Φ.ι Γ R'), Φ.noMu.IsDef a c P' → ∃ (g : R' →ₐ[Λ] R) (e : Φ.ι × Fin 2 → R'), Function.Surjective g ∧ RingHom.ker g = Ideal.span (Set.range e) := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hstd c hres ζ hζ hν R _ _ _ P hP R' _ _ _ P' hP'
  obtain ⟨g, hg, -⟩ := hP'.2 R P (lifts_noMu hP.1)
  have hPψ := (X1.muIff Φ l a hstd c hres ζ hζ hν R P (lifts_noMu hP.1)).mp hP.1
  let e : Φ.ι × Fin 2 → R' := fun p => P'.ψ p.1 (Fin.castLE (by norm_num) p.2) (ζ p.1) - 1
  let I : Ideal R' := Ideal.span (Set.range e)
  have hIg : ∀ x ∈ I, g x = 0 := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨⟨v, i⟩, rfl⟩
      have key : ∀ j : Fin 4, g (P'.ψ v j (ζ v)) = P.ψ v j (ζ v) := by
        intro j
        rw [← hg, PD.map_ψ]
        rfl
      fin_cases i
      · simp [e, key, (hPψ v).1]
      · simp [e, key, (hPψ v).2]
    · exact map_zero g
    · intro x y _ _ hx hy
      rw [map_add (f := _), hx, hy, add_zero]
    · intro r x _ hx
      rw [smul_eq_mul, map_mul, hx, mul_zero]
  have hne : I ≠ ⊤ := by
    intro htop
    have h1 := hIg 1 (htop ▸ Submodule.mem_top)
    rw [map_one] at h1
    exact one_ne_zero h1
  haveI : Nontrivial (R' ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hne
  let π : R' →ₐ[Λ] R' ⧸ I := Ideal.Quotient.mkₐ Λ I
  haveI : IsCO Λ (R' ⧸ I) := co_quot Λ R' (R' ⧸ I) π (Ideal.Quotient.mkₐ_surjective Λ I)
  have hQn : Φ.noMu.Lifts a c (P'.map (π : R' →+* R' ⧸ I)) := lifts_map hP'.1 π
  have hQ : Φ.Lifts a c (P'.map (π : R' →+* R' ⧸ I)) := by
    refine (X1.muIff Φ l a hstd c hres ζ hζ hν (R' ⧸ I) _ hQn).mpr (fun v => ⟨?_, ?_⟩)
    · rw [PD.map_ψ]
      have hm : e (v, 0) ∈ I := Ideal.subset_span ⟨(v, 0), rfl⟩
      have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr hm
      simp only [e, map_sub, map_one] at hz
      exact sub_eq_zero.mp hz
    · rw [PD.map_ψ]
      have hm : e (v, 1) ∈ I := Ideal.subset_span ⟨(v, 1), rfl⟩
      have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr hm
      simp only [e, map_sub, map_one] at hz
      exact sub_eq_zero.mp hz
  obtain ⟨h, hh, -⟩ := hP.2 (R' ⧸ I) _ hQ
  obtain ⟨π', -, huniq⟩ := hP'.2 (R' ⧸ I) _ hQn
  have hhg : h.comp g = π := by
    rw [huniq (h.comp g) (by beta_reduce; rw [AlgHom.comp_toRingHom, ← PD.map_map, hg, hh]),
      huniq π rfl]
  let gb : R' ⧸ I →ₐ[Λ] R := Ideal.Quotient.liftₐ I g hIg
  obtain ⟨i0, -, huniqP⟩ := hP.2 R P hP.1
  have hgb : gb.comp π = g := by
    ext x
    rfl
  have hid : gb.comp h = AlgHom.id Λ R := by
    rw [huniqP (gb.comp h) (by beta_reduce; rw [AlgHom.comp_toRingHom, ← PD.map_map, hh, PD.map_map,
        ← AlgHom.comp_toRingHom, hgb, hg]),
      huniqP (AlgHom.id Λ R) (by beta_reduce; rw [← hg, PD.map_map]; rfl)]
  refine ⟨g, e, ?_, ?_⟩
  · intro y
    obtain ⟨z, hz⟩ := Ideal.Quotient.mkₐ_surjective Λ I (h y)
    refine ⟨z, ?_⟩
    have hy := congrArg (fun f : R →ₐ[Λ] R => f y) hid
    simp only [AlgHom.comp_apply, AlgHom.id_apply] at hy
    rw [← hz] at hy
    exact hy
  · apply le_antisymm
    · intro x hx
      have hx' : π x = 0 := by
        rw [← hhg, AlgHom.comp_apply, RingHom.mem_ker.mp hx, map_zero]
      exact (Ideal.Quotient.eq_zero_iff_mem).mp hx'
    · intro x hx
      exact RingHom.mem_ker.mpr (hIg x hx)
end

section

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem ex_mu {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] [IsCO O A] (η : A)
    (hη : ∀ x ∈ maximalIdeal A, x * η = 0) :
    ∃ μ : ResidueField O →+ A, (∀ a : O, μ (residue O a) = a • η) ∧ ∀ (a : A) c, μ (res O A a * c) = a * μ c := by
  have k : ∀ a b : O, residue O a = residue O b → a • η = b • η := fun a b h => by
    rw [← sub_eq_zero, ← sub_smul, Algebra.smul_def]
    refine hη _ ?_
    rw [← res_eq_zero_iff O, AlgHom.commutes, ResidueField.algebraMap_eq, map_sub, h, sub_self]
  choose s hs using residue_surjective (R := O)
  have k2 : ∀ a : O, s (residue O a) • η = a • η := fun a => k _ _ (hs _)
  refine ⟨AddMonoidHom.mk' (fun c => s c • η) fun c d => ?_, k2, fun a c => ?_⟩
  · rw [← add_smul]
    exact k _ _ (by rw [map_add (f := _), hs, hs, hs])
  · obtain ⟨b, hb⟩ := IsCO.res_surj (O := O) a
    have e : res O A a = residue O b := by
      have := (res_eq_zero_iff O A _).2 hb
      rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this
    have e2 : a * η = b • η := by
      have := hη _ hb
      rwa [sub_mul, sub_eq_zero, ← Algebra.smul_def] at this
    show s _ • η = a * (s c • η)
    rw [mul_smul_comm, e2, smul_smul]
    exact k _ _ (by rw [map_mul, hs, hs, e, mul_comm])

private theorem mmap {O R S : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    (f : R →ₐ[O] S) (A B : M4 R) : (A * B).map f = A.map f * B.map f :=
  Matrix.map_mul (f := (f : R →+* S))

private theorem smap {O R S : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    (f : R →ₐ[O] S) (A B : M4 R) : (A - B).map f = A.map f - B.map f := by
  ext i j
  simp

private theorem amap {O R S : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    (f : R →ₐ[O] S) (A : M4 R) : (adj A).map f = adj (A.map f) := by
  ext i j
  rw [Matrix.map_apply, adj_apply, adj_apply, map_zsmul, Matrix.map_apply]

theorem UpperTheory.V.Ws.X1.obWeak :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ], IsUnit (2 : Λ) → ∀ {Γ V : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {Gv : V → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →* Γ), (∀ v, Continuous (loc v)) → ∀ {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R], ∀ (ν : Γ →* Λˣ) (r : Γ →* M4 R) (n : V → M4 R), AdicCont (maximalIdeal Λ) (fun g => (ν g : Λ)) → WP loc (fun g => algebraMap Λ R (ν g)) r n → (∀ i j, AdicCont (maximalIdeal R) fun g => r g i j) → ∀ (rb : Γ →* M4 (ResidueField Λ)) (nb : V → M4 (ResidueField Λ)) (hb : ∀ g, ∃ x, IsGSp x (rb g)), (∀ g, (r g).map (res Λ R) = rb g) → (∀ v, (n v).map (res Λ R) = nb v) → Obs Λ R (Fr.coneH2 loc (adSp rb hb) fun v => bor (nb v)) fun A' _ _ _ q => Function.Surjective q ∧ maximalIdeal A' * RingHom.ker q = ⊥ ∧ WLift loc ν r n q := by
  intro O _ _ _ _ h2 Γ V _ _ _ Gv _ _ _ loc hloc R _ _ _ ν r n hν hw hr rb nb hb hrb hnb A _ _ _ p hp hs κ _ ε hK hind
  classical
  obtain ⟨D, hD⟩ := X1.slEx h2 loc hloc p hp hs ν r n hν hw hr
  obtain ⟨co, k1, k2, k4⟩ := X1.coefEx (RingHom.ker p) hs κ ε hK hind
  choose z z0 z1 z2 using fun u : κ =>
    X1.obCoc loc hloc p hp hs ν r n hν hw hr rb nb hb hrb hnb D (co u) (k1 u) (k2 u)
  have d1 : ∀ s t, (D.om s t).map p = 0 := fun s t => by
    rw [SL.om, smap, mmap, D.rt_map, D.rt_map, D.rt_map, map_mul, sub_self]
  have d2 : ∀ v s, (D.de v s).map p = 0 := fun v s => by
    have e1 : adj (n v) * n v = 1 := by
      have := hw.sp v
      rwa [IsGSp, one_smul] at this
    have e2 : n v * adj (n v) = 1 := mul_eq_one_comm.1 e1
    rw [SL.de, smap, mmap, mmap, amap, D.rt_map, D.nt_map, D.t_map, ← mul_assoc, ← mul_assoc, e2, one_mul,
      mul_assoc, e2, mul_one, sub_self]
  refine ⟨fun u => Submodule.Quotient.mk ⟨z u, z0 u⟩, ?_⟩
  intro c hc A' _ _ _ p' p'' η hp' hpp hη hη0 e1
  have hx : ∑ u, residue O (c u) • z u ∈ Fr.continuousCoboundaries2 loc (adSp rb hb) (fun v => bor (nb v)) := by
    have h1 : (Submodule.Quotient.mk (∑ u, residue O (c u) •
        (⟨z u, z0 u⟩ : Fr.continuousCocycles2 loc (adSp rb hb) (fun v => bor (nb v)))) :
        Fr.coneH2 loc (adSp rb hb) (fun v => bor (nb v))) = 0 := by

      rw [← hc, ← Submodule.mkQ_apply, map_sum]
      rfl

    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, map_sum] at h1
    exact h1
  obtain ⟨μ, m1, m2⟩ := ex_mu (O := O) η hη
  have pp : ∀ x, p'' (p' x) = p x := fun x => DFunLike.congr_fun hpp x
  have key : ∀ x, p x = 0 → p' x = μ (∑ u, residue O (c u) * co u x) := fun x hx => by
    obtain ⟨a, ha, hxa⟩ := k4 x hx
    have : ∑ u, residue O (c u) * co u x = residue O (∑ u, a u * c u) := by

      rw [map_sum]
      exact Finset.sum_congr rfl fun u _ => by rw [map_mul, ha, mul_comm]
    rw [this, m1, Finset.sum_smul]
    conv_lhs => rw [hxa]

    rw [map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [map_smul, e1, mul_smul]
  have keyM : ∀ (M : M4 A) (Y : κ → sp4 (ResidueField O)) (g : M4 (ResidueField O)),
      M.map p = 0 → (∀ u, (Y u).1 * g = M.map (co u)) →
      M.map p' = ((∑ u, residue O (c u) • Y u).1 * g).map μ := fun M Y g h1 h3 => by
    ext a b
    have h4 : p (M a b) = 0 := congrFun (congrFun h1 a) b
    rw [Matrix.map_apply, key _ h4, Matrix.map_apply, Submodule.coe_sum, Finset.sum_mul, Matrix.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Submodule.coe_smul, smul_mul_assoc, h3]
    rfl
  have m3 : ∀ d, p'' (μ d) = 0 := fun d => by
    obtain ⟨a, rfl⟩ := residue_surjective d
    rw [m1, map_smul, hη0, smul_zero]
  have hp'' : Function.Surjective p'' := fun y => by
    obtain ⟨x, rfl⟩ := hp y
    exact ⟨p' x, pp x⟩
  have hs' : maximalIdeal A' * RingHom.ker p'' = ⊥ := by
    rw [eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    obtain ⟨y, rfl⟩ := hp' y
    rw [RingHom.mem_ker, pp] at hy
    rw [Ideal.mem_bot, key y hy, ← m2, (res_eq_zero_iff O A' x).2 hx, zero_mul, map_zero]
  obtain ⟨D', f1, f2⟩ := hD A' p' p'' hpp
  refine ⟨hp'', hs', X1.obCor loc hloc p'' hp'' hs' ν r n hν hw hr rb nb hb hrb hnb D' μ μ.map_add m2 m3 _ hx
    (fun s t => ?_) (fun v s => ?_)⟩
  · rw [f1, keyM _ (fun u => (z u).1 (s, t)) _ (d1 s t) fun u => z1 u s t, Prod.fst_sum, Finset.sum_apply]
    rfl
  · rw [f2, keyM _ (fun u => (z u).2 v s) _ (d2 v s) fun u => z2 u v s, Prod.snd_sum, Finset.sum_apply,
      Finset.sum_apply]
    rfl
end
