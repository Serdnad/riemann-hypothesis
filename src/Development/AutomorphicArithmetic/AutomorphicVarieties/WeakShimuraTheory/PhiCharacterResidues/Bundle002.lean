module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ContinuousResLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.AdjEqConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.PhiConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.PhiMu
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.phiPsiEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∃ (ψ : ∀ v : W.Vl l T.L, Fin 4 → Dec (F := T.L) (K.s.A v) →* X.Bˣ), K.IsPsiT X n ψ := by
  intro Ω _ _ _ l _ c D T c' h K X n
  have hmem : ∀ (v : W.Vl l T.L) (g : Dec (F := T.L) (K.s.A v)),
      resLe (Tower.F_le T) (g : G T.L Ω) ∈ (T.fr ∅).Gv (K.e v) := by
    intro v g
    show _ ∈ Dec (T.pl (K.e v))
    have hg : (g : G T.L Ω) ∈ Dec (F := T.L) (T.pl (K.e v)) := K.hA v ▸ g.2
    exact hg
  have hup : ∀ (M N : GradeZeroInterpolatingElement.M4 X.A), IsUp M → IsUp N → ∀ i, (M * N) i i = M i i * N i i := by
    intro M N hM hN i
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hlt | hlt
      · rw [hM i k hlt, zero_mul]
      · rw [hN k i hlt, mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hleft : ∀ w, adj (X.P.n w) * X.P.n w = 1 := by
    intro w
    have h1 := (X.pair.low w).1
    simpa [IsGSp] using h1
  have hright : ∀ w, X.P.n w * adj (X.P.n w) = 1 := fun w => mul_eq_one_comm.mp (hleft w)
  have hPmul : ∀ w i, ∀ s ∈ (T.fr ∅).Gv w, ∀ t ∈ (T.fr ∅).Gv w,
      X.P.ψ w i (s * t) = X.P.ψ w i s * X.P.ψ w i t := by
    intro w i s hs t ht
    have key : adj (X.P.n w) * X.P.r (s * t) * X.P.n w
        = (adj (X.P.n w) * X.P.r s * X.P.n w) * (adj (X.P.n w) * X.P.r t * X.P.n w) := by
      rw [map_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (X.P.n w) (adj (X.P.n w)), hright w, Matrix.one_mul]
    unfold PD.ψ
    rw [key]
    exact hup _ _ (X.pair.flag w s hs) (X.pair.flag w t ht) i
  have hψmul : ∀ w i, ∀ s ∈ (T.fr ∅).Gv w, ∀ t ∈ (T.fr ∅).Gv w,
      X.ψ w i (s * t) = X.ψ w i s * X.ψ w i t := by
    intro w i s hs t ht
    apply X.inj
    rw [map_mul, X.ψ_map w i _ (mul_mem hs ht), X.ψ_map w i s hs, X.ψ_map w i t ht]
    exact hPmul w i s hs t ht
  have hψone : ∀ w i, X.ψ w i 1 = 1 := by
    intro w i
    apply X.inj
    rw [map_one, X.ψ_map w i 1 (one_mem _)]
    unfold PD.ψ
    rw [map_one, Matrix.mul_one, hleft w, Matrix.one_apply_eq]
  have hψunit : ∀ w i, ∀ s ∈ (T.fr ∅).Gv w, IsUnit (X.ψ w i s) := by
    intro w i s hs
    by_contra hne
    have h0 : IsLocalRing.residue X.B (X.ψ w i s) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hne)
    have hr := X.ψ_red w i s hs
    have hu := ((((T.fr ∅).χ i s).isUnit.map (inc h)).map (IsLocalRing.residue c'.O))
    rw [← hr] at hu
    simp only [res, h0] at hu
    simp at hu
    exact hne hu
  have hsc : ∀ g g' : G T.L Ω, K.sc n (g * g') = K.sc n g * K.sc n g' := by
    intro g g'
    unfold Link.sc
    simp only [map_mul, Units.val_mul, mul_pow]
    ring
  have hsc1 : K.sc n 1 = 1 := by
    unfold Link.sc
    simp
  have hscu : ∀ g : G T.L Ω, IsUnit (K.sc n g) := by
    intro g
    exact (K.κ g).isUnit.mul ((K.β g).isUnit.pow n)
  refine ⟨fun v i => IsUnit.liftRight
    { toFun := fun g => algebraMap c'.O X.B (K.sc n (g : G T.L Ω)) *
        X.ψ (K.e v) i (resLe (Tower.F_le T) (g : G T.L Ω))
      map_one' := by
        simp only [OneMemClass.coe_one, map_one, hsc1]
        rw [one_mul]
        exact hψone (K.e v) i
      map_mul' := by
        intro g g'
        simp only [Subgroup.coe_mul]
        rw [map_mul (resLe (Tower.F_le T)), hψmul _ _ _ (hmem v g) _ (hmem v g'), hsc, map_mul]
        ring }
    (fun g => ((hscu (g : G T.L Ω)).map (algebraMap c'.O X.B)).mul (hψunit _ _ _ (hmem v g))), ?_⟩
  intro v i g
  rfl
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.phiFlag :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∀ (ψ : ∀ v : W.Vl l T.L, Fin 4 → Dec (F := T.L) (K.s.A v) →* X.Bˣ), K.IsPsiT X n ψ → ∀ v : W.Vl l T.L, W.HasFlag ((K.rho X n).toHomUnits.comp (Dec (F := T.L) (K.s.A v)).subtype) fun i => W.pushCh (algebraMap X.B X.A) (ψ v i) := by
  intro Ω _ _ _ l _ c D T c' h K X n ψ hψ v
  have hlow := X.pair.low (K.e v)
  have h1 : adj (X.P.n (K.e v)) * X.P.n (K.e v) = 1 := by
    have h0 := hlow.1
    simpa [UpperTheory.V.GradeZeroInterpolatingElement.IsGSp] using h0
  have h2 : X.P.n (K.e v) * adj (X.P.n (K.e v)) = 1 := mul_eq_one_comm.mp h1
  refine ⟨⟨adj (X.P.n (K.e v)), X.P.n (K.e v), h1, h2⟩, fun s => ?_⟩
  obtain ⟨s, hs⟩ := s
  have hs' : resLe T.F_le s ∈ (T.fr ∅).Gv (K.e v) := by
    show resLe T.F_le s ∈ Dec (F := T.F) (T.pl (K.e v))
    rw [← K.hA v]
    exact hs
  have hval : (((⟨adj (X.P.n (K.e v)), X.P.n (K.e v), h1, h2⟩ : GL (Fin 4) X.A) *
      ((K.rho X n).toHomUnits.comp (Dec (F := T.L) (K.s.A v)).subtype) ⟨s, hs⟩ *
      (⟨adj (X.P.n (K.e v)), X.P.n (K.e v), h1, h2⟩ : GL (Fin 4) X.A)⁻¹ : GL (Fin 4) X.A) :
        Matrix (Fin 4) (Fin 4) X.A) =
      (algebraMap c'.O X.A (K.sc n s)) • (adj (X.P.n (K.e v)) * X.P.r (resLe T.F_le s) * X.P.n (K.e v)) := by
    simp [UpperTheory.V.Ws.Link.rho_apply, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [hval, Matrix.smul_apply, X.pair.flag (K.e v) _ hs' i j hij, smul_zero]
  · rw [hval, Matrix.smul_apply]
    simp only [W.pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
    rw [hψ v i ⟨s, hs⟩, map_mul, ← IsScalarTower.algebraMap_apply, X.ψ_map _ _ _ hs', smul_eq_mul]
    rfl
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem charpoly_smul_unit {R n : Type} [CommRing R] [Nontrivial R] [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (c : R) (hc : IsUnit c) : (c • M).charpoly = M.charpoly.scaleRoots c := by
  have hinj : ∀ p q : R[X], p.comp (C c * X) = q.comp (C c * X) → p = q := by
    intro p q h
    ext i
    have hi := congrArg (fun r => r.coeff i) h
    simp only [comp_C_mul_X_coeff] at hi
    exact (hc.pow i).mul_right_cancel hi
  have key : (Polynomial.eval₂RingHom C (C c * X)).mapMatrix (Matrix.charmatrix (c • M)) =
      C c • Matrix.charmatrix M := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [Matrix.charmatrix_apply_eq, Matrix.smul_apply, C_mul, mul_sub]
    · simp [Matrix.charmatrix_apply_ne _ _ _ h, Matrix.smul_apply, C_mul]
  have hL : (c • M).charpoly.comp (C c * X) = C c ^ Fintype.card n * M.charpoly := by
    calc (c • M).charpoly.comp (C c * X)
        = Polynomial.eval₂RingHom C (C c * X) (Matrix.charmatrix (c • M)).det := rfl
      _ = (C c • Matrix.charmatrix M).det := by rw [RingHom.map_det, key]
      _ = C c ^ Fintype.card n * M.charpoly := by rw [Matrix.det_smul]; rfl
  have hR : (M.charpoly.scaleRoots c).comp (C c * X) = C c ^ Fintype.card n * M.charpoly := by
    ext i
    rw [comp_C_mul_X_coeff, coeff_scaleRoots, ← C_pow, coeff_C_mul, Matrix.charpoly_natDegree_eq_dim]
    by_cases hi : i ≤ Fintype.card n
    · rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hi, mul_comm]
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [Matrix.charpoly_natDegree_eq_dim]; omega)]
      simp
  apply hinj
  rw [hL, hR]

theorem UpperTheory.V.Ws.phiCpMap :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∀ g, (X.cp (resLe T.F_le g)).Monic ∧ (X.cp (resLe T.F_le g)).natDegree = 4 ∧ (K.cpT X n g).Monic ∧ (K.cpT X n g).map (algebraMap X.B X.A) = (K.rho X n g).charpoly := by
  intro Ω _ _ _ l _ c D T c' h K X n g
  have hinj : Function.Injective (algebraMap X.B X.A) := X.inj
  haveI : Nontrivial X.A := hinj.nontrivial
  have hmap := X.cp_map (resLe T.F_le g)
  have hmon : (X.cp (resLe T.F_le g)).Monic :=
    monic_of_injective hinj (by rw [hmap]; exact Matrix.charpoly_monic _)
  have hdeg : (X.cp (resLe T.F_le g)).natDegree = 4 := by
    rw [← natDegree_map_eq_of_injective hinj, hmap, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  have hmonT : (K.cpT X n g).Monic := by
    show ((X.cp (resLe T.F_le g)).scaleRoots _).leadingCoeff = 1
    rw [leadingCoeff, natDegree_scaleRoots, coeff_scaleRoots_natDegree]
    exact hmon
  refine ⟨hmon, hdeg, hmonT, ?_⟩
  have hu : IsUnit (K.sc n g) := by
    simp only [UpperTheory.V.Ws.Link.sc]
    exact (Units.isUnit _).mul ((Units.isUnit _).pow n)
  show ((X.cp (resLe T.F_le g)).scaleRoots _).map (algebraMap X.B X.A) = _
  rw [map_scaleRoots _ _ _ (by rw [hmon.leadingCoeff, map_one]; exact one_ne_zero), hmap,
    UpperTheory.V.Ws.Link.rho_apply, charpoly_smul_unit _ _ (hu.map _), ← IsScalarTower.algebraMap_apply]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.phiUnr :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∀ (A : ValuationSubring Ω) (v : W.Plc (W.Lp T.L)), IsPlaceOver A v → v ∉ K.V.S' → Ine (F := T.L) A ≤ (K.rho X n).ker := by
  intro Ω _ _ _ l _ c D T c' h K X n A v hA hv g hg
  have hS : v ∉ K.s.S := by rw [← K.hV]; exact hv
  have hl : ¬ A.valuation (l : Ω) < 1 := by
    intro hlt
    apply hS
    left
    apply (hA (l : 𝓞 (W.Lp T.L))).1
    simpa using hlt
  obtain ⟨hκ, hr⟩ := K.unr A v hA hS g hg
  have hβ : K.β g = 1 := K.β_t (K.t_unr A hl hg)
  have hmem : resLe T.F_le g ∈ (T.fr ∅).N := by
    refine ⟨A, ?_, ?_, ?_⟩
    · intro p hp
      have hp' : p = l := by simpa using hp
      rw [hp']
      exact hl
    · exact hg
    · have he : resQ T.F (resLe T.F_le g) = resQ T.L g := by
        ext x
        rfl
      rw [he]
      exact hr
  rw [MonoidHom.mem_ker, UpperTheory.V.Ws.Link.rho_apply]
  have hsc : K.sc n g = 1 := by simp [UpperTheory.V.Ws.Link.sc, hκ, hβ]
  rw [hsc, map_one, one_smul]
  exact X.pair.kill _ hmem
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem charpoly_gsp_conj_inv_scaled {R Γ : Type} [CommRing R] [Group Γ] (r : Γ →* M4 R) (x y : Γ) (ν s s' t : R)
    (hr : IsGSp ν (r x)) (hs : s * s' = 1) (ht : t = s * ν) :
    (t • r (y * x * y⁻¹)⁻¹).charpoly = (s • r x).charpoly := by
  have h1 : IsGSp (s * s * ν) (s • r x) := by
    have ha : adj (s • r x) = s • adj (r x) := by
      ext i j
      simp only [adj_apply, Matrix.smul_apply]
      rw [smul_comm]
    unfold IsGSp at hr ⊢
    rw [ha, Matrix.smul_mul, Matrix.mul_smul, hr, smul_smul, smul_smul]
  have h2 : (s • r x) * (s' • r x⁻¹) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs, one_smul, ← map_mul, mul_inv_cancel, map_one]
  have h3 := phiAdj _ _ _ h1 h2
  rw [← h3, smul_smul]
  have h4 : s * s * ν * s' = t := by rw [ht]; linear_combination (s * ν) * hs
  rw [h4]
  have h5 : t • r (y * x * y⁻¹)⁻¹ = r y * ((t • r x⁻¹) * r y⁻¹) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, ← map_mul, ← map_mul]
    congr 2
    group
  rw [h5, Matrix.charpoly_mul_comm, Matrix.mul_assoc, ← map_mul, inv_mul_cancel, map_one, Matrix.mul_one]

theorem UpperTheory.V.Ws.phiPol :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∀ g, ∃ g', K.V.pr g' = (K.V.frame.conj (K.V.pr g))⁻¹ ∧ (((K.V.frame.eps c'.O X.A (K.V.pr g) ^ (1 - ((4 : ℕ) : ℤ)) : X.Aˣ) : X.A) • K.rho X n g').charpoly = (K.rho X n g).charpoly := by
  intro Ω _ _ _ l _ c D T c' h K X n g
  obtain ⟨cF, hc⟩ := phiConj T K.s
  obtain ⟨g₂, h1, h2⟩ := hc g
  refine ⟨g₂⁻¹, ?_, ?_⟩
  · rw [map_inv]
    congr 1
    apply Subtype.ext
    change toGS Ω K.V.S' (W.resP T.L Ω g₂) = toGS Ω K.V.S' K.s.c * toGS Ω K.V.S' (W.resP T.L Ω g) * (toGS Ω K.V.S' K.s.c)⁻¹
    rw [h1, map_mul, map_mul, map_inv]
  · obtain ⟨k1, k2, -⟩ := K.conj g g₂ h1
    have he : K.V.frame.eps c'.O X.A (K.V.pr g) =
        Units.map (algebraMap c'.O X.A : c'.O →* X.A) (chiO T.L Ω l c'.O g) := by
      have : K.V.ε (toGS Ω K.V.S' (W.resP T.L Ω g)) = cycZ T.L Ω l g := DFunLike.congr_fun K.V.hε (W.resP T.L Ω g)
      apply Units.ext
      change algebraMap c'.O X.A (algebraMap ℤ_[l] c'.O (K.V.ε (toGS Ω K.V.S' (W.resP T.L Ω g)) : ℤ_[l]ˣ)) = _
      rw [this]
      rfl
    rw [Link.rho_apply, Link.rho_apply, smul_smul, map_inv, h2, he]
    refine charpoly_gsp_conj_inv_scaled X.P.r _ _ _ _ (algebraMap c'.O X.A (K.sc n g⁻¹)) _ (X.pair.mult (resLe T.F_le g)) ?_ ?_
    · rw [← map_mul, ← Link.sc_mul, mul_inv_cancel, Link.sc_one, map_one]
    · have hb : K.β g₂⁻¹ = K.β g := by rw [map_inv]; exact (eq_inv_of_mul_eq_one_left k2).symm
      rw [← map_zpow, Units.coe_map]
      change algebraMap c'.O X.A _ * _ = _ * algebraMap c'.O X.A (inc h (D.th (resQ T.L g)))
      rw [← map_mul, ← map_mul]
      congr 1
      simp only [Link.sc, hb]
      set e := chiO T.L Ω l c'.O g
      have e1 : ((e ^ (1 - ((4 : ℕ) : ℤ)) : c'.Oˣ) : c'.O) * (e : c'.O) ^ 3 = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_add]
        norm_num
      have e2 : ((K.κ g₂⁻¹ : c'.Oˣ) : c'.O) * K.κ g₂ = 1 := by
        rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
      generalize ((e ^ (1 - ((4 : ℕ) : ℤ)) : c'.Oˣ) : c'.O) = u at e1 ⊢
      generalize ((K.κ g₂⁻¹ : c'.Oˣ) : c'.O) = v at e2 ⊢
      generalize (inc h (D.th (resQ T.L g)) : c'.O) = θ at k1 ⊢
      generalize ((K.β g : c'.Oˣ) : c'.O) ^ n = b
      linear_combination (-u * v * b) * k1 + (b * (K.κ g : c'.O) * θ * u * (e : c'.O) ^ 3) * e2 + (b * (K.κ g : c'.O) * θ) * e1
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem adic_mul {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f g : Γ → R}
    (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun x => f x * g x := by
  intro N
  convert (hf N).mul (hg N) using 1
  funext x
  exact map_mul _ _ _

private theorem adic_pow {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f : Γ → R}
    (hf : AdicCont I f) (n : ℕ) : AdicCont I fun x => f x ^ n := by
  induction n with
  | zero =>
    intro N
    simp only [pow_zero, map_one]
    exact IsLocallyConstant.const _
  | succ k ih =>
    simp only [pow_succ]
    exact adic_mul ih hf

private theorem adic_alg {Γ O R : Type} [TopologicalSpace Γ] [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R]
    [IsCO O R] {f : Γ → O} (hf : AdicCont (maximalIdeal O) f) :
    AdicCont (maximalIdeal R) fun x => algebraMap O R (f x) := by
  have hloc : IsLocalHom (algebraMap O R) := IsCO.isLocalHom
  intro N
  have hN : (maximalIdeal O) ^ N ≤ Ideal.comap (algebraMap O R) ((maximalIdeal R) ^ N) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    refine Ideal.pow_right_mono ?_ N
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact map_nonunit (algebraMap O R) a ha
  have := (hf N).comp (Ideal.Quotient.lift ((maximalIdeal O) ^ N)
    ((Ideal.Quotient.mk ((maximalIdeal R) ^ N)).comp (algebraMap O R))
    (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (hN ha)))
  convert this using 1
  funext g
  simp only [Function.comp_apply, Ideal.Quotient.lift_mk, RingHom.coe_comp]

private theorem resLe_mem_Dec {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {F L : IntermediateField ℚ Ω}
    (h : F ≤ L) {A A' : ValuationSubring Ω} (e : A = A') (g : Dec (F := L) A) : resLe h g ∈ Dec (F := F) A' := by
  subst e
  exact g.2

theorem UpperTheory.V.Ws.phiIsPsi :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∀ (ψ : ∀ v : W.Vl l T.L, Fin 4 → Dec (F := T.L) (K.s.A v) →* X.Bˣ), K.IsPsiT X n ψ → ∀ v i, K.r.IsPsi v i (ψ v i) := by
  intro Ω _ _ _ l _ c D T c' h K X n ψ hψ v i
  change W.Vl l T.L at v
  have hmem : ∀ g : Dec (F := T.L) (K.s.A (v : W.Plc (W.Lp T.L))),
      resLe T.F_le (g : G T.L Ω) ∈ (T.fr ∅).Gv (K.e v) :=
    fun g => resLe_mem_Dec T.F_le (K.hA v) g
  refine ⟨?_, ?_, ?_⟩
  · have hsc : AdicCont (maximalIdeal X.B)
        fun g : Dec (F := T.L) (K.s.A (v : W.Plc (W.Lp T.L))) => algebraMap c'.O X.B (K.sc n g) := by
      have h0 : AdicCont (maximalIdeal c'.O) fun g : G T.L Ω => K.sc n g :=
        adic_mul K.κ_cont (adic_pow K.β_cont n)
      have h1 : AdicCont (maximalIdeal c'.O)
          fun g : Dec (F := T.L) (K.s.A (v : W.Plc (W.Lp T.L))) => K.sc n g :=
        fun N => (h0 N).comp_continuous continuous_subtype_val
      exact adic_alg h1
    have hX : AdicCont (maximalIdeal X.B)
        fun g : Dec (F := T.L) (K.s.A (v : W.Plc (W.Lp T.L))) => X.ψ (K.e v) i (resLe T.F_le g) := by
      intro N
      have hc : Continuous fun g : Dec (F := T.L) (K.s.A (v : W.Plc (W.Lp T.L))) =>
          (⟨resLe T.F_le g, hmem g⟩ : (T.fr ∅).Gv (K.e v)) :=
        ((continuous_resLe T.F_le).comp continuous_subtype_val).subtype_mk hmem
      exact (X.ψ_cont (K.e v) i N).comp_continuous hc
    show AdicCont (maximalIdeal X.B)
      fun g : Dec (F := T.L) (K.s.A (v : W.Plc (W.Lp T.L))) => ((ψ v i g : X.Bˣ) : X.B)
    convert adic_mul hsc hX using 1
    funext g
    exact hψ v i g
  · intro g
    change Dec (F := T.L) (K.s.A (v : W.Plc (W.Lp T.L))) at g
    show (res c'.O X.B) ((ψ v i g : X.Bˣ) : X.B) = ((K.r.psib v i g : _) : ResidueField c'.O)
    rw [hψ v i g, K.psib, K.chib, map_mul, AlgHom.commutes, X.ψ_red (K.e v) i _ (hmem g)]
    simp only [Link.sc, IsLocalRing.ResidueField.algebraMap_eq, map_mul, map_pow, K.β_red, one_pow,
      mul_one]
    rfl
  · intro g
    obtain ⟨hκ, ht⟩ := K.mu v g.1 g.2
    have hβ : K.β g.1.1 = 1 := MonoidHom.mem_ker.mp (K.β_t (MonoidHom.mem_ker.mpr ht))
    have hmu : resLe T.F_le g.1.1 ∈ (T.fr ∅).Mu (K.e v) :=
      phiMu ((resLe T.F_le).comp (Dec (F := T.L) (K.s.A (v : W.Plc (W.Lp T.L)))).subtype)
        ((continuous_resLe T.F_le).comp continuous_subtype_val)
        (Dec (F := T.F) (T.pl (K.e v))) hmem g.1 g.2
    have hψ1 : X.ψ (K.e v) i (resLe T.F_le g.1.1) = 1 := by
      apply X.inj
      rw [X.ψ_map _ _ _ (hmem g.1), map_one]
      exact X.pair.mu (K.e v) _ hmu i
    have hsc1 : K.sc n g.1.1 = 1 := by
      simp [Link.sc, hκ, hβ]
    have hth : ((K.r.th v i g : c'.Oˣ) : c'.O) = 1 := by
      have := congrArg (fun f => ((f g : c'.Oˣ) : c'.O)) (K.th v i)
      simpa using this
    show ((ψ v i g.1 : X.Bˣ) : X.B) = algebraMap c'.O X.B ((K.r.th v i g : c'.Oˣ) : c'.O)
    refine Eq.trans ?_ (congrArg (algebraMap c'.O X.B) hth).symm
    rw [map_one, hψ v i g.1, hsc1, hψ1, map_one, mul_one]
end
