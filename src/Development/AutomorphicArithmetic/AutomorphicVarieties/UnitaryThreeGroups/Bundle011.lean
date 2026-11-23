module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoordGrading
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle003
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart

@[expose] public section

section

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV

private theorem emb_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x : GG (m := 3) (R := R))
    (a b : Fin 3 ⊕ Fin 3) : emb (GG.map f x) a b = f (emb x a b) := by
  have h : (theta (GG.map f x).left : Matrix (Fin 3) (Fin 3) S) =
      (theta x.left : Matrix (Fin 3) (Fin 3) R).map f :=
    (congrArg Units.val (map_theta f x.left)).symm
  show (if (GG.map f x).right = 1 then Matrix.fromBlocks (GG.map f x).mat 0 0 (theta (GG.map f x).left : Matrix (Fin 3) (Fin 3) S)
    else Matrix.fromBlocks 0 (GG.map f x).mat (theta (GG.map f x).left : Matrix (Fin 3) (Fin 3) S) 0) a b =
    f ((if x.right = 1 then Matrix.fromBlocks x.mat 0 0 (theta x.left : Matrix (Fin 3) (Fin 3) R)
    else Matrix.fromBlocks 0 x.mat (theta x.left : Matrix (Fin 3) (Fin 3) R) 0) a b)
  rw [h, GG.map_mat, GG.map_right]
  split_ifs <;> rcases a with a | a <;> rcases b with b | b <;> simp

private theorem mat_eq_emb {R : Type} [CommRing R] (x : GG (m := 3) (R := R)) (a b : Fin 3) :
    x.mat a b = emb x (.inl a) (.inl b) + emb x (.inl a) (.inr b) := by
  show _ = (if x.right = 1 then Matrix.fromBlocks x.mat 0 0 (theta x.left : Matrix (Fin 3) (Fin 3) R)
    else Matrix.fromBlocks 0 x.mat (theta x.left : Matrix (Fin 3) (Fin 3) R) 0) _ _ +
    (if x.right = 1 then Matrix.fromBlocks x.mat 0 0 (theta x.left : Matrix (Fin 3) (Fin 3) R)
    else Matrix.fromBlocks 0 x.mat (theta x.left : Matrix (Fin 3) (Fin 3) R) 0) _ _
  split_ifs <;> simp

private theorem emb_tor {R : Type} [CommRing R] (t : Rˣ) :
    emb (GG.ofGL (tor R t)) = Matrix.diagonal fun i => ((t ^ wt6 i : Rˣ) : R) := by
  show (if (1 : ℤˣ) = 1 then Matrix.fromBlocks (tor R t : Matrix (Fin 3) (Fin 3) R) 0 0
    (theta (tor R t) : Matrix (Fin 3) (Fin 3) R) else Matrix.fromBlocks 0 (tor R t : Matrix (Fin 3) (Fin 3) R)
    (theta (tor R t) : Matrix (Fin 3) (Fin 3) R) 0) = _
  rw [if_pos rfl, theta_tor, tor_val, Matrix.fromBlocks_diagonal]
  congr 1
  funext i
  rcases i with i | i <;> rfl

private theorem emb_conj {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (t : Rˣ) (g : G)
    (a b : Fin 3 ⊕ Fin 3) :
    emb (conjBy (tor R t) r g) a b = ((t ^ (wt6 a - wt6 b) : Rˣ) : R) * emb (r g) a b := by
  have h : conjBy (tor R t) r g = GG.ofGL (tor R t) * r g * GG.ofGL (tor R t⁻¹) := by
    rw [map_inv, map_inv]; rfl
  rw [h, map_mul, map_mul, emb_tor, emb_tor, Matrix.mul_diagonal, Matrix.diagonal_mul, _root_.zpow_sub,
    Units.val_mul, _root_.inv_zpow]
  ring

private theorem unitaryEmbedding_residualRep_eq_zero_of_weight_ne {G R : Type} [Group G] [CommRing R] (η : G →* ℤˣ) (Ψ : G →* Rˣ) (g : G)
    (a b : Fin 3 ⊕ Fin 3) (h : wt6 a ≠ wt6 b) : emb (r0 η Ψ g) a b = 0 := by
  show (if (r0 η Ψ g).right = 1 then Matrix.fromBlocks (tor R (Ψ g) : Matrix (Fin 3) (Fin 3) R) 0 0
    (theta (tor R (Ψ g)) : Matrix (Fin 3) (Fin 3) R) else Matrix.fromBlocks 0 (tor R (Ψ g) : Matrix (Fin 3) (Fin 3) R)
    (theta (tor R (Ψ g)) : Matrix (Fin 3) (Fin 3) R) 0) a b = 0
  rw [theta_tor, tor_val]
  split_ifs <;> rcases a with a | a <;> rcases b with b | b <;>
    first
    | rfl
    | exact Matrix.diagonal_apply_ne (i := a) (j := b) (fun i => ((Ψ g ^ wt1 i : Rˣ) : R)) (by rintro rfl; exact h rfl)

private theorem map_reducible_three_dim {O : Type} [CommRing O] [IsLocalRing O] {G : Type} [Group G] (η : G →* ℤˣ) (Ψ : G →* Oˣ)
    (g : G) : GG.map (residue O) (r0 η Ψ g) = rbar O η Ψ g := by
  refine SemidirectProduct.ext (Units.ext ?_) rfl
  show (tor O (Ψ g) : Matrix (Fin 3) (Fin 3) O).map (residue O) = tor _ (barChar O Ψ g)
  rw [tor_val, tor_val, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  exact congrArg Units.val (map_zpow (Units.map (residue O).toMonoidHom) (Ψ g) (wt1 i))

private theorem res_zpow {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    (t : Rˣ) (ht : res O R t = 1) (j : ℤ) : res O R ((t ^ j : Rˣ) : R) = 1 := by
  have h1 : Units.map (res O R : R →* ResidueField O) t = 1 := Units.ext ht
  have h2 := map_zpow (Units.map (res O R : R →* ResidueField O)) t j
  rw [h1, _root_.one_zpow] at h2
  exact congrArg Units.val h2

private def torLift {O : Type} [CommRing O] [IsLocalRing O] {G : Type} [Group G] [TopologicalSpace G]
    {η : G →* ℤˣ} {Ψ : G →* Oˣ} {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (r : GLift O η Ψ R) (t : Rˣ)
    (ht : res O R t = 1) : GLift O η Ψ R where
  hom := conjBy (tor R t) r.hom
  cont a b N := by
    simp only [(conjBy_tor r.hom t).1, map_mul]
    exact (r.cont a b N).comp fun y => Ideal.Quotient.mk _ ((t ^ wt a b : Rˣ) : R) * y
  red g := by
    rw [← r.red g]
    refine SemidirectProduct.ext (Units.ext ?_) ((conjBy_tor r.hom t).2.1 g)
    ext a b
    show res O R ((conjBy (tor R t) r.hom g).mat a b) = res O R ((r.hom g).mat a b)
    rw [(conjBy_tor r.hom t).1, map_mul, res_zpow t ht, one_mul]

private theorem congOne_tor {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    (t : Rˣ) (ht : res O R t = 1) : CongOne (maximalIdeal R) (tor R t) := by
  intro a b
  rw [Matrix.sub_apply, tor_val]
  by_cases h : a = b
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, ← res_eq_zero_iff O, map_sub, res_zpow t ht, map_one, sub_self]
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h, sub_self]
    exact zero_mem _

theorem UpperTheory.V.U3.exists_locPres :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {η : H →* ℤˣ} {Ψ : H →* Oˣ}
      (U : Univ (GCond.noCondition O η Ψ)) (I : Ideal U.R), IsLocallyConstant η → LocGood U I → ∃ WB : WPres O ℤ (U.R ⧸ I), IsLocPres U I WB := by
  intro O _ _ _ _ _ H _ _ _ η Ψ U I _ hL
  obtain ⟨x, τ, _, w, φ, -, hφ, -⟩ := hL.chart
  have hne : I ≠ ⊤ := hφ.ker ▸ RingHom.ker_ne_top φ
  haveI : Nontrivial (U.R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hne
  haveI : IsCO O (U.R ⧸ I) :=
    co_quot O U.R (U.R ⧸ I) (Ideal.Quotient.mkₐ O I) (Ideal.Quotient.mkₐ_surjective O I)
  have hent : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : (U.R ⧸ I) →ₐ[O] R') g a b,
      f (emb (push (Ideal.Quotient.mkₐ O I) U.r.hom g) a b) =
        emb ((U.r.map (f.comp (Ideal.Quotient.mkₐ O I))).hom g) a b := fun R' _ _ _ f g a b =>
    (emb_map (f : (U.R ⧸ I) →+* R') _ a b).symm
  obtain ⟨W, u, hu, he⟩ := coord_grading O ℤ (U.R ⧸ I) (H × (Fin 3 ⊕ Fin 3) × (Fin 3 ⊕ Fin 3))
    (fun s => emb (push (Ideal.Quotient.mkₐ O I) U.r.hom s.1) s.2.1 s.2.2 -
      algebraMap O _ (emb (r0 η Ψ s.1) s.2.1 s.2.2)) (fun s => wt6 s.2.1 - wt6 s.2.2)
    (fun ⟨g, a, b⟩ => by
      have h1 := emb_map (res O (U.R ⧸ I) : (U.R ⧸ I) →+* ResidueField O)
        ((U.r.map (Ideal.Quotient.mkₐ O I)).hom g) a b
      rw [GLift.red, ← map_reducible_three_dim, emb_map] at h1
      rw [← res_eq_zero_iff O, map_sub, AlgHom.commutes, sub_eq_zero]
      exact h1.symm)
    (fun R' _ _ _ f f' h => by
      have h1 : U.r.map (f.comp (Ideal.Quotient.mkₐ O I)) = U.r.map (f'.comp (Ideal.Quotient.mkₐ O I)) := by
        refine GLift.ext (MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) rfl)
        ext a b
        have h2 : ∀ a b, emb ((U.r.map (f.comp (Ideal.Quotient.mkₐ O I))).hom g) a b =
            emb ((U.r.map (f'.comp (Ideal.Quotient.mkₐ O I))).hom g) a b := fun a b => by
          have := h (g, a, b)
          simp only [map_sub, AlgHom.commutes, sub_left_inj] at this
          rw [← hent, ← hent]
          exact this
        refine (mat_eq_emb _ a b).trans (Eq.trans ?_ (mat_eq_emb _ a b).symm)
        rw [h2, h2]
      exact Ideal.Quotient.algHom_ext O (((U.rep R').2 _ trivial).unique h1 rfl))
    (fun R' _ _ _ f t ht => by
      have hk : I ≤ RingHom.ker (f.comp (Ideal.Quotient.mkₐ O I)) := fun y hy => by
        show f (Ideal.Quotient.mk I y) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem.2 hy, map_zero]
      obtain ⟨f₁, hf₁, hk₁⟩ := hL.conj R' (U.r.map (f.comp (Ideal.Quotient.mkₐ O I)))
        (torLift _ (t (Multiplicative.ofAdd 1)) (ht _)) _ (congOne_tor _ (ht _)) rfl ⟨_, rfl, hk⟩
      have hc : (Ideal.Quotient.liftₐ I f₁ hk₁).comp (Ideal.Quotient.mkₐ O I) = f₁ := AlgHom.ext fun _ => rfl
      have htj : ∀ j : ℤ, t (Multiplicative.ofAdd 1) ^ j = t (Multiplicative.ofAdd j) := fun j => by
        rw [← map_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one]
      refine ⟨Ideal.Quotient.liftₐ I f₁ hk₁, fun ⟨g, a, b⟩ => ?_⟩
      dsimp only
      rw [map_sub, map_sub f, AlgHom.commutes, AlgHom.commutes, hent, hent, hc, hf₁, mul_sub, ← htj (wt6 a - wt6 b)]
      congr 1
      · exact emb_conj _ _ g a b
      · by_cases hab : wt6 a = wt6 b
        · simp [hab]
        · simp [unitaryEmbedding_residualRep_eq_zero_of_weight_ne η Ψ g a b hab])
  refine ⟨W, fun i => ⟨(u i).1, (u i).2.1, (u i).2.2, (hu i).2, (hu i).1⟩, fun g a b => ?_⟩
  have h1 := he (g, a, b)
  have h2 : algebraMap O (U.R ⧸ I) (emb (r0 η Ψ g) a b) ∈ W.part (wt6 a - wt6 b) := by
    by_cases hab : wt6 a = wt6 b
    · rw [hab, sub_self, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (SetLike.GradedOne.one_mem : (1 : U.R ⧸ I) ∈ W.part 0)
    · rw [unitaryEmbedding_residualRep_eq_zero_of_weight_ne η Ψ g a b hab, map_zero]
      exact zero_mem _
  simpa only [sub_add_cancel] using add_mem h1 h2
end

section

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

private theorem mat_symm {R : Type} [CommRing R] (x : GG (m := 3) (R := R))
    (h2 : x * x = 1) (hx : x.right = -1) :
    x.mat = Jmat (R := R) 3 * x.matᵀ * Jmat (R := R) 3 := by
  have h : x.left * theta x.left = 1 := by
    have := congrArg SemidirectProduct.left h2
    rwa [SemidirectProduct.mul_left, hx, sgnAct_neg_one] at this
  have h' : x.left = (theta x.left)⁻¹ := eq_inv_of_mul_eq_one_left h
  have := theta_inv_val x.left
  rw [← h'] at this
  exact this

private theorem norm_iff {G R : Type} [Group G] [CommRing R] (c g₁ : G)
    (r : G →* GG (m := 3) (R := R)) (hc : c * c = 1)
    (hr : (r c).right = -1) : Normalised c g₁ r ↔ ∀ i, nEq c g₁ r i = 0 := by
  have hs := mat_symm (r c) (by rw [← map_mul, hc, map_one]) hr
  have hsym : ∀ i j, (r c).mat i j = (r c).mat j.rev i.rev := by
    intro i j
    conv_lhs => rw [hs]
    fin_cases j <;> simp [Matrix.mul_apply, Jmat, Fin.sum_univ_three]
  constructor
  · rintro ⟨h1, h2, h3⟩ i
    fin_cases i <;> simp [nEq, h1, h2, h3]
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have h4 := h 4
    have h5 := h 5
    have h6 := h 6
    have h7 := h 7
    simp [nEq, sub_eq_zero] at h0 h1 h2 h3 h4 h5 h6 h7
    have e12 : (r c).mat 1 2 = (r c).mat 0 1 := hsym 1 2
    have e21 : (r c).mat 2 1 = (r c).mat 1 0 := hsym 2 1
    have e22 : (r c).mat 2 2 = (r c).mat 0 0 := hsym 2 2
    refine ⟨?_, h6, h7⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h0, h1, h2, h3, h4, h5, e12, e21, e22]

private theorem nEq_map {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} (c g₁ : Γ) {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R']
    [Algebra O R'] [IsCO O R'] (r : GLift O η Ψ R) (f : R →ₐ[O] R') (i : Fin 8) :
    nEq c g₁ (r.map f).hom i = f (nEq c g₁ r.hom i) := by
  have hm : ∀ g, ((r.map f).hom g).mat = (r.hom g).mat.map f := fun g => GG.map_mat (f : R →+* R') (r.hom g)
  fin_cases i <;> simp [nEq, zmat, hm, map_sub, map_one]

private theorem ext_lemma {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (a b : GLift O η Ψ R) (h : ∀ x, (a.hom x).mat = (b.hom x).mat) : a = b := by
  apply GLift.ext
  apply MonoidHom.ext
  intro x
  apply SemidirectProduct.ext
  · exact Units.ext (h x)
  · rw [a.hasMult x, b.hasMult x]

private theorem gLift_map_hom_mat_eq_map {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R']
    [Algebra O R'] [IsCO O R'] (r : GLift O η Ψ R) (f : R →ₐ[O] R') (x : Γ) :
    ((r.map f).hom x).mat = (r.hom x).mat.map f :=
  GG.map_mat (f : R →+* R') (r.hom x)

private theorem comp_lemma_3 {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {R R' R'' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R']
    [Algebra O R'] [IsCO O R'] [CommRing R''] [Algebra O R''] [IsCO O R''] (r : GLift O η Ψ R)
    (f : R →ₐ[O] R') (g : R' →ₐ[O] R'') : r.map (g.comp f) = (r.map f).map g := by
  apply ext_lemma
  intro x
  rw [gLift_map_hom_mat_eq_map, gLift_map_hom_mat_eq_map, gLift_map_hom_mat_eq_map]
  ext i j
  simp

private theorem gLift_map_id {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (r : GLift O η Ψ R) : r.map (AlgHom.id O R) = r := by
  apply ext_lemma
  intro x
  rw [gLift_map_hom_mat_eq_map]
  ext i j
  simp

theorem UpperTheory.exists_surjection_univ_normCond_ker_span_nEq :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ] {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {P : GCond O η Ψ} (c g₁ : Γ)
          (B : Univ P) (S : Univ (NormCond c g₁ P)), c * c = 1 → η c = -1 →
          ∃ p : B.R →ₐ[O] S.R, Function.Surjective p ∧ B.r.map p = S.r ∧ RingHom.ker p = Ideal.span (Set.range (nEq c g₁ B.r.hom)) := by
  intro O _ _ Γ _ _ η Ψ P c g₁ B S hc hη
  have hr : ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (r : GLift O η Ψ R),
      (r.hom c).right = -1 := fun R _ _ _ r => by rw [r.hasMult c, hη]
  have hNS : NormCond c g₁ P S.R S.r := by
    have h := (S.rep S.R).1 (AlgHom.id O S.R)
    rwa [gLift_map_id] at h
  obtain ⟨p, hp, -⟩ := (B.rep S.R).2 S.r hNS.2
  have hI : Ideal.span (Set.range (nEq c g₁ B.r.hom)) ≤ RingHom.ker p := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    show p (nEq c g₁ B.r.hom i) = 0
    rw [← nEq_map, hp]
    exact (norm_iff c g₁ S.r.hom hc (hr _ S.r)).1 hNS.1 i
  set I := Ideal.span (Set.range (nEq c g₁ B.r.hom)) with hIdef
  haveI : Nontrivial (B.R ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (RingHom.ker_ne_top _) hI)
  haveI : IsCO O (B.R ⧸ I) := co_quot O B.R (B.R ⧸ I) (Ideal.Quotient.mkₐ O I) (Ideal.Quotient.mkₐ_surjective O I)
  have hNq : NormCond c g₁ P (B.R ⧸ I) (B.r.map (Ideal.Quotient.mkₐ O I)) := by
    refine ⟨(norm_iff c g₁ _ hc (hr _ _)).2 (fun i => ?_), (B.rep _).1 _⟩
    rw [nEq_map]
    show Ideal.Quotient.mk I _ = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)
  obtain ⟨s, hs, -⟩ := (S.rep (B.R ⧸ I)).2 _ hNq
  have hsp : s.comp p = Ideal.Quotient.mkₐ O I := by
    obtain ⟨u, -, hu⟩ := (B.rep (B.R ⧸ I)).2 _ hNq.2
    have e1 := hu (s.comp p) (by
      show GLift.map (s.comp p) B.r = _
      rw [comp_lemma_3, hp, hs])
    have e2 := hu (Ideal.Quotient.mkₐ O I) rfl
    rw [e1, e2]
  have hker : RingHom.ker p = I := by
    refine le_antisymm (fun x hx => ?_) hI
    have h0 : Ideal.Quotient.mkₐ O I x = 0 := by
      rw [← hsp, AlgHom.comp_apply, RingHom.mem_ker.1 hx, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.1 h0
  have hI' : ∀ a ∈ I, p a = 0 := fun a ha => RingHom.mem_ker.1 (hI ha)
  let p' := Ideal.Quotient.liftₐ I p hI'
  have hp'q : ∀ z, p' (Ideal.Quotient.mkₐ O I z) = p z := fun z => by
    show Ideal.Quotient.lift I (p : B.R →+* S.R) hI' (Ideal.Quotient.mk I z) = p z
    exact Ideal.Quotient.lift_mk I _ _
  have hpq : p'.comp (Ideal.Quotient.mkₐ O I) = p := AlgHom.ext hp'q
  have hid : p'.comp s = AlgHom.id O S.R := by
    obtain ⟨u, -, hu⟩ := (S.rep S.R).2 S.r hNS
    have e1 := hu (p'.comp s) (by
      show GLift.map (p'.comp s) S.r = S.r
      rw [comp_lemma_3, hs, ← comp_lemma_3, hpq, hp])
    have e2 := hu (AlgHom.id O S.R) (gLift_map_id _)
    rw [e1, e2]
  refine ⟨p, fun y => ?_, hp, hker⟩
  obtain ⟨z, hz⟩ := Ideal.Quotient.mkₐ_surjective O I (s y)
  refine ⟨z, ?_⟩
  rw [← hp'q, hz]
  exact congrArg (fun f => f y) hid
end
