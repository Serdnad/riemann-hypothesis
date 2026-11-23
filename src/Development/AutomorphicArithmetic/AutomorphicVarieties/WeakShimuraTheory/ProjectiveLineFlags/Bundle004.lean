module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicMat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.ThFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ConjPlace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CpSmul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.GspForm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.LevEps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.TraceSwap
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

private theorem up_diag_mul {R : Type} [CommRing R] {A B : M4 R} (hA : IsUp A) (hB : IsUp B) (i : Fin 4) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)
  rcases lt_or_gt_of_ne hj with h | h
  · rw [hA i j h, zero_mul]
  · rw [hB j i h, mul_zero]

private theorem low_left {R : Type} [CommRing R] {N : M4 R} (h : IsLow N) : adj N * N = 1 := by
  have := h.1
  rwa [IsGSp, one_smul] at this

private theorem pair_psi_one {O Γ R : Type} [CommRing O] [Group Γ] [CommRing R] {Φ : Fr O Γ} {a : O →+* R}
    {Q : PD Φ.ι Γ R} (hQ : Φ.IsPair a Q) (v : Φ.ι) (i : Fin 4) : Q.ψ v i 1 = 1 := by
  rw [PD.ψ, map_one, mul_one, low_left (hQ.low v), Matrix.one_apply_eq]

private theorem pair_psi_mul {O Γ R : Type} [CommRing O] [Group Γ] [CommRing R] {Φ : Fr O Γ} {a : O →+* R}
    {Q : PD Φ.ι Γ R} (hQ : Φ.IsPair a Q) (v : Φ.ι) (i : Fin 4) {s t : Γ} (hs : s ∈ Φ.Gv v) (ht : t ∈ Φ.Gv v) :
    Q.ψ v i (s * t) = Q.ψ v i s * Q.ψ v i t := by
  rw [PD.ψ, PD.ψ, PD.ψ, ← up_diag_mul (hQ.flag v s hs) (hQ.flag v t ht), map_mul]
  have h1 : Q.n v * adj (Q.n v) = 1 := mul_eq_one_comm.1 (low_left (hQ.low v))
  have h2 : adj (Q.n v) * Q.r s * Q.n v * (adj (Q.n v) * Q.r t * Q.n v) =
      adj (Q.n v) * Q.r s * (Q.n v * adj (Q.n v)) * Q.r t * Q.n v := by
    simp only [mul_assoc]
  rw [h2, h1, mul_one, mul_assoc (adj (Q.n v)) (Q.r s)]

private theorem hasFlag_push {H A B : Type} [Group H] [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B)
    {r : H →* GL (Fin n) A} {κ : Fin n → H →* Aˣ} (h : W.HasFlag r κ) :
    W.HasFlag (W.pushRep f r) fun i => W.pushCh f (κ i) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨Matrix.GeneralLinearGroup.map f g, fun s => ?_⟩
  have key : ∀ i j, (Matrix.GeneralLinearGroup.map f g * W.pushRep f r s * (Matrix.GeneralLinearGroup.map f g)⁻¹ :
      GL (Fin n) B) i j = f ((g * r s * g⁻¹ : GL (Fin n) A) i j) := by
    intro i j
    rw [MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul]
    rfl
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [key, (hg s).1 i j hij, map_zero]
  · rw [key, (hg s).2 i]
    rfl

theorem UpperTheory.V.Ws.P1.psiEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (R : Type) [CommRing R] [Algebra c'.O R] (Q : PD T.ι (G T.F Ω) R) (ρ : K.V.frame.G₀ →* GL (Fin 4) R), (T.fr ∅).IsPair ((algebraMap c'.O R).comp (inc h)) Q → K.IsRho ρ Q →
          ∃ ψ : ∀ v : K.V.frame.Vl, Fin 4 → K.V.frame.Gv v →* Rˣ, K.IsPsi ψ Q ∧ ∀ (R' : Type) [CommRing R'] (f : R →+* R') (v : K.V.frame.Vl),
            W.HasFlag (W.pushRep f (ρ.comp (K.V.frame.φ v))) fun i => W.pushCh f (ψ v i) := by
  intro Ω _ _ _ l _ c D T c' h K R _ _ Q ρ hQ hρ
  have hd : ∀ (v : W.Vl l T.L) (g : Dec (F := T.L) (K.s.A v)), resLe T.F_le g ∈ (T.fr ∅).Gv (K.e v) := by
    intro v g
    have h1 : (g : G T.L Ω) ∈ Dec (F := T.L) (T.pl (K.e v)) := by
      rw [← K.hA]; exact g.2
    exact h1
  let p : ∀ v : W.Vl l T.L, Fin 4 → Dec (F := T.L) (K.s.A v) →* R := fun v i =>
    { toFun := fun g => algebraMap c'.O R (K.κ g) * Q.ψ (K.e v) i (resLe T.F_le g)
      map_one' := by
        rw [OneMemClass.coe_one, map_one, map_one, Units.val_one, map_one, one_mul]
        exact pair_psi_one (Φ := T.fr ∅) hQ (K.e v) i
      map_mul' := fun g g' => by
        have h2 := pair_psi_mul (Φ := T.fr ∅) hQ (K.e v) i (hd v g) (hd v g')
        rw [Subgroup.coe_mul, map_mul, map_mul, Units.val_mul, map_mul]
        erw [h2]
        exact mul_mul_mul_comm _ _ _ _ }
  refine ⟨fun v i => (p v i).toHomUnits, fun v i g => rfl, fun R' _ f v => hasFlag_push f ?_⟩
  have h1 : adj (Q.n (K.e v)) * Q.n (K.e v) = 1 := low_left (hQ.low (K.e v))
  refine ⟨⟨adj (Q.n (K.e v)), Q.n (K.e v), h1, mul_eq_one_comm.mp h1⟩, fun s => ?_⟩
  have key : ∀ i j, ((⟨adj (Q.n (K.e v)), Q.n (K.e v), h1, mul_eq_one_comm.mp h1⟩ : GL (Fin 4) R) *
      (ρ.comp (K.V.frame.φ v)) s *
      (⟨adj (Q.n (K.e v)), Q.n (K.e v), h1, mul_eq_one_comm.mp h1⟩ : GL (Fin 4) R)⁻¹ : GL (Fin 4) R) i j =
      algebraMap c'.O R (K.κ s.1) *
        (adj (Q.n (K.e v)) * Q.r (resLe T.F_le s.1) * Q.n (K.e v)) i j := by
    intro i j
    change (adj (Q.n (K.e v)) * W.mat ρ (K.V.pr s.1) * Q.n (K.e v)) i j = _
    rw [hρ, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [key]
    have := hQ.flag (K.e v) _ (hd v s) i j hij
    erw [this]
    exact mul_zero _
  · rw [key]
    rfl
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem scale_pt {A B R : Type} [CommRing A] [CommRing B] [CommRing R] {n : ℕ} (i : B →+* A)
    (hi : Function.Injective i) (y : A →+* R) (p : B[X]) (M : Matrix (Fin n) (Fin n) A) (hp : p.map i = M.charpoly)
    (b : B) : (p.scaleRoots b).map (y.comp i) = (y (i b) • M.map y).charpoly := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  have h1 : i p.leadingCoeff = 1 := by
    rw [← leadingCoeff_map_of_injective hi, hp, (Matrix.charpoly_monic M).leadingCoeff]
  rw [map_scaleRoots _ _ _ (by simp [h1]), (UpperTheory.V.Ws.P1.cpSmul _ _).1, ← Polynomial.map_map, hp, Matrix.charpoly_map]
  rfl

theorem UpperTheory.V.Ws.P1.mapsPt :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (φ : B.B →ₐ[c'.O] X.B), K.IsPhi X 0 B φ →
          ∀ (R : Type) [CommRing R] [Algebra c'.O R] (y : X.A →ₐ[c'.O] R) (ρ : K.V.frame.G₀ →* GL (Fin 4) R) (ψ : ∀ v : K.V.frame.Vl, Fin 4 → K.V.frame.Gv v →* Rˣ),
          K.IsRho ρ (X.P.map (y : X.A →+* R)) → K.IsPsi ψ (X.P.map (y : X.A →+* R)) →
          B.u.Maps (((y : X.A →+* R).comp (algebraMap X.B X.A)).comp (φ : B.B →+* X.B)) (W.GDet.ofRep (W.mat ρ)) ψ := by
  intro Ω _ _ _ l _ c D T c' h K X B φ hφ R _ _ y ρ ψ hρ hψ
  have hs : ∀ a : c'.O, (y : X.A →+* R) (algebraMap X.B X.A (algebraMap c'.O X.B a)) = algebraMap c'.O R a := by
    intro a
    rw [← IsScalarTower.algebraMap_apply]
    exact y.commutes a
  refine ⟨UpperTheory.V.Ws.P1.detExt _ _ _ fun g0 => ?_, fun v i => ?_⟩
  · obtain ⟨g, rfl⟩ := (UpperTheory.V.Ws.phiKer K.V).1 g0
    refine Eq.trans ?_ ((AlgebraTools.Det.repApi _).2.1 _).symm
    rw [← Polynomial.map_map]
    refine (congrArg (Polynomial.map _) (hφ.1 g)).trans ?_
    rw [scale_pt _ X.inj _ _ _ (X.cp_map _), hs, pow_zero, mul_one]
    exact congrArg Matrix.charpoly (hρ g).symm
  · refine MonoidHom.ext fun g => Units.ext ?_
    have hd0 : ∀ (v : W.Vl l T.L) (g : Dec (F := T.L) (K.s.A v)), resLe T.F_le g ∈ Dec (F := T.F) (T.pl (K.e v)) := by
      intro v g
      rw [← K.hA v]; exact g.2
    have hd := hd0 v g
    refine Eq.trans ?_ (hψ v i g).symm
    refine (congrArg (fun b => (y : X.A →+* R) (algebraMap X.B X.A b)) (hφ.2 v i g)).trans ?_
    simp only [pow_zero, mul_one]
    rw [map_mul, map_mul, hs, X.ψ_map _ _ _ hd]
    exact congrArg _ ((UpperTheory.V.Ws.sxPdMap (Φ := T.fr ∅) ((algebraMap c'.O X.A).comp (inc h)) (y : X.A →+* R) X.P).1 _ _ _).symm
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.P1.redDet :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (k : Type) [Field k] [Algebra (ResidueField c'.O) k] [Algebra c'.O k] [IsScalarTower c'.O (ResidueField c'.O) k] (Q : PD T.ι (G T.F Ω) (PowerSeries k)), T.PsPair h k Q → ∀ ρ : K.V.frame.G₀ →* GL (Fin 4) (PowerSeries k), K.IsRho ρ Q →
          (W.GDet.ofRep (W.mat ρ)).map (PowerSeries.constantCoeff : PowerSeries k →+* k) = K.r.Dbar.map (algebraMap (ResidueField c'.O) k) := by
  intro Ω _ _ _ l _ c D T c' h K k _ _ _ _ Q hQ ρ hρ
  have hc : ∀ a : c'.O, PowerSeries.constantCoeff (algebraMap c'.O (PowerSeries k) a) = algebraMap c'.O k a := by
    intro a
    first
      | rfl
      | simp
  rw [W.Resid.Dbar, (AlgebraTools.Det.repApi (W.diagRep K.r.chib)).2.2.2.2.2.1 (algebraMap (ResidueField c'.O) k)]
  apply P1.detExt
  intro g
  rw [(AlgebraTools.Det.repApi (W.mat ρ)).2.1, (AlgebraTools.Det.repApi _).2.1]
  obtain ⟨g', hg'⟩ := (phiKer K.V).1 g
  subst hg'
  have hlc : ∀ M : Matrix (Fin 4) (Fin 4) (PowerSeries k),
      (PowerSeries.constantCoeff : PowerSeries k →+* k) M.charpoly.leadingCoeff ≠ 0 := by
    intro M
    rw [(Matrix.charpoly_monic M).leadingCoeff, map_one]
    exact one_ne_zero
  rw [hρ g', (P1.cpSmul _ _).1, map_scaleRoots _ _ _ (hlc _), hQ.cp,
    (P1.cpSmul _ (0 : Matrix (Fin 4) (Fin 4) k)).2]
  change _ = ((Matrix.diagonal fun i => ((K.r.chib i (K.V.pr g') : (ResidueField c'.O)ˣ) : ResidueField c'.O)).map
    (algebraMap (ResidueField c'.O) k)).charpoly
  rw [Matrix.diagonal_map (map_zero _), Matrix.charpoly_diagonal]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [K.chib i g', hc, ← IsLocalRing.ResidueField.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply (↥c'.O) (ResidueField ↥c'.O) k, map_mul (algebraMap c'.O k)]
  rfl
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem ac_map {Γ R S : Type} [TopologicalSpace Γ] [CommRing R] [CommRing S] {I : Ideal R} {J : Ideal S}
    (φ : R →+* S) (hφ : I ≤ J.comap φ) {f : Γ → R} (hf : AdicCont I f) : AdicCont J fun g => φ (f g) := by
  intro N
  have hN : I ^ N ≤ (J ^ N).comap φ := (Ideal.pow_right_mono hφ N).trans (Ideal.le_comap_pow φ N)
  exact (hf N).comp (Ideal.quotientMap (J ^ N) φ hN)

private theorem ac_mul {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f g : Γ → R}
    (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun x => f x * g x := by
  intro N
  have h := IsLocallyConstant.comp₂ (hf N) (hg N) (· * ·)
  convert h using 1
  funext x
  simp [map_mul]

private theorem ac_comp {Γ Γ' R : Type} [TopologicalSpace Γ] [TopologicalSpace Γ'] [CommRing R] {I : Ideal R} {f : Γ → R}
    (hf : AdicCont I f) {u : Γ' → Γ} (hu : Continuous u) : AdicCont I fun x => f (u x) :=
  fun N => (hf N).comp_continuous hu

theorem UpperTheory.V.Ws.P1.redPsi :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (k : Type) [Field k] [Algebra (ResidueField c'.O) k] [Algebra c'.O k] [IsScalarTower c'.O (ResidueField c'.O) k] (Q : PD T.ι (G T.F Ω) (PowerSeries k)), T.PsPair h k Q → ∀ ψ : ∀ v : K.V.frame.Vl, Fin 4 → K.V.frame.Gv v →* (PowerSeries k)ˣ, K.IsPsi ψ Q →
          (∀ v i, W.pushCh (PowerSeries.constantCoeff : PowerSeries k →+* k) (ψ v i) = W.pushCh (algebraMap (ResidueField c'.O) k) (K.r.psib v i)) ∧
          ∀ v i, AdicCont (maximalIdeal (PowerSeries k)) fun g => ((ψ v i g : (PowerSeries k)ˣ) : PowerSeries k) := by
  intro Ω _ _ _ l _ c D T c' h K k _ _ _ _ Q hQ ψ hψ
  obtain ⟨-, -, hcont, -, hres, hdec⟩ := P1.towerGal D T
  have hc : ∀ a : c'.O, PowerSeries.constantCoeff (algebraMap c'.O (PowerSeries k) a) = algebraMap c'.O k a := by
    intro a
    first
      | rfl
      | simp
  constructor
  · intro v i
    ext g
    simp only [W.pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
    rw [hψ v i g, map_mul, K.psib v i g, K.chib i]
    obtain ⟨g, hg0⟩ := (show ↥(Dec (K.s.A ↑(show W.Vl l T.L from v))) from g)
    have hg : (resLe T.F_le) g ∈ Dec (T.pl (K.e v)) := by
      rw [← K.hA v]
      exact (hdec _ _).1.2 hg0
    rw [hQ.psi _ _ _ hg, (hres g).1, hc, map_mul (residue _), map_mul,
      ← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  · intro v i
    have hφ : maximalIdeal c'.O ≤ (maximalIdeal (PowerSeries k)).comap (algebraMap c'.O (PowerSeries k)) := by
      intro a ha
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        PowerSeries.isUnit_iff_constantCoeff, hc, hQ.loc a ha]
      exact not_isUnit_zero
    have h1 : AdicCont (maximalIdeal (PowerSeries k))
        (fun g : Dec (K.s.A ↑(show W.Vl l T.L from v)) => algebraMap c'.O (PowerSeries k) ↑(K.κ g.1)) :=
      ac_comp (ac_map _ hφ K.κ_cont) continuous_subtype_val
    have h2 : AdicCont (maximalIdeal (PowerSeries k))
        (fun g : Dec (K.s.A ↑(show W.Vl l T.L from v)) => Q.ψ (K.e v) i (resLe T.F_le g.1)) := by
      have := (sxAdicMat _ _ hQ.cont).2 (adj (Q.n (K.e v))) (Q.n (K.e v)) i i
      exact ac_comp this (hcont.comp continuous_subtype_val)
    have key := ac_mul h1 h2
    have e : (fun g : Dec (K.s.A ↑(show W.Vl l T.L from v)) => ((ψ v i g : (PowerSeries k)ˣ) : PowerSeries k)) =
        fun g => algebraMap c'.O (PowerSeries k) ↑(K.κ g.1) * Q.ψ (K.e v) i (resLe T.F_le g.1) :=
      funext fun g => hψ v i g
    show AdicCont _ (fun g : Dec (K.s.A ↑(show W.Vl l T.L from v)) => ((ψ v i g : (PowerSeries k)ˣ) : PowerSeries k))
    rw [e]
    exact key
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Ws.P1.psPair_fac {Λ B k : Type} [CommRing Λ] [IsLocalRing Λ] [CommRing B] [Algebra Λ B] [IsCO Λ B]
    [Field k] [Algebra Λ k] (φ : B →+* k) (h1 : ∀ a, φ (algebraMap Λ B a) = algebraMap Λ k a)
    (h2 : ∀ b ∈ maximalIdeal B, φ b = 0) :
    ∃ j : ResidueField Λ →+* k, (∀ a, j (residue Λ a) = algebraMap Λ k a) ∧ ∀ b, j (res Λ B b) = φ b := by
  have h3 : ∀ a ∈ maximalIdeal Λ, algebraMap Λ k a = 0 := fun a ha => by
    rw [← h1]
    exact h2 _ fun hu => ha (IsLocalHom.map_nonunit a hu)
  refine ⟨Ideal.Quotient.lift _ (algebraMap Λ k) h3, fun a => rfl, fun b => ?_⟩
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := Λ) b
  have e1 : res Λ B b = residue Λ a := by
    have := (res_eq_zero_iff Λ B _).2 ha
    rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this
  have e2 := h2 _ ha
  rw [map_sub, sub_eq_zero, h1] at e2
  rw [e1, e2]
  rfl

private theorem UpperTheory.V.Ws.P1.psPair_cont {Γ A R : Type} [TopologicalSpace Γ] [CommRing A] [CommRing R] (f : A →+* R)
    {I : Ideal A} {J : Ideal R} (hI : I.map f ≤ J) {u : Γ → A} (hu : AdicCont I u) : AdicCont J fun g => f (u g) := by
  intro N
  have hN : I ^ N ≤ (J ^ N).comap f := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hI N
  exact (hu N).comp (Ideal.quotientMap (J ^ N) f hN)

theorem UpperTheory.V.Ws.P1.psPair :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (k : Type) [Field k] [Algebra c'.O k] (y : X.A →ₐ[c'.O] PowerSeries k),
          (∀ b ∈ maximalIdeal X.B, PowerSeries.constantCoeff (y (algebraMap X.B X.A b)) = 0) → T.PsPair h k (X.P.map (y : X.A →+* PowerSeries k)) := by
  intro Ω _ _ _ l _ c D T c' h X k _ _ y hy
  let φ : X.B →+* k := ((PowerSeries.constantCoeff : PowerSeries k →+* k).comp (y : X.A →+* PowerSeries k)).comp (algebraMap X.B X.A)
  have hφ : ∀ b, φ b = PowerSeries.constantCoeff (y (algebraMap X.B X.A b)) := fun b => rfl
  have h1 : ∀ a, φ (algebraMap c'.O X.B a) = algebraMap c'.O k a := fun a => by
    rw [hφ, ← IsScalarTower.algebraMap_apply, AlgHom.commutes, PowerSeries.algebraMap_apply, PowerSeries.constantCoeff_C]
  obtain ⟨j, hj1, hj2⟩ := UpperTheory.V.Ws.P1.psPair_fac φ h1 hy
  obtain ⟨hψ, hp, -⟩ := sxPdMap (Φ := T.fr ∅) ((algebraMap c'.O X.A).comp (inc h)) (y : X.A →+* PowerSeries k) X.P
  refine ⟨fun a ha => ?_, ?_, fun i i' => ?_, fun g => ?_, fun v i s hs => ?_⟩
  · rw [← hj1, (residue_eq_zero_iff a).2 ha, map_zero]
  · have := hp X.pair
    rwa [← RingHom.comp_assoc, AlgHom.comp_algebraMap] at this
  · refine UpperTheory.V.Ws.P1.psPair_cont (y : X.A →+* PowerSeries k) ?_ (X.cont i i')
    rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
    have := hy b hb
    intro hu
    exact hu.ne_zero this
  · have e : (X.P.map (y : X.A →+* PowerSeries k)).r g = (X.P.r g).map (y : X.A →+* PowerSeries k) := rfl
    have e2 : φ = j.comp (res c'.O X.B : X.B →+* ResidueField c'.O) := RingHom.ext fun b => (hj2 b).symm
    rw [e, Matrix.charpoly_map, ← X.cp_map, Polynomial.map_map, Polynomial.map_map]
    show (X.cp g).map φ = _
    rw [e2, ← Polynomial.map_map, X.cp_red, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, map_X, map_C, hj1]
    rfl
  · have e1 := hψ v i s
    rw [← X.ψ_map v i s hs] at e1
    have e2 := hj2 (X.ψ v i s)
    rw [X.ψ_red v i s hs, hj1] at e2
    exact (congrArg PowerSeries.constantCoeff e1).trans e2.symm
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem transpose_form_mul_involution {R : Type} [CommRing R] (J C : M4 R) (hJ : J.transpose = -J) (hC : C * C = 1)
    (h : C.transpose * J * C = -J) : (J * C).transpose = J * C := by
  have hT : C.transpose * J = -(J * C) := by
    calc C.transpose * J = C.transpose * J * (C * C) := by rw [hC, Matrix.mul_one]
      _ = -J * C := by rw [← Matrix.mul_assoc, h]
      _ = -(J * C) := Matrix.neg_mul _ _
  rw [Matrix.transpose_mul, hJ, Matrix.mul_neg, hT, neg_neg]

private theorem hermOrthExt_gram_entry_eq_single_and_frame_gram_eq_zero {R : Type} [CommRing R] (J C A : M4 R) (hC : C * C = 1) (x y ν : R)
    (h : A.transpose * J * A = ν • J) :
    (x • A).transpose * (J * C) * (y • (C * A * C)) = (x * y * ν) • (J * C) := by
  have hA : A.transpose * (J * C) * (C * A * C) = ν • (J * C) := by
    calc A.transpose * (J * C) * (C * A * C) = A.transpose * J * (C * C) * A * C := by
          simp only [Matrix.mul_assoc]
      _ = (ν • J) * C := by rw [hC, Matrix.mul_one, h]
      _ = ν • (J * C) := Matrix.smul_mul _ _ _
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, hA, smul_smul, smul_smul]
  congr 1
  ring

private theorem unit_aux {R : Type} [CommRing R] (e : Rˣ) (z : R) (h : z * (e : R) ^ 3 = 1) :
    ((e ^ (1 - ((4 : ℕ) : ℤ)) : Rˣ) : R) = z := by
  have h3 : ((1 : ℤ) - ((4 : ℕ) : ℤ)) = -3 := by norm_num
  rw [h3, zpow_neg, zpow_ofNat]
  rw [eq_comm]
  exact Units.eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using h)

private theorem exists_gl4_form_mul_involution {R : Type} [CommRing R] (J : (M4 R)ˣ) (C : M4 R) (hC : C * C = 1) :
    ∃ P : GL (Fin 4) R, (P : Matrix (Fin 4) (Fin 4) R) = (J : M4 R) * C := by
  exact ⟨J * ⟨C, C, hC, hC⟩, rfl⟩

theorem UpperTheory.V.Ws.P1.formEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (R : Type) [CommRing R] [Algebra c'.O R] (Q : PD T.ι (G T.F Ω) R) (ρ : K.V.frame.G₀ →* GL (Fin 4) R), (T.fr ∅).IsPair ((algebraMap c'.O R).comp (inc h)) Q → K.IsRho ρ Q →
          ∃ P : GL (Fin 4) R, (P : Matrix (Fin 4) (Fin 4) R).transpose = P ∧ K.V.frame.IsForm c'.O 4 ρ P := by
  intro Ω _ _ _ l _ c D T hF hD c' h K R _ _ Q ρ hQ hρ
  obtain ⟨J, hJ, hG⟩ := P1.gspForm R
  obtain ⟨cF, hc, hcc⟩ := P1.ccEx D T K.s
  obtain ⟨h2, hν⟩ := (X1.thFacts D T hF hD).2.2.1 cF hc
  obtain ⟨e1, -, -, e4⟩ := P1.levEps K.V
  have hC : Q.r cF * Q.r cF = 1 := by rw [← map_mul, h2, map_one]
  have hCJ : (Q.r cF).transpose * (J : M4 R) * Q.r cF = -(J : M4 R) := by
    rw [hG _ _ (hQ.mult cF), hν]
    simp
  obtain ⟨P, hP⟩ := exists_gl4_form_mul_involution J _ hC
  refine ⟨P, by rw [hP]; exact transpose_form_mul_involution _ _ hJ hC hCJ, fun x => ?_⟩
  obtain ⟨g, rfl⟩ := (phiKer K.V).1 x
  obtain ⟨g', hg, hg'⟩ := hcc g
  have hk := congrArg (algebraMap c'.O R) (K.conj g g' hg).1
  have h3 : Q.r (resLe T.F_le g') = Q.r cF * Q.r (resLe T.F_le g) * Q.r cF := by
    rw [hg', inv_eq_of_mul_eq_one_right h2, map_mul, map_mul]
  have h4 := hermOrthExt_gram_entry_eq_single_and_frame_gram_eq_zero _ _ _ hC (algebraMap c'.O R (K.κ g)) (algebraMap c'.O R (K.κ g')) _
    (hG _ _ (hQ.mult (resLe T.F_le g)))
  rw [map_mul, map_mul, map_mul, map_pow, map_one, ← e4 c'.O R g] at hk
  rw [e1 g g' hg, hρ g, hρ g', h3, unit_aux _ _ hk, hP]
  exact h4
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem trace_of_cp {R k : Type} [CommRing R] [Field k] (f : R →+* k) (M : Matrix (Fin 4) (Fin 4) R) (a : Fin 4 → k)
    (h : M.charpoly.map f = ∏ i, (X - C (a i))) : f M.trace = ∑ i, a i := by
  have h1 := Matrix.trace_eq_neg_charpoly_nextCoeff (M.map f)
  rw [Matrix.charpoly_map, h, Polynomial.prod_X_sub_C_nextCoeff, neg_neg] at h1
  rw [← h1]

  simp [Matrix.trace, map_sum]

theorem UpperTheory.V.Ws.P1.irrL :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (x : W.Point K.r) (Q : PD T.ι (G T.F Ω) x.A), T.PsPair h x.K Q → K.IsRho x.ρ Q → Irr (mapRep (algebraMap x.A x.Fr) Q.r) →
          U3.MatIrr ⊤ (W.mat (W.pushRep (algebraMap x.Fr x.Fb) x.ρF)) := by
  intro Ω _ _ _ l hl c D T c' h K x Q hP hρ hI
  obtain ⟨hrange, -, -, hidx, hres, -⟩ := UpperTheory.V.Ws.P1.towerGal D T
  have hsurj := (UpperTheory.V.Ws.phiKer K.V).1
  have htow : ∀ a : c'.O, algebraMap (ResidueField c'.O) x.K (residue c'.O a) = algebraMap c'.O x.K a :=
    fun a => (IsScalarTower.algebraMap_apply c'.O (ResidueField c'.O) x.K a).symm
  have hinj : Function.Injective (algebraMap x.A x.Fr) := IsFractionRing.injective x.A x.Fr
  have h2 : (2 : x.Fr) ≠ 0 := by
    haveI := (UpperTheory.V.Ws.P1.coefRes c').2.1
    intro h0
    have h1 : (2 : x.A) = 0 := hinj (by rw [map_ofNat, map_zero]; exact h0)
    have h3 : (2 : x.K) = 0 := by
      have := congrArg (PowerSeries.constantCoeff : PowerSeries x.K →+* x.K) h1
      rwa [map_ofNat, map_zero] at this
    have h4 : ((2 : ℕ) : ResidueField c'.O) = 0 :=
      (algebraMap (ResidueField c'.O) x.K).injective (by rw [map_natCast, map_zero]; exact_mod_cast h3)
    exact K.s.odd ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 ((CharP.cast_eq_zero_iff _ l 2).1 h4))
  let χ : Fin (3 + 1) → G T.F Ω →* x.Kˣ := fun i =>
    W.pushCh ((algebraMap c'.O x.K).comp (inc h)) ((chi D T.pr i).comp (resQ T.F))
  have hχ : Function.Injective fun i => (χ i).comp T.GalL.subtype := by
    intro i j hij
    refine K.r.chib_inj (MonoidHom.ext fun y => ?_)
    obtain ⟨g, rfl⟩ := hsurj y
    have hg : resLe T.F_le g ∈ T.GalL := hrange ▸ ⟨g, rfl⟩
    have e : algebraMap c'.O x.K (inc h (chi D T.pr i (resQ T.L g))) =
        algebraMap c'.O x.K (inc h (chi D T.pr j (resQ T.L g))) := by
      have e1 := congrArg Units.val (DFunLike.congr_fun hij ⟨_, hg⟩)
      rw [← (hres g).1]
      exact e1
    apply Units.ext
    apply (algebraMap (ResidueField c'.O) x.K).injective
    rw [K.chib, K.chib, htow, htow, map_mul, map_mul, e]
  have htr : T.GalL = ⊤ ∨ ∃ g, g ∉ T.GalL ∧ (mapRep (algebraMap x.A x.Fr) Q.r g).trace ≠ 0 := by
    refine (UpperTheory.V.Ws.P1.trNe T.GalL χ hχ).imp id fun ⟨g, hg, hs⟩ => ⟨g, hg, fun h0 => hs ?_⟩
    have e1 : (Q.r g).trace = 0 := hinj (by
      rw [map_zero, ← h0]

      simp [Matrix.trace, map_sum])
    have e2 := trace_of_cp _ _ _ (hP.cp g)
    rw [e1, map_zero] at e2
    exact e2.symm
  have hM := UpperTheory.V.Ws.P1.irrTr (algebraMap x.Fr x.Fb) T.GalL _ h2 hI hidx htr
  intro U hW
  refine hM U fun y hy v hv => ?_
  rw [← hrange] at hy
  obtain ⟨g, rfl⟩ := hy
  have h5 := hW (K.V.pr g) trivial v hv
  let u : x.Fbˣ := Units.map (((algebraMap x.Fr x.Fb).comp ((algebraMap x.A x.Fr).comp (algebraMap c'.O x.A)) : c'.O →+* x.Fb) : c'.O →* x.Fb) (K.κ g)
  have e : W.mat (W.pushRep (algebraMap x.Fr x.Fb) x.ρF) (K.V.pr g) =
      (u : x.Fb) • mapRep (algebraMap x.Fr x.Fb) (mapRep (algebraMap x.A x.Fr) Q.r) (resLe T.F_le g) := by
    ext i j
    have e0 := congrFun (congrFun (hρ g) i) j
    show algebraMap x.Fr x.Fb (algebraMap x.A x.Fr (W.mat x.ρ (K.V.pr g) i j)) = _
    rw [e0, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul]
    rfl
  rw [e, Matrix.smul_mulVec] at h5
  exact (U.smul_mem_iff u.ne_zero).1 h5
end
