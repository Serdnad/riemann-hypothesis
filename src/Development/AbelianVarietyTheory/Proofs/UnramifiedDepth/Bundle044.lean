module

public import Formalism.IncomingBounds.Bundle002
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JetAt0ProdRename
public import ReciprocityTheory.DualLattices.Bundle012
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle036
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
public import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle033
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001

@[expose] public section

section

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem isUnit_of_map_eq_one {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (h : M.map (Ideal.Quotient.mk I) = 1) : IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have h1 : Ideal.Quotient.mk I M.det = Ideal.Quotient.mk I 1 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, h, Matrix.det_one, map_one]
  have h2 := IsAdicComplete.le_jacobson_bot I (Ideal.Quotient.eq.1 h1)
  have := Ideal.mem_jacobson_bot.1 h2 1
  simpa using this

private theorem splitEx_of_exact {K : Type} [CommRing K] {d r g : ℕ} (A : Matrix (Fin d) (Fin r) K)
    (B : Matrix (Fin g) (Fin d) K) (h0 : B * A = 0) (h1 : ∀ w, ∃ v, B *ᵥ v = w)
    (h2 : ∀ v, B *ᵥ v = 0 → ∃ t, A *ᵥ t = v) (h3 : ∀ t, A *ᵥ t = 0 → t = 0) : SplitEx A B := by
  choose v hv using h1
  let B' : Matrix (Fin d) (Fin g) K := Matrix.of fun i j => v (Pi.single j 1) i
  have hB : B * B' = 1 := by
    ext i j
    have := congrFun (hv (Pi.single j 1)) i
    rw [Matrix.one_apply, ← Pi.single_apply j (1 : K) i, ← this]
    rfl
  have h4 : ∀ j : Fin d, ∃ t, A *ᵥ t = (1 - B' * B) *ᵥ (Pi.single j 1) := fun j => h2 _ (by
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, ← Matrix.mul_assoc, hB, Matrix.mul_one, Matrix.one_mul, sub_self,
      Matrix.zero_mulVec])
  choose t ht using h4
  let A' : Matrix (Fin r) (Fin d) K := Matrix.of fun i j => t j i
  have hA : A * A' = 1 - B' * B := by
    ext i j
    have := congrFun (ht j) i
    rw [Matrix.mulVec_single_one] at this
    exact this
  refine ⟨h0, A', B', ?_, hB, by rw [hA]; simp⟩
  have h5 : A * (A' * A - 1) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hA, Matrix.sub_mul, Matrix.mul_assoc, h0]; simp
  rw [← sub_eq_zero]
  ext i j
  have := h3 ((A' * A - 1) *ᵥ Pi.single j 1) (by rw [Matrix.mulVec_mulVec, h5, Matrix.zero_mulVec])
  rw [Matrix.mulVec_single_one] at this
  exact congrFun this i

private theorem splitEx_lift {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R] {d r g : ℕ}
    (A : Matrix (Fin d) (Fin r) R) (B : Matrix (Fin g) (Fin d) R) (h0 : B * A = 0)
    (h : SplitEx (A.map (Ideal.Quotient.mk I)) (B.map (Ideal.Quotient.mk I))) : SplitEx A B := by
  obtain ⟨-, A1, B1, h1, h2, h3⟩ := h
  let A0 : Matrix (Fin r) (Fin d) R := A1.map (Function.surjInv Ideal.Quotient.mk_surjective)
  let B0 : Matrix (Fin d) (Fin g) R := B1.map (Function.surjInv Ideal.Quotient.mk_surjective)
  have hA0 : A0.map (Ideal.Quotient.mk I) = A1 := by
    ext i j; exact Function.surjInv_eq _ _
  have hB0 : B0.map (Ideal.Quotient.mk I) = B1 := by
    ext i j; exact Function.surjInv_eq _ _
  obtain ⟨U, hU⟩ := isUnit_of_map_eq_one I (A0 * A) (by rw [Matrix.map_mul, hA0, h1])
  obtain ⟨V, hV⟩ := isUnit_of_map_eq_one I (B * B0) (by rw [Matrix.map_mul, hB0, h2])
  obtain ⟨M, hM⟩ := isUnit_of_map_eq_one I (A * A0 + B0 * B) (by
    rw [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, hA0, hB0, h3])
  obtain ⟨B', hB', hB0'⟩ : ∃ B' : Matrix (Fin d) (Fin g) R, B * B' = 1 ∧ B0 = B' * V.val :=
    ⟨B0 * (V⁻¹).val, by rw [← Matrix.mul_assoc, ← hV]; simp, by rw [Matrix.mul_assoc]; simp⟩
  obtain ⟨A2, hA2⟩ : ∃ A2 : Matrix (Fin r) (Fin d) R, A2 * A = 1 :=
    ⟨(U⁻¹).val * A0, by rw [Matrix.mul_assoc, ← hU]; simp⟩
  have e1 : A2 * (1 - B' * B) * A = 1 := by
    rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_assoc, h0]; simp [hA2]
  have e2 : A2 * (1 - B' * B) * B' = 0 := by
    rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_assoc, hB']; simp
  refine ⟨h0, A2 * (1 - B' * B), B', e1, hB', ?_⟩
  generalize A2 * (1 - B' * B) = A' at e1 e2
  have p1 : (A * A' + B' * B) * A = A := by
    rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, e1, h0]; simp
  have p2 : (A * A' + B' * B) * B' = B' := by
    rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, e2, hB']; simp
  have p3 : (A * A' + B' * B) * M.val = 1 * M.val := by
    rw [hM, hB0', Matrix.mul_add, ← Matrix.mul_assoc, p1, Matrix.mul_assoc B', ← Matrix.mul_assoc _ B', p2,
      Matrix.one_mul]
  exact (Units.mul_left_inj M).1 p3

section Dual
variable {R : Type} [CommRing R] {K : Type} [CommRing K] [Algebra R K]

private def epsV {n : ℕ} (v : Fin n → K) : Fin n → DualNumber K := fun i => TrivSqZeroExt.inr (v i)

private theorem epsV_nil {n : ℕ} (v : Fin n → K) (i : Fin n) : IsNilpotent (epsV v i) :=
  ⟨2, by rw [pow_two]; exact TrivSqZeroExt.inr_mul_inr _ _ _⟩

private theorem epsV_zero {n : ℕ} : epsV (0 : Fin n → K) = 0 := by
  funext i; exact TrivSqZeroExt.inr_zero _

private theorem epsV_inj {n : ℕ} {v w : Fin n → K} (h : epsV v = epsV w) : v = w := by
  funext i; exact TrivSqZeroExt.inr_injective (congrFun h i)

private theorem nv_epsV {n m : ℕ} (φ : Fin m → PS R 1 n) (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0)
    (v : Fin n → K) : (fun j => nv (algebraMap R (DualNumber K)) (φ j) ![epsV v]) =
      epsV ((lin φ).map (algebraMap R K) *ᵥ v) := by
  funext j
  have h := (nv_calculus R (DualNumber K) (algebraMap R _) 1 n ![epsV v]
    (fun i j => by simpa using epsV_nil v j)).2.2.2.2.2
    (fun i j i' j' => by simp [epsV]) (φ j)
  rw [h, hφ, map_zero, zero_add, Fintype.sum_prod_type, Fin.sum_univ_one]
  simp only [epsV, Matrix.mulVec, dotProduct, TrivSqZeroExt.inr_sum, Matrix.map_apply, lin, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Algebra.smul_def, ← Algebra.smul_def, TrivSqZeroExt.inr_smul]
  rfl

private theorem kills_dual {I : Ideal R} {k : ℕ} (h : Kills I k K) : Kills I k (DualNumber K) := fun t ht => by
  rw [TrivSqZeroExt.algebraMap_eq_inl', h t ht, TrivSqZeroExt.inl_zero]

private theorem exists_char {X : Type} [AddCommGroup X] {r : ℕ} (β : Module.Basis (Fin r) ℤ X) (t : Fin r → K) :
    ∃ χ : Multiplicative X →* (DualNumber K)ˣ, ∀ j,
      (χ (Multiplicative.ofAdd (β j)) : DualNumber K) = 1 + epsV t j := by
  let u : Fin r → (DualNumber K)ˣ := fun j => (epsV_nil t j).isUnit_one_add.unit
  let f : X →ₗ[ℤ] Additive (DualNumber K)ˣ := β.constr ℤ fun j => Additive.ofMul (u j)
  refine ⟨AddMonoidHom.toMultiplicativeLeft f.toAddMonoidHom, fun j => ?_⟩
  have : f (β j) = Additive.ofMul (u j) := β.constr_basis ℤ _ j
  change ((Additive.toMul (f (β j)) : (DualNumber K)ˣ) : DualNumber K) = _
  rw [this]; rfl

private theorem eq_epsV {n : ℕ} (a : Fin n → DualNumber K) (h : ∀ i, (a i).fst = 0) :
    a = epsV fun i => (a i).snd := by
  funext i; ext <;> simp [epsV, h]

end Dual

theorem tangent_splitEx : ∀ (R : Type) [CommRing R] (I : Ideal R) [IsAdicComplete I R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B] (X : Type) [AddCommGroup X] (E : PtExt I G B X) (d g : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (x : Fam G d) (xB : Fam B g), NilChart G F.F x → NilChart B FB.F xB → ∀ (r : ℕ) (β : Module.Basis (Fin r) ℤ X) (J : Fin d → PS R 1 r) (Q : Fin g → PS R 1 d), (∀ j, MvPowerSeries.constantCoeff (J j) = 0) → (∀ j, MvPowerSeries.constantCoeff (Q j) = 0) → (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (a : Fin d → S), (∀ i, IsNilpotent (a i)) → E.q S h (x S a) = xB S (fun j => nv (algebraMap R S) (Q j) ![a])) → (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (χ : Multiplicative X →* Sˣ) (t : Fin r → S), (∀ i, IsNilpotent (t i)) → (∀ j, (χ (Multiplicative.ofAdd (β j)) : S) = 1 + t j) → E.i S h χ = x S (fun j => nv (algebraMap R S) (J j) ![t])) → SplitEx (lin J) (lin Q) := by
  intro R _ I _ G _ _ B _ _ X _ E d g F FB x xB hx hxB r β J Q hJ hQ hq hi
  have key : ∀ (K : Type) [CommRing K] [Algebra R K] (k : ℕ), Kills I k K →
      SplitEx ((lin J).map (algebraMap R K)) ((lin Q).map (algebraMap R K)) := by
    intro K _ _ k hK
    have hS : ∃ k, Kills I k (DualNumber K) := ⟨k, kills_dual hK⟩
    have hq' : ∀ v, E.q _ hS (x _ (epsV v)) = xB _ (epsV ((lin Q).map (algebraMap R K) *ᵥ v)) := fun v => by
      rw [hq _ hS _ (epsV_nil v), nv_epsV Q hQ]
    have hi' : ∀ (χ : Multiplicative X →* (DualNumber K)ˣ) t, (∀ j,
        (χ (Multiplicative.ofAdd (β j)) : DualNumber K) = 1 + epsV t j) →
        E.i _ hS χ = x _ (epsV ((lin J).map (algebraMap R K) *ᵥ t)) := fun χ t h => by
      rw [hi _ hS χ _ (epsV_nil t) h, nv_epsV J hJ]
    let ρ : DualNumber K →ₐ[R] K := TrivSqZeroExt.fstHom R K K
    let σ : K →ₐ[R] DualNumber K := TrivSqZeroExt.inlAlgHom R K K
    have hρσ : ρ.comp σ = AlgHom.id R K := by ext; rfl
    have hker : RingHom.ker ρ ^ 2 = ⊥ := by
      rw [pow_two, eq_bot_iff, Ideal.mul_le]
      intro a ha b hb
      have ha' : a.fst = 0 := ha
      have hb' : b.fst = 0 := hb
      rw [Ideal.mem_bot]
      ext <;> simp [ha', hb']
    have hred : ∀ {n : ℕ} (v : Fin n → K), (fun i => ρ (epsV v i)) = 0 := fun v => rfl
    refine splitEx_of_exact _ _ ?_ (fun w => ?_) (fun v hv => ?_) (fun t ht => ?_)
    · refine Matrix.ext_of_mulVec_single fun j => ?_
      obtain ⟨χ, hχ⟩ := exists_char β (Pi.single j (1 : K))
      have h1 := (E.exact _ hS _).2 ⟨χ, rfl⟩
      rw [hi' χ _ hχ, hq', ← hxB.zero, ← epsV_zero] at h1
      have h2 := epsV_inj (hxB.inj _ _ _ (epsV_nil _) (epsV_nil _) h1)
      rw [← Matrix.mulVec_mulVec, h2, Matrix.zero_mulVec]
    · obtain ⟨z, hz, hz'⟩ := E.lift _ hS K ρ σ hρσ hker (xB _ (epsV w))
        (by rw [hxB.nat _ _ _ _ (epsV_nil w), hred, hxB.zero])
      obtain ⟨a, ha, rfl⟩ := hx.surj _ K ρ σ hρσ ⟨2, hker⟩ z hz
      rw [eq_epsV a ha, hq'] at hz'
      exact ⟨_, epsV_inj (hxB.inj _ _ _ (epsV_nil _) (epsV_nil _) hz')⟩
    · have h1 := hq' v
      rw [hv, epsV_zero, hxB.zero] at h1
      obtain ⟨χ, hχ⟩ := (E.exact _ hS _).1 h1
      have h2 := E.i_nat _ K ρ hS ⟨k, hK⟩ χ
      rw [hχ, hx.nat _ _ _ _ (epsV_nil v), hred, hx.zero, ← map_one (E.i K ⟨k, hK⟩)] at h2
      have h3 := E.i_inj _ _ h2
      have h4 : ∀ j, ((χ (Multiplicative.ofAdd (β j)) : DualNumber K) - 1).fst = 0 := fun j => by
        have := congrArg Units.val (DFunLike.congr_fun h3 (Multiplicative.ofAdd (β j)))
        rw [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one, sub_eq_zero]
        exact this
      have h5 := hi' χ _ (fun j => (sub_eq_iff_eq_add'.1 (congrFun (eq_epsV _ h4) j)))
      rw [hχ] at h5
      exact ⟨_, (epsV_inj (hx.inj _ _ _ (epsV_nil _) (epsV_nil _) h5)).symm⟩
    · obtain ⟨χ, hχ⟩ := exists_char β t
      have h1 := hi' χ t hχ
      rw [ht, epsV_zero, hx.zero, ← map_one (E.i _ hS)] at h1
      have h2 := E.i_inj _ _ h1
      apply epsV_inj
      rw [epsV_zero]
      funext j
      have := hχ j
      rw [h2] at this
      simpa using this
  refine splitEx_lift I _ _ ?_ (key (R ⧸ I) 0 fun t ht => Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using ht))
  ext i j
  refine IsHausdorff.haus (inferInstance : IsHausdorff I R) _ fun k => ?_
  have h1 := (key (R ⧸ I ^ (k + 1)) k fun t ht => Ideal.Quotient.eq_zero_iff_mem.2 ht).1
  rw [← Matrix.map_mul] at h1
  have h2 : (lin Q * lin J) i j ∈ I ^ (k + 1) := Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (congrFun h1 i) j)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact Ideal.pow_le_pow_right (Nat.le_succ k) h2

end GlobalTheory.ChF
end
end

section

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

section
variable {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {d : ℕ} (F : FGLaw R d)

private theorem kill_cc : ∀ (N : ℕ) (j : Fin d), MvPowerSeries.constantCoeff (mulF F.F N j) = 0
  | 0, j => by simp [mulF]
  | N + 1, j => by
    have h : ∀ q : Fin 2 × Fin d, MvPowerSeries.constantCoeff
        ((![mulF F.F N, pt R d 0] : Fin 2 → Pt R 1 d) q.1 q.2) = 0 := by
      rintro ⟨x, l⟩
      fin_cases x
      · exact kill_cc N l
      · simp [pt]
    exact MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero h) h (F.const j)

private theorem kill_X {n : ℕ} (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) (i : Fin n) (j : Fin d) :
    nv s (pt R d i j) a = a i j := by
  obtain ⟨ψ, h1, -, h3⟩ := (nv_calculus R S s n d a ha).1
  exact (h1 _).symm.trans (h3 (i, j))

private theorem kill_zero {n : ℕ} (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) :
    nv s (0 : PS R n d) a = 0 := by
  obtain ⟨ψ, h1, -, -⟩ := (nv_calculus R S s n d a ha).1
  exact (h1 _).symm.trans (map_zero ψ)

private theorem kill_one {a : Fin d → S} (ha : ∀ i, IsNilpotent (a i)) :
    ∀ i j, IsNilpotent ((![a] : Fin 1 → Fin d → S) i j) := fun i j => by
  fin_cases i; exact ha j

private theorem kill_two {a b : Fin d → S} (ha : ∀ i, IsNilpotent (a i)) (hb : ∀ i, IsNilpotent (b i)) :
    ∀ i j, IsNilpotent ((![a, b] : Fin 2 → Fin d → S) i j) := fun i j => by
  fin_cases i
  · exact ha j
  · exact hb j

private theorem kill_add {n : ℕ} (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) (x y : Pt R n d)
    (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0) (hy : ∀ j, MvPowerSeries.constantCoeff (y j) = 0)
    (f : PS R 2 d) : nv s (ev ![x, y] f) a = nv s f ![fun l => nv s (x l) a, fun l => nv s (y l) a] := by
  have := (nv_calculus R S s n d a ha).2.2.1 2 d ![x, y] f (fun i j => by
    fin_cases i
    · exact hx j
    · exact hy j)
  refine this.trans ?_
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem kill_succ {a : Fin d → S} (ha : ∀ i, IsNilpotent (a i)) (N : ℕ) (j : Fin d) :
    nv s (mulF F.F (N + 1) j) ![a] = nv s (F.F j) ![fun l => nv s (mulF F.F N l) ![a], a] := by
  refine (kill_add s ![a] (kill_one ha) _ _ (kill_cc F N) (fun l => by simp [pt]) (F.F j)).trans ?_
  congr 3
  funext l
  exact kill_X s ![a] (kill_one ha) 0 l

private theorem kill_unitL {c : Fin d → S} (hc : ∀ i, IsNilpotent (c i)) (j : Fin d) :
    nv s (F.F j) ![0, c] = c j := by
  have h := kill_add s ![c] (kill_one hc) 0 (pt R d 0) (fun l => by simp) (fun l => by simp [pt]) (F.F j)
  rw [F.unit j] at h
  have h1 : (fun l => nv s ((0 : Pt R 1 d) l) ![c]) = 0 := funext fun l => kill_zero s _ (kill_one hc)
  have h2 : (fun l => nv s (pt R d (0 : Fin 1) l) ![c]) = c := funext fun l => kill_X s _ (kill_one hc) 0 l
  rw [h1, h2] at h
  exact h.symm.trans (kill_X s _ (kill_one hc) 0 j)

private theorem kill_unitR {b : Fin d → S} (hb : ∀ i, IsNilpotent (b i)) (j : Fin d) :
    nv s (F.F j) ![b, 0] = b j := by
  have h0 := kill_two hb (fun _ => IsNilpotent.zero : ∀ i, IsNilpotent ((0 : Fin d → S) i))
  have h := kill_add s ![b, 0] h0 (pt R d 1) (pt R d 0) (fun l => by simp [pt]) (fun l => by simp [pt]) (F.F j)
  rw [F.comm j] at h
  have h1 : (fun l => nv s (pt R d (1 : Fin 2) l) ![b, 0]) = 0 := funext fun l => kill_X s _ h0 1 l
  have h2 : (fun l => nv s (pt R d (0 : Fin 2) l) ![b, 0]) = b := funext fun l => kill_X s _ h0 0 l
  rw [h1, h2] at h
  exact h.trans (kill_unitL s F hb j)

private theorem kill_sq (K : Ideal S) (hK : ∀ x ∈ K, ∀ y ∈ K, x * y = 0) {b c : Fin d → S}
    (hb : ∀ i, b i ∈ K) (hc : ∀ i, c i ∈ K) (j : Fin d) : nv s (F.F j) ![b, c] = b j + c j := by
  have hn : ∀ x ∈ K, IsNilpotent x := fun x hx => ⟨2, by rw [pow_two]; exact hK x hx x hx⟩
  have key : ∀ b c : Fin d → S, (∀ i, b i ∈ K) → (∀ i, c i ∈ K) → nv s (F.F j) ![b, c] =
      ∑ l, s (MvPowerSeries.coeff (Finsupp.single (0, l) 1) (F.F j)) * b l +
        ∑ l, s (MvPowerSeries.coeff (Finsupp.single (1, l) 1) (F.F j)) * c l := by
    intro b c hb hc
    have hm : ∀ i l, (![b, c] : Fin 2 → Fin d → S) i l ∈ K := fun i l => by
      fin_cases i
      · exact hb l
      · exact hc l
    rw [(nv_calculus R S s 2 d ![b, c] (fun i l => hn _ (hm i l))).2.2.2.2.2
      (fun _ _ _ _ => hK _ (hm _ _) _ (hm _ _)), F.const j, map_zero, zero_add, Fintype.sum_prod_type,
      Fin.sum_univ_two]
    rfl
  have h1 := key b 0 hb (fun _ => K.zero_mem)
  have h2 := key 0 c (fun _ => K.zero_mem) hc
  rw [kill_unitR s F (fun i => hn _ (hb i))] at h1
  rw [kill_unitL s F (fun i => hn _ (hc i))] at h2
  rw [key b c hb hc, h1, h2]
  simp

private theorem kill_sqN (K : Ideal S) (hK : ∀ x ∈ K, ∀ y ∈ K, x * y = 0) {c : Fin d → S}
    (hc : ∀ i, c i ∈ K) (N : ℕ) : ∀ j, nv s (mulF F.F N j) ![c] = (N : S) * c j := by
  have hn : ∀ i, IsNilpotent (c i) := fun i => ⟨2, by rw [pow_two]; exact hK _ (hc i) _ (hc i)⟩
  induction N with
  | zero => intro j; exact (kill_zero s ![c] (kill_one hn)).trans (by simp)
  | succ N ih =>
    intro j
    rw [kill_succ s F hn, funext ih, kill_sq s F K hK (fun i => K.mul_mem_left _ (hc i)) hc]
    push_cast
    ring

private theorem kill_lin (K : Ideal S) {c : Fin d → S} (hn : ∀ i, IsNilpotent (c i))
    (hc : ∀ i, c i ∈ K) (N : ℕ) (j : Fin d) : nv s (mulF F.F N j) ![c] - (N : S) * c j ∈ K * K := by
  let t := Ideal.Quotient.mk (K * K)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_mul, map_natCast]
  refine ((nv_calculus R S s 1 d ![c] (kill_one hn)).2.2.2.2.1 _ t _).trans ?_
  have h : (fun i l => t ((![c] : Fin 1 → Fin d → S) i l)) = ![fun l => t (c l)] := by
    funext i; fin_cases i; rfl
  rw [h]
  refine kill_sqN (t.comp s) F (K.map t) ?_ (fun i => Ideal.mem_map_of_mem t (hc i)) N j
  intro x hx y hy
  obtain ⟨x, hx', rfl⟩ := (Ideal.mem_map_iff_of_surjective t Ideal.Quotient.mk_surjective).1 hx
  obtain ⟨y, hy', rfl⟩ := (Ideal.mem_map_iff_of_surjective t Ideal.Quotient.mk_surjective).1 hy
  rw [← map_mul]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_mul hx' hy')

private theorem kill_nil {c : Fin d → S} (hn : ∀ i, IsNilpotent (c i)) (N : ℕ) (j : Fin d) :
    IsNilpotent (nv s (mulF F.F N j) ![c]) :=
  ((nv_calculus R S s 1 d ![c] (kill_one hn)).2.1 _ (kill_cc F N j)).1

end

theorem bxChart_nsmul_and_killed : ∀ (R₀ : Type) [CommRing R₀] (B : BX R₀) (O : LAlg R₀) (g : ℕ) (F : FGLaw (O : Type) g) (Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R), BXChart B O F.F Y → ∀ (p : ℕ) (R : LAlg R₀) (s : LHom O R) (a : Fin g → (R : Type)), IsNilpotent (p : (R : Type)) → (∀ i, IsNilpotent (a i)) → (∀ N : ℕ, N • Y R s a = Y R s (fun j => nv s.1.toRingHom (mulF F.F N j) ![a])) ∧ ∃ n : ℕ, p ^ (n + 1) • Y R s a = 0 := by
  intro R₀ _ B O g F Y hY p R s a hp ha
  have h1 : ∀ a : Fin g → (R : Type), (∀ i, IsNilpotent (a i)) → ∀ N : ℕ,
      N • Y R s a = Y R s (fun j => nv s.1.toRingHom (mulF F.F N j) ![a]) := by
    intro a ha N
    induction N with
    | zero =>
      rw [zero_nsmul, ← hY.zero R s]
      congr 1
      funext j
      exact (kill_zero _ ![a] (kill_one ha)).symm
    | succ N ih =>
      rw [succ_nsmul, ih, hY.law R s _ _ (kill_nil _ F ha N) ha]
      congr 1
      funext j
      exact (kill_succ _ F ha N j).symm
  refine ⟨h1 a ha, ?_⟩
  let J : Ideal (R : Type) := Ideal.span (insert (p : (R : Type)) (Set.range a))
  have hpJ : (p : (R : Type)) ∈ J := Ideal.subset_span (Set.mem_insert _ _)
  have h2 : ∀ k : ℕ, ∃ b : Fin g → (R : Type), (∀ i, IsNilpotent (b i)) ∧ (∀ i, b i ∈ J ^ (k + 1)) ∧
      p ^ k • Y R s a = Y R s b := by
    intro k
    induction k with
    | zero =>
      refine ⟨a, ha, fun i => ?_, by simp⟩
      rw [zero_add, pow_one]
      exact Ideal.subset_span (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
    | succ k ih =>
      obtain ⟨b, hb, hbJ, e⟩ := ih
      refine ⟨_, kill_nil _ F hb p, fun i => ?_, by rw [pow_succ', mul_smul, e, h1 b hb p]⟩
      have h3 := kill_lin s.1.toRingHom F (J ^ (k + 1)) hb hbJ p i
      rw [← pow_add] at h3
      have h4 : (p : (R : Type)) * b i ∈ J ^ (k + 1 + 1) := by
        rw [pow_succ' J (k + 1)]
        exact Ideal.mul_mem_mul hpJ (hbJ i)
      simpa using add_mem (Ideal.pow_le_pow_right (by omega : k + 1 + 1 ≤ k + 1 + (k + 1)) h3) h4
  have hfg : J.FG := Submodule.fg_span ((Set.finite_range a).insert _)
  have hle : J ≤ nilradical (R : Type) := by
    refine Ideal.span_le.2 ?_
    rintro _ (rfl | ⟨i, rfl⟩)
    · exact hp
    · exact ha i
  obtain ⟨n, hn⟩ := (Ideal.FG.isNilpotent_iff_le_nilradical hfg).2 hle
  obtain ⟨b, -, hbJ, e⟩ := h2 (n + 1)
  refine ⟨n, ?_⟩
  rw [e, ← hY.zero R s]
  congr 1
  funext i
  have := Ideal.pow_le_pow_right (by omega : n ≤ n + 1 + 1) (hbJ i)
  rw [hn] at this
  simpa using this

end GlobalTheory.ChF
end
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.JetProdSubst

theorem jetAt0_prod_subst : ∀ (C : Type) [Field C] (Orb : Type) [Fintype Orb] (σ : Orb → Type) [∀ o, Fintype (σ o)] (τ : Type) (e : ∀ o, σ o → τ), Function.Injective (fun x : (Σ o, σ o) => e x.1 x.2) → ∀ (P : ∀ o, MvPolynomial (σ o) C) (F : ∀ o, MvPowerSeries (σ o) C), jetAt0 (∏ o, MvPolynomial.rename (e o) (P o)) (∏ o, MvPowerSeries.subst (fun x : σ o => (MvPowerSeries.X (e o x) : MvPowerSeries τ C)) (F o)) = ∏ o, jetAt0 (P o) (F o) := by
  intro C _ Orb _ σ _ τ e he P F
  let e' : ∀ o, σ o ↪ τ := fun o => ⟨e o, fun x y h => by
    have h1 : (⟨o, x⟩ : Σ o, σ o) = ⟨o, y⟩ := he h
    simpa using h1⟩
  have hd : ∀ i j x y, e' i x = e' j y → i = j := fun i j x y h =>
    congrArg Sigma.fst (he (a₁ := ⟨i, x⟩) (a₂ := ⟨j, y⟩) h)
  rw [← GlobalTheory.JetProd.jetAt0_prod_rename e' hd]
  congr 1
  refine Finset.prod_congr rfl fun o _ => ?_
  rw [MvPowerSeries.rename_eq_subst]
  rfl

end GlobalTheory.JetProdSubst
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianFunctorNilChart_of_nilpotent_chart : ∀ (R₀ : Type) [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) → (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) → ∀ (O : LAlg R₀) (G' : Over (Spec (CommRingCat.of (O : Type)))) [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left), Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R₀ (O : Type)))) φ → ∀ (g : ℕ) (F : Fin g → PS (O : Type) 2 g) (X : Fam G' g), NilChart G' F X → ∃ Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R, BXChart B O F Y ∧ ∀ (f : G' ⟶ G') (α : Fin g → PS (O : Type) 1 g) (A : OEnd B O), Reads X X f α → (∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R) (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G'), x'.left ≫ φ = (e R x).left → (x' ≫ f).left ≫ φ = (e R (A.f s x)).left) → ∀ (R : LAlg R₀) (s : LHom O R) (a : Fin g → (R : Type)), (∀ i, IsNilpotent (a i)) → A.f s (Y R s a) = Y R s (fun j => nv s.1.toRingHom (α j) ![a]) := by
  first | exact @GlobalTheory.ChF.bxChart_of_nilChart | exact GlobalTheory.ChF.bxChart_of_nilChart | (intros; apply GlobalTheory.ChF.bxChart_of_nilChart <;> assumption)
end
